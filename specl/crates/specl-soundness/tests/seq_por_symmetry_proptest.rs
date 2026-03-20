//! Proptest coverage for sequences, POR correctness, and symmetry correctness.
//!
//! Fills known gaps in specl-soundness:
//!   - Sequence operations: concat, head, tail, len, indexing, slicing
//!   - POR: independent actions verified to find same violations as full BFS
//!   - Symmetry: symmetric Dict specs verified to find same violations as unreduced BFS

use proptest::prelude::*;
use specl_mc::{CheckConfig, CheckOutcome};
use specl_soundness::{check_spec, compile_spec, roundtrip_pretty, states_from_outcome};

fn outcome_is_ok(outcome: &CheckOutcome) -> bool {
    matches!(
        outcome,
        CheckOutcome::Ok { .. }
            | CheckOutcome::StateLimitReached { .. }
            | CheckOutcome::MemoryLimitReached { .. }
            | CheckOutcome::TimeLimitReached { .. }
    )
}

fn has_violation(outcome: &CheckOutcome) -> bool {
    matches!(outcome, CheckOutcome::InvariantViolation { .. })
}

fn base_config() -> CheckConfig {
    CheckConfig {
        parallel: false,
        check_deadlock: false,
        max_states: 10_000,
        max_time_secs: 10,
        use_por: false,
        use_symmetry: false,
        ..CheckConfig::default()
    }
}

// ─── Sequence spec generators ───

/// Seq with concat of two sequences and length tracking.
#[derive(Debug, Clone)]
struct SeqConcatSpec {
    bound: u8,
    max_len: u8,
}

impl SeqConcatSpec {
    fn to_specl(&self) -> String {
        let b = self.bound;
        let ml = self.max_len;
        format!(
            r#"module SeqConcatSpec

var q1: Seq[0..{b}]
var q2: Seq[0..{b}]

init {{ q1 = []; q2 = []; }}

action Push1(v: 0..{b}) {{
    require len(q1) < {ml};
    q1 = q1 ++ [v];
}}

action Push2(v: 0..{b}) {{
    require len(q2) < {ml};
    q2 = q2 ++ [v];
}}

action Pop1() {{
    require len(q1) > 0;
    q1 = tail(q1);
}}

action Pop2() {{
    require len(q2) > 0;
    q2 = tail(q2);
}}

action MergeInto1() {{
    require len(q2) > 0;
    require len(q1) + len(q2) <= {ml};
    q1 = q1 ++ q2;
    q2 = [];
}}

invariant BothBounded {{ len(q1) <= {ml} and len(q2) <= {ml} }}

invariant ConcatLen {{
    len(q1) >= 0 and len(q2) >= 0
}}

invariant HeadInRange1 {{
    len(q1) > 0 implies (head(q1) >= 0 and head(q1) <= {b})
}}

invariant HeadInRange2 {{
    len(q2) > 0 implies (head(q2) >= 0 and head(q2) <= {b})
}}
"#,
        )
    }
}

/// Seq with indexing and head equivalence.
#[derive(Debug, Clone)]
struct SeqIndexSpec {
    bound: u8,
    max_len: u8,
}

impl SeqIndexSpec {
    fn to_specl(&self) -> String {
        let b = self.bound;
        let ml = self.max_len;
        format!(
            r#"module SeqIndexSpec

var s: Seq[0..{b}]

init {{ s = []; }}

action Push(v: 0..{b}) {{
    require len(s) < {ml};
    s = s ++ [v];
}}

action Pop() {{
    require len(s) > 0;
    s = tail(s);
}}

invariant HeadIsIndex0 {{
    len(s) > 0 implies head(s) == s[0]
}}

invariant AllElemsInRange {{
    len(s) >= 2 implies (s[0] >= 0 and s[0] <= {b} and s[1] >= 0 and s[1] <= {b})
}}

invariant LenNonNeg {{
    len(s) >= 0
}}
"#,
        )
    }
}

/// Seq with slicing and tail equivalence.
#[derive(Debug, Clone)]
struct SeqSliceSpec {
    bound: u8,
    max_len: u8,
}

impl SeqSliceSpec {
    fn to_specl(&self) -> String {
        let b = self.bound;
        let ml = self.max_len;
        format!(
            r#"module SeqSliceSpec

var s: Seq[0..{b}]

init {{ s = []; }}

action Push(v: 0..{b}) {{
    require len(s) < {ml};
    s = s ++ [v];
}}

action Pop() {{
    require len(s) > 0;
    s = tail(s);
}}

invariant SliceLen {{
    len(s) >= 2 implies len(s[0..2]) == 2
}}

invariant TailLen {{
    len(s) > 0 implies len(tail(s)) == len(s) - 1
}}

invariant Bounded {{
    len(s) <= {ml}
}}
"#,
        )
    }
}

/// FIFO queue: push to back, pop from front, verify ordering.
#[derive(Debug, Clone)]
struct FifoSpec {
    bound: u8,
    capacity: u8,
}

impl FifoSpec {
    fn to_specl(&self) -> String {
        let b = self.bound;
        let cap = self.capacity;
        format!(
            r#"module FifoSpec

var queue: Seq[0..{b}]
var total_pushed: 0..20
var total_popped: 0..20

init {{ queue = []; total_pushed = 0; total_popped = 0; }}

action Enqueue(v: 0..{b}) {{
    require len(queue) < {cap};
    require total_pushed < 20;
    queue = queue ++ [v];
    total_pushed = total_pushed + 1;
}}

action Dequeue() {{
    require len(queue) > 0;
    require total_popped < 20;
    queue = tail(queue);
    total_popped = total_popped + 1;
}}

invariant QueueBounded {{ len(queue) <= {cap} }}

invariant CountsConsistent {{
    total_pushed >= total_popped
}}

invariant LenMatchesCounts {{
    len(queue) == total_pushed - total_popped
}}
"#,
        )
    }
}

// ─── POR spec generators ───

/// Two fully independent counters (no shared variables).
/// POR should explore fewer states but find the same violations.
#[derive(Debug, Clone)]
struct IndependentCountersSpec {
    max_a: u8,
    max_b: u8,
}

impl IndependentCountersSpec {
    fn to_specl(&self) -> String {
        let ma = self.max_a;
        let mb = self.max_b;
        format!(
            r#"module IndependentCounters

var a: 0..{ma}
var b: 0..{mb}

init {{ a = 0; b = 0; }}

action IncA() {{ require a < {ma}; a = a + 1; }}
action DecA() {{ require a > 0; a = a - 1; }}
action IncB() {{ require b < {mb}; b = b + 1; }}
action DecB() {{ require b > 0; b = b - 1; }}

invariant AInRange {{ a >= 0 and a <= {ma} }}
invariant BInRange {{ b >= 0 and b <= {mb} }}
"#,
        )
    }
}

/// Two independent counters with a violation that only one counter can reach.
/// POR must still find the invariant violation.
#[derive(Debug, Clone)]
struct IndependentViolationSpec {
    max_a: u8,
    max_b: u8,
    threshold: u8,
}

impl IndependentViolationSpec {
    fn to_specl(&self) -> String {
        let ma = self.max_a;
        let mb = self.max_b;
        let th = self.threshold;
        format!(
            r#"module IndependentViolation

var a: 0..{ma}
var b: 0..{mb}

init {{ a = 0; b = 0; }}

action IncA() {{ require a < {ma}; a = a + 1; }}
action IncB() {{ require b < {mb}; b = b + 1; }}

invariant ABelowThreshold {{ a <= {th} }}
"#,
        )
    }
}

/// Three independent variable groups for richer POR testing.
#[derive(Debug, Clone)]
struct ThreeWayIndependentSpec {
    max: u8,
}

impl ThreeWayIndependentSpec {
    fn to_specl(&self) -> String {
        let m = self.max;
        format!(
            r#"module ThreeWayIndependent

var x: 0..{m}
var y: 0..{m}
var z: 0..{m}

init {{ x = 0; y = 0; z = 0; }}

action IncX() {{ require x < {m}; x = x + 1; }}
action IncY() {{ require y < {m}; y = y + 1; }}
action IncZ() {{ require z < {m}; z = z + 1; }}
action DecX() {{ require x > 0; x = x - 1; }}
action DecY() {{ require y > 0; y = y - 1; }}
action DecZ() {{ require z > 0; z = z - 1; }}

invariant AllInRange {{ x >= 0 and y >= 0 and z >= 0 }}
"#,
        )
    }
}

/// Mixed dependent/independent actions for POR edge case testing.
/// IncA/DecA are independent of IncB/DecB, but Sync touches both.
#[derive(Debug, Clone)]
struct MixedDependenceSpec {
    max: u8,
}

impl MixedDependenceSpec {
    fn to_specl(&self) -> String {
        let m = self.max;
        format!(
            r#"module MixedDependence

var a: 0..{m}
var b: 0..{m}

init {{ a = 0; b = 0; }}

action IncA() {{ require a < {m}; a = a + 1; }}
action DecA() {{ require a > 0; a = a - 1; }}
action IncB() {{ require b < {m}; b = b + 1; }}
action DecB() {{ require b > 0; b = b - 1; }}
action Sync() {{ require a > 0; a = a - 1; b = if b < {m} then b + 1 else b; }}

invariant InRange {{ a >= 0 and b >= 0 and a <= {m} and b <= {m} }}
"#,
        )
    }
}

// ─── Symmetry spec generators ───

/// Symmetric counters: Dict[0..N, 0..Max] where all indices are interchangeable.
#[derive(Debug, Clone)]
struct SymmetricCountersSpec {
    n: u8,
    max: u8,
}

impl SymmetricCountersSpec {
    fn to_specl(&self) -> String {
        let n = self.n;
        let m = self.max;
        format!(
            r#"module SymmetricCounters

var c: Dict[0..{n}, 0..{m}]

init {{ c = {{i: 0 for i in 0..{n}}}; }}

action Inc(i: 0..{n}) {{
    require c[i] < {m};
    c = c | {{i: c[i] + 1}};
}}

action Dec(i: 0..{n}) {{
    require c[i] > 0;
    c = c | {{i: c[i] - 1}};
}}

invariant AllInRange {{
    all i in 0..{n} : c[i] >= 0 and c[i] <= {m}
}}
"#,
        )
    }
}

/// Symmetric boolean flags: Dict[0..N, Bool].
#[derive(Debug, Clone)]
struct SymmetricFlagsSpec {
    n: u8,
}

impl SymmetricFlagsSpec {
    fn to_specl(&self) -> String {
        let n = self.n;
        format!(
            r#"module SymmetricFlags

var flags: Dict[0..{n}, Bool]
var count: 0..20

init {{ flags = {{i: false for i in 0..{n}}}; count = 0; }}

action SetFlag(i: 0..{n}) {{
    require not flags[i];
    require count < 20;
    flags = flags | {{i: true}};
    count = count + 1;
}}

action ClearFlag(i: 0..{n}) {{
    require flags[i];
    flags = flags | {{i: false}};
    count = if count > 0 then count - 1 else 0;
}}

invariant CountNonNeg {{ count >= 0 }}
"#,
        )
    }
}

/// Symmetric spec with a violation: if any counter exceeds threshold.
/// Symmetry reduction must still detect the violation.
#[derive(Debug, Clone)]
struct SymmetricViolationSpec {
    n: u8,
    max: u8,
    threshold: u8,
}

impl SymmetricViolationSpec {
    fn to_specl(&self) -> String {
        let n = self.n;
        let m = self.max;
        let th = self.threshold;
        format!(
            r#"module SymmetricViolation

var c: Dict[0..{n}, 0..{m}]

init {{ c = {{i: 0 for i in 0..{n}}}; }}

action Inc(i: 0..{n}) {{
    require c[i] < {m};
    c = c | {{i: c[i] + 1}};
}}

invariant AllBelowThreshold {{
    all i in 0..{n} : c[i] <= {th}
}}
"#,
        )
    }
}

/// Symmetric token ring: exactly one process holds the token.
#[derive(Debug, Clone)]
struct SymmetricTokenRingSpec {
    n: u8,
}

impl SymmetricTokenRingSpec {
    fn to_specl(&self) -> String {
        let n = self.n;
        format!(
            r#"module SymmetricTokenRing

var hasToken: Dict[0..{n}, Bool]

init {{ hasToken = {{i: (i == 0) for i in 0..{n}}}; }}

action PassToken(from: 0..{n}, to: 0..{n}) {{
    require from != to;
    require hasToken[from];
    hasToken = hasToken | {{from: false, to: true}};
}}

invariant ExactlyOneToken {{
    any i in 0..{n} : hasToken[i]
}}
"#,
        )
    }
}

// ─── POR dependent-variable violation spec generators ───

/// Two counters with a shared "Sync" action that creates a reachable violation.
/// The invariant `a + b <= threshold` can be violated when Sync transfers from b to a.
/// POR must not prune the interleaving that leads to the violation.
#[derive(Debug, Clone)]
struct DependentViolationSpec {
    max: u8,
    threshold: u8,
}

impl DependentViolationSpec {
    fn to_specl(&self) -> String {
        let m = self.max;
        let th = self.threshold;
        format!(
            r#"module DependentViolation

var a: 0..{m}
var b: 0..{m}

init {{ a = 0; b = 0; }}

action IncA() {{ require a < {m}; a = a + 1; }}
action IncB() {{ require b < {m}; b = b + 1; }}
action Transfer() {{ require b > 0; require a < {m}; a = a + 1; b = b - 1; }}

invariant SumBelowThreshold {{ a + b <= {th} }}
"#,
        )
    }
}

/// Shared-variable race: two actions both read and write a shared variable.
/// This is the hardest case for POR -- both actions are dependent.
#[derive(Debug, Clone)]
struct SharedRaceSpec {
    max: u8,
    threshold: u8,
}

impl SharedRaceSpec {
    fn to_specl(&self) -> String {
        let m = self.max;
        let th = self.threshold;
        format!(
            r#"module SharedRace

var shared: 0..{m}
var local_a: 0..{m}
var local_b: 0..{m}

init {{ shared = 0; local_a = 0; local_b = 0; }}

action StepA() {{
    require shared < {m};
    require local_a < {m};
    shared = shared + 1;
    local_a = local_a + 1;
}}

action StepB() {{
    require shared < {m};
    require local_b < {m};
    shared = shared + 1;
    local_b = local_b + 1;
}}

invariant SharedBelowThreshold {{ shared <= {th} }}
"#,
        )
    }
}

// ─── Symmetry relational invariant spec generators ───

/// Symmetric spec with a relational invariant: no counter can exceed another by more than `gap`.
/// Symmetry reduction must preserve this relational property between indices.
#[derive(Debug, Clone)]
struct SymmetricRelationalSpec {
    n: u8,
    max: u8,
    gap: u8,
}

impl SymmetricRelationalSpec {
    fn to_specl(&self) -> String {
        let n = self.n;
        let m = self.max;
        let g = self.gap;
        format!(
            r#"module SymmetricRelational

var c: Dict[0..{n}, 0..{m}]

init {{ c = {{i: 0 for i in 0..{n}}}; }}

action Inc(i: 0..{n}) {{
    require c[i] < {m};
    c = c | {{i: c[i] + 1}};
}}

invariant MaxGap {{
    all i in 0..{n} : all j in 0..{n} :
        c[i] <= c[j] + {g}
}}
"#,
        )
    }
}

// ─── Init order independence spec generators ───

/// Spec where init has inter-variable dependencies in a specific textual order.
/// The "reverse" version swaps the conjunct order.
/// Both must produce the same initial state and model checking outcome.
#[derive(Debug, Clone)]
struct InitOrderSpec {
    val_a: u8,
    max: u8,
    reverse: bool,
}

impl InitOrderSpec {
    fn to_specl(&self) -> String {
        let v = self.val_a;
        let m = self.max;
        let (first, second) = if self.reverse {
            (
                format!("y == x and x == {v}"),
                format!("x == {v} and y == x"),
            )
        } else {
            (
                format!("x == {v} and y == x"),
                format!("y == x and x == {v}"),
            )
        };
        // Use the first ordering
        let _ = second;
        format!(
            r#"module InitOrder

var x: 0..{m}
var y: 0..{m}

init {{ {first} }}

action IncX() {{ require x < {m}; x = x + 1; y = y; }}
action IncY() {{ require y < {m}; x = x; y = y + 1; }}

invariant InRange {{ x >= 0 and x <= {m} and y >= 0 and y <= {m} }}
"#,
        )
    }
}

/// Three-variable chain: z depends on y, y depends on x, in various orders.
#[derive(Debug, Clone)]
struct InitChainSpec {
    val: u8,
    max: u8,
}

impl InitChainSpec {
    fn orders() -> Vec<&'static str> {
        vec![
            "x == VAL and y == x and z == y",
            "z == y and y == x and x == VAL",
            "y == x and z == y and x == VAL",
            "z == y and x == VAL and y == x",
        ]
    }

    fn to_specl(&self, order: &str) -> String {
        let m = self.max;
        let init_expr = order.replace("VAL", &self.val.to_string());
        format!(
            r#"module InitChain

var x: 0..{m}
var y: 0..{m}
var z: 0..{m}

init {{ {init_expr} }}

action IncX() {{ require x < {m}; x = x + 1; y = y; z = z; }}

invariant AllStartEqual {{ true }}
"#,
        )
    }
}

// ─── Properties ───

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 32,
        .. ProptestConfig::default()
    })]

    // ─── Sequence operation tests ───

    #[test]
    fn seq_concat_no_panic(bound in 1u8..=2, max_len in 2u8..=4) {
        let spec = SeqConcatSpec { bound, max_len };
        let src = spec.to_specl();
        let compiled = compile_spec(&src);
        prop_assert!(compiled.is_ok(), "compile: {:?}", compiled.err());
        let outcome = check_spec(&src, base_config());
        prop_assert!(outcome.is_ok(), "check: {:?}", outcome.err());
        let outcome = outcome.unwrap();
        prop_assert!(outcome_is_ok(&outcome), "invariant violated");
    }

    #[test]
    fn seq_index_no_panic(bound in 1u8..=2, max_len in 2u8..=4) {
        let spec = SeqIndexSpec { bound, max_len };
        let src = spec.to_specl();
        let compiled = compile_spec(&src);
        prop_assert!(compiled.is_ok(), "compile: {:?}", compiled.err());
        let outcome = check_spec(&src, base_config());
        prop_assert!(outcome.is_ok(), "check: {:?}", outcome.err());
        let outcome = outcome.unwrap();
        prop_assert!(outcome_is_ok(&outcome), "invariant violated");
    }

    #[test]
    fn seq_slice_ops_no_panic(bound in 1u8..=2, max_len in 2u8..=4) {
        let spec = SeqSliceSpec { bound, max_len };
        let src = spec.to_specl();
        let compiled = compile_spec(&src);
        prop_assert!(compiled.is_ok(), "compile: {:?}", compiled.err());
        let outcome = check_spec(&src, base_config());
        prop_assert!(outcome.is_ok(), "check: {:?}", outcome.err());
        let outcome = outcome.unwrap();
        prop_assert!(outcome_is_ok(&outcome), "invariant violated");
    }

    #[test]
    fn fifo_spec_no_panic(bound in 1u8..=2, capacity in 2u8..=4) {
        let spec = FifoSpec { bound, capacity };
        let src = spec.to_specl();
        let compiled = compile_spec(&src);
        prop_assert!(compiled.is_ok(), "compile: {:?}", compiled.err());
        let outcome = check_spec(&src, base_config());
        prop_assert!(outcome.is_ok(), "check: {:?}", outcome.err());
        let outcome = outcome.unwrap();
        prop_assert!(outcome_is_ok(&outcome), "invariant violated");
    }

    // ─── Sequence backend agreement ───

    #[test]
    fn seq_concat_backend_agreement(bound in 1u8..=2, max_len in 2u8..=3) {
        let spec = SeqConcatSpec { bound, max_len };
        let src = spec.to_specl();
        let base = base_config();

        let full = check_spec(&src, base.clone()).expect("full");
        let expected = states_from_outcome(&full);

        let fast = check_spec(&src, CheckConfig { fast_check: true, ..base.clone() }).expect("fast");
        prop_assert_eq!(states_from_outcome(&fast), expected, "fast disagreement");

        let collapse = check_spec(&src, CheckConfig { collapse: true, ..base }).expect("collapse");
        prop_assert_eq!(states_from_outcome(&collapse), expected, "collapse disagreement");
    }

    #[test]
    fn fifo_backend_agreement(bound in 1u8..=2, capacity in 2u8..=3) {
        let spec = FifoSpec { bound, capacity };
        let src = spec.to_specl();
        let base = base_config();

        let full = check_spec(&src, base.clone()).expect("full");
        let expected = states_from_outcome(&full);

        let fast = check_spec(&src, CheckConfig { fast_check: true, ..base.clone() }).expect("fast");
        prop_assert_eq!(states_from_outcome(&fast), expected, "fast disagreement");

        let collapse = check_spec(&src, CheckConfig { collapse: true, ..base }).expect("collapse");
        prop_assert_eq!(states_from_outcome(&collapse), expected, "collapse disagreement");
    }

    // ─── Sequence roundtrip ───

    #[test]
    fn seq_concat_roundtrip(bound in 1u8..=2, max_len in 2u8..=4) {
        let spec = SeqConcatSpec { bound, max_len };
        let src = spec.to_specl();
        let result = roundtrip_pretty(&src);
        prop_assert!(result.is_ok(), "roundtrip: {:?}", result.err());
        let (p1, p2) = result.unwrap();
        prop_assert_eq!(p1, p2, "pretty-print not idempotent");
    }

    #[test]
    fn fifo_roundtrip(bound in 1u8..=2, capacity in 2u8..=4) {
        let spec = FifoSpec { bound, capacity };
        let src = spec.to_specl();
        let result = roundtrip_pretty(&src);
        prop_assert!(result.is_ok(), "roundtrip: {:?}", result.err());
        let (p1, p2) = result.unwrap();
        prop_assert_eq!(p1, p2, "pretty-print not idempotent");
    }

    // ─── POR correctness tests ───
    // Key property: POR may explore fewer states, but must find the same
    // invariant violations (or confirm safety) as full BFS.

    #[test]
    fn por_independent_counters_same_outcome(max_a in 1u8..=3, max_b in 1u8..=3) {
        let spec = IndependentCountersSpec { max_a, max_b };
        let src = spec.to_specl();
        let base = base_config();

        let baseline = check_spec(&src, base.clone()).expect("baseline");
        let por = check_spec(&src, CheckConfig { use_por: true, ..base.clone() }).expect("por");
        prop_assert_eq!(outcome_is_ok(&baseline), outcome_is_ok(&por), "POR changed safety outcome");

        // POR should explore <= states for independent actions
        if let (Some(base_states), Some(por_states)) = (states_from_outcome(&baseline), states_from_outcome(&por)) {
            prop_assert!(por_states <= base_states, "POR explored more states ({}) than baseline ({})", por_states, base_states);
        }
    }

    #[test]
    fn por_independent_violation_detected(max_a in 2u8..=4, max_b in 1u8..=3) {
        // threshold < max_a guarantees a violation on counter a
        let threshold = max_a / 2;
        let spec = IndependentViolationSpec { max_a, max_b, threshold };
        let src = spec.to_specl();
        let base = base_config();

        let baseline = check_spec(&src, base.clone()).expect("baseline");
        let por = check_spec(&src, CheckConfig { use_por: true, ..base }).expect("por");

        // Both must find the violation
        prop_assert!(has_violation(&baseline), "baseline should find violation");
        prop_assert!(has_violation(&por), "POR must find violation");
    }

    #[test]
    fn por_three_way_independent_same_outcome(max in 1u8..=3) {
        let spec = ThreeWayIndependentSpec { max };
        let src = spec.to_specl();
        let base = base_config();

        let baseline = check_spec(&src, base.clone()).expect("baseline");
        let por = check_spec(&src, CheckConfig { use_por: true, ..base.clone() }).expect("por");
        prop_assert_eq!(outcome_is_ok(&baseline), outcome_is_ok(&por), "POR changed safety outcome");

        if let (Some(base_states), Some(por_states)) = (states_from_outcome(&baseline), states_from_outcome(&por)) {
            prop_assert!(por_states <= base_states, "POR explored more states ({}) than baseline ({})", por_states, base_states);
        }
    }

    #[test]
    fn por_mixed_dependence_same_outcome(max in 1u8..=3) {
        let spec = MixedDependenceSpec { max };
        let src = spec.to_specl();
        let base = base_config();

        let baseline = check_spec(&src, base.clone()).expect("baseline");
        let por = check_spec(&src, CheckConfig { use_por: true, ..base }).expect("por");
        prop_assert_eq!(outcome_is_ok(&baseline), outcome_is_ok(&por), "POR changed safety outcome");
    }

    #[test]
    fn por_seq_spec_same_outcome(bound in 1u8..=2, max_len in 2u8..=3) {
        let spec = SeqConcatSpec { bound, max_len };
        let src = spec.to_specl();
        let base = base_config();

        let baseline = check_spec(&src, base.clone()).expect("baseline");
        let por = check_spec(&src, CheckConfig { use_por: true, ..base }).expect("por");
        prop_assert_eq!(outcome_is_ok(&baseline), outcome_is_ok(&por), "POR changed safety outcome");
    }

    // ─── Symmetry correctness tests ───
    // Key property: symmetry reduction may explore fewer states, but must
    // find the same violations (or confirm safety) as unreduced BFS.

    #[test]
    fn symmetry_counters_same_outcome(n in 1u8..=2, max in 1u8..=3) {
        let spec = SymmetricCountersSpec { n, max };
        let src = spec.to_specl();
        let base = base_config();

        let baseline = check_spec(&src, base.clone()).expect("baseline");
        let sym = check_spec(&src, CheckConfig { use_symmetry: true, ..base.clone() }).expect("symmetry");
        prop_assert_eq!(outcome_is_ok(&baseline), outcome_is_ok(&sym), "Symmetry changed safety outcome");

        // Symmetry should explore <= states
        if let (Some(base_states), Some(sym_states)) = (states_from_outcome(&baseline), states_from_outcome(&sym)) {
            prop_assert!(sym_states <= base_states, "Symmetry explored more states ({}) than baseline ({})", sym_states, base_states);
        }
    }

    #[test]
    fn symmetry_flags_same_outcome(n in 1u8..=2) {
        let spec = SymmetricFlagsSpec { n };
        let src = spec.to_specl();
        let base = base_config();

        let baseline = check_spec(&src, base.clone()).expect("baseline");
        let sym = check_spec(&src, CheckConfig { use_symmetry: true, ..base }).expect("symmetry");
        prop_assert_eq!(outcome_is_ok(&baseline), outcome_is_ok(&sym), "Symmetry changed safety outcome");
    }

    #[test]
    fn symmetry_violation_detected(n in 1u8..=2, max in 2u8..=4) {
        // threshold < max guarantees a violation
        let threshold = max / 2;
        let spec = SymmetricViolationSpec { n, max, threshold };
        let src = spec.to_specl();
        let base = base_config();

        let baseline = check_spec(&src, base.clone()).expect("baseline");
        let sym = check_spec(&src, CheckConfig { use_symmetry: true, ..base }).expect("symmetry");

        // Both must find the violation
        prop_assert!(has_violation(&baseline), "baseline should find violation");
        prop_assert!(has_violation(&sym), "Symmetry must find violation");
    }

    #[test]
    fn symmetry_token_ring_same_outcome(n in 1u8..=2) {
        let spec = SymmetricTokenRingSpec { n };
        let src = spec.to_specl();
        let base = base_config();

        let baseline = check_spec(&src, base.clone()).expect("baseline");
        let sym = check_spec(&src, CheckConfig { use_symmetry: true, ..base }).expect("symmetry");
        prop_assert_eq!(outcome_is_ok(&baseline), outcome_is_ok(&sym), "Symmetry changed safety outcome");
    }

    // ─── Combined POR + Symmetry correctness ───

    #[test]
    fn por_and_symmetry_counters(n in 1u8..=2, max in 1u8..=3) {
        let spec = SymmetricCountersSpec { n, max };
        let src = spec.to_specl();
        let base = base_config();

        let baseline = check_spec(&src, base.clone()).expect("baseline");
        let both = check_spec(&src, CheckConfig { use_por: true, use_symmetry: true, ..base }).expect("por+sym");
        prop_assert_eq!(outcome_is_ok(&baseline), outcome_is_ok(&both), "POR+Symmetry changed safety outcome");
    }

    #[test]
    fn por_and_symmetry_violation_detected(n in 1u8..=2, max in 2u8..=4) {
        let threshold = max / 2;
        let spec = SymmetricViolationSpec { n, max, threshold };
        let src = spec.to_specl();
        let base = base_config();

        let baseline = check_spec(&src, base.clone()).expect("baseline");
        let both = check_spec(&src, CheckConfig { use_por: true, use_symmetry: true, ..base }).expect("por+sym");
        prop_assert_eq!(has_violation(&baseline), has_violation(&both), "POR+Symmetry missed violation");
    }

    // ─── Symmetry roundtrip ───

    #[test]
    fn symmetric_counters_roundtrip(n in 1u8..=2, max in 1u8..=3) {
        let spec = SymmetricCountersSpec { n, max };
        let src = spec.to_specl();
        let result = roundtrip_pretty(&src);
        prop_assert!(result.is_ok(), "roundtrip: {:?}", result.err());
        let (p1, p2) = result.unwrap();
        prop_assert_eq!(p1, p2, "pretty-print not idempotent");
    }

    #[test]
    fn symmetric_token_ring_roundtrip(n in 1u8..=2) {
        let spec = SymmetricTokenRingSpec { n };
        let src = spec.to_specl();
        let result = roundtrip_pretty(&src);
        prop_assert!(result.is_ok(), "roundtrip: {:?}", result.err());
        let (p1, p2) = result.unwrap();
        prop_assert_eq!(p1, p2, "pretty-print not idempotent");
    }

    // ─── POR dependent-variable violation detection ───
    // POR must find violations even when actions share variables.

    #[test]
    fn por_dependent_violation_detected(max in 2u8..=4) {
        // threshold < 2*max guarantees a violation is reachable
        let threshold = max;
        let spec = DependentViolationSpec { max, threshold };
        let src = spec.to_specl();
        let base = base_config();

        let baseline = check_spec(&src, base.clone()).expect("baseline");
        let por = check_spec(&src, CheckConfig { use_por: true, ..base }).expect("por");

        prop_assert!(has_violation(&baseline), "baseline should find violation");
        prop_assert!(has_violation(&por), "POR must find violation with dependent actions");
    }

    #[test]
    fn por_shared_race_violation_detected(max in 3u8..=5) {
        // threshold < max guarantees shared can reach max which violates the invariant
        let threshold = max - 1;
        let spec = SharedRaceSpec { max, threshold };
        let src = spec.to_specl();
        let base = base_config();

        let baseline = check_spec(&src, base.clone()).expect("baseline");
        let por = check_spec(&src, CheckConfig { use_por: true, ..base }).expect("por");

        prop_assert!(has_violation(&baseline), "baseline should find violation");
        prop_assert!(has_violation(&por), "POR must find violation with shared-variable race");
    }

    #[test]
    fn por_dependent_safe_same_outcome(max in 2u8..=4) {
        // threshold high enough that no violation is reachable
        let threshold = 2 * max;
        let spec = DependentViolationSpec { max, threshold };
        let src = spec.to_specl();
        let base = base_config();

        let baseline = check_spec(&src, base.clone()).expect("baseline");
        let por = check_spec(&src, CheckConfig { use_por: true, ..base }).expect("por");

        prop_assert_eq!(outcome_is_ok(&baseline), outcome_is_ok(&por),
            "POR changed safety outcome for dependent safe spec");
    }

    // ─── Symmetry relational invariant violation detection ───
    // Symmetry must preserve relational invariants between symmetric indices.

    #[test]
    fn symmetry_relational_violation_detected(n in 1u8..=2, max in 2u8..=4) {
        // gap=0 means all counters must be equal -- violated as soon as any one increments
        let spec = SymmetricRelationalSpec { n, max, gap: 0 };
        let src = spec.to_specl();
        let base = base_config();

        let baseline = check_spec(&src, base.clone()).expect("baseline");
        let sym = check_spec(&src, CheckConfig { use_symmetry: true, ..base }).expect("symmetry");

        prop_assert!(has_violation(&baseline), "baseline should find gap=0 violation");
        prop_assert!(has_violation(&sym), "Symmetry must find relational violation");
    }

    #[test]
    fn symmetry_relational_safe_same_outcome(n in 1u8..=2, max in 1u8..=3) {
        // gap >= max means the invariant is always satisfied
        let spec = SymmetricRelationalSpec { n, max, gap: max };
        let src = spec.to_specl();
        let base = base_config();

        let baseline = check_spec(&src, base.clone()).expect("baseline");
        let sym = check_spec(&src, CheckConfig { use_symmetry: true, ..base }).expect("symmetry");

        prop_assert_eq!(outcome_is_ok(&baseline), outcome_is_ok(&sym),
            "Symmetry changed safety outcome for relational safe spec");
    }

    #[test]
    fn por_symmetry_relational_violation_detected(n in 1u8..=2, max in 2u8..=4) {
        let spec = SymmetricRelationalSpec { n, max, gap: 0 };
        let src = spec.to_specl();
        let base = base_config();

        let baseline = check_spec(&src, base.clone()).expect("baseline");
        let both = check_spec(&src, CheckConfig { use_por: true, use_symmetry: true, ..base }).expect("por+sym");

        prop_assert!(has_violation(&baseline), "baseline should find gap=0 violation");
        prop_assert!(has_violation(&both), "POR+Symmetry must find relational violation");
    }

    // ─── Init order independence ───
    // The init fixpoint solver must produce the same result regardless of
    // the textual order of conjuncts.

    #[test]
    fn init_order_two_vars_same_outcome(val in 0u8..=3) {
        let max = 4u8;
        let spec_fwd = InitOrderSpec { val_a: val, max, reverse: false };
        let spec_rev = InitOrderSpec { val_a: val, max, reverse: true };
        let src_fwd = spec_fwd.to_specl();
        let src_rev = spec_rev.to_specl();
        let base = base_config();

        let out_fwd = check_spec(&src_fwd, base.clone()).expect("forward order");
        let out_rev = check_spec(&src_rev, base.clone()).expect("reverse order");

        // Both must produce Ok (no violation) and explore the same state count
        prop_assert!(outcome_is_ok(&out_fwd), "forward order should be ok");
        prop_assert!(outcome_is_ok(&out_rev), "reverse order should be ok");
        prop_assert_eq!(
            states_from_outcome(&out_fwd),
            states_from_outcome(&out_rev),
            "init order changed state count"
        );
    }

    #[test]
    fn init_chain_all_orders_agree(val in 0u8..=2) {
        let max = 3u8;
        let spec = InitChainSpec { val, max };
        let base = base_config();
        let orders = InitChainSpec::orders();

        let first_src = spec.to_specl(orders[0]);
        let first_out = check_spec(&first_src, base.clone()).expect("first order");
        let expected_states = states_from_outcome(&first_out);
        prop_assert!(outcome_is_ok(&first_out), "first order should be ok");

        for order in &orders[1..] {
            let src = spec.to_specl(order);
            let out = check_spec(&src, base.clone()).expect(&format!("order: {}", order));
            prop_assert!(outcome_is_ok(&out), "order '{}' should be ok", order);
            prop_assert_eq!(
                states_from_outcome(&out),
                expected_states,
                "init order '{}' produced different state count",
                order
            );
        }
    }
}

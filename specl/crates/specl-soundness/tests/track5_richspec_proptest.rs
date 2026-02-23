//! Track 5: Rich spec generation for parser/type-checker/evaluator robustness.
//!
//! Generates random specl programs exercising language features that the
//! existing MiniSpec generator does not cover: sets, dicts, quantifiers,
//! functions, let-bindings, if-then-else, comprehensions, membership tests,
//! sequences, tuples, fix expressions, iff, subset_of, intersect, powerset.
//!
//! Properties tested:
//!   1. Parse never panics (returns Ok or Err, no crash)
//!   2. Type-check never panics on parsed specs
//!   3. Pretty-print roundtrip: parse(pretty(parse(s))) idempotent
//!   4. Backend agreement on well-typed specs
//!   5. Evaluation never panics on well-typed, checked specs

use proptest::prelude::*;
use specl_mc::CheckConfig;
use specl_soundness::{check_spec, compile_spec, roundtrip_pretty, states_from_outcome};

// ─── Expression generators ───

/// Generate a random expression string at a given depth.
fn expr_strategy(vars: Vec<String>, depth: u32) -> BoxedStrategy<String> {
    let leaf = {
        let vars = vars.clone();
        prop_oneof![
            (0i64..=5).prop_map(|n| n.to_string()),
            prop::sample::select(vars).prop_map(|v| v.to_string()),
            prop::bool::ANY.prop_map(|b| if b { "true".into() } else { "false".into() }),
        ]
    }
    .boxed();

    if depth == 0 {
        return leaf;
    }

    let v = vars.clone();
    prop_oneof![
        10 => leaf,
        // Binary arithmetic
        3 => {
            let v = v.clone();
            (expr_strategy(v.clone(), depth - 1), prop::sample::select(vec!["+".to_string(), "-".into()]), expr_strategy(v, depth - 1))
                .prop_map(|(l, op, r)| format!("({l} {op} {r})"))
        },
        // Comparison
        3 => {
            let v = v.clone();
            (expr_strategy(v.clone(), depth - 1), prop::sample::select(vec!["==".to_string(), "!=".into(), "<".into(), "<=".into(), ">".into(), ">=".into()]), expr_strategy(v, depth - 1))
                .prop_map(|(l, op, r)| format!("({l} {op} {r})"))
        },
        // Boolean operators
        3 => {
            let v = v.clone();
            (expr_strategy(v.clone(), depth - 1), prop::sample::select(vec!["and".to_string(), "or".into(), "implies".into()]), expr_strategy(v, depth - 1))
                .prop_map(|(l, op, r)| format!("({l} {op} {r})"))
        },
        // Unary not
        2 => {
            let v = v.clone();
            expr_strategy(v, depth - 1).prop_map(|e| format!("not({e})"))
        },
        // Set literal
        2 => prop::collection::vec(0u8..=3, 0..=3)
            .prop_map(|elems| {
                let es: Vec<String> = elems.iter().map(|e| e.to_string()).collect();
                format!("{{{}}}", es.join(", "))
            }),
        // Membership test
        3 => {
            let v = v.clone();
            let v2 = v.clone();
            (expr_strategy(v, depth - 1), prop::sample::select(v2))
                .prop_map(|(elem, var)| format!("({elem} in {var})"))
        },
        // If-then-else
        2 => {
            let v = v.clone();
            (expr_strategy(v.clone(), depth - 1), expr_strategy(v.clone(), depth - 1), expr_strategy(v, depth - 1))
                .prop_map(|(c, t, e)| format!("(if {c} then {t} else {e})"))
        },
        // Let binding
        2 => {
            let v = v.clone();
            (expr_strategy(v.clone(), depth - 1), expr_strategy(v, depth - 1))
                .prop_map(|(val, body)| format!("(let _tmp = {val} in {body})"))
        },
    ]
    .boxed()
}

/// Generate a boolean expression (for invariants, guards).
fn bool_expr_strategy(vars: Vec<String>, depth: u32) -> BoxedStrategy<String> {
    let leaf = {
        let v = vars.clone();
        let v2 = vars.clone();
        prop_oneof![
            prop::bool::ANY.prop_map(|b| if b { "true".into() } else { "false".into() }),
            (
                prop::sample::select(v),
                prop::sample::select(vec![
                    "==".to_string(),
                    "!=".into(),
                    "<".into(),
                    "<=".into(),
                    ">".into(),
                    ">=".into()
                ]),
                0i64..=5
            )
                .prop_map(|(v, op, n)| format!("({v} {op} {n})")),
            (0u8..=3, prop::sample::select(v2)).prop_map(|(n, v)| format!("({n} in {v})")),
        ]
    }
    .boxed();

    if depth == 0 {
        return leaf;
    }

    let v = vars.clone();
    prop_oneof![
        10 => leaf,
        3 => {
            let v = v.clone();
            (bool_expr_strategy(v.clone(), depth - 1), prop::sample::select(vec!["and".to_string(), "or".into()]), bool_expr_strategy(v, depth - 1))
                .prop_map(|(l, op, r)| format!("({l} {op} {r})"))
        },
        2 => {
            let v = v.clone();
            (bool_expr_strategy(v.clone(), depth - 1), bool_expr_strategy(v, depth - 1))
                .prop_map(|(l, r)| format!("({l} implies {r})"))
        },
        2 => {
            let v = v.clone();
            bool_expr_strategy(v, depth - 1).prop_map(|e| format!("not({e})"))
        },
        // Quantifier: all k in 0..bound : body
        3 => {
            let v = v.clone();
            (1u8..=3, bool_expr_strategy(v, depth - 1))
                .prop_map(|(bound, body)| format!("(all _qv in 0..{bound} : {body})"))
        },
        // Quantifier: any
        2 => {
            let v = v.clone();
            (1u8..=3, bool_expr_strategy(v, depth - 1))
                .prop_map(|(bound, body)| format!("(any _qv in 0..{bound} : {body})"))
        },
        // Quantifier with membership in body (exercises issue #69 fix)
        3 => {
            let v = v.clone();
            (prop::sample::select(v.clone()), 1u8..=3)
                .prop_map(|(var, bound)| format!("(all _qv in 0..{bound} : _qv in {var})"))
        },
        // Iff (biconditional)
        2 => {
            let v = v.clone();
            (bool_expr_strategy(v.clone(), depth - 1), bool_expr_strategy(v, depth - 1))
                .prop_map(|(l, r)| format!("({l} iff {r})"))
        },
        // subset_of
        2 => {
            let v = v.clone();
            (prop::sample::select(v.clone()), prop::sample::select(v))
                .prop_map(|(l, r)| format!("({l} subset_of {r})"))
        },
    ]
    .boxed()
}

// ─── Spec generators ───

#[derive(Debug, Clone)]
struct SetSpec {
    bound: u8,
    n_actions: u8,
}

impl SetSpec {
    fn to_specl(&self) -> String {
        let bound = self.bound;
        let mut actions = String::new();
        for i in 0..self.n_actions {
            actions.push_str(&format!(
                "action Add{i}(k: 0..{bound}) {{ s = s union {{k}}; }}\n"
            ));
        }
        format!(
            r#"module SetSpec

var s: Set[0..{bound}]

init {{ s = {{}}; }}

{actions}
action Remove(k: 0..{bound}) {{ require k in s; s = s diff {{k}}; }}

invariant NonNegLen {{ len(s) >= 0 }}

invariant MembershipConsistent {{
    all k in 0..{bound} : k in s implies k in s
}}

invariant AnyImpliesNonempty {{
    (any k in 0..{bound} : k in s) implies len(s) > 0
}}
"#,
        )
    }
}

#[derive(Debug, Clone)]
struct DictSpec {
    key_bound: u8,
    val_bound: u8,
}

impl DictSpec {
    fn to_specl(&self) -> String {
        let kb = self.key_bound;
        let vb = self.val_bound;
        format!(
            r#"module DictSpec

var d: Dict[0..{kb}, 0..{vb}]

init {{ d = {{k: 0 for k in 0..{kb}}}; }}

action Update(k: 0..{kb}, v: 0..{vb}) {{ d = d | {{k: v}}; }}

invariant AllKeysInRange {{
    all k in 0..{kb} : d[k] >= 0 and d[k] <= {vb}
}}
"#,
        )
    }
}

#[derive(Debug, Clone)]
struct FuncSpec {
    bound: u8,
}

impl FuncSpec {
    fn to_specl(&self) -> String {
        let b = self.bound;
        format!(
            r#"module FuncSpec

var s: Set[0..{b}]

func IsComplete(ws) {{
    all k in 0..{b} : k in ws
}}

func CountTrue(ws, v) {{
    if v in ws then 1 else 0
}}

init {{ s = {{}}; }}

action Add(k: 0..{b}) {{ s = s union {{k}}; }}

invariant CompleteImpliesFull {{
    IsComplete(s) implies len(s) == {b} + 1
}}

invariant CountTrueNonNeg {{
    all k in 0..{b} : CountTrue(s, k) >= 0
}}
"#,
        )
    }
}

#[derive(Debug, Clone)]
struct LetIfSpec {
    bound: u8,
}

impl LetIfSpec {
    fn to_specl(&self) -> String {
        let b = self.bound;
        format!(
            r#"module LetIfSpec

var x: 0..{b}
var y: 0..{b}

init {{ x = 0; y = 0; }}

action Step() {{
    x = if x < {b} then x + 1 else 0;
    y = if y < {b} then y + 1 else 0;
}}

action ConditionalStep() {{
    x = if x + 1 <= {b} then x + 1 else x;
    y = if y == x then 0 else y;
}}

invariant XInRange {{ x >= 0 and x <= {b} }}
invariant YInRange {{ y >= 0 and y <= {b} }}

invariant LetExprWorks {{
    let sum = x + y in sum >= 0
}}
"#,
        )
    }
}

#[derive(Debug, Clone)]
struct ComprehensionSpec {
    bound: u8,
}

impl ComprehensionSpec {
    fn to_specl(&self) -> String {
        let b = self.bound;
        format!(
            r#"module ComprehensionSpec

var s: Set[0..{b}]

init {{ s = {{}}; }}

action Add(k: 0..{b}) {{ s = s union {{k}}; }}

invariant FilterSubset {{
    all k in 0..{b} :
        (k in {{ x in 0..{b} if x in s }}) implies (k in s)
}}
"#,
        )
    }
}

// ─── New spec generators (sequences, tuples, fix, set ops) ───

#[derive(Debug, Clone)]
struct SeqSpec {
    bound: u8,
    max_len: u8,
}

impl SeqSpec {
    fn to_specl(&self) -> String {
        let b = self.bound;
        let ml = self.max_len;
        format!(
            r#"module SeqSpec

var msgs: Seq[0..{b}]

init {{ msgs = []; }}

action Send(v: 0..{b}) {{
    require len(msgs) < {ml};
    msgs = msgs ++ [v];
}}

action Recv() {{
    require len(msgs) > 0;
    msgs = tail(msgs);
}}

invariant Bounded {{ len(msgs) <= {ml} }}

invariant HeadInRange {{
    len(msgs) > 0 implies (head(msgs) >= 0 and head(msgs) <= {b})
}}
"#,
        )
    }
}

#[derive(Debug, Clone)]
struct TupleSpec {
    bound: u8,
}

impl TupleSpec {
    fn to_specl(&self) -> String {
        let b = self.bound;
        format!(
            r#"module TupleSpec

var pair: (0..{b}, 0..{b})

init {{ pair = (0, 0); }}

action StepBoth() {{
    require pair.0 < {b};
    require pair.1 < {b};
    pair = (pair.0 + 1, pair.1 + 1);
}}

action StepFirst() {{
    require pair.0 < {b};
    pair = (pair.0 + 1, pair.1);
}}

invariant FirstBounded {{ pair.0 >= 0 and pair.0 <= {b} }}
invariant SecondBounded {{ pair.1 >= 0 and pair.1 <= {b} }}
invariant FirstGeSecond {{ pair.0 >= pair.1 }}
"#,
        )
    }
}

#[derive(Debug, Clone)]
struct FixSpec {
    bound: u8,
}

impl FixSpec {
    fn to_specl(&self) -> String {
        let b = self.bound;
        format!(
            r#"module FixSpec

var s: Set[0..{b}]

func FirstMissing(ws) {{
    if (all k in 0..{b} : k in ws) then
        {b} + 1
    else
        fix k in 0..{b} : not(k in ws)
}}

init {{ s = {{}}; }}

action Add(k: 0..{b}) {{ s = s union {{k}}; }}

invariant FirstMissingValid {{
    let fm = FirstMissing(s) in fm >= 0
}}

invariant FirstMissingBound {{
    FirstMissing(s) <= {b} + 1
}}
"#,
        )
    }
}

#[derive(Debug, Clone)]
struct SetOpsSpec {
    bound: u8,
}

impl SetOpsSpec {
    fn to_specl(&self) -> String {
        let b = self.bound;
        format!(
            r#"module SetOpsSpec

var s1: Set[0..{b}]
var s2: Set[0..{b}]

init {{ s1 = {{}}; s2 = {{}}; }}

action Add1(k: 0..{b}) {{ s1 = s1 union {{k}}; }}
action Add2(k: 0..{b}) {{ s2 = s2 union {{k}}; }}

invariant IntersectSubset {{
    (s1 intersect s2) subset_of s1
}}

invariant UnionContainsBoth {{
    s1 subset_of (s1 union s2) and s2 subset_of (s1 union s2)
}}

invariant DiffDisjoint {{
    len((s1 diff s2) intersect s2) == 0
}}

invariant IffConsistent {{
    all k in 0..{b} : (k in s1 iff k in s1)
}}
"#,
        )
    }
}

#[derive(Debug, Clone)]
struct PowersetSpec {
    bound: u8,
}

impl PowersetSpec {
    fn to_specl(&self) -> String {
        let b = self.bound;
        format!(
            r#"module PowersetSpec

var s: Set[0..{b}]

init {{ s = {{}}; }}

action Add(k: 0..{b}) {{ s = s union {{k}}; }}

invariant SelfInPowerset {{ s in powerset(0..{b}) }}

invariant EmptyInPowerset {{ {{}} in powerset(0..{b}) }}

invariant PowersetSize {{
    all sub in powerset(s) : sub subset_of s
}}
"#,
        )
    }
}

// ─── Properties ───

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 256,
        .. ProptestConfig::default()
    })]

    #[test]
    fn set_spec_no_panic(bound in 1u8..=4, n_actions in 1u8..=3) {
        let spec = SetSpec { bound, n_actions };
        let src = spec.to_specl();
        let compiled = compile_spec(&src);
        prop_assert!(compiled.is_ok(), "compile failed: {:?}", compiled.err());
        let outcome = check_spec(&src, CheckConfig {
            check_deadlock: false,
            max_states: 5_000,
            ..CheckConfig::default()
        });
        prop_assert!(outcome.is_ok(), "check failed: {:?}", outcome.err());
    }

    #[test]
    fn dict_spec_no_panic(kb in 1u8..=3, vb in 1u8..=3) {
        let spec = DictSpec { key_bound: kb, val_bound: vb };
        let src = spec.to_specl();
        let compiled = compile_spec(&src);
        prop_assert!(compiled.is_ok(), "compile failed: {:?}", compiled.err());
        let outcome = check_spec(&src, CheckConfig {
            check_deadlock: false,
            max_states: 5_000,
            ..CheckConfig::default()
        });
        prop_assert!(outcome.is_ok(), "check failed: {:?}", outcome.err());
    }

    #[test]
    fn func_spec_no_panic(bound in 1u8..=3) {
        let spec = FuncSpec { bound };
        let src = spec.to_specl();
        let compiled = compile_spec(&src);
        prop_assert!(compiled.is_ok(), "compile failed: {:?}", compiled.err());
        let outcome = check_spec(&src, CheckConfig {
            check_deadlock: false,
            max_states: 5_000,
            ..CheckConfig::default()
        });
        prop_assert!(outcome.is_ok(), "check failed: {:?}", outcome.err());
    }

    #[test]
    fn let_if_spec_no_panic(bound in 1u8..=4) {
        let spec = LetIfSpec { bound };
        let src = spec.to_specl();
        let compiled = compile_spec(&src);
        prop_assert!(compiled.is_ok(), "compile failed: {:?}", compiled.err());
        let outcome = check_spec(&src, CheckConfig {
            check_deadlock: false,
            max_states: 5_000,
            ..CheckConfig::default()
        });
        prop_assert!(outcome.is_ok(), "check failed: {:?}", outcome.err());
    }

    #[test]
    fn comprehension_spec_no_panic(bound in 1u8..=3) {
        let spec = ComprehensionSpec { bound };
        let src = spec.to_specl();
        let compiled = compile_spec(&src);
        prop_assert!(compiled.is_ok(), "compile failed: {:?}", compiled.err());
        let outcome = check_spec(&src, CheckConfig {
            check_deadlock: false,
            max_states: 5_000,
            ..CheckConfig::default()
        });
        prop_assert!(outcome.is_ok(), "check failed: {:?}", outcome.err());
    }

    // ─── New spec generators: no-panic tests ───

    #[test]
    fn seq_spec_no_panic(bound in 1u8..=2, max_len in 2u8..=4) {
        let spec = SeqSpec { bound, max_len };
        let src = spec.to_specl();
        let compiled = compile_spec(&src);
        prop_assert!(compiled.is_ok(), "compile failed: {:?}", compiled.err());
        let outcome = check_spec(&src, CheckConfig {
            check_deadlock: false,
            max_states: 5_000,
            ..CheckConfig::default()
        });
        prop_assert!(outcome.is_ok(), "check failed: {:?}", outcome.err());
    }

    #[test]
    fn tuple_spec_no_panic(bound in 1u8..=3) {
        let spec = TupleSpec { bound };
        let src = spec.to_specl();
        let compiled = compile_spec(&src);
        prop_assert!(compiled.is_ok(), "compile failed: {:?}", compiled.err());
        let outcome = check_spec(&src, CheckConfig {
            check_deadlock: false,
            max_states: 5_000,
            ..CheckConfig::default()
        });
        prop_assert!(outcome.is_ok(), "check failed: {:?}", outcome.err());
    }

    #[test]
    fn fix_spec_no_panic(bound in 1u8..=3) {
        let spec = FixSpec { bound };
        let src = spec.to_specl();
        let compiled = compile_spec(&src);
        prop_assert!(compiled.is_ok(), "compile failed: {:?}", compiled.err());
        let outcome = check_spec(&src, CheckConfig {
            check_deadlock: false,
            max_states: 5_000,
            ..CheckConfig::default()
        });
        prop_assert!(outcome.is_ok(), "check failed: {:?}", outcome.err());
    }

    #[test]
    fn set_ops_spec_no_panic(bound in 1u8..=3) {
        let spec = SetOpsSpec { bound };
        let src = spec.to_specl();
        let compiled = compile_spec(&src);
        prop_assert!(compiled.is_ok(), "compile failed: {:?}", compiled.err());
        let outcome = check_spec(&src, CheckConfig {
            check_deadlock: false,
            max_states: 5_000,
            ..CheckConfig::default()
        });
        prop_assert!(outcome.is_ok(), "check failed: {:?}", outcome.err());
    }

    #[test]
    fn powerset_spec_no_panic(bound in 1u8..=2) {
        let spec = PowersetSpec { bound };
        let src = spec.to_specl();
        let compiled = compile_spec(&src);
        prop_assert!(compiled.is_ok(), "compile failed: {:?}", compiled.err());
        let outcome = check_spec(&src, CheckConfig {
            check_deadlock: false,
            max_states: 10_000,
            ..CheckConfig::default()
        });
        prop_assert!(outcome.is_ok(), "check failed: {:?}", outcome.err());
    }

    // Pretty-print roundtrip tests

    #[test]
    fn set_spec_roundtrip(bound in 1u8..=4, n_actions in 1u8..=3) {
        let spec = SetSpec { bound, n_actions };
        let src = spec.to_specl();
        let result = roundtrip_pretty(&src);
        prop_assert!(result.is_ok(), "roundtrip failed: {:?}", result.err());
        let (p1, p2) = result.unwrap();
        prop_assert_eq!(p1, p2, "pretty-print not idempotent");
    }

    #[test]
    fn dict_spec_roundtrip(kb in 1u8..=3, vb in 1u8..=3) {
        let spec = DictSpec { key_bound: kb, val_bound: vb };
        let src = spec.to_specl();
        let result = roundtrip_pretty(&src);
        prop_assert!(result.is_ok(), "roundtrip failed: {:?}", result.err());
        let (p1, p2) = result.unwrap();
        prop_assert_eq!(p1, p2, "pretty-print not idempotent");
    }

    #[test]
    fn func_spec_roundtrip(bound in 1u8..=3) {
        let spec = FuncSpec { bound };
        let src = spec.to_specl();
        let result = roundtrip_pretty(&src);
        prop_assert!(result.is_ok(), "roundtrip failed: {:?}", result.err());
        let (p1, p2) = result.unwrap();
        prop_assert_eq!(p1, p2, "pretty-print not idempotent");
    }

    #[test]
    fn let_if_spec_roundtrip(bound in 1u8..=4) {
        let spec = LetIfSpec { bound };
        let src = spec.to_specl();
        let result = roundtrip_pretty(&src);
        prop_assert!(result.is_ok(), "roundtrip failed: {:?}", result.err());
        let (p1, p2) = result.unwrap();
        prop_assert_eq!(p1, p2, "pretty-print not idempotent");
    }

    // ─── New spec generators: roundtrip tests ───

    #[test]
    fn seq_spec_roundtrip(bound in 1u8..=2, max_len in 2u8..=4) {
        let spec = SeqSpec { bound, max_len };
        let src = spec.to_specl();
        let result = roundtrip_pretty(&src);
        prop_assert!(result.is_ok(), "roundtrip failed: {:?}", result.err());
        let (p1, p2) = result.unwrap();
        prop_assert_eq!(p1, p2, "pretty-print not idempotent");
    }

    #[test]
    fn tuple_spec_roundtrip(bound in 1u8..=3) {
        let spec = TupleSpec { bound };
        let src = spec.to_specl();
        let result = roundtrip_pretty(&src);
        prop_assert!(result.is_ok(), "roundtrip failed: {:?}", result.err());
        let (p1, p2) = result.unwrap();
        prop_assert_eq!(p1, p2, "pretty-print not idempotent");
    }

    #[test]
    fn fix_spec_roundtrip(bound in 1u8..=3) {
        let spec = FixSpec { bound };
        let src = spec.to_specl();
        let result = roundtrip_pretty(&src);
        prop_assert!(result.is_ok(), "roundtrip failed: {:?}", result.err());
        let (p1, p2) = result.unwrap();
        prop_assert_eq!(p1, p2, "pretty-print not idempotent");
    }

    #[test]
    fn set_ops_spec_roundtrip(bound in 1u8..=3) {
        let spec = SetOpsSpec { bound };
        let src = spec.to_specl();
        let result = roundtrip_pretty(&src);
        prop_assert!(result.is_ok(), "roundtrip failed: {:?}", result.err());
        let (p1, p2) = result.unwrap();
        prop_assert_eq!(p1, p2, "pretty-print not idempotent");
    }

    #[test]
    fn powerset_spec_roundtrip(bound in 1u8..=2) {
        let spec = PowersetSpec { bound };
        let src = spec.to_specl();
        let result = roundtrip_pretty(&src);
        prop_assert!(result.is_ok(), "roundtrip failed: {:?}", result.err());
        let (p1, p2) = result.unwrap();
        prop_assert_eq!(p1, p2, "pretty-print not idempotent");
    }

    // Backend agreement

    #[test]
    fn set_spec_backend_agreement(bound in 1u8..=3, n_actions in 1u8..=2) {
        let spec = SetSpec { bound, n_actions };
        let src = spec.to_specl();
        let base = CheckConfig {
            parallel: false,
            check_deadlock: false,
            max_states: 5_000,
            use_por: false,
            use_symmetry: false,
            ..CheckConfig::default()
        };

        let full = check_spec(&src, base.clone()).expect("full");
        let expected = states_from_outcome(&full);

        let fast = check_spec(&src, CheckConfig { fast_check: true, ..base.clone() }).expect("fast");
        prop_assert_eq!(states_from_outcome(&fast), expected, "fast disagreement");

        let collapse = check_spec(&src, CheckConfig { collapse: true, ..base.clone() }).expect("collapse");
        prop_assert_eq!(states_from_outcome(&collapse), expected, "collapse disagreement");
    }

    // ─── Backend agreement for all spec generators ───

    #[test]
    fn dict_spec_backend_agreement(kb in 1u8..=2, vb in 1u8..=2) {
        let spec = DictSpec { key_bound: kb, val_bound: vb };
        let src = spec.to_specl();
        let base = CheckConfig {
            parallel: false,
            check_deadlock: false,
            max_states: 5_000,
            use_por: false,
            use_symmetry: false,
            ..CheckConfig::default()
        };

        let full = check_spec(&src, base.clone()).expect("full");
        let expected = states_from_outcome(&full);

        let fast = check_spec(&src, CheckConfig { fast_check: true, ..base.clone() }).expect("fast");
        prop_assert_eq!(states_from_outcome(&fast), expected, "fast disagreement");

        let collapse = check_spec(&src, CheckConfig { collapse: true, ..base.clone() }).expect("collapse");
        prop_assert_eq!(states_from_outcome(&collapse), expected, "collapse disagreement");
    }

    #[test]
    fn func_spec_backend_agreement(bound in 1u8..=2) {
        let spec = FuncSpec { bound };
        let src = spec.to_specl();
        let base = CheckConfig {
            parallel: false,
            check_deadlock: false,
            max_states: 5_000,
            use_por: false,
            use_symmetry: false,
            ..CheckConfig::default()
        };

        let full = check_spec(&src, base.clone()).expect("full");
        let expected = states_from_outcome(&full);

        let fast = check_spec(&src, CheckConfig { fast_check: true, ..base.clone() }).expect("fast");
        prop_assert_eq!(states_from_outcome(&fast), expected, "fast disagreement");

        let collapse = check_spec(&src, CheckConfig { collapse: true, ..base.clone() }).expect("collapse");
        prop_assert_eq!(states_from_outcome(&collapse), expected, "collapse disagreement");
    }

    #[test]
    fn let_if_spec_backend_agreement(bound in 1u8..=3) {
        let spec = LetIfSpec { bound };
        let src = spec.to_specl();
        let base = CheckConfig {
            parallel: false,
            check_deadlock: false,
            max_states: 5_000,
            use_por: false,
            use_symmetry: false,
            ..CheckConfig::default()
        };

        let full = check_spec(&src, base.clone()).expect("full");
        let expected = states_from_outcome(&full);

        let fast = check_spec(&src, CheckConfig { fast_check: true, ..base.clone() }).expect("fast");
        prop_assert_eq!(states_from_outcome(&fast), expected, "fast disagreement");

        let collapse = check_spec(&src, CheckConfig { collapse: true, ..base.clone() }).expect("collapse");
        prop_assert_eq!(states_from_outcome(&collapse), expected, "collapse disagreement");
    }

    #[test]
    fn comprehension_spec_backend_agreement(bound in 1u8..=2) {
        let spec = ComprehensionSpec { bound };
        let src = spec.to_specl();
        let base = CheckConfig {
            parallel: false,
            check_deadlock: false,
            max_states: 5_000,
            use_por: false,
            use_symmetry: false,
            ..CheckConfig::default()
        };

        let full = check_spec(&src, base.clone()).expect("full");
        let expected = states_from_outcome(&full);

        let fast = check_spec(&src, CheckConfig { fast_check: true, ..base.clone() }).expect("fast");
        prop_assert_eq!(states_from_outcome(&fast), expected, "fast disagreement");

        let collapse = check_spec(&src, CheckConfig { collapse: true, ..base.clone() }).expect("collapse");
        prop_assert_eq!(states_from_outcome(&collapse), expected, "collapse disagreement");
    }

    #[test]
    fn seq_spec_backend_agreement(bound in 1u8..=2, max_len in 2u8..=3) {
        let spec = SeqSpec { bound, max_len };
        let src = spec.to_specl();
        let base = CheckConfig {
            parallel: false,
            check_deadlock: false,
            max_states: 5_000,
            use_por: false,
            use_symmetry: false,
            ..CheckConfig::default()
        };

        let full = check_spec(&src, base.clone()).expect("full");
        let expected = states_from_outcome(&full);

        let fast = check_spec(&src, CheckConfig { fast_check: true, ..base.clone() }).expect("fast");
        prop_assert_eq!(states_from_outcome(&fast), expected, "fast disagreement");

        let collapse = check_spec(&src, CheckConfig { collapse: true, ..base.clone() }).expect("collapse");
        prop_assert_eq!(states_from_outcome(&collapse), expected, "collapse disagreement");
    }

    #[test]
    fn set_ops_spec_backend_agreement(bound in 1u8..=2) {
        let spec = SetOpsSpec { bound };
        let src = spec.to_specl();
        let base = CheckConfig {
            parallel: false,
            check_deadlock: false,
            max_states: 5_000,
            use_por: false,
            use_symmetry: false,
            ..CheckConfig::default()
        };

        let full = check_spec(&src, base.clone()).expect("full");
        let expected = states_from_outcome(&full);

        let fast = check_spec(&src, CheckConfig { fast_check: true, ..base.clone() }).expect("fast");
        prop_assert_eq!(states_from_outcome(&fast), expected, "fast disagreement");

        let collapse = check_spec(&src, CheckConfig { collapse: true, ..base.clone() }).expect("collapse");
        prop_assert_eq!(states_from_outcome(&collapse), expected, "collapse disagreement");
    }

    // Random expression fuzzing — parser and type-checker crash detection

    #[test]
    fn random_bool_expr_no_crash(bound in 1u8..=3, inv_expr in bool_expr_strategy(vec!["s".into()], 2)) {
        let src = format!(
            "module RandomBoolExpr\nvar s: Set[0..{bound}]\ninit {{ s = {{}}; }}\naction A(k: 0..{bound}) {{ s = s union {{k}}; }}\ninvariant I {{ {inv_expr} }}\n",
        );
        let parsed = specl_syntax::parse(&src);
        if let Ok(module) = parsed {
            let _ = specl_types::check_module(&module);
        }
    }

    #[test]
    fn random_expr_no_parser_crash(expr in expr_strategy(vec!["x".into(), "y".into()], 3)) {
        let src = format!(
            "module RandomExpr\nvar x: 0..5\nvar y: 0..5\ninit {{ x = 0; y = 0; }}\naction A() {{ x = x; y = y; }}\ninvariant I {{ let _v = ({expr}) in true }}\n",
        );
        let parsed = specl_syntax::parse(&src);
        if let Ok(module) = parsed {
            let _ = specl_types::check_module(&module);
        }
    }
}

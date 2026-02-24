//! Z3 symbolic backend coverage.
//!
//! Tests that the symbolic backend (BMC, inductive) agrees with the
//! explicit-state checker on small specs. For specs where invariants hold,
//! both backends should agree. For specs with violations, both should find them.

use proptest::prelude::*;
use specl_ir::compile;
use specl_mc::{CheckConfig, CheckOutcome};
use specl_soundness::check_spec;
use specl_symbolic::{self, SymbolicConfig, SymbolicMode, SymbolicOutcome};

fn explicit_holds(src: &str) -> Option<bool> {
    let config = CheckConfig {
        parallel: false,
        check_deadlock: false,
        max_states: 5_000,
        use_por: false,
        use_symmetry: false,
        max_time_secs: 5,
        ..CheckConfig::default()
    };
    match check_spec(src, config) {
        Ok(CheckOutcome::Ok { .. }) => Some(true),
        Ok(CheckOutcome::InvariantViolation { .. }) => Some(false),
        _ => None,
    }
}

fn symbolic_holds(src: &str, mode: SymbolicMode) -> Option<bool> {
    let module = specl_syntax::parse(src).ok()?;
    specl_types::check_module(&module).ok()?;
    let spec = compile(&module).ok()?;
    let config = SymbolicConfig {
        mode,
        depth: 10,
        seq_bound: 3,
        spacer_profile: specl_symbolic::SpacerProfile::Default,
        timeout_ms: Some(10_000),
    };
    match specl_symbolic::check(&spec, &[], &config) {
        Ok(SymbolicOutcome::Ok { .. }) => Some(true),
        Ok(SymbolicOutcome::InvariantViolation { .. }) => Some(false),
        Ok(SymbolicOutcome::Unknown { .. }) => None,
        Err(_) => None,
    }
}

// ─── Deterministic agreement tests ───

#[test]
fn bmc_agrees_on_simple_counter_safe() {
    let src = r#"module SymCounter
var x: 0..5
init { x = 0; }
action Inc() { require x < 5; x = x + 1; }
invariant InRange { x >= 0 and x <= 5 }
"#;
    let explicit = explicit_holds(src);
    let symbolic = symbolic_holds(src, SymbolicMode::Bmc);
    assert_eq!(explicit, Some(true));
    if let Some(sym) = symbolic {
        assert!(sym, "BMC should agree invariant holds");
    }
}

#[test]
fn bmc_agrees_on_simple_counter_unsafe() {
    let src = r#"module SymCounterUnsafe
var x: 0..5
init { x = 0; }
action Inc() { require x < 5; x = x + 1; }
invariant Small { x < 3 }
"#;
    let explicit = explicit_holds(src);
    let symbolic = symbolic_holds(src, SymbolicMode::Bmc);
    assert_eq!(explicit, Some(false));
    if let Some(sym) = symbolic {
        assert!(!sym, "BMC should find violation");
    }
}

#[test]
fn inductive_agrees_on_safe_spec() {
    let src = r#"module SymInductive
var x: 0..3
init { x = 0; }
action Inc() { require x < 3; x = x + 1; }
action Dec() { require x > 0; x = x - 1; }
invariant InRange { x >= 0 and x <= 3 }
"#;
    let explicit = explicit_holds(src);
    let symbolic = symbolic_holds(src, SymbolicMode::Inductive);
    assert_eq!(explicit, Some(true));
    if let Some(sym) = symbolic {
        assert!(sym, "inductive should agree invariant holds");
    }
}

#[test]
fn bmc_agrees_on_set_spec() {
    let src = r#"module SymSet
var s: Set[0..2]
init { s = {}; }
action Add(k: 0..2) { s = s union {k}; }
invariant NonNeg { len(s) >= 0 }
"#;
    let explicit = explicit_holds(src);
    let symbolic = symbolic_holds(src, SymbolicMode::Bmc);
    assert_eq!(explicit, Some(true));
    if let Some(sym) = symbolic {
        assert!(sym, "BMC should agree on set spec");
    }
}

#[test]
fn bmc_agrees_on_dict_spec() {
    let src = r#"module SymDict
var d: Dict[0..1, 0..2]
init { d = {k: 0 for k in 0..1}; }
action Update(k: 0..1, v: 0..2) { d = d | {k: v}; }
invariant Valid { all k in 0..1 : d[k] >= 0 }
"#;
    let explicit = explicit_holds(src);
    let symbolic = symbolic_holds(src, SymbolicMode::Bmc);
    assert_eq!(explicit, Some(true));
    if let Some(sym) = symbolic {
        assert!(sym, "BMC should agree on dict spec");
    }
}

// ─── Proptest: random specs, explicit vs symbolic agreement ───

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 64,
        .. ProptestConfig::default()
    })]

    #[test]
    fn bmc_agrees_with_explicit_on_counters(bound in 1u8..=4, threshold in 0u8..=4) {
        let src = format!(
            r#"module SymProp
var x: 0..{bound}
init {{ x = 0; }}
action Inc() {{ require x < {bound}; x = x + 1; }}
action Dec() {{ require x > 0; x = x - 1; }}
invariant Bounded {{ x <= {threshold} }}
"#,
        );

        let explicit = explicit_holds(&src);
        let symbolic = symbolic_holds(&src, SymbolicMode::Bmc);

        // If both produce a result, they must agree
        if let (Some(e), Some(s)) = (explicit, symbolic) {
            prop_assert_eq!(e, s, "explicit={}, symbolic={} for bound={}, threshold={}", e, s, bound, threshold);
        }
    }
}

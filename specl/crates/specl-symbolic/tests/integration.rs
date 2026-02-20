//! Integration tests for specl-symbolic backend.
//!
//! Each test compiles a showcase spec and runs a specific symbolic mode,
//! asserting the expected outcome.

use specl_eval::Value;
use specl_ir::CompiledSpec;
use specl_symbolic::{
    SpacerProfile, SymbolicConfig, SymbolicMode, SymbolicOutcome, SymbolicResult,
};

/// Resolve the path to a spec in examples/other/ relative to the workspace root.
fn example_path(name: &str) -> String {
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    format!("{}/../../examples/other/{}", manifest_dir, name)
}

/// Parse constants from a list of "NAME=VALUE" strings against a compiled spec.
fn parse_consts(pairs: &[(&str, i64)], spec: &CompiledSpec) -> Vec<Value> {
    let mut values = vec![Value::none(); spec.consts.len()];
    for (name, val) in pairs {
        let decl = spec
            .consts
            .iter()
            .find(|c| c.name == *name)
            .unwrap_or_else(|| panic!("unknown constant: {name}"));
        values[decl.index] = Value::int(*val);
    }
    // Fill defaults for any unset constants
    for c in &spec.consts {
        if values[c.index].is_none() {
            if let Some(default) = c.default_value {
                values[c.index] = Value::int(default);
            } else {
                panic!("constant '{}' not provided and has no default", c.name);
            }
        }
    }
    values
}

/// Load, parse, compile a spec and run symbolic checking.
fn run_symbolic(
    spec_file: &str,
    consts: &[(&str, i64)],
    mode: SymbolicMode,
) -> SymbolicResult<SymbolicOutcome> {
    let path = example_path(spec_file);
    let source =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("failed to read {path}: {e}"));
    let module = specl_syntax::parse(&source)
        .unwrap_or_else(|e| panic!("parse error in {spec_file}: {e:?}"));
    let spec =
        specl_ir::compile(&module).unwrap_or_else(|e| panic!("compile error in {spec_file}: {e}"));
    let consts = parse_consts(consts, &spec);
    let config = SymbolicConfig {
        mode,
        depth: 20,
        seq_bound: 5,
        spacer_profile: SpacerProfile::Default,
        timeout_ms: None,
    };
    specl_symbolic::check(&spec, &consts, &config)
}

// ============================================================================
// BMC tests
// ============================================================================

#[test]
fn bmc_bounded_buffer_ok() {
    let outcome = run_symbolic(
        "bounded-buffer.specl",
        &[("N", 2), ("Cap", 3)],
        SymbolicMode::Bmc,
    )
    .unwrap();
    assert!(
        matches!(outcome, SymbolicOutcome::Ok { .. }),
        "expected Ok, got: {outcome:?}"
    );
}

#[test]
fn bmc_reader_writer_ok() {
    let outcome = run_symbolic("reader-writer.specl", &[("N", 2)], SymbolicMode::Bmc).unwrap();
    assert!(
        matches!(outcome, SymbolicOutcome::Ok { .. }),
        "expected Ok, got: {outcome:?}"
    );
}

#[test]
fn bmc_dekker_ok() {
    let outcome = run_symbolic("dekker.specl", &[], SymbolicMode::Bmc).unwrap();
    assert!(
        matches!(outcome, SymbolicOutcome::Ok { .. }),
        "expected Ok, got: {outcome:?}"
    );
}

#[test]
fn bmc_cas_register_ok() {
    let outcome = run_symbolic("cas-register.specl", &[("N", 3)], SymbolicMode::Bmc).unwrap();
    assert!(
        matches!(outcome, SymbolicOutcome::Ok { .. }),
        "expected Ok, got: {outcome:?}"
    );
}

// ============================================================================
// Inductive tests
// ============================================================================

#[test]
fn inductive_reader_writer_ok() {
    let outcome =
        run_symbolic("reader-writer.specl", &[("N", 2)], SymbolicMode::Inductive).unwrap();
    assert!(
        matches!(outcome, SymbolicOutcome::Ok { .. }),
        "expected Ok, got: {outcome:?}"
    );
}

#[test]
fn inductive_bounded_buffer_ok() {
    let outcome = run_symbolic(
        "bounded-buffer.specl",
        &[("N", 2), ("Cap", 3)],
        SymbolicMode::Inductive,
    )
    .unwrap();
    assert!(
        matches!(outcome, SymbolicOutcome::Ok { .. }),
        "expected Ok, got: {outcome:?}"
    );
}

#[test]
fn inductive_dekker_not_inductive() {
    // Dekker is NOT 1-inductive (needs k=2), so simple induction should find a CTI
    let outcome = run_symbolic("dekker.specl", &[], SymbolicMode::Inductive).unwrap();
    assert!(
        matches!(outcome, SymbolicOutcome::InvariantViolation { .. }),
        "expected InvariantViolation (CTI), got: {outcome:?}"
    );
}

// ============================================================================
// k-Induction tests
// ============================================================================

#[test]
fn kind_dekker_not_k_inductive() {
    // Dekker is not naturally k-inductive (needs invariant strengthening).
    // Smart mode handles it via IC3/Spacer instead.
    let outcome = run_symbolic("dekker.specl", &[], SymbolicMode::KInduction(2)).unwrap();
    assert!(
        matches!(outcome, SymbolicOutcome::Unknown { .. }),
        "expected Unknown (not k-inductive), got: {outcome:?}"
    );
}

#[test]
fn kind_cas_register_ok() {
    let outcome = run_symbolic(
        "cas-register.specl",
        &[("N", 3)],
        SymbolicMode::KInduction(2),
    )
    .unwrap();
    assert!(
        matches!(outcome, SymbolicOutcome::Ok { .. }),
        "expected Ok, got: {outcome:?}"
    );
}

#[test]
fn kind_bounded_buffer_ok() {
    let outcome = run_symbolic(
        "bounded-buffer.specl",
        &[("N", 2), ("Cap", 3)],
        SymbolicMode::KInduction(2),
    )
    .unwrap();
    assert!(
        matches!(outcome, SymbolicOutcome::Ok { .. }),
        "expected Ok, got: {outcome:?}"
    );
}

// ============================================================================
// IC3 tests
// ============================================================================

#[test]
fn ic3_bounded_buffer_ok() {
    let outcome = run_symbolic(
        "bounded-buffer.specl",
        &[("N", 2), ("Cap", 3)],
        SymbolicMode::Ic3,
    )
    .unwrap();
    assert!(
        matches!(outcome, SymbolicOutcome::Ok { .. }),
        "expected Ok, got: {outcome:?}"
    );
}

#[test]
fn ic3_reader_writer_ok() {
    let outcome = run_symbolic("reader-writer.specl", &[("N", 2)], SymbolicMode::Ic3).unwrap();
    assert!(
        matches!(outcome, SymbolicOutcome::Ok { .. }),
        "expected Ok, got: {outcome:?}"
    );
}

// ============================================================================
// Smart mode tests
// ============================================================================

#[test]
fn smart_dekker_ok() {
    let outcome = run_symbolic("dekker.specl", &[], SymbolicMode::Smart).unwrap();
    assert!(
        matches!(outcome, SymbolicOutcome::Ok { .. }),
        "expected Ok, got: {outcome:?}"
    );
}

#[test]
fn smart_bounded_buffer_ok() {
    let outcome = run_symbolic(
        "bounded-buffer.specl",
        &[("N", 2), ("Cap", 3)],
        SymbolicMode::Smart,
    )
    .unwrap();
    assert!(
        matches!(outcome, SymbolicOutcome::Ok { .. }),
        "expected Ok, got: {outcome:?}"
    );
}

// ============================================================================
// Portfolio mode tests
// ============================================================================

#[test]
fn portfolio_reader_writer_ok() {
    let outcome =
        run_symbolic("reader-writer.specl", &[("N", 2)], SymbolicMode::Portfolio).unwrap();
    assert!(
        matches!(outcome, SymbolicOutcome::Ok { .. }),
        "expected Ok, got: {outcome:?}"
    );
}

#[test]
fn portfolio_dekker_ok() {
    let outcome = run_symbolic("dekker.specl", &[], SymbolicMode::Portfolio).unwrap();
    assert!(
        matches!(outcome, SymbolicOutcome::Ok { .. }),
        "expected Ok, got: {outcome:?}"
    );
}

// ============================================================================
// Auxiliary invariant tests
// ============================================================================

#[test]
fn inductive_auxiliary_invariant_ok() {
    let outcome = run_symbolic(
        "auxiliary-test.specl",
        &[("N", 10)],
        SymbolicMode::Inductive,
    )
    .unwrap();
    assert!(
        matches!(outcome, SymbolicOutcome::Ok { .. }),
        "expected Ok with auxiliary invariant, got: {outcome:?}"
    );
}

#[test]
fn kind_auxiliary_invariant_ok() {
    let outcome = run_symbolic(
        "auxiliary-test.specl",
        &[("N", 10)],
        SymbolicMode::KInduction(2),
    )
    .unwrap();
    assert!(
        matches!(outcome, SymbolicOutcome::Ok { .. }),
        "expected Ok with auxiliary invariant, got: {outcome:?}"
    );
}

// ============================================================================
// Tuple type tests
// ============================================================================

#[test]
fn inductive_tuple_ok() {
    let outcome = run_symbolic("tuple-test.specl", &[("N", 5)], SymbolicMode::Inductive).unwrap();
    assert!(
        matches!(outcome, SymbolicOutcome::Ok { .. }),
        "expected Ok with tuple type, got: {outcome:?}"
    );
}

#[test]
fn bmc_tuple_ok() {
    let outcome = run_symbolic("tuple-test.specl", &[("N", 5)], SymbolicMode::Bmc).unwrap();
    assert!(
        matches!(outcome, SymbolicOutcome::Ok { .. }),
        "expected Ok with tuple type BMC, got: {outcome:?}"
    );
}

// ============================================================================
// Option type tests
// ============================================================================

#[test]
fn inductive_option_ok() {
    let outcome = run_symbolic("option-test.specl", &[("N", 5)], SymbolicMode::Inductive).unwrap();
    assert!(
        matches!(outcome, SymbolicOutcome::Ok { .. }),
        "expected Ok with option type, got: {outcome:?}"
    );
}

#[test]
fn bmc_option_ok() {
    let outcome = run_symbolic("option-test.specl", &[("N", 5)], SymbolicMode::Bmc).unwrap();
    assert!(
        matches!(outcome, SymbolicOutcome::Ok { .. }),
        "expected Ok with option type BMC, got: {outcome:?}"
    );
}

// ============================================================================
// CTI learning tests
// ============================================================================

#[test]
fn smart_dekker_uses_ic3() {
    // Dekker is NOT 1-inductive and NOT naturally k-inductive (k=2..5).
    // Smart mode should collect CTI lemmas from k-induction and pass them to IC3.
    // The result should be Ok with method "smart(IC3)".
    let outcome = run_symbolic("dekker.specl", &[], SymbolicMode::Smart).unwrap();
    match outcome {
        SymbolicOutcome::Ok { method } => {
            assert_eq!(
                method, "smart(IC3)",
                "Dekker should be proved via smart(IC3), got: {method}"
            );
        }
        other => panic!("expected Ok, got: {other:?}"),
    }
}

#[test]
fn k_induction_with_cti_extracts_lemmas() {
    // Dekker at k=2 should fail the inductive step and extract CTI lemmas.
    let path = example_path("dekker.specl");
    let source = std::fs::read_to_string(&path).unwrap();
    let module = specl_syntax::parse(&source).unwrap();
    let spec = specl_ir::compile(&module).unwrap();
    let consts = parse_consts(&[], &spec);

    let result =
        specl_symbolic::k_induction::check_k_induction_with_cti(&spec, &consts, 2, 5, None)
            .unwrap();

    assert!(
        matches!(result.outcome, SymbolicOutcome::Unknown { .. }),
        "expected Unknown at k=2, got: {:?}",
        result.outcome
    );
    assert!(
        !result.cti_lemmas.is_empty(),
        "expected CTI lemmas to be extracted at k=2, got none"
    );
}

#[test]
fn ic3_with_auxiliary_invariants_dekker() {
    // Verify that check_ic3 correctly applies auxiliary invariants.
    // Use a trivially true auxiliary invariant (true) and verify Dekker is still proved.
    let path = example_path("dekker.specl");
    let source = std::fs::read_to_string(&path).unwrap();
    let module = specl_syntax::parse(&source).unwrap();
    let mut spec = specl_ir::compile(&module).unwrap();
    let consts = parse_consts(&[], &spec);

    // Add a trivially true auxiliary invariant
    spec.auxiliary_invariants
        .push(specl_ir::CompiledInvariant {
            name: "trivially_true".to_string(),
            body: specl_ir::CompiledExpr::Bool(true),
        });

    let config = SymbolicConfig {
        mode: SymbolicMode::Ic3,
        depth: 20,
        seq_bound: 5,
        spacer_profile: SpacerProfile::Default,
        timeout_ms: None,
    };
    let outcome = specl_symbolic::check(&spec, &consts, &config).unwrap();
    assert!(
        matches!(outcome, SymbolicOutcome::Ok { .. }),
        "expected Ok with auxiliary invariant, got: {outcome:?}"
    );
}

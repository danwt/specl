//! Counterexample trace validation.
//!
//! When the model checker finds an invariant violation and produces a
//! counterexample trace, we validate that:
//!   1. The first state in the trace satisfies Init
//!   2. Each consecutive pair (s, s') is connected by a valid action transition
//!   3. The final state actually violates the claimed invariant
//!
//! We do this by constructing specs with known violations and checking the trace.

use specl_mc::{CheckConfig, CheckOutcome};
use specl_soundness::check_spec;

fn check_with_trace(src: &str) -> CheckOutcome {
    check_spec(
        src,
        CheckConfig {
            parallel: false,
            check_deadlock: false,
            max_states: 10_000,
            use_por: false,
            use_symmetry: false,
            max_time_secs: 5,
            ..CheckConfig::default()
        },
    )
    .expect("check should not error")
}

fn var_as_int(state: &specl_mc::State, idx: usize) -> i64 {
    state.vars[idx].as_int().expect("variable should be an integer")
}

#[test]
fn violation_trace_is_nonempty() {
    let src = r#"module TraceTest
var x: 0..5
init { x = 0; }
action Inc() { require x < 5; x = x + 1; }
invariant Small { x < 3 }
"#;
    let outcome = check_with_trace(src);
    match outcome {
        CheckOutcome::InvariantViolation { trace, .. } => {
            assert!(!trace.is_empty(), "violation trace should not be empty");
            assert!(trace.len() >= 2, "trace should have init + at least one step");
        }
        other => panic!("expected InvariantViolation, got: {:?}", other),
    }
}

#[test]
fn violation_trace_first_state_is_init() {
    let src = r#"module TraceInit
var x: 0..5
init { x = 0; }
action Inc() { require x < 5; x = x + 1; }
invariant Small { x < 3 }
"#;
    let outcome = check_with_trace(src);
    match outcome {
        CheckOutcome::InvariantViolation { trace, .. } => {
            let (first_state, first_action) = &trace[0];
            assert!(
                first_action.is_none(),
                "first trace step should have no action (init), got: {:?}",
                first_action
            );
            let x_val = var_as_int(first_state, 0);
            assert_eq!(x_val, 0, "init state should have x=0, got x={}", x_val);
        }
        other => panic!("expected InvariantViolation, got: {:?}", other),
    }
}

#[test]
fn violation_trace_final_state_violates_invariant() {
    let src = r#"module TraceFinal
var x: 0..5
init { x = 0; }
action Inc() { require x < 5; x = x + 1; }
invariant Small { x < 3 }
"#;
    let outcome = check_with_trace(src);
    match outcome {
        CheckOutcome::InvariantViolation { trace, .. } => {
            let (last_state, _) = trace.last().unwrap();
            let x_val = var_as_int(last_state, 0);
            assert!(
                x_val >= 3,
                "final state should violate x < 3, got x={}",
                x_val
            );
        }
        other => panic!("expected InvariantViolation, got: {:?}", other),
    }
}

#[test]
fn violation_trace_steps_are_monotonic() {
    let src = r#"module TraceMonotonic
var x: 0..5
init { x = 0; }
action Inc() { require x < 5; x = x + 1; }
invariant Small { x < 3 }
"#;
    let outcome = check_with_trace(src);
    match outcome {
        CheckOutcome::InvariantViolation { trace, .. } => {
            for i in 1..trace.len() {
                let prev_x = var_as_int(&trace[i - 1].0, 0);
                let curr_x = var_as_int(&trace[i].0, 0);
                assert_eq!(
                    curr_x,
                    prev_x + 1,
                    "step {}: expected x={}, got x={}",
                    i,
                    prev_x + 1,
                    curr_x
                );
            }
        }
        other => panic!("expected InvariantViolation, got: {:?}", other),
    }
}

#[test]
fn violation_trace_actions_are_labeled() {
    let src = r#"module TraceActions
var x: 0..5
init { x = 0; }
action Inc() { require x < 5; x = x + 1; }
invariant Small { x < 3 }
"#;
    let outcome = check_with_trace(src);
    match outcome {
        CheckOutcome::InvariantViolation { trace, .. } => {
            for (i, (_, action)) in trace.iter().enumerate().skip(1) {
                assert!(
                    action.is_some(),
                    "step {} should have an action name",
                    i
                );
            }
        }
        other => panic!("expected InvariantViolation, got: {:?}", other),
    }
}

#[test]
fn violation_trace_consistent_across_backends() {
    let src = r#"module TraceBackends
var x: 0..5
init { x = 0; }
action Inc() { require x < 5; x = x + 1; }
invariant Small { x < 3 }
"#;

    let base = CheckConfig {
        parallel: false,
        check_deadlock: false,
        max_states: 10_000,
        use_por: false,
        use_symmetry: false,
        max_time_secs: 5,
        ..CheckConfig::default()
    };

    let full = check_spec(src, base.clone()).unwrap();
    let collapse = check_spec(
        src,
        CheckConfig {
            collapse: true,
            ..base.clone()
        },
    )
    .unwrap();

    assert!(
        matches!(full, CheckOutcome::InvariantViolation { .. }),
        "full should find violation"
    );
    assert!(
        matches!(collapse, CheckOutcome::InvariantViolation { .. }),
        "collapse should find violation"
    );

    if let (
        CheckOutcome::InvariantViolation {
            trace: trace_full, ..
        },
        CheckOutcome::InvariantViolation {
            trace: trace_collapse,
            ..
        },
    ) = (&full, &collapse)
    {
        let full_final_x = var_as_int(&trace_full.last().unwrap().0, 0);
        let collapse_final_x = var_as_int(&trace_collapse.last().unwrap().0, 0);
        assert_eq!(
            full_final_x, collapse_final_x,
            "violation state should match across backends"
        );
    }
}

#[test]
fn deadlock_trace_ends_at_deadlock() {
    let src = r#"module TraceDeadlock
var x: 0..3
init { x = 0; }
action Inc() { require x < 3; x = x + 1; }
"#;
    let outcome = check_spec(
        src,
        CheckConfig {
            parallel: false,
            check_deadlock: true,
            max_states: 10_000,
            use_por: false,
            use_symmetry: false,
            max_time_secs: 5,
            ..CheckConfig::default()
        },
    )
    .expect("check should not error");

    match outcome {
        CheckOutcome::Deadlock { trace } => {
            let last_x = var_as_int(&trace.last().unwrap().0, 0);
            assert_eq!(last_x, 3, "deadlock state should have x=3, got x={}", last_x);
        }
        other => panic!("expected Deadlock, got: {:?}", other),
    }
}

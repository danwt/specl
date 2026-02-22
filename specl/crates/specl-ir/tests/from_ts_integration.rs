//! Integration tests: lower TransitionSystem → CompiledSpec → Explorer → check.

use specl_eval::Value;
use specl_ir::from_ts::lower;
use specl_mc::{CheckConfig, CheckOutcome, Explorer};
use specl_ts::*;

fn make_counter(max_default: i64, invariant_bound_op: TsBinOp) -> TransitionSystem {
    TransitionSystem {
        name: "Counter".to_string(),
        variables: vec![TsVariable {
            name: "count".to_string(),
            ty: TsType::Nat,
        }],
        constants: vec![TsConstant {
            name: "MAX".to_string(),
            ty: TsType::Nat,
            default_value: Some(max_default),
        }],
        init: vec![TsAssignment {
            var_idx: 0,
            value: TsExpr::Int { value: 0 },
        }],
        actions: vec![TsAction {
            name: "Inc".to_string(),
            params: vec![],
            guard: TsExpr::Binary {
                op: TsBinOp::Lt,
                left: Box::new(TsExpr::Var { index: 0 }),
                right: Box::new(TsExpr::Const { index: 0 }),
            },
            assignments: vec![TsAssignment {
                var_idx: 0,
                value: TsExpr::Binary {
                    op: TsBinOp::Add,
                    left: Box::new(TsExpr::Var { index: 0 }),
                    right: Box::new(TsExpr::Int { value: 1 }),
                },
            }],
        }],
        invariants: vec![TsInvariant {
            name: "Bounded".to_string(),
            body: TsExpr::Binary {
                op: invariant_bound_op,
                left: Box::new(TsExpr::Var { index: 0 }),
                right: Box::new(TsExpr::Const { index: 0 }),
            },
        }],
        auxiliary_invariants: vec![],
        view_variables: None,
    }
}

fn check(ts: TransitionSystem) -> CheckOutcome {
    let spec = lower(&ts).unwrap();
    let consts: Vec<Value> = spec
        .consts
        .iter()
        .map(|c| Value::int(c.default_value.expect("test constants must have defaults")))
        .collect();
    let config = CheckConfig {
        check_deadlock: false,
        ..CheckConfig::default()
    };
    let mut explorer = Explorer::new(spec, consts, config);
    explorer.check().unwrap()
}

#[test]
fn counter_ok() {
    // count <= MAX holds for all reachable states when guard is count < MAX
    let outcome = check(make_counter(5, TsBinOp::Le));
    assert!(matches!(outcome, CheckOutcome::Ok { .. }));
    if let CheckOutcome::Ok {
        states_explored, ..
    } = outcome
    {
        assert_eq!(states_explored, 6); // 0, 1, 2, 3, 4, 5
    }
}

#[test]
fn counter_invariant_violation() {
    // count < MAX is violated at count=MAX (the terminal state)
    let outcome = check(make_counter(3, TsBinOp::Lt));
    assert!(matches!(outcome, CheckOutcome::InvariantViolation { .. }));
    if let CheckOutcome::InvariantViolation { invariant, trace } = outcome {
        assert_eq!(invariant, "Bounded");
        // Trace should reach count=3 (which violates count < 3)
        assert!(!trace.is_empty());
    }
}

#[test]
fn two_independent_counters() {
    let ts = TransitionSystem {
        name: "TwoCounters".to_string(),
        variables: vec![
            TsVariable {
                name: "x".to_string(),
                ty: TsType::Nat,
            },
            TsVariable {
                name: "y".to_string(),
                ty: TsType::Nat,
            },
        ],
        constants: vec![TsConstant {
            name: "N".to_string(),
            ty: TsType::Nat,
            default_value: Some(2),
        }],
        init: vec![
            TsAssignment {
                var_idx: 0,
                value: TsExpr::Int { value: 0 },
            },
            TsAssignment {
                var_idx: 1,
                value: TsExpr::Int { value: 0 },
            },
        ],
        actions: vec![
            TsAction {
                name: "IncX".to_string(),
                params: vec![],
                guard: TsExpr::Binary {
                    op: TsBinOp::Lt,
                    left: Box::new(TsExpr::Var { index: 0 }),
                    right: Box::new(TsExpr::Const { index: 0 }),
                },
                assignments: vec![TsAssignment {
                    var_idx: 0,
                    value: TsExpr::Binary {
                        op: TsBinOp::Add,
                        left: Box::new(TsExpr::Var { index: 0 }),
                        right: Box::new(TsExpr::Int { value: 1 }),
                    },
                }],
            },
            TsAction {
                name: "IncY".to_string(),
                params: vec![],
                guard: TsExpr::Binary {
                    op: TsBinOp::Lt,
                    left: Box::new(TsExpr::Var { index: 1 }),
                    right: Box::new(TsExpr::Const { index: 0 }),
                },
                assignments: vec![TsAssignment {
                    var_idx: 1,
                    value: TsExpr::Binary {
                        op: TsBinOp::Add,
                        left: Box::new(TsExpr::Var { index: 1 }),
                        right: Box::new(TsExpr::Int { value: 1 }),
                    },
                }],
            },
        ],
        invariants: vec![TsInvariant {
            name: "BothBounded".to_string(),
            body: TsExpr::Binary {
                op: TsBinOp::And,
                left: Box::new(TsExpr::Binary {
                    op: TsBinOp::Le,
                    left: Box::new(TsExpr::Var { index: 0 }),
                    right: Box::new(TsExpr::Const { index: 0 }),
                }),
                right: Box::new(TsExpr::Binary {
                    op: TsBinOp::Le,
                    left: Box::new(TsExpr::Var { index: 1 }),
                    right: Box::new(TsExpr::Const { index: 0 }),
                }),
            },
        }],
        auxiliary_invariants: vec![],
        view_variables: None,
    };

    let spec = lower(&ts).unwrap();

    // IncX and IncY should be independent (different read/write sets)
    assert!(spec.independent[0][1]);
    assert!(spec.independent[1][0]);

    // Check passes with POR enabled
    let consts = vec![Value::int(2)];
    let config = CheckConfig {
        check_deadlock: false,
        use_por: true,
        ..CheckConfig::default()
    };
    let mut explorer = Explorer::new(spec, consts, config);
    let outcome = explorer.check().unwrap();
    assert!(matches!(outcome, CheckOutcome::Ok { .. }));
    // With POR, state count should be reduced from 9 (3x3 grid) to fewer
    if let CheckOutcome::Ok {
        states_explored, ..
    } = outcome
    {
        assert!(states_explored <= 9);
    }
}

#[test]
fn json_file_roundtrip() {
    let ts = make_counter(10, TsBinOp::Le);
    let json = serde_json::to_string_pretty(&ts).unwrap();
    let ts2: TransitionSystem = serde_json::from_str(&json).unwrap();
    assert_eq!(ts, ts2);

    // Lowered specs should produce same check result
    let outcome1 = check(ts);
    let outcome2 = check(ts2);
    match (&outcome1, &outcome2) {
        (
            CheckOutcome::Ok {
                states_explored: s1,
                ..
            },
            CheckOutcome::Ok {
                states_explored: s2,
                ..
            },
        ) => assert_eq!(s1, s2),
        _ => panic!("expected both Ok"),
    }
}

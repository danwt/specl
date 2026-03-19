//! Regression tests for specific parser and type-checker bugs.

use specl_eval::{EvalError, Value};
use specl_ir::compile;
use specl_mc::{CheckConfig, CheckOutcome, Explorer};
use specl_syntax::parse;

/// Helper: parse + typecheck a specl source string, returning the error message on failure.
fn parse_and_typecheck(source: &str) -> Result<(), String> {
    let module = parse(source).map_err(|e| format!("parse: {e}"))?;
    specl_types::check_module(&module).map_err(|e| format!("typecheck: {e}"))?;
    Ok(())
}

/// Helper: parse + typecheck + model-check a specl source with constants.
fn check_spec(source: &str, constants: &[(&str, i64)]) -> Result<CheckOutcome, String> {
    let module = parse(source).map_err(|e| format!("parse: {e}"))?;
    specl_types::check_module(&module).map_err(|e| format!("typecheck: {e}"))?;
    let spec = compile(&module).map_err(|e| format!("compile: {e}"))?;

    let mut const_values = vec![Value::none(); spec.consts.len()];
    for const_decl in &spec.consts {
        for &(name, val) in constants {
            if const_decl.name == name {
                const_values[const_decl.index] = Value::int(val);
            }
        }
    }

    let config = CheckConfig {
        check_deadlock: false,
        max_states: 10_000,
        max_depth: 100,
        ..Default::default()
    };
    let mut explorer = Explorer::new(spec, const_values, config);
    explorer.check().map_err(|e| format!("check: {e}"))
}

// ─── Issue #69: `in` operator in quantifier/fix bodies ───

#[test]
fn issue_69_in_operator_in_all_body() {
    let source = r#"
module Test
const MaxKey: 0..3
var written: Set[0..MaxKey]
invariant AllWritten {
    all key in 0..MaxKey : key in written
        implies len(written) == MaxKey + 1
}
init { written = {}; }
action Write(k: 0..MaxKey) { written = written union {k}; }
"#;
    parse_and_typecheck(source).expect("should parse and typecheck");
}

#[test]
fn issue_69_in_operator_in_any_body() {
    let source = r#"
module Test
const MaxKey: 0..3
var s: Set[0..MaxKey]
invariant AnyMember {
    (any k in 0..MaxKey : k in s) implies len(s) > 0
}
init { s = {}; }
action Add(k: 0..MaxKey) { s = s union {k}; }
"#;
    parse_and_typecheck(source).expect("should parse and typecheck");
}

#[test]
fn issue_69_in_operator_in_fix_body() {
    let source = r#"
module Test
const MaxKey: 0..3
var written: Set[0..MaxKey]
func FirstHole(ws) {
    if (all key in 0..MaxKey : key in ws) then
        MaxKey + 1
    else
        fix key in 0..MaxKey :
            not(key in ws) and (all k in 0..key : k in ws)
}
init { written = {}; }
action Write(k: 0..MaxKey) {
    require not(k in written);
    written = written union {k};
}
invariant HoleValid {
    let h = FirstHole(written) in h >= 0
}
"#;
    parse_and_typecheck(source).expect("should parse and typecheck");
}

#[test]
fn issue_69_nested_quantifiers_with_in() {
    let source = r#"
module Test
const N: 0..3
var s: Set[0..N]
invariant NestedIn {
    all x in 0..N : all y in 0..N :
        x in s and y in s implies x in s
}
init { s = {}; }
action Add(k: 0..N) { s = s union {k}; }
"#;
    parse_and_typecheck(source).expect("should parse and typecheck");
}

#[test]
fn issue_69_model_check_all_in() {
    let source = r#"
module Test
const MaxKey: 0..3
var written: Set[0..MaxKey]
init { written = {}; }
action Write(k: 0..MaxKey) { written = written union {k}; }
invariant Subset {
    all k in 0..MaxKey : k in written implies k in written
}
"#;
    let outcome = check_spec(source, &[("MaxKey", 2)]).expect("should check");
    assert!(
        matches!(
            outcome,
            CheckOutcome::Ok { .. } | CheckOutcome::StateLimitReached { .. }
        ),
        "expected OK, got: {outcome:?}"
    );
}

// ─── Issue #70: type inference for `in` with untyped func params ───

#[test]
fn issue_70_in_with_untyped_func_param() {
    let source = r#"
module Test
var s: Set[0..3]
func contains(S, x) { x in S }
init { s = {}; }
action Add(k: 0..3) { s = s union {k}; }
invariant ContainsWorks {
    all k in 0..3 : (k in s) implies contains(s, k)
}
"#;
    parse_and_typecheck(source).expect("should parse and typecheck");
}

#[test]
fn issue_70_if_in_with_untyped_func_param() {
    let source = r#"
module Test
var s: Set[0..3]
func addIfMissing(S, x) {
    if x in S then S else S union {x}
}
init { s = {}; }
action Add(k: 0..3) { s = addIfMissing(s, k); }
invariant AddWorks {
    all k in 0..3 : (k in s) implies (k in addIfMissing(s, k))
}
"#;
    parse_and_typecheck(source).expect("should parse and typecheck");
}

// ─── Ensure `let...in` still works (no regression from fix) ───

#[test]
fn let_in_still_works() {
    let source = r#"
module Test
var x: 0..10
init { x = 0; }
action Inc() { require x < 10; x = x + 1; }
invariant LetWorks {
    let y = x + 1 in y >= 1
}
"#;
    parse_and_typecheck(source).expect("let...in should still parse");
}

// ─── Issue #72: `not in` binary operator ───

#[test]
fn issue_72_not_in_parses() {
    let source = r#"
module Test
var s: Set[0..3]
init { s = {}; }
action Add(k: 0..3) {
    require k not in s;
    s = s union {k};
}
invariant NotInWorks {
    all k in 0..3 : k not in s or k in s
}
"#;
    parse_and_typecheck(source).expect("`not in` should parse as binary operator");
}

#[test]
fn issue_72_not_in_func_param() {
    let source = r#"
module Test
var s: Set[0..3]
func isMissing(S, x) { x not in S }
init { s = {}; }
action Add(k: 0..3) { s = s union {k}; }
invariant FuncNotIn {
    all k in 0..3 : isMissing(s, k) implies not(k in s)
}
"#;
    parse_and_typecheck(source).expect("`not in` should work in func with untyped params");
}

#[test]
fn issue_72_not_in_model_check() {
    let source = r#"
module Test
const N: 0..3
var s: Set[0..N]
init { s = {}; }
action Add(k: 0..N) {
    require k not in s;
    s = s union {k};
}
invariant NotInConsistent {
    all k in 0..N : k not in s or k in s
}
"#;
    let outcome = check_spec(source, &[("N", 2)]).expect("should check");
    assert!(
        matches!(
            outcome,
            CheckOutcome::Ok { .. } | CheckOutcome::StateLimitReached { .. }
        ),
        "expected OK, got: {outcome:?}"
    );
}

// ─── Issue #73: type inference for built-in functions with untyped params ───

#[test]
fn issue_73_keys_untyped_param() {
    let source = r#"
module Test
var d: Dict[0..3, 0..3]
func getKeys(D) { keys(D) }
init { d = {k: 0 for k in 0..3}; }
action Noop() { d = d; }
invariant KeysWork { getKeys(d) == 0..3 }
"#;
    parse_and_typecheck(source).expect("keys() should work with untyped param");
}

#[test]
fn issue_73_values_untyped_param() {
    let source = r#"
module Test
var d: Dict[0..3, 0..3]
func getValues(D) { values(D) }
init { d = {k: 0 for k in 0..3}; }
action Noop() { d = d; }
invariant ValuesSubset { all v in getValues(d) : v in 0..3 }
"#;
    parse_and_typecheck(source).expect("values() should work with untyped param");
}

#[test]
fn issue_73_powerset_untyped_param() {
    let source = r#"
module Test
var s: Set[0..3]
func getPowerset(S) { powerset(S) }
init { s = {}; }
action Add(k: 0..3) { s = s union {k}; }
invariant PowersetContainsSelf { s in getPowerset(s) }
"#;
    parse_and_typecheck(source).expect("powerset() should work with untyped param");
}

#[test]
fn issue_73_keys_model_check() {
    let source = r#"
module Test
const N: 0..3
var d: Dict[0..N, 0..N]
func getKeys(D) { keys(D) }
init { d = {k: 0 for k in 0..N}; }
action Update(k: 0..N, v: 0..N) { d = d | {k: v}; }
invariant KeysDomain { getKeys(d) == 0..N }
"#;
    let outcome = check_spec(source, &[("N", 2)]).expect("should check");
    assert!(
        matches!(
            outcome,
            CheckOutcome::Ok { .. } | CheckOutcome::StateLimitReached { .. }
        ),
        "expected OK, got: {outcome:?}"
    );
}

// ─── Ensure `let...in` still works (no regression from fix) ───

#[test]
fn let_in_inside_quantifier_body() {
    // In `let x = EXPR in BODY`, `in` is a keyword separator, so membership
    // tests in the value position require parentheses: `let x = (k in s) in ...`
    let source = r#"
module Test
const N: 0..3
var s: Set[0..N]
init { s = {}; }
action Add(k: 0..N) { s = s union {k}; }
invariant LetInQuantifier {
    all k in 0..N :
        let present = (k in s) in
        present or not(present)
}
"#;
    parse_and_typecheck(source).expect("let...in inside quantifier body should work");
}

// ─── Overflow detection ───

#[test]
fn overflow_detected_in_eval() {
    // Verify that checked arithmetic produces EvalError::Overflow.
    use specl_eval::{eval, EvalContext};
    use specl_ir::{BinOp, CompiledExpr};

    let big = CompiledExpr::Int(i64::MAX);
    let one = CompiledExpr::Int(1);
    let overflow_expr = CompiledExpr::Binary {
        op: BinOp::Add,
        left: Box::new(big),
        right: Box::new(one),
    };
    let ctx_vars: Vec<Value> = vec![];
    let ctx_consts: Vec<Value> = vec![];
    let ctx_params: Vec<Value> = vec![];
    let mut ctx = EvalContext::new(&ctx_vars, &ctx_vars, &ctx_consts, &ctx_params);
    let result = eval(&overflow_expr, &mut ctx);
    assert!(result.is_err(), "i64::MAX + 1 should produce overflow");
    assert!(
        matches!(result.unwrap_err(), EvalError::Overflow),
        "expected EvalError::Overflow"
    );
}

#[test]
fn overflow_detected_in_eval_mul() {
    use specl_eval::{eval, EvalContext};
    use specl_ir::{BinOp, CompiledExpr};

    let big = CompiledExpr::Int(i64::MAX);
    let two = CompiledExpr::Int(2);
    let overflow_expr = CompiledExpr::Binary {
        op: BinOp::Mul,
        left: Box::new(big),
        right: Box::new(two),
    };
    let vars: Vec<Value> = vec![];
    let consts: Vec<Value> = vec![];
    let params: Vec<Value> = vec![];
    let mut ctx = EvalContext::new(&vars, &vars, &consts, &params);
    let result = eval(&overflow_expr, &mut ctx);
    assert!(result.is_err(), "i64::MAX * 2 should produce overflow");
    assert!(
        matches!(result.unwrap_err(), EvalError::Overflow),
        "expected EvalError::Overflow"
    );
}

#[test]
fn overflow_spec_handled_gracefully() {
    // The model checker silently treats eval errors in action effects as
    // "action disabled" (no successors). This test verifies the checker
    // doesn't crash when an action causes overflow.
    let source = r#"
module Overflow
var x: 0..100000
init { x = 100000; }
action Square() { x = x * x; }
invariant NoOverflow { x >= 0 }
"#;
    let result = check_spec(source, &[]);
    assert!(
        result.is_ok(),
        "model checker should handle overflow gracefully, got: {result:?}"
    );
}

// ─── Bounds checking ───

#[test]
fn bounds_check_dict_missing_key_graceful() {
    // Dict access with a missing key in an action effect is treated as
    // "action disabled" by the model checker (no crash).
    let source = r#"
module BoundsCheck
var d: Dict[0..2, 0..5]
var result: 0..5
init {
    d = {k: k for k in 0..2};
    result = 0;
}
action LookupOutOfBounds() {
    result = d[3];
}
invariant ResultValid { result >= 0 }
"#;
    let result = check_spec(source, &[]);
    assert!(
        result.is_ok(),
        "model checker should handle missing key gracefully, got: {result:?}"
    );
}

#[test]
fn bounds_check_seq_index_out_of_bounds_graceful() {
    // Seq access with an out-of-bounds index in an action effect is treated
    // as "action disabled" by the model checker (no crash).
    let source = r#"
module SeqBounds
var s: Seq[0..3]
var result: 0..3
init {
    s = [1, 2];
    result = 0;
}
action IndexOutOfBounds() {
    result = s[5];
}
invariant ResultValid { result >= 0 }
"#;
    let result = check_spec(source, &[]);
    assert!(
        result.is_ok(),
        "model checker should handle out-of-bounds index gracefully, got: {result:?}"
    );
}

#[test]
fn bounds_check_key_not_found_in_eval() {
    // Verify that dict key-not-found produces EvalError::KeyNotFound at the eval level.
    use specl_eval::{eval, EvalContext};
    use specl_ir::CompiledExpr;

    // Build: {0: 10, 1: 20}[5]  -- key 5 doesn't exist
    let dict_expr = CompiledExpr::DictLit(vec![
        (CompiledExpr::Int(0), CompiledExpr::Int(10)),
        (CompiledExpr::Int(1), CompiledExpr::Int(20)),
    ]);
    let index_expr = CompiledExpr::Index {
        base: Box::new(dict_expr),
        index: Box::new(CompiledExpr::Int(5)),
    };
    let vars: Vec<Value> = vec![];
    let consts: Vec<Value> = vec![];
    let params: Vec<Value> = vec![];
    let mut ctx = EvalContext::new(&vars, &vars, &consts, &params);
    let result = eval(&index_expr, &mut ctx);
    assert!(
        result.is_err(),
        "dict access with missing key should produce error"
    );
    let err = result.unwrap_err();
    assert!(
        matches!(err, EvalError::KeyNotFound(_)),
        "expected KeyNotFound, got: {err:?}"
    );
}

#[test]
fn bounds_check_seq_index_in_eval() {
    // Verify that seq index-out-of-bounds produces EvalError::IndexOutOfBounds at the eval level.
    use specl_eval::{eval, EvalContext};
    use specl_ir::CompiledExpr;

    // Build: [10, 20][5]  -- index 5 is out of bounds for length-2 seq
    let seq_expr = CompiledExpr::SeqLit(vec![CompiledExpr::Int(10), CompiledExpr::Int(20)]);
    let index_expr = CompiledExpr::Index {
        base: Box::new(seq_expr),
        index: Box::new(CompiledExpr::Int(5)),
    };
    let vars: Vec<Value> = vec![];
    let consts: Vec<Value> = vec![];
    let params: Vec<Value> = vec![];
    let mut ctx = EvalContext::new(&vars, &vars, &consts, &params);
    let result = eval(&index_expr, &mut ctx);
    assert!(
        result.is_err(),
        "seq access with out-of-bounds index should produce error"
    );
    let err = result.unwrap_err();
    assert!(
        matches!(err, EvalError::IndexOutOfBounds { .. }),
        "expected IndexOutOfBounds, got: {err:?}"
    );
}

// ─── Edge case: dead action (guard always false) ───

#[test]
fn dead_action_single_state_explored() {
    let source = r#"
module DeadAction
var x: 0..2
init { x = 0; }
action DeadAction() {
    require x > 100;
    x = 1;
}
invariant Trivial { x >= 0 }
"#;
    let outcome = check_spec(source, &[]).expect("should check");
    match &outcome {
        CheckOutcome::Ok {
            states_explored, ..
        } => {
            assert_eq!(
                *states_explored, 1,
                "dead action should yield only the init state"
            );
        }
        other => panic!("expected Ok with 1 state, got: {other:?}"),
    }
}

#[test]
fn dead_action_no_deadlock_when_disabled() {
    // With check_deadlock=false, a spec whose only action is dead should still pass.
    let source = r#"
module DeadAction
var x: 0..2
init { x = 0; }
action DeadAction() {
    require x > 100;
    x = 1;
}
invariant Trivial { x >= 0 }
"#;
    let module = parse(source).unwrap();
    specl_types::check_module(&module).unwrap();
    let spec = compile(&module).unwrap();
    let config = CheckConfig {
        check_deadlock: false,
        max_states: 10_000,
        max_depth: 100,
        ..Default::default()
    };
    let mut explorer = Explorer::new(spec, vec![], config);
    let outcome = explorer.check().expect("should check");
    assert!(
        matches!(outcome, CheckOutcome::Ok { .. }),
        "expected Ok, got: {outcome:?}"
    );
}

#[test]
fn dead_action_deadlock_when_enabled() {
    // With check_deadlock=true, a spec whose only action is dead should report deadlock.
    let source = r#"
module DeadAction
var x: 0..2
init { x = 0; }
action DeadAction() {
    require x > 100;
    x = 1;
}
invariant Trivial { x >= 0 }
"#;
    let module = parse(source).unwrap();
    specl_types::check_module(&module).unwrap();
    let spec = compile(&module).unwrap();
    let config = CheckConfig {
        check_deadlock: true,
        max_states: 10_000,
        max_depth: 100,
        ..Default::default()
    };
    let mut explorer = Explorer::new(spec, vec![], config);
    let outcome = explorer.check().expect("should check");
    assert!(
        matches!(outcome, CheckOutcome::Deadlock { .. }),
        "expected Deadlock, got: {outcome:?}"
    );
}

// ─── Edge case: single reachable state ───

#[test]
fn single_state_noop_action() {
    let source = r#"
module SingleState
var x: Bool
init { x = true; }
action Noop() { x = true; }
invariant Always { x }
"#;
    let outcome = check_spec(source, &[]).expect("should check");
    match &outcome {
        CheckOutcome::Ok {
            states_explored, ..
        } => {
            assert_eq!(
                *states_explored, 1,
                "noop should yield exactly 1 reachable state"
            );
        }
        other => panic!("expected Ok with 1 state, got: {other:?}"),
    }
}

// ─── Edge case: large constant values ───

#[test]
fn large_constant_linear_state_space() {
    let source = r#"
module LargeConstant
const N: 1..1000
var x: 0..N
init { x = 0; }
action Inc() {
    require x < N;
    x = x + 1;
}
invariant Bound { x <= N }
"#;
    let outcome = check_spec(source, &[("N", 100)]).expect("should check");
    match &outcome {
        CheckOutcome::Ok {
            states_explored, ..
        } => {
            assert_eq!(
                *states_explored, 101,
                "N=100 should produce exactly 101 states (0..100)"
            );
        }
        other => panic!("expected Ok with 101 states, got: {other:?}"),
    }
}

#[test]
fn large_constant_invariant_holds() {
    let source = r#"
module LargeConstant
const N: 1..1000
var x: 0..N
init { x = 0; }
action Inc() {
    require x < N;
    x = x + 1;
}
invariant Bound { x <= N }
"#;
    let outcome = check_spec(source, &[("N", 500)]).expect("should check");
    assert!(
        matches!(
            outcome,
            CheckOutcome::Ok { .. } | CheckOutcome::StateLimitReached { .. }
        ),
        "expected Ok or StateLimitReached, got: {outcome:?}"
    );
}

// ─── Edge case: nested dict access and update ───

#[test]
fn nested_dict_model_check() {
    let source = r#"
module NestedDict
const N: 0..3
var grid: Dict[0..N, Dict[0..N, 0..5]]
init {
    grid = {i: {j: 0 for j in 0..N} for i in 0..N};
}
action Bump(i: 0..N, j: 0..N) {
    require grid[i][j] < 5;
    grid = grid | {i: grid[i] | {j: grid[i][j] + 1}};
}
invariant Pos {
    all i in 0..N: all j in 0..N: grid[i][j] >= 0
}
"#;
    let outcome = check_spec(source, &[("N", 1)]).expect("should check");
    assert!(
        matches!(
            outcome,
            CheckOutcome::Ok { .. } | CheckOutcome::StateLimitReached { .. }
        ),
        "expected Ok or StateLimitReached, got: {outcome:?}"
    );
}

#[test]
fn nested_dict_state_count() {
    // With N=1 we have a 2x2 grid each cell in 0..5, giving 6^4 = 1296 states.
    let source = r#"
module NestedDict
const N: 0..3
var grid: Dict[0..N, Dict[0..N, 0..5]]
init {
    grid = {i: {j: 0 for j in 0..N} for i in 0..N};
}
action Bump(i: 0..N, j: 0..N) {
    require grid[i][j] < 5;
    grid = grid | {i: grid[i] | {j: grid[i][j] + 1}};
}
invariant Pos {
    all i in 0..N: all j in 0..N: grid[i][j] >= 0
}
"#;
    let outcome = check_spec(source, &[("N", 1)]).expect("should check");
    match &outcome {
        CheckOutcome::Ok {
            states_explored, ..
        } => {
            assert_eq!(
                *states_explored, 1296,
                "2x2 grid with 0..5 should yield 6^4 = 1296 states"
            );
        }
        other => panic!("expected Ok with 1296 states, got: {other:?}"),
    }
}

// ─── Edge case: set comprehension with filter ───

#[test]
fn set_comprehension_filter_complement() {
    // s starts as {3,4,5}, Expand sets s to complement {0,1,2}, then back to {3,4,5}.
    // Two reachable states.
    let source = r#"
module SetComprehensionFilter
const N: 0..10
var s: Set[0..N]
init {
    s = {i in 0..N if i > 2};
}
action Expand() {
    s = {i in 0..N if not(i in s)};
}
invariant NonEmpty { len(s) > 0 }
"#;
    let outcome = check_spec(source, &[("N", 5)]).expect("should check");
    match &outcome {
        CheckOutcome::Ok {
            states_explored, ..
        } => {
            assert_eq!(
                *states_explored, 2,
                "complement toggle should yield exactly 2 states"
            );
        }
        other => panic!("expected Ok with 2 states, got: {other:?}"),
    }
}

#[test]
fn set_comprehension_filter_invariant_holds() {
    let source = r#"
module SetComprehensionFilter
const N: 0..10
var s: Set[0..N]
init {
    s = {i in 0..N if i > 2};
}
action Expand() {
    s = {i in 0..N if not(i in s)};
}
invariant NonEmpty { len(s) > 0 }
"#;
    let outcome = check_spec(source, &[("N", 5)]).expect("should check");
    assert!(
        matches!(outcome, CheckOutcome::Ok { .. }),
        "NonEmpty invariant should hold, got: {outcome:?}"
    );
}

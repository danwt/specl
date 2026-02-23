//! Regression tests for specific parser and type-checker bugs.

use specl_eval::Value;
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
        matches!(outcome, CheckOutcome::Ok { .. } | CheckOutcome::StateLimitReached { .. }),
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

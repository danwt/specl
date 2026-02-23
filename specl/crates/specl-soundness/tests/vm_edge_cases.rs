//! Crash-free VM edge case tests.
//!
//! Hand-crafted expressions through the full pipeline (parse -> typecheck ->
//! compile -> eval/check) asserting no panics on tricky edge cases:
//! empty collections, division by zero, deep nesting, powerset of empty set,
//! sequence operations on empty sequences.

use specl_mc::CheckConfig;
use specl_soundness::{check_spec, compile_spec};

fn default_config() -> CheckConfig {
    CheckConfig {
        check_deadlock: false,
        max_states: 10_000,
        max_depth: 100,
        ..CheckConfig::default()
    }
}

/// Assert spec compiles and model-checks without panic.
fn assert_no_crash(source: &str) {
    let compiled = compile_spec(source);
    assert!(compiled.is_ok(), "compile failed: {:?}", compiled.err());
    let outcome = check_spec(source, default_config());
    assert!(outcome.is_ok(), "check failed: {:?}", outcome.err());
}

// ─── Empty sets and dicts ───

#[test]
fn empty_set_len() {
    assert_no_crash(
        r#"module Test
var s: Set[0..2]
init { s = {}; }
action Add(k: 0..2) { s = s union {k}; }
invariant EmptyLen { len({}) == 0 }
"#,
    );
}

#[test]
fn empty_set_union() {
    assert_no_crash(
        r#"module Test
var s: Set[0..2]
init { s = {}; }
action Add(k: 0..2) { s = s union {k}; }
invariant UnionEmpty { {} union {} == {} }
invariant UnionIdentity { s union {} == s }
"#,
    );
}

#[test]
fn empty_set_diff() {
    assert_no_crash(
        r#"module Test
var s: Set[0..2]
init { s = {}; }
action Add(k: 0..2) { s = s union {k}; }
invariant DiffEmpty { s diff {} == s }
invariant EmptyDiff { {} diff s == {} }
"#,
    );
}

#[test]
fn empty_set_intersect() {
    assert_no_crash(
        r#"module Test
var s: Set[0..2]
init { s = {}; }
action Add(k: 0..2) { s = s union {k}; }
invariant IntersectEmpty { s intersect {} == {} }
"#,
    );
}

#[test]
fn empty_set_subset() {
    assert_no_crash(
        r#"module Test
var s: Set[0..2]
init { s = {}; }
action Add(k: 0..2) { s = s union {k}; }
invariant EmptySubset { {} subset_of s }
"#,
    );
}

#[test]
fn empty_dict_access() {
    assert_no_crash(
        r#"module Test
var d: Dict[0..2, 0..2]
init { d = {k: 0 for k in 0..2}; }
action Update(k: 0..2, v: 0..2) { d = d | {k: v}; }
invariant AllKeysExist { all k in 0..2 : d[k] >= 0 }
"#,
    );
}

// ─── Deep nesting ───

#[test]
fn deep_nested_quantifiers() {
    assert_no_crash(
        r#"module Test
var s: Set[0..2]
init { s = {}; }
action Add(k: 0..2) { s = s union {k}; }
invariant DeepNesting {
    all x in 0..2 :
        all y in 0..2 :
            all z in 0..2 :
                (x in s and y in s and z in s) implies true
}
"#,
    );
}

#[test]
fn deep_nested_let() {
    assert_no_crash(
        r#"module Test
var x: 0..3
init { x = 0; }
action Inc() { require x < 3; x = x + 1; }
invariant DeepLet {
    let a = x in
    let b = a + 1 in
    let c = b + 1 in
    let d = c + 1 in
    d >= 3
}
"#,
    );
}

#[test]
fn deep_nested_if() {
    assert_no_crash(
        r#"module Test
var x: 0..3
init { x = 0; }
action Inc() { require x < 3; x = x + 1; }
invariant DeepIf {
    (if x == 0 then
        (if x == 1 then false else true)
    else
        (if x == 2 then true else true))
}
"#,
    );
}

// ─── Powerset ───

#[test]
fn powerset_empty_set() {
    assert_no_crash(
        r#"module Test
var s: Set[0..1]
init { s = {}; }
action Add(k: 0..1) { s = s union {k}; }
invariant EmptyInPowerset { {} in powerset(0..1) }
invariant SelfInPowerset { s in powerset(0..1) }
"#,
    );
}

// ─── Fix expressions ───

#[test]
fn fix_basic() {
    assert_no_crash(
        r#"module Test
var s: Set[0..2]
init { s = {}; }
action Add(k: 0..2) { s = s union {k}; }
invariant FixValid {
    len(s) < 3 implies (
        let fm = (fix k in 0..2 : not(k in s)) in fm >= 0
    )
}
"#,
    );
}

// ─── Sequence operations ───

#[test]
fn seq_empty_len() {
    assert_no_crash(
        r#"module Test
var msgs: Seq[0..1]
init { msgs = []; }
action Send(v: 0..1) { require len(msgs) < 2; msgs = msgs ++ [v]; }
action Recv() { require len(msgs) > 0; msgs = tail(msgs); }
invariant EmptySeqLen { len([]) == 0 }
"#,
    );
}

#[test]
fn seq_head_guarded() {
    assert_no_crash(
        r#"module Test
var msgs: Seq[0..1]
init { msgs = []; }
action Send(v: 0..1) { require len(msgs) < 2; msgs = msgs ++ [v]; }
action Recv() { require len(msgs) > 0; msgs = tail(msgs); }
invariant HeadGuarded {
    len(msgs) > 0 implies head(msgs) >= 0
}
"#,
    );
}

#[test]
fn seq_concat_empty() {
    assert_no_crash(
        r#"module Test
var msgs: Seq[0..1]
init { msgs = []; }
action Send(v: 0..1) { require len(msgs) < 2; msgs = msgs ++ [v]; }
invariant ConcatEmpty { msgs ++ [] == msgs }
"#,
    );
}

// ─── Comprehensions with complex filters ───

#[test]
fn comprehension_nested_filter() {
    assert_no_crash(
        r#"module Test
var s: Set[0..3]
init { s = {}; }
action Add(k: 0..3) { s = s union {k}; }
invariant CompFilter {
    {x in 0..3 if x in s and x > 0} subset_of s
}
"#,
    );
}

#[test]
fn comprehension_empty_result() {
    assert_no_crash(
        r#"module Test
var s: Set[0..2]
init { s = {}; }
action Add(k: 0..2) { s = s union {k}; }
invariant InitiallyEmpty {
    len(s) == 0 implies {x in 0..2 if x in s} == {}
}
"#,
    );
}

// ─── Iff and boolean edge cases ───

#[test]
fn iff_basic() {
    assert_no_crash(
        r#"module Test
var x: 0..2
init { x = 0; }
action Inc() { require x < 2; x = x + 1; }
invariant IffSelfTrue { (x == 0) iff (x == 0) }
invariant IffCommutative { (x == 1 iff x == 1) }
"#,
    );
}

// ─── Tuple operations ───

#[test]
fn tuple_basic() {
    assert_no_crash(
        r#"module Test
var pair: (0..2, 0..2)
init { pair = (0, 0); }
action StepBoth() {
    require pair.0 < 2;
    require pair.1 < 2;
    pair = (pair.0 + 1, pair.1 + 1);
}
invariant PairBounded { pair.0 <= 2 and pair.1 <= 2 }
"#,
    );
}

// ─── Set operations chain ───

#[test]
fn set_ops_chain() {
    assert_no_crash(
        r#"module Test
var s1: Set[0..2]
var s2: Set[0..2]
init { s1 = {}; s2 = {}; }
action Add1(k: 0..2) { s1 = s1 union {k}; }
action Add2(k: 0..2) { s2 = s2 union {k}; }
invariant ChainOps {
    (s1 union s2) diff (s1 intersect s2) == (s1 diff s2) union (s2 diff s1)
}
"#,
    );
}

// ─── Dict comprehension ───

#[test]
fn dict_comprehension() {
    assert_no_crash(
        r#"module Test
var d: Dict[0..2, 0..2]
init { d = {k: 0 for k in 0..2}; }
action Update(k: 0..2, v: 0..2) { d = d | {k: v}; }
invariant ComprehensionKeys {
    all k in 0..2 : d[k] >= 0
}
"#,
    );
}

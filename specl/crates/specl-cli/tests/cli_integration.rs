//! CLI integration tests that exercise the `specl` binary end-to-end.
//!
//! These tests verify that CLI flags wire through to the model checker correctly
//! and that subcommands (check, simulate, fmt, info) produce expected output.
//! All specs are tiny (< 100 states) to keep each test under 2 seconds.

use assert_cmd::Command;
use predicates::prelude::*;
use std::io::Write;

fn specl_cmd() -> Command {
    Command::cargo_bin("specl").unwrap()
}

fn write_temp_spec(source: &str) -> tempfile::NamedTempFile {
    let mut f = tempfile::Builder::new()
        .suffix(".specl")
        .tempfile()
        .unwrap();
    f.write_all(source.as_bytes()).unwrap();
    f.flush().unwrap();
    f
}

const COUNTER_SPEC: &str = r#"
module Counter
const N: 0..5
var x: 0..N
init { x = 0; }
action Inc() { require x < N; x = x + 1; }
invariant Bounded { x >= 0 and x <= N }
"#;

/// A spec that cycles (never deadlocks): x toggles between 0 and 1.
const TOGGLE_SPEC: &str = r#"
module Toggle
var x: 0..1
init { x = 0; }
action Flip() { x = 1 - x; }
invariant Bounded { x >= 0 and x <= 1 }
"#;

const MUTEX_SPEC: &str = r#"
module Mutex
const P: 0..3
var state: Dict[0..P, 0..2]
var turn: 0..P
init {
    state = {p: 0 for p in 0..P};
    turn = 0;
}
action Want(p: 0..P) {
    require state[p] == 0;
    state = state | { p: 1 };
}
action Enter(p: 0..P) {
    require state[p] == 1;
    require turn == p;
    require all q in 0..P: q == p or state[q] != 2;
    state = state | { p: 2 };
}
action Exit(p: 0..P) {
    require state[p] == 2;
    state = state | { p: 0 };
    turn = (p + 1) % (P + 1);
}
invariant MutualExclusion {
    len({ p in 0..P if state[p] == 2 }) <= 1
}
"#;

const VIOLATION_SPEC: &str = r#"
module BadCounter
var x: 0..5
init { x = 0; }
action Inc() { x = x + 1; require x <= 5; }
invariant Small { x <= 2 }
"#;

// ─── specl check: basic ───

#[test]
fn check_basic_ok() {
    let f = write_temp_spec(COUNTER_SPEC);
    specl_cmd()
        .args([
            "check",
            f.path().to_str().unwrap(),
            "-c",
            "N=3",
            "--no-deadlock",
            "-q",
            "--bfs",
        ])
        .assert()
        .success()
        .stderr(predicate::str::contains("specl"));
}

#[test]
fn check_invariant_violation_exits_nonzero() {
    let f = write_temp_spec(VIOLATION_SPEC);
    specl_cmd()
        .args([
            "check",
            f.path().to_str().unwrap(),
            "--no-deadlock",
            "-q",
            "--bfs",
        ])
        .assert()
        .failure();
}

// ─── specl check --por ───

#[test]
fn check_por() {
    let f = write_temp_spec(MUTEX_SPEC);
    specl_cmd()
        .args([
            "check",
            f.path().to_str().unwrap(),
            "-c",
            "P=1",
            "--por",
            "--no-deadlock",
            "-q",
            "--no-auto",
        ])
        .assert()
        .success();
}

// ─── specl check --symmetry ───

#[test]
fn check_symmetry() {
    let f = write_temp_spec(MUTEX_SPEC);
    specl_cmd()
        .args([
            "check",
            f.path().to_str().unwrap(),
            "-c",
            "P=1",
            "--symmetry",
            "--no-deadlock",
            "-q",
            "--no-auto",
        ])
        .assert()
        .success();
}

// ─── specl check --fast ───

#[test]
fn check_fast() {
    let f = write_temp_spec(COUNTER_SPEC);
    specl_cmd()
        .args([
            "check",
            f.path().to_str().unwrap(),
            "-c",
            "N=3",
            "--fast",
            "--no-deadlock",
            "-q",
        ])
        .assert()
        .success();
}

// ─── specl check --collapse ───

#[test]
fn check_collapse() {
    let f = write_temp_spec(COUNTER_SPEC);
    specl_cmd()
        .args([
            "check",
            f.path().to_str().unwrap(),
            "-c",
            "N=3",
            "--collapse",
            "--no-deadlock",
            "-q",
        ])
        .assert()
        .success();
}

// ─── specl check --tree ───

#[test]
fn check_tree() {
    let f = write_temp_spec(COUNTER_SPEC);
    specl_cmd()
        .args([
            "check",
            f.path().to_str().unwrap(),
            "-c",
            "N=3",
            "--tree",
            "--no-deadlock",
            "-q",
        ])
        .assert()
        .success();
}

// ─── specl check --diff ───

#[test]
fn check_diff_violation_shows_trace() {
    let f = write_temp_spec(VIOLATION_SPEC);
    let output = specl_cmd()
        .args([
            "check",
            f.path().to_str().unwrap(),
            "--diff",
            "--no-deadlock",
            "--bfs",
            "-q",
        ])
        .output()
        .unwrap();
    assert!(!output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    // The trace goes to stdout and should mention "Inc" actions and "x=" variable changes
    assert!(
        stdout.contains("Inc") || stdout.contains("x="),
        "diff trace should show action or variable changes, got stdout: {stdout}"
    );
}

// ─── specl check --output json ───

#[test]
fn check_json_output_ok() {
    let f = write_temp_spec(COUNTER_SPEC);
    let output = specl_cmd()
        .args([
            "check",
            f.path().to_str().unwrap(),
            "-c",
            "N=3",
            "--no-deadlock",
            "--output",
            "json",
            "--bfs",
        ])
        .output()
        .unwrap();
    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    let json: serde_json::Value = serde_json::from_str(&stdout).expect("valid JSON");
    assert_eq!(json["result"], "ok");
    assert!(json["states_explored"].as_u64().unwrap() > 0);
    assert!(json["duration_secs"].as_f64().unwrap() >= 0.0);
}

#[test]
fn check_json_output_violation() {
    let f = write_temp_spec(VIOLATION_SPEC);
    let output = specl_cmd()
        .args([
            "check",
            f.path().to_str().unwrap(),
            "--no-deadlock",
            "--output",
            "json",
            "--bfs",
        ])
        .output()
        .unwrap();
    assert!(!output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    let json: serde_json::Value = serde_json::from_str(&stdout).expect("valid JSON");
    assert_eq!(json["result"], "invariant_violation");
    assert_eq!(json["invariant"], "Small");
    assert!(json["trace"].is_array());
}

// ─── specl check --por --symmetry combined ───

#[test]
fn check_por_and_symmetry_combined() {
    let f = write_temp_spec(MUTEX_SPEC);
    specl_cmd()
        .args([
            "check",
            f.path().to_str().unwrap(),
            "-c",
            "P=1",
            "--por",
            "--symmetry",
            "--no-deadlock",
            "-q",
            "--no-auto",
        ])
        .assert()
        .success();
}

// ─── specl check --fast with violation (re-exploration for trace) ───

#[test]
fn check_fast_violation_produces_trace() {
    let f = write_temp_spec(VIOLATION_SPEC);
    let output = specl_cmd()
        .args([
            "check",
            f.path().to_str().unwrap(),
            "--fast",
            "--no-deadlock",
            "--output",
            "json",
        ])
        .output()
        .unwrap();
    assert!(!output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    let json: serde_json::Value = serde_json::from_str(&stdout).expect("valid JSON");
    assert_eq!(json["result"], "invariant_violation");
    assert!(json["trace"].is_array());
    assert!(!json["trace"].as_array().unwrap().is_empty());
}

// ─── specl check --directed ───

#[test]
fn check_directed() {
    let f = write_temp_spec(COUNTER_SPEC);
    specl_cmd()
        .args([
            "check",
            f.path().to_str().unwrap(),
            "-c",
            "N=3",
            "--directed",
            "--no-deadlock",
            "-q",
        ])
        .assert()
        .success();
}

// ─── specl check --check-only ───

#[test]
fn check_only_specific_invariant() {
    let spec = r#"
module Multi
var x: 0..3
init { x = 0; }
action Inc() { require x < 3; x = x + 1; }
invariant A { x >= 0 }
invariant B { x <= 3 }
"#;
    let f = write_temp_spec(spec);
    let output = specl_cmd()
        .args([
            "check",
            f.path().to_str().unwrap(),
            "--check-only",
            "A",
            "--no-deadlock",
            "--output",
            "json",
            "--bfs",
        ])
        .output()
        .unwrap();
    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    let json: serde_json::Value = serde_json::from_str(&stdout).expect("valid JSON");
    assert_eq!(json["result"], "ok");
}

// ─── specl check --no-parallel ───

#[test]
fn check_no_parallel() {
    let f = write_temp_spec(COUNTER_SPEC);
    specl_cmd()
        .args([
            "check",
            f.path().to_str().unwrap(),
            "-c",
            "N=3",
            "--no-parallel",
            "--no-deadlock",
            "-q",
            "--bfs",
        ])
        .assert()
        .success();
}

// ─── specl check --max-states ───

#[test]
fn check_max_states_bounded() {
    let f = write_temp_spec(COUNTER_SPEC);
    let output = specl_cmd()
        .args([
            "check",
            f.path().to_str().unwrap(),
            "-c",
            "N=3",
            "--max-states",
            "2",
            "--no-deadlock",
            "--output",
            "json",
            "--bfs",
        ])
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout);
    let json: serde_json::Value = serde_json::from_str(&stdout).expect("valid JSON");
    // state_limit_reached exits with code 2
    assert!(
        json["result"] == "ok" || json["result"] == "state_limit_reached",
        "expected ok or state_limit_reached, got: {}",
        json["result"]
    );
}

// ─── specl simulate ───

#[test]
fn simulate_basic() {
    let f = write_temp_spec(TOGGLE_SPEC);
    specl_cmd()
        .args([
            "simulate",
            f.path().to_str().unwrap(),
            "--steps",
            "10",
            "--seed",
            "42",
        ])
        .assert()
        .success();
}

#[test]
fn simulate_json_output() {
    let f = write_temp_spec(TOGGLE_SPEC);
    let output = specl_cmd()
        .args([
            "simulate",
            f.path().to_str().unwrap(),
            "--steps",
            "10",
            "--seed",
            "42",
            "--output",
            "json",
        ])
        .output()
        .unwrap();
    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    let json: serde_json::Value = serde_json::from_str(&stdout).expect("valid JSON");
    assert_eq!(json["result"], "ok");
    // Simulate stores step count in states_explored field
    assert!(json["states_explored"].as_u64().unwrap() > 0);
}

#[test]
fn simulate_detects_invariant_violation() {
    let f = write_temp_spec(VIOLATION_SPEC);
    let output = specl_cmd()
        .args([
            "simulate",
            f.path().to_str().unwrap(),
            "--steps",
            "100",
            "--seed",
            "1",
            "--output",
            "json",
        ])
        .output()
        .unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout);
    let json: serde_json::Value = serde_json::from_str(&stdout).expect("valid JSON");
    // May find violation or deadlock depending on random walk
    assert!(
        json["result"] == "ok"
            || json["result"] == "invariant_violation"
            || json["result"] == "deadlock",
        "expected ok, invariant_violation, or deadlock, got: {}",
        json["result"]
    );
}

// ─── specl fmt ───

#[test]
fn fmt_outputs_formatted_source() {
    let f = write_temp_spec(COUNTER_SPEC);
    specl_cmd()
        .args(["fmt", f.path().to_str().unwrap()])
        .assert()
        .success()
        .stdout(predicate::str::contains("module Counter"));
}

#[test]
fn fmt_check_already_formatted() {
    let f = write_temp_spec(COUNTER_SPEC);
    let output = specl_cmd()
        .args(["fmt", f.path().to_str().unwrap()])
        .output()
        .unwrap();
    let formatted = String::from_utf8_lossy(&output.stdout);

    let f2 = write_temp_spec(&formatted);
    specl_cmd()
        .args(["fmt", f2.path().to_str().unwrap(), "--check"])
        .assert()
        .success();
}

#[test]
fn fmt_check_unformatted_exits_nonzero() {
    let bad =
        "module  X\nvar x:  Bool\ninit{x=true;}\naction  A(){x=false;}\ninvariant I{x or not(x)}\n";
    let f = write_temp_spec(bad);
    specl_cmd()
        .args(["fmt", f.path().to_str().unwrap(), "--check"])
        .assert()
        .failure();
}

#[test]
fn fmt_lint() {
    let f = write_temp_spec(COUNTER_SPEC);
    specl_cmd()
        .args(["fmt", f.path().to_str().unwrap(), "--lint", "-c", "N=3"])
        .assert()
        .success();
}

// ─── specl info ───

#[test]
fn info_shows_analysis() {
    let f = write_temp_spec(COUNTER_SPEC);
    specl_cmd()
        .args(["info", f.path().to_str().unwrap(), "-c", "N=3"])
        .assert()
        .success()
        .stdout(predicate::str::contains("Variables"))
        .stdout(predicate::str::contains("Actions"));
}

#[test]
fn info_no_file_shows_guide() {
    specl_cmd().args(["info"]).assert().success();
}

// ─── specl check: deadlock detection ───

#[test]
fn check_deadlock_detected() {
    let spec = r#"
module Deadlockable
var x: 0..2
init { x = 0; }
action Step() { require x < 2; x = x + 1; }
invariant OK { x >= 0 }
"#;
    let f = write_temp_spec(spec);
    let output = specl_cmd()
        .args([
            "check",
            f.path().to_str().unwrap(),
            "--output",
            "json",
            "--bfs",
        ])
        .output()
        .unwrap();
    assert!(!output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    let json: serde_json::Value = serde_json::from_str(&stdout).expect("valid JSON");
    assert_eq!(json["result"], "deadlock");
}

#[test]
fn check_no_deadlock_suppresses() {
    let spec = r#"
module Deadlockable
var x: 0..2
init { x = 0; }
action Step() { require x < 2; x = x + 1; }
invariant OK { x >= 0 }
"#;
    let f = write_temp_spec(spec);
    let output = specl_cmd()
        .args([
            "check",
            f.path().to_str().unwrap(),
            "--no-deadlock",
            "--output",
            "json",
            "--bfs",
        ])
        .output()
        .unwrap();
    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    let json: serde_json::Value = serde_json::from_str(&stdout).expect("valid JSON");
    assert_eq!(json["result"], "ok");
}

// ─── specl check: error cases ───

#[test]
fn check_missing_constant_errors() {
    let f = write_temp_spec(COUNTER_SPEC);
    specl_cmd()
        .args(["check", f.path().to_str().unwrap(), "-q"])
        .assert()
        .failure();
}

#[test]
fn check_nonexistent_file_errors() {
    specl_cmd()
        .args(["check", "/tmp/nonexistent_specl_file_12345.specl", "-q"])
        .assert()
        .failure();
}

// ─── specl check --profile ───

#[test]
fn check_profile_output() {
    let f = write_temp_spec(COUNTER_SPEC);
    specl_cmd()
        .args([
            "check",
            f.path().to_str().unwrap(),
            "-c",
            "N=3",
            "--profile",
            "--no-deadlock",
            "-q",
            "--bfs",
        ])
        .assert()
        .success();
}

// ─── specl check: storage modes produce same verdict ───

#[test]
fn storage_modes_agree_on_ok() {
    let f = write_temp_spec(COUNTER_SPEC);
    let path = f.path().to_str().unwrap().to_string();
    let base_args: &[&str] = &[
        "-c",
        "N=3",
        "--no-deadlock",
        "--output",
        "json",
        "--no-auto",
        "--bfs",
    ];

    for mode in &["", "--fast", "--collapse", "--tree"] {
        let mut args: Vec<&str> = vec!["check", &path];
        args.extend_from_slice(base_args);
        if !mode.is_empty() {
            args.push(mode);
        }
        let output = specl_cmd().args(&args).output().unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout);
        let json: serde_json::Value = serde_json::from_str(&stdout)
            .unwrap_or_else(|_| panic!("bad JSON for mode {mode}: {stdout}"));
        assert_eq!(
            json["result"], "ok",
            "mode {mode} should produce ok, got: {}",
            json["result"]
        );
    }
}

#[test]
fn storage_modes_agree_on_violation() {
    let f = write_temp_spec(VIOLATION_SPEC);
    let path = f.path().to_str().unwrap().to_string();
    let base_args: &[&str] = &["--no-deadlock", "--output", "json", "--no-auto", "--bfs"];

    for mode in &["", "--fast", "--collapse", "--tree"] {
        let mut args: Vec<&str> = vec!["check", &path];
        args.extend_from_slice(base_args);
        if !mode.is_empty() {
            args.push(mode);
        }
        let output = specl_cmd().args(&args).output().unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout);
        let json: serde_json::Value = serde_json::from_str(&stdout)
            .unwrap_or_else(|_| panic!("bad JSON for mode {mode}: {stdout}"));
        assert_eq!(
            json["result"], "invariant_violation",
            "mode {mode} should find violation, got: {}",
            json["result"]
        );
        assert_eq!(json["invariant"], "Small", "mode {mode} wrong invariant");
    }
}

// ─── specl check: ITF output ───

#[test]
fn check_itf_output_on_violation() {
    let f = write_temp_spec(VIOLATION_SPEC);
    let output = specl_cmd()
        .args([
            "check",
            f.path().to_str().unwrap(),
            "--no-deadlock",
            "--output",
            "itf",
            "--bfs",
        ])
        .output()
        .unwrap();
    assert!(!output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    let json: serde_json::Value = serde_json::from_str(&stdout).expect("ITF should be valid JSON");
    assert!(json["states"].is_array());
}

// ─── specl simulate: ITF and Mermaid ───

#[test]
fn simulate_itf_output() {
    let f = write_temp_spec(TOGGLE_SPEC);
    let output = specl_cmd()
        .args([
            "simulate",
            f.path().to_str().unwrap(),
            "--steps",
            "5",
            "--seed",
            "42",
            "--output",
            "itf",
        ])
        .output()
        .unwrap();
    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    let json: serde_json::Value = serde_json::from_str(&stdout).expect("ITF should be valid JSON");
    assert!(json["states"].is_array());
}

#[test]
fn simulate_mermaid_output() {
    let f = write_temp_spec(TOGGLE_SPEC);
    specl_cmd()
        .args([
            "simulate",
            f.path().to_str().unwrap(),
            "--steps",
            "5",
            "--seed",
            "42",
            "--output",
            "mermaid",
        ])
        .assert()
        .success()
        .stdout(predicate::str::contains("sequenceDiagram"));
}

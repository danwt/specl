//! Integration tests that verify all example .specl files can be processed.

use specl_eval::Value;
use specl_ir::compile;
use specl_mc::{CheckConfig, CheckOutcome, Explorer};
use specl_syntax::parse;
use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};

fn find_specl_files(dir: &Path) -> Vec<PathBuf> {
    let mut files = Vec::new();
    if dir.is_dir() {
        for entry in fs::read_dir(dir).unwrap() {
            let entry = entry.unwrap();
            let path = entry.path();
            if path.is_dir() {
                files.extend(find_specl_files(&path));
            } else if path.extension().map_or(false, |e| e == "specl") {
                files.push(path);
            }
        }
    }
    files
}

fn parse_use_comment(source: &str) -> HashMap<String, i64> {
    let mut constants = HashMap::new();
    for line in source.lines() {
        if line.starts_with("// Use:") {
            let rest = line.trim_start_matches("// Use:");
            for part in rest.split_whitespace() {
                if part.starts_with("-c") {
                    continue;
                }
                if let Some((name, value)) = part.split_once('=') {
                    if let Ok(v) = value.parse::<i64>() {
                        constants.insert(name.to_string(), v);
                    }
                }
            }
            break;
        }
    }
    constants
}

fn examples_dir() -> PathBuf {
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    PathBuf::from(manifest_dir)
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join("examples")
}

#[test]
fn all_examples_parse() {
    let examples = examples_dir();
    let files = find_specl_files(&examples);
    assert!(!files.is_empty(), "no .specl files found in {examples:?}");

    let mut failures = Vec::new();
    for file in &files {
        let source = fs::read_to_string(file).unwrap();
        if let Err(e) = parse(&source) {
            failures.push(format!("{}: {e}", file.display()));
        }
    }

    if !failures.is_empty() {
        panic!("parse failures:\n{}", failures.join("\n"));
    }
}

#[test]
fn all_examples_typecheck() {
    let examples = examples_dir();
    let files = find_specl_files(&examples);
    assert!(!files.is_empty(), "no .specl files found in {examples:?}");

    let mut failures = Vec::new();
    for file in &files {
        let source = fs::read_to_string(file).unwrap();
        let module = match parse(&source) {
            Ok(m) => m,
            Err(e) => {
                failures.push(format!("{}: parse error: {e}", file.display()));
                continue;
            }
        };

        if let Err(e) = specl_types::check_module(&module) {
            failures.push(format!("{}: {e}", file.display()));
        }
    }

    if !failures.is_empty() {
        panic!("typecheck failures:\n{}", failures.join("\n"));
    }
}

// Skip specs that are too large to check in CI
const SKIP_MODEL_CHECK: &[&str] = &[
    "RaftMongo.specl",        // Large state space with sequences
    "ChainReplication.specl", // Large state space with sequences
];

#[test]
fn examples_with_constants_check() {
    let examples = examples_dir();
    let files = find_specl_files(&examples);

    let mut failures = Vec::new();
    let mut checked = 0;

    for file in &files {
        // Skip files that are too large
        let filename = file.file_name().unwrap().to_str().unwrap();
        if SKIP_MODEL_CHECK.contains(&filename) {
            continue;
        }

        let source = fs::read_to_string(file).unwrap();
        let constants = parse_use_comment(&source);

        // Skip files without constants specified or with "No constants needed"
        if constants.is_empty() && !source.contains("No constants needed") {
            continue;
        }

        let module = match parse(&source) {
            Ok(m) => m,
            Err(e) => {
                failures.push(format!("{}: parse error: {e}", file.display()));
                continue;
            }
        };

        if let Err(e) = specl_types::check_module(&module) {
            failures.push(format!("{}: typecheck error: {e}", file.display()));
            continue;
        }

        let spec = match compile(&module) {
            Ok(s) => s,
            Err(e) => {
                failures.push(format!("{}: compile error: {e}", file.display()));
                continue;
            }
        };

        // Build constant values
        let mut const_values = vec![Value::None; spec.consts.len()];
        for const_decl in &spec.consts {
            if let Some(&v) = constants.get(&const_decl.name) {
                const_values[const_decl.index] = Value::Int(v);
            } else {
                // Use default value of 1 for unspecified constants
                const_values[const_decl.index] = Value::Int(1);
            }
        }

        let config = CheckConfig {
            check_deadlock: false,
            max_states: 10000,
            max_depth: 100,
            ..Default::default()
        };

        let mut explorer = Explorer::new(spec, const_values, config);
        match explorer.check() {
            Ok(CheckOutcome::Ok { .. }) => {
                checked += 1;
            }
            Ok(CheckOutcome::StateLimitReached { .. }) => {
                checked += 1;
            }
            Ok(CheckOutcome::MemoryLimitReached { .. }) => {
                checked += 1;
            }
            Ok(CheckOutcome::InvariantViolation { invariant, .. }) => {
                // Some examples intentionally have bugs (like Transfer.specl)
                if !source.contains("intentional") && !source.contains("bug") {
                    failures.push(format!(
                        "{}: invariant violation: {invariant}",
                        file.display()
                    ));
                } else {
                    checked += 1;
                }
            }
            Ok(CheckOutcome::Deadlock { .. }) => {
                checked += 1;
            }
            Err(e) => {
                failures.push(format!("{}: check error: {e}", file.display()));
            }
        }
    }

    eprintln!("checked {checked} examples with model checker");

    if !failures.is_empty() {
        panic!("model check failures:\n{}", failures.join("\n"));
    }
}

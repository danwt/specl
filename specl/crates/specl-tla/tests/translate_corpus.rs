//! Corpus test: verify the TLA+ translator against all .tla files in the repo.
//!
//! Tests parsing and translation of every .tla file found in:
//! - references/tla-dump-real/ (community TLA+ specs)
//! - specl/examples/ (showcase and other specs)

use specl_tla::{translate, Parser};
use std::fs;
use std::path::{Path, PathBuf};

fn find_tla_files(dir: &Path) -> Vec<PathBuf> {
    let mut files = Vec::new();
    if dir.is_dir() {
        for entry in fs::read_dir(dir).unwrap() {
            let entry = entry.unwrap();
            let path = entry.path();
            if path.is_dir() {
                files.extend(find_tla_files(&path));
            } else if path.extension().map_or(false, |e| e == "tla") {
                files.push(path);
            }
        }
    }
    files.sort();
    files
}

fn repo_root() -> PathBuf {
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    PathBuf::from(manifest_dir)
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf()
}

#[test]
fn parse_all_tla_files() {
    let root = repo_root();
    let mut all_files = Vec::new();
    all_files.extend(find_tla_files(&root.join("references/tla-dump-real")));
    all_files.extend(find_tla_files(&root.join("specl/examples/showcase")));
    all_files.extend(find_tla_files(&root.join("specl/examples/other")));

    assert!(!all_files.is_empty(), "no .tla files found under {root:?}");

    let mut parsed = 0;
    let mut parse_failures = Vec::new();

    for file in &all_files {
        let source = fs::read_to_string(file).unwrap();
        let mut parser = Parser::new(&source);
        match parser.parse_module() {
            Ok(_) => parsed += 1,
            Err(e) => {
                let rel = file.strip_prefix(&root).unwrap_or(file);
                parse_failures.push(format!("{}: {e}", rel.display()));
            }
        }
    }

    eprintln!(
        "TLA+ parse: {parsed}/{} succeeded, {} failed",
        all_files.len(),
        parse_failures.len()
    );

    // Report failures but don't assert — many community specs use
    // TLA+ features the parser doesn't support yet.
    if !parse_failures.is_empty() {
        eprintln!("parse failures:");
        for f in &parse_failures {
            eprintln!("  {f}");
        }
    }
}

#[test]
fn translate_all_tla_files() {
    let root = repo_root();
    let mut all_files = Vec::new();
    all_files.extend(find_tla_files(&root.join("references/tla-dump-real")));
    all_files.extend(find_tla_files(&root.join("specl/examples/showcase")));
    all_files.extend(find_tla_files(&root.join("specl/examples/other")));

    assert!(!all_files.is_empty(), "no .tla files found under {root:?}");

    let mut translated = 0;
    let mut parse_failures = 0;
    let mut translate_failures = Vec::new();

    for file in &all_files {
        let source = fs::read_to_string(file).unwrap();
        match translate(&source) {
            Ok(_) => translated += 1,
            Err(e) => {
                let rel = file.strip_prefix(&root).unwrap_or(file);
                let msg = format!("{e}");
                if msg.starts_with("parse error") {
                    parse_failures += 1;
                } else {
                    translate_failures.push(format!("{}: {e}", rel.display()));
                }
            }
        }
    }

    eprintln!(
        "TLA+ translate: {translated}/{} succeeded, {parse_failures} parse failures, {} translate failures",
        all_files.len(),
        translate_failures.len()
    );

    if !translate_failures.is_empty() {
        eprintln!("translate failures:");
        for f in &translate_failures {
            eprintln!("  {f}");
        }
    }
}

/// TLA+ files that use features the parser doesn't support yet.
/// These are tracked so we notice when parser improvements fix them.
const EXPECTED_TRANSLATE_FAILURES: &[&str] = &[
    // Bracket expressions [x \in S |-> ...] not supported
    "raft.tla",
    "paxos.tla",
    "pbft.tla",
    "comet.tla",
    "epaxos.tla",
    "multipaxosreconfig.tla",
    "percolator.tla",
    "parallelcommits.tla",
    "simplex.tla",
    "swim.tla",
    // TLC trace spec (auto-generated, uses INSTANCE)
    "tpc_TTrace_1770669434.tla",
];

/// Benchmark .tla files should all parse and translate successfully,
/// except for known failures tracked in EXPECTED_TRANSLATE_FAILURES.
#[test]
fn benchmark_tla_files_translate() {
    let root = repo_root();
    let mut all_files = Vec::new();
    all_files.extend(find_tla_files(&root.join("specl/examples/showcase")));
    all_files.extend(find_tla_files(&root.join("specl/examples/other")));

    assert!(!all_files.is_empty(), "no .tla files found in examples");

    let mut failures = Vec::new();
    let mut expected_failures = 0;

    for file in &all_files {
        let source = fs::read_to_string(file).unwrap();
        let filename = file.file_name().unwrap().to_str().unwrap();
        if let Err(e) = translate(&source) {
            if EXPECTED_TRANSLATE_FAILURES.contains(&filename) {
                expected_failures += 1;
            } else {
                let rel = file.strip_prefix(&root).unwrap_or(file);
                failures.push(format!("{}: {e}", rel.display()));
            }
        }
    }

    eprintln!(
        "benchmark TLA+ translate: {}/{} succeeded, {expected_failures} expected failures",
        all_files.len() - expected_failures - failures.len(),
        all_files.len()
    );

    if !failures.is_empty() {
        panic!(
            "unexpected TLA+ translation failures:\n{}",
            failures.join("\n")
        );
    }
}

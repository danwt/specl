//! Criterion benchmarks for the model checker.
//!
//! Run with: cargo bench -p specl-mc

use criterion::{criterion_group, criterion_main, Criterion};
use specl_eval::Value;
use specl_ir::compile;
use specl_mc::{CheckConfig, Explorer};
use specl_syntax::parse;
use std::fs;
use std::path::PathBuf;

fn examples_dir() -> PathBuf {
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    PathBuf::from(manifest_dir)
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join("examples")
}

fn load_spec(path: &str, constants: &[(&str, i64)]) -> (specl_ir::CompiledSpec, Vec<Value>) {
    let source = fs::read_to_string(examples_dir().join(path)).unwrap();
    let module = parse(&source).unwrap();
    specl_types::check_module(&module).unwrap();
    let spec = compile(&module).unwrap();

    let mut const_values = vec![Value::none(); spec.consts.len()];
    for const_decl in &spec.consts {
        for &(name, val) in constants {
            if const_decl.name == name {
                const_values[const_decl.index] = Value::int(val);
            }
        }
    }
    (spec, const_values)
}

fn bench_check(
    c: &mut Criterion,
    name: &str,
    path: &str,
    constants: &[(&str, i64)],
    config: CheckConfig,
) {
    let (spec, const_values) = load_spec(path, constants);
    c.bench_function(name, |b| {
        b.iter(|| {
            let mut explorer = Explorer::new(spec.clone(), const_values.clone(), config.clone());
            explorer.check().unwrap();
        })
    });
}

fn benchmarks(c: &mut Criterion) {
    let default = CheckConfig {
        check_deadlock: false,
        ..Default::default()
    };

    let fast_check = CheckConfig {
        check_deadlock: false,
        fast_check: true,
        parallel: false,
        ..Default::default()
    };

    let no_parallel = CheckConfig {
        check_deadlock: false,
        parallel: false,
        ..Default::default()
    };

    // Small specs: fast iteration, regression detection
    bench_check(
        c,
        "counters_N2_MAX5",
        "benchmark/10-counters/counters.specl",
        &[("N", 2), ("MAX", 5)],
        no_parallel.clone(),
    );

    bench_check(
        c,
        "ewd840_N4",
        "benchmark/04-ewd840/ewd840.specl",
        &[("N", 4)],
        no_parallel.clone(),
    );

    bench_check(
        c,
        "tpc_N2",
        "benchmark/03-tpc/tpc.specl",
        &[("N", 2)],
        no_parallel.clone(),
    );

    bench_check(
        c,
        "dining_N3",
        "benchmark/07-dining-philosophers/dining-philosophers.specl",
        &[],
        no_parallel.clone(),
    );

    // Fast-check mode
    bench_check(
        c,
        "counters_N2_MAX5_fast",
        "benchmark/10-counters/counters.specl",
        &[("N", 2), ("MAX", 5)],
        fast_check,
    );

    // Parallel mode
    bench_check(
        c,
        "counters_N3_MAX5_parallel",
        "benchmark/10-counters/counters.specl",
        &[("N", 3), ("MAX", 5)],
        default.clone(),
    );

    // Dict-heavy (medium size, ~10K-100K states)
    bench_check(
        c,
        "paxos_small",
        "benchmark/02-paxos/paxos.specl",
        &[("N", 2), ("MaxBallot", 1), ("V", 1)],
        no_parallel.clone(),
    );

    bench_check(
        c,
        "pbft_small",
        "benchmark/08-pbft/pbft.specl",
        &[("N", 3), ("F", 1), ("MaxView", 0), ("MaxSeq", 0), ("V", 1)],
        no_parallel,
    );
}

criterion_group!(benches, benchmarks);
criterion_main!(benches);

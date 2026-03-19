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

    // --- Small specs: fast iteration, regression detection ---

    // Counters: Dict[0..N, 0..M] with Inc/Dec/Transfer (~1K states at N=2 M=5)
    bench_check(
        c,
        "counters_N2_M5",
        "benchmark/counters.specl",
        &[("N", 2), ("M", 5)],
        no_parallel.clone(),
    );

    // Token ring: mutual exclusion on a ring (~253 states at N=4)
    bench_check(
        c,
        "token_ring_N4",
        "benchmark/token-ring.specl",
        &[("N", 4)],
        no_parallel.clone(),
    );

    // Two-phase commit: coordinator crash scenario (~500 states at N=2)
    bench_check(
        c,
        "tpc_N2",
        "other/tpc.specl",
        &[("N", 2)],
        no_parallel.clone(),
    );

    // Dining philosophers: fixed 3 philosophers, no constants
    bench_check(
        c,
        "dining_3",
        "other/dining-philosophers-benchmark.specl",
        &[],
        no_parallel.clone(),
    );

    // Cache coherence: MESI protocol (~76 states at N=5)
    bench_check(
        c,
        "cache_coherence_N5",
        "benchmark/cache-coherence.specl",
        &[("N", 5)],
        no_parallel.clone(),
    );

    // --- Storage mode variants ---

    // Fast-check mode (fingerprint-only, ~10x less memory)
    bench_check(
        c,
        "counters_N2_M5_fast",
        "benchmark/counters.specl",
        &[("N", 2), ("M", 5)],
        fast_check,
    );

    // Parallel mode (multi-threaded exploration)
    bench_check(
        c,
        "counters_N3_M5_parallel",
        "benchmark/counters.specl",
        &[("N", 3), ("M", 5)],
        default.clone(),
    );

    // --- Dict-heavy / medium size specs ---

    // Paxos: consensus with ballots (~316K states at N=2 MaxBallot=3 V=2)
    bench_check(
        c,
        "paxos_small",
        "showcase/paxos.specl",
        &[("N", 2), ("MaxBallot", 1), ("V", 1)],
        no_parallel.clone(),
    );

    // PBFT: Byzantine fault tolerance (~2.6K states at N=3 F=1 MaxVal=1)
    bench_check(
        c,
        "pbft_small",
        "other/pbft.specl",
        &[("N", 3), ("F", 1), ("MaxVal", 1)],
        no_parallel.clone(),
    );

    // Leader election: ring-based LCR (large state space at N=4)
    bench_check(
        c,
        "leader_election_N4",
        "benchmark/leader-election.specl",
        &[("N", 4)],
        CheckConfig {
            check_deadlock: false,
            parallel: false,
            ..Default::default()
        },
    );
}

criterion_group!(benches, benchmarks);
criterion_main!(benches);

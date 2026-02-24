use specl_mc::{CheckConfig, CheckOutcome};
use specl_soundness::{check_spec, max_depth_from_outcome, states_from_outcome};

const SPEC: &str = r#"
module InternalConsistency

var x: 0..2
var y: 0..2

init { x in 0..2 and y in 0..2 }

invariant TypeOK { x in 0..2 and y in 0..2 }

action IncX() { require x < 2; x = x + 1; }
action DecX() { require x > 0; x = x - 1; }
action IncY() { require y < 2; y = y + 1; }
action DecY() { require y > 0; y = y - 1; }
"#;

fn run(config: CheckConfig) -> CheckOutcome {
    check_spec(SPEC, config).expect("check should succeed")
}

fn base_config() -> CheckConfig {
    CheckConfig {
        check_deadlock: true,
        parallel: false,
        use_por: false,
        use_symmetry: false,
        fast_check: false,
        bloom: false,
        collapse: false,
        tree: false,
        max_time_secs: 10,
        ..CheckConfig::default()
    }
}

#[test]
fn multi_backend_consistency() {
    let baseline = run(base_config());
    assert!(matches!(baseline, CheckOutcome::Ok { .. }));
    let baseline_states = states_from_outcome(&baseline).unwrap();
    let baseline_depth = max_depth_from_outcome(&baseline).unwrap();

    let fast = run(CheckConfig {
        fast_check: true,
        ..base_config()
    });
    let collapse = run(CheckConfig {
        collapse: true,
        ..base_config()
    });
    let tree = run(CheckConfig {
        tree: true,
        ..base_config()
    });
    let bloom = run(CheckConfig {
        bloom: true,
        bloom_bits: 34,
        ..base_config()
    });

    for outcome in [&fast, &collapse, &tree] {
        assert_eq!(states_from_outcome(outcome), Some(baseline_states));
        assert_eq!(max_depth_from_outcome(outcome), Some(baseline_depth));
    }

    // Bloom filter is probabilistic: it must never over-count states.
    assert!(states_from_outcome(&bloom).unwrap() <= baseline_states);
}

#[test]
fn parallel_vs_sequential_consistency() {
    let sequential = run(base_config());
    let parallel = run(CheckConfig {
        parallel: true,
        num_threads: 0,
        ..base_config()
    });

    assert_eq!(
        states_from_outcome(&sequential),
        states_from_outcome(&parallel)
    );
    assert_eq!(
        max_depth_from_outcome(&sequential),
        max_depth_from_outcome(&parallel)
    );
}

#[test]
fn deterministic_repeated_runs() {
    let mut expected_states = None;
    let mut expected_depth = None;
    for _ in 0..10 {
        let out = run(CheckConfig {
            parallel: true,
            num_threads: 0,
            ..base_config()
        });
        let states = states_from_outcome(&out);
        let depth = max_depth_from_outcome(&out);
        if expected_states.is_none() {
            expected_states = states;
            expected_depth = depth;
        }
        assert_eq!(states, expected_states);
        assert_eq!(depth, expected_depth);
    }
}

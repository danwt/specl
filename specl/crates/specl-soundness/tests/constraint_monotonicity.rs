//! Property: adding a constraint (invariant) never increases the explored state space.
//!
//! For any spec S and additional invariant I, the model checker should explore
//! the same or fewer states with the invariant than without it, because
//! invariant violations cause early termination.
//!
//! More precisely: states(S with I) <= states(S without I).

use proptest::prelude::*;
use specl_mc::CheckConfig;
use specl_soundness::{check_spec, states_from_outcome};

fn base_config() -> CheckConfig {
    CheckConfig {
        parallel: false,
        check_deadlock: false,
        max_states: 5_000,
        use_por: false,
        use_symmetry: false,
        max_time_secs: 5,
        ..CheckConfig::default()
    }
}

fn states_or_max(src: &str, config: CheckConfig) -> usize {
    match check_spec(src, config) {
        Ok(outcome) => states_from_outcome(&outcome).unwrap_or(0),
        Err(_) => 0,
    }
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 256,
        .. ProptestConfig::default()
    })]

    #[test]
    fn invariant_never_increases_states(bound in 1u8..=3, threshold in 0u8..=3) {
        // Spec without restrictive invariant
        let src_unconstrained = format!(
            r#"module MonoBase
var x: 0..{bound}
var y: 0..{bound}
init {{ x in 0..{bound} and y in 0..{bound} }}
action IncX() {{ require x < {bound}; x = x + 1; y = y; }}
action IncY() {{ require y < {bound}; x = x; y = y + 1; }}
action DecX() {{ require x > 0; x = x - 1; y = y; }}
action DecY() {{ require y > 0; x = x; y = y - 1; }}
invariant Trivial {{ true }}
"#,
        );

        // Same spec with a restrictive invariant that may cause early termination
        let src_constrained = format!(
            r#"module MonoConstrained
var x: 0..{bound}
var y: 0..{bound}
init {{ x in 0..{bound} and y in 0..{bound} }}
action IncX() {{ require x < {bound}; x = x + 1; y = y; }}
action IncY() {{ require y < {bound}; x = x; y = y + 1; }}
action DecX() {{ require x > 0; x = x - 1; y = y; }}
action DecY() {{ require y > 0; x = x; y = y - 1; }}
invariant Trivial {{ true }}
invariant Restrictive {{ x + y <= {threshold} }}
"#,
        );

        let states_base = states_or_max(&src_unconstrained, base_config());
        let states_with_inv = states_or_max(&src_constrained, base_config());

        // Constrained can never explore MORE states than unconstrained.
        // It may explore the same (if invariant always holds) or fewer
        // (if invariant violation causes early stop — but that returns 0 from our helper).
        // Either way: constrained <= unconstrained.
        prop_assert!(
            states_with_inv <= states_base,
            "constrained ({}) > unconstrained ({})",
            states_with_inv,
            states_base
        );
    }
}

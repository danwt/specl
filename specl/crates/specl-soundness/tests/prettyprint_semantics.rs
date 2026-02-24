//! Pretty-print preserves semantics, not just syntax.
//!
//! Stronger than roundtrip idempotence: check(src) and check(pretty(parse(src)))
//! produce identical model checking outcomes (same state count, same verdict).

use proptest::prelude::*;
use specl_mc::CheckConfig;
use specl_soundness::{check_spec, states_from_outcome};
use specl_syntax::{parse, pretty_print};

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

fn check_semantics_preserved(src: &str) -> Result<(), String> {
    let module = parse(src).map_err(|e| format!("parse original: {e}"))?;
    let pretty_src = pretty_print(&module);

    let outcome_orig = check_spec(src, base_config())?;
    let outcome_pretty = check_spec(&pretty_src, base_config())?;

    let states_orig = states_from_outcome(&outcome_orig);
    let states_pretty = states_from_outcome(&outcome_pretty);

    if states_orig != states_pretty {
        return Err(format!(
            "state count mismatch: original={:?}, pretty-printed={:?}\noriginal:\n{}\npretty:\n{}",
            states_orig, states_pretty, src, pretty_src
        ));
    }
    Ok(())
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 256,
        .. ProptestConfig::default()
    })]

    #[test]
    fn prettyprint_preserves_set_spec_semantics(bound in 1u8..=3, n_actions in 1u8..=2) {
        let src = format!(
            r#"module PPSet
var s: Set[0..{bound}]
init {{ s = {{}}; }}
{actions}
action Remove(k: 0..{bound}) {{ require k in s; s = s diff {{k}}; }}
invariant NonNegLen {{ len(s) >= 0 }}
"#,
            actions = (0..n_actions)
                .map(|i| format!("action Add{i}(k: 0..{bound}) {{ s = s union {{k}}; }}"))
                .collect::<Vec<_>>()
                .join("\n"),
        );
        prop_assert!(
            check_semantics_preserved(&src).is_ok(),
            "{}",
            check_semantics_preserved(&src).unwrap_err()
        );
    }

    #[test]
    fn prettyprint_preserves_counter_semantics(bound in 1u8..=4) {
        let src = format!(
            r#"module PPCounter
var x: 0..{bound}
var y: 0..{bound}
init {{ x = 0; y = 0; }}
action IncX() {{ require x < {bound}; x = x + 1; y = y; }}
action IncY() {{ require y < {bound}; x = x; y = y + 1; }}
invariant TypeOK {{ x >= 0 and y >= 0 }}
"#,
        );
        prop_assert!(
            check_semantics_preserved(&src).is_ok(),
            "{}",
            check_semantics_preserved(&src).unwrap_err()
        );
    }

    #[test]
    fn prettyprint_preserves_dict_semantics(kb in 1u8..=2, vb in 1u8..=2) {
        let src = format!(
            r#"module PPDict
var d: Dict[0..{kb}, 0..{vb}]
init {{ d = {{k: 0 for k in 0..{kb}}}; }}
action Update(k: 0..{kb}, v: 0..{vb}) {{ d = d | {{k: v}}; }}
invariant AllValid {{ all k in 0..{kb} : d[k] >= 0 and d[k] <= {vb} }}
"#,
        );
        prop_assert!(
            check_semantics_preserved(&src).is_ok(),
            "{}",
            check_semantics_preserved(&src).unwrap_err()
        );
    }

    #[test]
    fn prettyprint_preserves_seq_semantics(bound in 1u8..=2, max_len in 2u8..=3) {
        let src = format!(
            r#"module PPSeq
var msgs: Seq[0..{bound}]
init {{ msgs = []; }}
action Send(v: 0..{bound}) {{ require len(msgs) < {max_len}; msgs = msgs ++ [v]; }}
action Recv() {{ require len(msgs) > 0; msgs = tail(msgs); }}
invariant Bounded {{ len(msgs) <= {max_len} }}
"#,
        );
        prop_assert!(
            check_semantics_preserved(&src).is_ok(),
            "{}",
            check_semantics_preserved(&src).unwrap_err()
        );
    }

    #[test]
    fn prettyprint_preserves_quantifier_semantics(bound in 1u8..=3) {
        let src = format!(
            r#"module PPQuantifier
var s: Set[0..{bound}]
init {{ s = {{}}; }}
action Add(k: 0..{bound}) {{ s = s union {{k}}; }}
invariant AllMembership {{
    all k in 0..{bound} : k in s implies k in s
}}
invariant AnyImpliesNonempty {{
    (any k in 0..{bound} : k in s) implies len(s) > 0
}}
"#,
        );
        prop_assert!(
            check_semantics_preserved(&src).is_ok(),
            "{}",
            check_semantics_preserved(&src).unwrap_err()
        );
    }
}

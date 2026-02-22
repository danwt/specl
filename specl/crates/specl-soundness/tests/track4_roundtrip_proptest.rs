use proptest::prelude::*;
use specl_soundness::roundtrip_pretty;

fn synth_spec(n_vars: u8, bound: u8, step: u8) -> String {
    let vars: Vec<String> = (0..n_vars).map(|i| format!("v{i}")).collect();
    let decls: Vec<String> = vars
        .iter()
        .map(|v| format!("var {v}: 0..{bound}"))
        .collect();
    let inits: Vec<String> = vars.iter().map(|v| format!("{v} in 0..{bound}")).collect();
    let invs: Vec<String> = vars.iter().map(|v| format!("{v} in 0..{bound}")).collect();
    let effects: Vec<String> = vars
        .iter()
        .enumerate()
        .map(|(i, v)| {
            if i == 0 {
                format!("{v} = (if {v} + {step} <= {bound} then {v} + {step} else {v})")
            } else {
                format!("{v} = {v}")
            }
        })
        .collect();

    format!(
        "module Roundtrip{n_vars}_{bound}_{step}\n\n{}\n\ninit {{ {} }}\n\ninvariant TypeOK {{ {} }}\n\naction Step() {{ require true; {}; }}\n",
        decls.join("\n"),
        inits.join(" and "),
        invs.join(" and "),
        effects.join("; ")
    )
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 512,
        .. ProptestConfig::default()
    })]

    #[test]
    fn parser_pretty_roundtrip(n_vars in 1u8..=3, bound in 1u8..=6, step in 1u8..=2) {
        let source = synth_spec(n_vars, bound, step);
        let (p1, p2) = roundtrip_pretty(&source).expect("roundtrip parse should succeed");
        prop_assert_eq!(p1, p2);
    }
}

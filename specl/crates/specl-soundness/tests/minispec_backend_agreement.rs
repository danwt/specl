use proptest::prelude::*;
use specl_mc::CheckConfig;
use specl_soundness::{check_spec, states_from_outcome};

#[derive(Debug, Clone)]
struct MiniSpec {
    max_x: u8,
    max_y: u8,
    inc_x: u8,
    dec_x: u8,
    inc_y: u8,
    dec_y: u8,
}

impl MiniSpec {
    fn to_specl(&self) -> String {
        format!(
            r#"
module MiniSpec

var x: 0..{max_x}
var y: 0..{max_y}

init {{ x in 0..{max_x} and y in 0..{max_y} }}

invariant TypeOK {{ x in 0..{max_x} and y in 0..{max_y} }}

action IncX() {{ require x + {inc_x} <= {max_x}; x = x + {inc_x}; y = y; }}
action DecX() {{ require x >= {dec_x}; x = x - {dec_x}; y = y; }}
action IncY() {{ require y + {inc_y} <= {max_y}; y = y + {inc_y}; x = x; }}
action DecY() {{ require y >= {dec_y}; y = y - {dec_y}; x = x; }}
"#,
            max_x = self.max_x,
            max_y = self.max_y,
            inc_x = self.inc_x.max(1),
            dec_x = self.dec_x.max(1),
            inc_y = self.inc_y.max(1),
            dec_y = self.dec_y.max(1),
        )
    }
}

fn strategy() -> impl Strategy<Value = MiniSpec> {
    (1u8..=5, 1u8..=5, 1u8..=2, 1u8..=2, 1u8..=2, 1u8..=2).prop_map(
        |(max_x, max_y, inc_x, dec_x, inc_y, dec_y)| MiniSpec {
            max_x,
            max_y,
            inc_x,
            dec_x,
            inc_y,
            dec_y,
        },
    )
}

proptest! {
    #![proptest_config(ProptestConfig {
        // Override in CI with PROPTEST_CASES env var.
        cases: 512,
        .. ProptestConfig::default()
    })]

    #[test]
    fn minispec_backend_agreement(spec in strategy()) {
        let src = spec.to_specl();
        let base = CheckConfig {
            parallel: false,
            check_deadlock: true,
            use_por: false,
            use_symmetry: false,
            ..CheckConfig::default()
        };

        let full = check_spec(&src, base.clone()).expect("full mode");
        let fast = check_spec(&src, CheckConfig { fast_check: true, ..base.clone() }).expect("fast mode");
        let collapse = check_spec(&src, CheckConfig { collapse: true, ..base.clone() }).expect("collapse mode");
        let tree = check_spec(&src, CheckConfig { tree: true, ..base.clone() }).expect("tree mode");
        let expected = states_from_outcome(&full);
        prop_assert_eq!(states_from_outcome(&fast), expected);
        prop_assert_eq!(states_from_outcome(&collapse), expected);
        prop_assert_eq!(states_from_outcome(&tree), expected);
    }
}

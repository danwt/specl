#![no_main]
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    if let Ok(s) = std::str::from_utf8(data) {
        if let Ok(module) = specl_syntax::parse(s) {
            if specl_types::check_module(&module).is_ok() {
                if let Ok(spec) = specl_ir::compile(&module) {
                    if spec.consts.is_empty() {
                        let config = specl_mc::CheckConfig {
                            parallel: false,
                            check_deadlock: false,
                            max_states: 1_000,
                            max_depth: 50,
                            max_time_secs: 2,
                            ..specl_mc::CheckConfig::default()
                        };
                        let mut explorer =
                            specl_mc::Explorer::new(spec, Vec::<specl_eval::Value>::new(), config);
                        let _ = explorer.check();
                    }
                }
            }
        }
    }
});

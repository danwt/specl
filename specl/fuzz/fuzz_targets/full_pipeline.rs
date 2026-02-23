#![no_main]
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    if let Ok(s) = std::str::from_utf8(data) {
        if let Ok(module) = specl_syntax::parse(s) {
            if specl_types::check_module(&module).is_ok() {
                let _ = specl_ir::compile(&module);
            }
        }
    }
});

use specl_eval::Value;
use specl_ir::{compile, CompiledSpec};
use specl_mc::{CheckConfig, CheckOutcome, Explorer};
use specl_syntax::{parse, pretty_print};

pub fn compile_spec(source: &str) -> Result<CompiledSpec, String> {
    let module = parse(source).map_err(|e| e.to_string())?;
    specl_types::check_module(&module).map_err(|e| e.to_string())?;
    compile(&module).map_err(|e| e.to_string())
}

pub fn check_spec(source: &str, config: CheckConfig) -> Result<CheckOutcome, String> {
    let spec = compile_spec(source)?;
    if !spec.consts.is_empty() {
        return Err("spec has constants; check_spec expects no constants".to_string());
    }
    let mut explorer = Explorer::new(spec, Vec::<Value>::new(), config);
    explorer.check().map_err(|e| e.to_string())
}

pub fn states_from_outcome(outcome: &CheckOutcome) -> Option<usize> {
    match outcome {
        CheckOutcome::Ok {
            states_explored, ..
        } => Some(*states_explored),
        CheckOutcome::StateLimitReached {
            states_explored, ..
        } => Some(*states_explored),
        CheckOutcome::MemoryLimitReached {
            states_explored, ..
        } => Some(*states_explored),
        CheckOutcome::TimeLimitReached {
            states_explored, ..
        } => Some(*states_explored),
        CheckOutcome::InvariantViolation { .. } | CheckOutcome::Deadlock { .. } => None,
    }
}

pub fn max_depth_from_outcome(outcome: &CheckOutcome) -> Option<usize> {
    match outcome {
        CheckOutcome::Ok { max_depth, .. } => Some(*max_depth),
        CheckOutcome::StateLimitReached { max_depth, .. } => Some(*max_depth),
        CheckOutcome::MemoryLimitReached { max_depth, .. } => Some(*max_depth),
        CheckOutcome::TimeLimitReached { max_depth, .. } => Some(*max_depth),
        CheckOutcome::InvariantViolation { .. } | CheckOutcome::Deadlock { .. } => None,
    }
}

pub fn roundtrip_pretty(source: &str) -> Result<(String, String), String> {
    let m1 = parse(source).map_err(|e| e.to_string())?;
    let p1 = pretty_print(&m1);
    let m2 = parse(&p1).map_err(|e| e.to_string())?;
    let p2 = pretty_print(&m2);
    Ok((p1, p2))
}

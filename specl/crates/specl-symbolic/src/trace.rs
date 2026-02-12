//! Counterexample trace extraction from Z3 models.

use crate::state_vars::{VarKind, VarLayout};
use crate::TraceStep;
use specl_eval::Value;
use specl_ir::CompiledSpec;
use z3::ast::Dynamic;
use z3::Model;

/// Extract a counterexample trace from a Z3 model.
pub fn extract_trace(
    model: &Model,
    layout: &VarLayout,
    step_vars: &[Vec<Vec<Dynamic>>],
    _spec: &CompiledSpec,
    _consts: &[Value],
    depth: usize,
) -> Vec<TraceStep> {
    let mut trace = Vec::new();

    for step in 0..=depth {
        let state = extract_state(model, layout, &step_vars[step]);
        let action = None; // Action identification is a future improvement
        trace.push(TraceStep { state, action });
    }

    trace
}

fn extract_state(
    model: &Model,
    layout: &VarLayout,
    vars: &[Vec<Dynamic>],
) -> Vec<(String, String)> {
    let mut state = Vec::new();

    for (var_idx, entry) in layout.entries.iter().enumerate() {
        let z3_vars = &vars[var_idx];
        let value_str = match &entry.kind {
            VarKind::Bool => model
                .eval(&z3_vars[0], true)
                .and_then(|v| v.as_bool())
                .and_then(|b| b.as_bool())
                .map(|b| b.to_string())
                .unwrap_or_else(|| "?".to_string()),
            VarKind::Int { .. } => model
                .eval(&z3_vars[0], true)
                .and_then(|v| v.as_int())
                .and_then(|i| i.as_i64())
                .map(|n| n.to_string())
                .unwrap_or_else(|| "?".to_string()),
            VarKind::ExplodedDict { key_lo, key_hi, .. } => {
                let mut pairs = Vec::new();
                for (i, k) in (*key_lo..=*key_hi).enumerate() {
                    let val = model
                        .eval(&z3_vars[i], true)
                        .and_then(|v| {
                            v.as_int()
                                .and_then(|i| i.as_i64())
                                .map(|n| n.to_string())
                                .or_else(|| {
                                    v.as_bool().and_then(|b| b.as_bool()).map(|b| b.to_string())
                                })
                        })
                        .unwrap_or_else(|| "?".to_string());
                    pairs.push(format!("{}: {}", k, val));
                }
                format!("{{{}}}", pairs.join(", "))
            }
            VarKind::ExplodedSet { lo, hi } => {
                let mut members = Vec::new();
                for (i, k) in (*lo..=*hi).enumerate() {
                    let is_member = model
                        .eval(&z3_vars[i], true)
                        .and_then(|v| v.as_bool())
                        .and_then(|b| b.as_bool())
                        .unwrap_or(false);
                    if is_member {
                        members.push(k.to_string());
                    }
                }
                format!("{{{}}}", members.join(", "))
            }
        };

        state.push((entry.name.clone(), value_str));
    }

    state
}

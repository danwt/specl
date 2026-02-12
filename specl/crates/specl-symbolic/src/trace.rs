//! Counterexample trace extraction from Z3 models.

use crate::encoder::EncoderCtx;
use crate::state_vars::{VarKind, VarLayout};
use crate::TraceStep;
use specl_eval::Value;
use specl_ir::CompiledSpec;
use z3::ast::{Dynamic, Int};
use z3::Model;

/// Extract a counterexample trace from a Z3 model.
pub fn extract_trace(
    model: &Model,
    layout: &VarLayout,
    step_vars: &[Vec<Vec<Dynamic>>],
    spec: &CompiledSpec,
    consts: &[Value],
    depth: usize,
) -> Vec<TraceStep> {
    let mut trace = Vec::new();

    for step in 0..=depth {
        let state = extract_state(model, layout, &step_vars[step]);
        let action = if step > 0 {
            identify_action(model, layout, step_vars, spec, consts, step - 1)
        } else {
            Some("init".to_string())
        };
        trace.push(TraceStep { state, action });
    }

    trace
}

/// Identify which action fired at the given step by evaluating guards against the model.
fn identify_action(
    model: &Model,
    layout: &VarLayout,
    step_vars: &[Vec<Vec<Dynamic>>],
    spec: &CompiledSpec,
    consts: &[Value],
    step: usize,
) -> Option<String> {
    for action in &spec.actions {
        let param_ranges: Vec<(i64, i64)> = action
            .params
            .iter()
            .enumerate()
            .filter_map(|(i, (_, ty))| {
                use specl_types::Type;
                match ty {
                    Type::Range(lo, hi) => Some((*lo, *hi)),
                    Type::Int => action
                        .param_type_exprs
                        .get(i)
                        .and_then(|te| crate::state_vars::eval_type_expr_range(te, spec, consts)),
                    Type::String => {
                        let n = layout.string_table.len() as i64;
                        if n > 0 {
                            Some((0, n - 1))
                        } else {
                            None
                        }
                    }
                    _ => None,
                }
            })
            .collect();

        if param_ranges.len() != action.params.len() {
            continue;
        }

        if param_ranges.is_empty() {
            // No parameters — just evaluate the guard
            if guard_satisfied(model, layout, step_vars, spec, consts, action, step, &[]) {
                return Some(action.name.clone());
            }
        } else {
            // Try each parameter combination
            let mut combos = Vec::new();
            enumerate_param_combos(&param_ranges, 0, &mut Vec::new(), &mut combos);
            for combo in &combos {
                if guard_satisfied(model, layout, step_vars, spec, consts, action, step, combo) {
                    let params_str = combo
                        .iter()
                        .map(|v| v.to_string())
                        .collect::<Vec<_>>()
                        .join(", ");
                    return Some(format!("{}({})", action.name, params_str));
                }
            }
        }
    }

    None
}

/// Check if an action's guard is satisfied in the model at the given step.
fn guard_satisfied(
    model: &Model,
    layout: &VarLayout,
    step_vars: &[Vec<Vec<Dynamic>>],
    _spec: &CompiledSpec,
    consts: &[Value],
    action: &specl_ir::CompiledAction,
    step: usize,
    params: &[i64],
) -> bool {
    let z3_params: Vec<Dynamic> = params
        .iter()
        .map(|v| Dynamic::from_ast(&Int::from_i64(*v)))
        .collect();

    let mut enc = EncoderCtx {
        layout,
        consts,
        step_vars,
        current_step: step,
        next_step: step + 1,
        params: &z3_params,
        locals: Vec::new(),
        compound_locals: Vec::new(),
        set_locals: Vec::new(),
    };

    let Ok(guard) = enc.encode_bool(&action.guard) else {
        return false;
    };

    model
        .eval(&Dynamic::from_ast(&guard), true)
        .and_then(|v| v.as_bool())
        .and_then(|b| b.as_bool())
        .unwrap_or(false)
}

fn enumerate_param_combos(
    ranges: &[(i64, i64)],
    depth: usize,
    current: &mut Vec<i64>,
    result: &mut Vec<Vec<i64>>,
) {
    if depth == ranges.len() {
        result.push(current.clone());
        return;
    }
    let (lo, hi) = ranges[depth];
    for v in lo..=hi {
        current.push(v);
        enumerate_param_combos(ranges, depth + 1, current, result);
        current.pop();
    }
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
                .map(|n| format_int_value(n, &entry.kind, &layout.string_table))
                .unwrap_or_else(|| "?".to_string()),
            VarKind::ExplodedDict {
                key_lo,
                key_hi,
                value_kind,
            } => {
                let stride = value_kind.z3_var_count();
                let mut pairs = Vec::new();
                for (i, k) in (*key_lo..=*key_hi).enumerate() {
                    if stride == 1 {
                        let val = model
                            .eval(&z3_vars[i], true)
                            .and_then(|v| {
                                v.as_int()
                                    .and_then(|i| i.as_i64())
                                    .map(|n| format_int_value(n, value_kind, &layout.string_table))
                                    .or_else(|| {
                                        v.as_bool().and_then(|b| b.as_bool()).map(|b| b.to_string())
                                    })
                            })
                            .unwrap_or_else(|| "?".to_string());
                        pairs.push(format!("{}: {}", k, val));
                    } else {
                        // Compound value (e.g., Seq)
                        let key_offset = i * stride;
                        let key_vars = &z3_vars[key_offset..key_offset + stride];
                        let val_str = format_compound_value(
                            model,
                            value_kind,
                            key_vars,
                            &layout.string_table,
                        );
                        pairs.push(format!("{}: {}", k, val_str));
                    }
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
            VarKind::ExplodedSeq { max_len, elem_kind } => {
                let len = model
                    .eval(&z3_vars[0], true)
                    .and_then(|v| v.as_int())
                    .and_then(|i| i.as_i64())
                    .unwrap_or(0) as usize;
                let len = len.min(*max_len);
                let mut elems = Vec::new();
                for i in 0..len {
                    let val = model
                        .eval(&z3_vars[1 + i], true)
                        .and_then(|v| {
                            v.as_int()
                                .and_then(|i| i.as_i64())
                                .map(|n| format_int_value(n, elem_kind, &layout.string_table))
                                .or_else(|| {
                                    v.as_bool().and_then(|b| b.as_bool()).map(|b| b.to_string())
                                })
                        })
                        .unwrap_or_else(|| "?".to_string());
                    elems.push(val);
                }
                format!("[{}]", elems.join(", "))
            }
        };

        state.push((entry.name.clone(), value_str));
    }

    state
}

/// Format a compound value (e.g., Seq, Dict, Set within a Dict).
fn format_compound_value(
    model: &Model,
    kind: &VarKind,
    vars: &[Dynamic],
    string_table: &[String],
) -> String {
    match kind {
        VarKind::ExplodedSeq { max_len, elem_kind } => {
            let len = model
                .eval(&vars[0], true)
                .and_then(|v| v.as_int())
                .and_then(|i| i.as_i64())
                .unwrap_or(0) as usize;
            let len = len.min(*max_len);
            let mut elems = Vec::new();
            for i in 0..len {
                let val = model
                    .eval(&vars[1 + i], true)
                    .and_then(|v| {
                        v.as_int()
                            .and_then(|i| i.as_i64())
                            .map(|n| format_int_value(n, elem_kind, string_table))
                            .or_else(|| {
                                v.as_bool().and_then(|b| b.as_bool()).map(|b| b.to_string())
                            })
                    })
                    .unwrap_or_else(|| "?".to_string());
                elems.push(val);
            }
            format!("[{}]", elems.join(", "))
        }
        VarKind::ExplodedDict {
            key_lo,
            key_hi,
            value_kind,
        } => {
            let inner_stride = value_kind.z3_var_count();
            let mut pairs = Vec::new();
            for (i, k) in (*key_lo..=*key_hi).enumerate() {
                if inner_stride == 1 {
                    let val = model
                        .eval(&vars[i], true)
                        .and_then(|v| {
                            v.as_int()
                                .and_then(|i| i.as_i64())
                                .map(|n| format_int_value(n, value_kind, string_table))
                                .or_else(|| {
                                    v.as_bool().and_then(|b| b.as_bool()).map(|b| b.to_string())
                                })
                        })
                        .unwrap_or_else(|| "?".to_string());
                    pairs.push(format!("{}: {}", k, val));
                } else {
                    let offset = i * inner_stride;
                    let inner_vars = &vars[offset..offset + inner_stride];
                    let val_str =
                        format_compound_value(model, value_kind, inner_vars, string_table);
                    pairs.push(format!("{}: {}", k, val_str));
                }
            }
            format!("{{{}}}", pairs.join(", "))
        }
        VarKind::ExplodedSet { lo, hi } => {
            let mut members = Vec::new();
            for (i, k) in (*lo..=*hi).enumerate() {
                let is_member = model
                    .eval(&vars[i], true)
                    .and_then(|v| v.as_bool())
                    .and_then(|b| b.as_bool())
                    .unwrap_or(false);
                if is_member {
                    members.push(k.to_string());
                }
            }
            format!("{{{}}}", members.join(", "))
        }
        VarKind::Bool => model
            .eval(&vars[0], true)
            .and_then(|v| v.as_bool())
            .and_then(|b| b.as_bool())
            .map(|b| b.to_string())
            .unwrap_or_else(|| "?".to_string()),
        VarKind::Int { .. } => model
            .eval(&vars[0], true)
            .and_then(|v| v.as_int())
            .and_then(|i| i.as_i64())
            .map(|n| format_int_value(n, kind, string_table))
            .unwrap_or_else(|| "?".to_string()),
    }
}

/// Format an integer value, using string table reverse-lookup if applicable.
fn format_int_value(n: i64, kind: &VarKind, string_table: &[String]) -> String {
    if let VarKind::Int {
        lo: Some(0),
        hi: Some(hi),
    } = kind
    {
        if !string_table.is_empty() && *hi == string_table.len() as i64 - 1 {
            if let Some(s) = string_table.get(n as usize) {
                return format!("\"{}\"", s);
            }
        }
    }
    n.to_string()
}

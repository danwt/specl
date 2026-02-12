//! Transition and init encoding: actions → Z3 constraints.

use crate::encoder::EncoderCtx;
use crate::state_vars::{VarKind, VarLayout};
use crate::{SymbolicError, SymbolicResult};
use specl_eval::Value;
use specl_ir::{BinOp, CompiledAction, CompiledExpr, CompiledSpec};
use specl_types::Type;
use z3::ast::{Bool, Dynamic, Int};
use z3::Solver;

/// Encode the init predicate as Z3 constraints on step-0 variables.
pub fn encode_init(
    solver: &Solver,
    spec: &CompiledSpec,
    consts: &[Value],
    layout: &VarLayout,
    step_vars: &[Vec<Vec<Dynamic>>],
) -> SymbolicResult<()> {
    encode_init_expr(solver, &spec.init, consts, layout, step_vars)
}

fn encode_init_expr(
    solver: &Solver,
    expr: &CompiledExpr,
    consts: &[Value],
    layout: &VarLayout,
    step_vars: &[Vec<Vec<Dynamic>>],
) -> SymbolicResult<()> {
    match expr {
        CompiledExpr::Bool(true) => Ok(()),
        CompiledExpr::Bool(false) => {
            solver.assert(&Bool::from_bool(false));
            Ok(())
        }

        // Conjunction: recurse on both sides
        CompiledExpr::Binary {
            op: BinOp::And,
            left,
            right,
        } => {
            encode_init_expr(solver, left, consts, layout, step_vars)?;
            encode_init_expr(solver, right, consts, layout, step_vars)
        }

        // Assignment: PrimedVar(idx) == rhs or Var(idx) == rhs
        CompiledExpr::Binary {
            op: BinOp::Eq,
            left,
            right,
        } => {
            let var_idx = match left.as_ref() {
                CompiledExpr::PrimedVar(idx) | CompiledExpr::Var(idx) => Some(*idx),
                _ => None,
            };

            if let Some(var_idx) = var_idx {
                encode_init_assignment(solver, var_idx, right, consts, layout, step_vars)
            } else {
                let mut enc = EncoderCtx {
                    layout,
                    consts,
                    step_vars,
                    current_step: 0,
                    next_step: 0,
                    params: &[],
                    locals: Vec::new(),
                };
                let constraint = enc.encode_bool(expr)?;
                solver.assert(&constraint);
                Ok(())
            }
        }

        // Unchanged in init — skip
        CompiledExpr::Unchanged(_) => Ok(()),

        // Anything else: try general encoding
        _ => {
            let mut enc = EncoderCtx {
                layout,
                consts,
                step_vars,
                current_step: 0,
                next_step: 0,
                params: &[],
                locals: Vec::new(),
            };
            let constraint = enc.encode_bool(expr)?;
            solver.assert(&constraint);
            Ok(())
        }
    }
}

fn encode_init_assignment(
    solver: &Solver,
    var_idx: usize,
    rhs: &CompiledExpr,
    consts: &[Value],
    layout: &VarLayout,
    step_vars: &[Vec<Vec<Dynamic>>],
) -> SymbolicResult<()> {
    let entry = &layout.entries[var_idx];
    let z3_vars = &step_vars[0][var_idx];

    match &entry.kind {
        VarKind::Bool | VarKind::Int { .. } => {
            let mut enc = EncoderCtx {
                layout,
                consts,
                step_vars,
                current_step: 0,
                next_step: 0,
                params: &[],
                locals: Vec::new(),
            };
            let rhs_z3 = enc.encode(rhs)?;
            if let (Some(vi), Some(ri)) = (z3_vars[0].as_int(), rhs_z3.as_int()) {
                solver.assert(&vi.eq(&ri));
            } else if let (Some(vb), Some(rb)) = (z3_vars[0].as_bool(), rhs_z3.as_bool()) {
                solver.assert(&vb.eq(&rb));
            }
            Ok(())
        }
        VarKind::ExplodedDict { key_lo, key_hi, .. } => {
            let key_lo = *key_lo;
            let key_hi = *key_hi;
            match rhs {
                CompiledExpr::FnLit { domain: _, body } => {
                    for (i, k) in (key_lo..=key_hi).enumerate() {
                        let mut enc = EncoderCtx {
                            layout,
                            consts,
                            step_vars,
                            current_step: 0,
                            next_step: 0,
                            params: &[],
                            locals: Vec::new(),
                        };
                        let k_val = Dynamic::from_ast(&Int::from_i64(k));
                        enc.locals.push(k_val);
                        let body_z3 = enc.encode(body)?;
                        if let (Some(vi), Some(ri)) = (z3_vars[i].as_int(), body_z3.as_int()) {
                            solver.assert(&vi.eq(&ri));
                        } else if let (Some(vb), Some(rb)) =
                            (z3_vars[i].as_bool(), body_z3.as_bool())
                        {
                            solver.assert(&vb.eq(&rb));
                        }
                    }
                    Ok(())
                }
                CompiledExpr::DictLit(pairs) => {
                    for (key_expr, val_expr) in pairs {
                        let mut enc = EncoderCtx {
                            layout,
                            consts,
                            step_vars,
                            current_step: 0,
                            next_step: 0,
                            params: &[],
                            locals: Vec::new(),
                        };
                        let key_val = enc.extract_concrete_int_helper(key_expr)?;
                        let offset = (key_val - key_lo) as usize;
                        let val_z3 = enc.encode(val_expr)?;
                        if let (Some(vi), Some(ri)) = (z3_vars[offset].as_int(), val_z3.as_int()) {
                            solver.assert(&vi.eq(&ri));
                        } else if let (Some(vb), Some(rb)) =
                            (z3_vars[offset].as_bool(), val_z3.as_bool())
                        {
                            solver.assert(&vb.eq(&rb));
                        }
                    }
                    Ok(())
                }
                _ => Err(SymbolicError::Encoding(format!(
                    "cannot assign dict from expression: {:?}",
                    std::mem::discriminant(rhs)
                ))),
            }
        }
        VarKind::ExplodedSet { .. } => {
            // Default: empty set
            for var in z3_vars {
                solver.assert(&var.as_bool().unwrap().not());
            }
            Ok(())
        }
    }
}

/// Encode the transition relation for one step: step → step+1.
/// Returns a Bool that is the disjunction of all enabled actions.
pub fn encode_transition(
    spec: &CompiledSpec,
    consts: &[Value],
    layout: &VarLayout,
    step_vars: &[Vec<Vec<Dynamic>>],
    step: usize,
) -> SymbolicResult<Bool> {
    let mut action_encodings = Vec::new();

    for action in &spec.actions {
        let action_enc = encode_action(action, consts, layout, step_vars, step)?;
        action_encodings.push(action_enc);
    }

    Ok(Bool::or(&action_encodings))
}

fn encode_action(
    action: &CompiledAction,
    consts: &[Value],
    layout: &VarLayout,
    step_vars: &[Vec<Vec<Dynamic>>],
    step: usize,
) -> SymbolicResult<Bool> {
    let param_ranges: Vec<(i64, i64)> = action
        .params
        .iter()
        .map(|(_, ty)| match ty {
            Type::Range(lo, hi) => Ok((*lo, *hi)),
            Type::Nat => Ok((0, 100)),
            Type::Int => Err(SymbolicError::Unsupported("unbounded Int parameter".into())),
            _ => Err(SymbolicError::Unsupported(format!(
                "parameter type: {:?}",
                ty
            ))),
        })
        .collect::<SymbolicResult<Vec<_>>>()?;

    if param_ranges.is_empty() {
        let mut enc = EncoderCtx {
            layout,
            consts,
            step_vars,
            current_step: step,
            next_step: step + 1,
            params: &[],
            locals: Vec::new(),
        };

        let guard = enc.encode_bool(&action.guard)?;
        let effect = encode_effect(action, consts, layout, step_vars, step, &[])?;
        let frame = encode_frame(action, layout, step_vars, step)?;

        Ok(Bool::and(&[guard, effect, frame]))
    } else {
        let mut combos = Vec::new();
        enumerate_param_combos(&param_ranges, 0, &mut Vec::new(), &mut combos);

        let mut disjuncts = Vec::new();
        for combo in &combos {
            let z3_params: Vec<Dynamic> = combo
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
            };

            let guard = enc.encode_bool(&action.guard)?;
            let effect = encode_effect(action, consts, layout, step_vars, step, &z3_params)?;
            let frame = encode_frame(action, layout, step_vars, step)?;

            disjuncts.push(Bool::and(&[guard, effect, frame]));
        }

        Ok(Bool::or(&disjuncts))
    }
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

fn encode_effect(
    action: &CompiledAction,
    consts: &[Value],
    layout: &VarLayout,
    step_vars: &[Vec<Vec<Dynamic>>],
    step: usize,
    params: &[Dynamic],
) -> SymbolicResult<Bool> {
    let mut enc = EncoderCtx {
        layout,
        consts,
        step_vars,
        current_step: step,
        next_step: step + 1,
        params,
        locals: Vec::new(),
    };

    encode_effect_expr(&action.effect, &mut enc, layout, step_vars, step)
}

fn encode_effect_expr(
    expr: &CompiledExpr,
    enc: &mut EncoderCtx,
    layout: &VarLayout,
    step_vars: &[Vec<Vec<Dynamic>>],
    step: usize,
) -> SymbolicResult<Bool> {
    match expr {
        CompiledExpr::Bool(true) => Ok(Bool::from_bool(true)),

        CompiledExpr::Binary {
            op: BinOp::And,
            left,
            right,
        } => {
            let l = encode_effect_expr(left, enc, layout, step_vars, step)?;
            let r = encode_effect_expr(right, enc, layout, step_vars, step)?;
            Ok(Bool::and(&[l, r]))
        }

        // PrimedVar(idx) == rhs
        CompiledExpr::Binary {
            op: BinOp::Eq,
            left,
            right,
        } => {
            if let CompiledExpr::PrimedVar(var_idx) = left.as_ref() {
                encode_primed_assignment(*var_idx, right, enc, layout, step_vars, step)
            } else {
                enc.encode_bool(expr)
            }
        }

        CompiledExpr::Unchanged(var_idx) => {
            let d = enc.encode_unchanged(*var_idx)?;
            d.as_bool()
                .ok_or_else(|| SymbolicError::Encoding("unchanged not bool".into()))
        }

        _ => enc.encode_bool(expr),
    }
}

fn encode_primed_assignment(
    var_idx: usize,
    rhs: &CompiledExpr,
    enc: &mut EncoderCtx,
    layout: &VarLayout,
    step_vars: &[Vec<Vec<Dynamic>>],
    step: usize,
) -> SymbolicResult<Bool> {
    let entry = &layout.entries[var_idx];
    let next_vars = &step_vars[step + 1][var_idx];

    match &entry.kind {
        VarKind::Bool | VarKind::Int { .. } => {
            let rhs_z3 = enc.encode(rhs)?;
            if let (Some(vi), Some(ri)) = (next_vars[0].as_int(), rhs_z3.as_int()) {
                Ok(vi.eq(&ri))
            } else if let (Some(vb), Some(rb)) = (next_vars[0].as_bool(), rhs_z3.as_bool()) {
                Ok(vb.eq(&rb))
            } else {
                Err(SymbolicError::Encoding(
                    "type mismatch in primed assignment".into(),
                ))
            }
        }
        VarKind::ExplodedDict { key_lo, key_hi, .. } => {
            let key_lo = *key_lo;
            let key_hi = *key_hi;
            let curr_vars = &step_vars[step][var_idx];

            match rhs {
                CompiledExpr::FnUpdate {
                    base: _,
                    key,
                    value,
                } => {
                    let mut conjuncts = Vec::new();
                    let key_z3 = enc.encode_int(key)?;
                    let val_z3 = enc.encode(value)?;

                    for (i, k) in (key_lo..=key_hi).enumerate() {
                        let k_z3 = Int::from_i64(k);
                        let is_updated = key_z3.eq(&k_z3);

                        if let (Some(ni), Some(vi), Some(ci)) = (
                            next_vars[i].as_int(),
                            val_z3.as_int(),
                            curr_vars[i].as_int(),
                        ) {
                            conjuncts.push(ni.eq(&is_updated.ite(&vi, &ci)));
                        } else if let (Some(nb), Some(vb), Some(cb)) = (
                            next_vars[i].as_bool(),
                            val_z3.as_bool(),
                            curr_vars[i].as_bool(),
                        ) {
                            conjuncts.push(nb.eq(&is_updated.ite(&vb, &cb)));
                        }
                    }

                    Ok(Bool::and(&conjuncts))
                }
                CompiledExpr::FnLit { domain: _, body } => {
                    let mut conjuncts = Vec::new();
                    for (i, k) in (key_lo..=key_hi).enumerate() {
                        let k_val = Dynamic::from_ast(&Int::from_i64(k));
                        enc.locals.push(k_val);
                        let body_z3 = enc.encode(body)?;
                        enc.locals.pop();

                        if let (Some(ni), Some(ri)) = (next_vars[i].as_int(), body_z3.as_int()) {
                            conjuncts.push(ni.eq(&ri));
                        } else if let (Some(nb), Some(rb)) =
                            (next_vars[i].as_bool(), body_z3.as_bool())
                        {
                            conjuncts.push(nb.eq(&rb));
                        }
                    }
                    Ok(Bool::and(&conjuncts))
                }
                // Dict merge: state | { k1: v1, k2: v2, ... }
                // For each key in range: next[k] = if k matches any pair key then pair value else curr[k]
                CompiledExpr::Binary {
                    op: BinOp::Union,
                    left: _,
                    right,
                } => encode_dict_merge(right, enc, next_vars, curr_vars, key_lo, key_hi),
                _ => Err(SymbolicError::Encoding(format!(
                    "unsupported dict rhs: {:?}",
                    std::mem::discriminant(rhs)
                ))),
            }
        }
        VarKind::ExplodedSet { .. } => Err(SymbolicError::Unsupported(
            "set variable assignment in effect".into(),
        )),
    }
}

/// Encode a dict merge: for each key k, next[k] = if k matches a pair key then pair value else curr[k].
/// The `merge_expr` is the right side of the Union operator (typically a DictLit).
fn encode_dict_merge(
    merge_expr: &CompiledExpr,
    enc: &mut EncoderCtx,
    next_vars: &[Dynamic],
    curr_vars: &[Dynamic],
    key_lo: i64,
    key_hi: i64,
) -> SymbolicResult<Bool> {
    // Extract the pairs from DictLit, or treat a single-pair merge
    let pairs: Vec<(&CompiledExpr, &CompiledExpr)> = match merge_expr {
        CompiledExpr::DictLit(ps) => ps.iter().map(|(k, v)| (k, v)).collect(),
        // Could also be a nested Union for multi-key merge
        _ => {
            return Err(SymbolicError::Encoding(format!(
                "unsupported dict merge rhs: {:?}",
                std::mem::discriminant(merge_expr)
            )));
        }
    };

    // Encode all pair keys and values upfront
    let mut encoded_pairs: Vec<(Int, Dynamic)> = Vec::new();
    for (key_expr, val_expr) in &pairs {
        let key_z3 = enc.encode_int(key_expr)?;
        let val_z3 = enc.encode(val_expr)?;
        encoded_pairs.push((key_z3, val_z3));
    }

    let mut conjuncts = Vec::new();
    for (i, k) in (key_lo..=key_hi).enumerate() {
        let k_z3 = Int::from_i64(k);

        // Build nested ITE: if key0 == k then val0 else if key1 == k then val1 else curr[k]
        // Start from curr[k] and layer on updates in reverse
        if let Some(ci) = curr_vars[i].as_int() {
            let mut result = ci;
            for (pair_key, pair_val) in encoded_pairs.iter().rev() {
                if let Some(vi) = pair_val.as_int() {
                    let is_match = pair_key.eq(&k_z3);
                    result = is_match.ite(&vi, &result);
                }
            }
            if let Some(ni) = next_vars[i].as_int() {
                conjuncts.push(ni.eq(&result));
            }
        } else if let Some(cb) = curr_vars[i].as_bool() {
            let mut result = cb;
            for (pair_key, pair_val) in encoded_pairs.iter().rev() {
                if let Some(vb) = pair_val.as_bool() {
                    let is_match = pair_key.eq(&k_z3);
                    result = is_match.ite(&vb, &result);
                }
            }
            if let Some(nb) = next_vars[i].as_bool() {
                conjuncts.push(nb.eq(&result));
            }
        }
    }

    Ok(Bool::and(&conjuncts))
}

fn encode_frame(
    action: &CompiledAction,
    layout: &VarLayout,
    step_vars: &[Vec<Vec<Dynamic>>],
    step: usize,
) -> SymbolicResult<Bool> {
    let mut conjuncts = Vec::new();

    for (var_idx, _entry) in layout.entries.iter().enumerate() {
        if action.changes.contains(&var_idx) {
            continue;
        }

        let curr = &step_vars[step][var_idx];
        let next = &step_vars[step + 1][var_idx];

        for (c, n) in curr.iter().zip(next.iter()) {
            if let (Some(ci), Some(ni)) = (c.as_int(), n.as_int()) {
                conjuncts.push(ci.eq(&ni));
            } else if let (Some(cb), Some(nb)) = (c.as_bool(), n.as_bool()) {
                conjuncts.push(cb.eq(&nb));
            }
        }
    }

    if conjuncts.is_empty() {
        return Ok(Bool::from_bool(true));
    }

    Ok(Bool::and(&conjuncts))
}

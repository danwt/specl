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
            solver.assert(Bool::from_bool(false));
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
                    compound_locals: Vec::new(),
                    set_locals: Vec::new(),
                    whole_var_locals: Vec::new(),
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
                compound_locals: Vec::new(),
                set_locals: Vec::new(),
                whole_var_locals: Vec::new(),
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
                compound_locals: Vec::new(),
                set_locals: Vec::new(),
                whole_var_locals: Vec::new(),
            };
            let rhs_z3 = enc.encode(rhs)?;
            if let (Some(vi), Some(ri)) = (z3_vars[0].as_int(), rhs_z3.as_int()) {
                solver.assert(vi.eq(&ri));
            } else if let (Some(vb), Some(rb)) = (z3_vars[0].as_bool(), rhs_z3.as_bool()) {
                solver.assert(vb.eq(&rb));
            }
            Ok(())
        }
        VarKind::ExplodedDict {
            key_lo,
            key_hi,
            value_kind,
        } => {
            let key_lo = *key_lo;
            let key_hi = *key_hi;
            let stride = value_kind.z3_var_count();
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
                            compound_locals: Vec::new(),
                            set_locals: Vec::new(),
                            whole_var_locals: Vec::new(),
                        };
                        let k_val = Dynamic::from_ast(&Int::from_i64(k));
                        enc.locals.push(k_val);

                        let is_scalar_value =
                            matches!(value_kind.as_ref(), VarKind::Bool | VarKind::Int { .. });
                        if is_scalar_value {
                            let body_z3 = enc.encode(body)?;
                            if let (Some(vi), Some(ri)) = (z3_vars[i].as_int(), body_z3.as_int()) {
                                solver.assert(vi.eq(&ri));
                            } else if let (Some(vb), Some(rb)) =
                                (z3_vars[i].as_bool(), body_z3.as_bool())
                            {
                                solver.assert(vb.eq(&rb));
                            }
                        } else {
                            let key_offset = i * stride;
                            let key_vars = &z3_vars[key_offset..key_offset + stride];
                            encode_init_compound_body(
                                solver, &mut enc, body, key_vars, value_kind, consts,
                            )?;
                        }
                    }
                    Ok(())
                }
                CompiledExpr::DictLit(pairs) if stride == 1 => {
                    for (key_expr, val_expr) in pairs {
                        let mut enc = EncoderCtx {
                            layout,
                            consts,
                            step_vars,
                            current_step: 0,
                            next_step: 0,
                            params: &[],
                            locals: Vec::new(),
                            compound_locals: Vec::new(),
                            set_locals: Vec::new(),
                            whole_var_locals: Vec::new(),
                        };
                        let key_val = enc.extract_concrete_int_helper(key_expr)?;
                        let offset = (key_val - key_lo) as usize;
                        let val_z3 = enc.encode(val_expr)?;
                        if let (Some(vi), Some(ri)) = (z3_vars[offset].as_int(), val_z3.as_int()) {
                            solver.assert(vi.eq(&ri));
                        } else if let (Some(vb), Some(rb)) =
                            (z3_vars[offset].as_bool(), val_z3.as_bool())
                        {
                            solver.assert(vb.eq(&rb));
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
        VarKind::ExplodedSet { lo, hi } => {
            let mut enc = EncoderCtx {
                layout,
                consts,
                step_vars,
                current_step: 0,
                next_step: 0,
                params: &[],
                locals: Vec::new(),
                compound_locals: Vec::new(),
                set_locals: Vec::new(),
                whole_var_locals: Vec::new(),
            };
            let flags = enc.encode_as_set(rhs, *lo, *hi)?;
            for (i, flag) in flags.iter().enumerate() {
                let vb = z3_vars[i].as_bool().unwrap();
                solver.assert(vb.eq(flag));
            }
            Ok(())
        }
        VarKind::ExplodedSeq { max_len, elem_kind } => {
            let mut enc = EncoderCtx {
                layout,
                consts,
                step_vars,
                current_step: 0,
                next_step: 0,
                params: &[],
                locals: Vec::new(),
                compound_locals: Vec::new(),
                set_locals: Vec::new(),
                whole_var_locals: Vec::new(),
            };
            match rhs {
                CompiledExpr::SeqLit(elems) => {
                    // len = elems.len()
                    let len_var = z3_vars[0].as_int().unwrap();
                    solver.assert(len_var.eq(Int::from_i64(elems.len() as i64)));
                    // assign each element
                    let elem_stride = elem_kind.z3_var_count();
                    for (i, elem_expr) in elems.iter().enumerate() {
                        if i >= *max_len {
                            break;
                        }
                        let val = enc.encode(elem_expr)?;
                        let offset = 1 + i * elem_stride;
                        if let (Some(vi), Some(ri)) = (z3_vars[offset].as_int(), val.as_int()) {
                            solver.assert(vi.eq(&ri));
                        } else if let (Some(vb), Some(rb)) =
                            (z3_vars[offset].as_bool(), val.as_bool())
                        {
                            solver.assert(vb.eq(&rb));
                        }
                    }
                    Ok(())
                }
                _ => Err(SymbolicError::Encoding(format!(
                    "unsupported seq init rhs: {:?}",
                    std::mem::discriminant(rhs)
                ))),
            }
        }
    }
}

/// Recursively encode init for compound value bodies (inner dict, set, seq).
fn encode_init_compound_body(
    solver: &Solver,
    enc: &mut EncoderCtx,
    body: &CompiledExpr,
    slot_vars: &[Dynamic],
    value_kind: &VarKind,
    consts: &[Value],
) -> SymbolicResult<()> {
    match value_kind {
        VarKind::ExplodedSeq { max_len, .. } => {
            if let CompiledExpr::SeqLit(elems) = body {
                let len_var = slot_vars[0].as_int().unwrap();
                solver.assert(len_var.eq(Int::from_i64(elems.len() as i64)));
                for (ei, elem_expr) in elems.iter().enumerate() {
                    if ei >= *max_len {
                        break;
                    }
                    let val = enc.encode(elem_expr)?;
                    let offset = 1 + ei;
                    if let (Some(vi), Some(ri)) = (slot_vars[offset].as_int(), val.as_int()) {
                        solver.assert(vi.eq(&ri));
                    } else if let (Some(vb), Some(rb)) =
                        (slot_vars[offset].as_bool(), val.as_bool())
                    {
                        solver.assert(vb.eq(&rb));
                    }
                }
                Ok(())
            } else {
                Err(SymbolicError::Encoding(
                    "compound init: expected SeqLit for Seq value".into(),
                ))
            }
        }
        VarKind::ExplodedDict {
            key_lo,
            key_hi,
            value_kind: inner_vk,
        } => {
            if let CompiledExpr::FnLit {
                domain: _,
                body: inner_body,
            } = body
            {
                let inner_stride = inner_vk.z3_var_count();
                for (j_idx, j) in (*key_lo..=*key_hi).enumerate() {
                    let j_val = Dynamic::from_ast(&Int::from_i64(j));
                    enc.locals.push(j_val);
                    let inner_offset = j_idx * inner_stride;
                    let inner_vars = &slot_vars[inner_offset..inner_offset + inner_stride];
                    if matches!(inner_vk.as_ref(), VarKind::Bool | VarKind::Int { .. }) {
                        let body_z3 = enc.encode(inner_body)?;
                        if let (Some(vi), Some(ri)) = (inner_vars[0].as_int(), body_z3.as_int()) {
                            solver.assert(vi.eq(&ri));
                        } else if let (Some(vb), Some(rb)) =
                            (inner_vars[0].as_bool(), body_z3.as_bool())
                        {
                            solver.assert(vb.eq(&rb));
                        }
                    } else {
                        encode_init_compound_body(
                            solver, enc, inner_body, inner_vars, inner_vk, consts,
                        )?;
                    }
                    enc.locals.pop();
                }
                Ok(())
            } else {
                Err(SymbolicError::Encoding(format!(
                    "compound init: expected FnLit for Dict value, got {:?}",
                    std::mem::discriminant(body)
                )))
            }
        }
        VarKind::ExplodedSet { lo, hi } => {
            let flags = enc.encode_as_set(body, *lo, *hi)?;
            for (i, flag) in flags.iter().enumerate() {
                let vb = slot_vars[i].as_bool().unwrap();
                solver.assert(vb.eq(flag));
            }
            Ok(())
        }
        _ => {
            let body_z3 = enc.encode(body)?;
            if let (Some(vi), Some(ri)) = (slot_vars[0].as_int(), body_z3.as_int()) {
                solver.assert(vi.eq(&ri));
            } else if let (Some(vb), Some(rb)) = (slot_vars[0].as_bool(), body_z3.as_bool()) {
                solver.assert(vb.eq(&rb));
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
        let action_enc = encode_action(action, spec, consts, layout, step_vars, step)?;
        action_encodings.push(action_enc);
    }

    Ok(Bool::or(&action_encodings))
}

fn encode_action(
    action: &CompiledAction,
    spec: &CompiledSpec,
    consts: &[Value],
    layout: &VarLayout,
    step_vars: &[Vec<Vec<Dynamic>>],
    step: usize,
) -> SymbolicResult<Bool> {
    let param_ranges: Vec<(i64, i64)> = action
        .params
        .iter()
        .enumerate()
        .map(|(i, (_, ty))| match ty {
            Type::Range(lo, hi) => Ok((*lo, *hi)),
            Type::Nat => Ok((0, 100)),
            Type::Int => {
                // Try resolving from AST type expressions (handles const-dependent ranges)
                if let Some(type_expr) = action.param_type_exprs.get(i) {
                    crate::state_vars::eval_type_expr_range(type_expr, spec, consts)
                        .ok_or_else(|| SymbolicError::Unsupported("unbounded Int parameter".into()))
                } else {
                    Err(SymbolicError::Unsupported("unbounded Int parameter".into()))
                }
            }
            Type::String => {
                let n = layout.string_table.len() as i64;
                if n == 0 {
                    Err(SymbolicError::Encoding(
                        "String parameter but no strings in spec".into(),
                    ))
                } else {
                    Ok((0, n - 1))
                }
            }
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
            compound_locals: Vec::new(),
            set_locals: Vec::new(),
            whole_var_locals: Vec::new(),
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
                compound_locals: Vec::new(),
                set_locals: Vec::new(),
                whole_var_locals: Vec::new(),
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
        compound_locals: Vec::new(),
        set_locals: Vec::new(),
        whole_var_locals: Vec::new(),
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
        VarKind::ExplodedDict {
            key_lo,
            key_hi,
            value_kind,
        } => {
            let key_lo = *key_lo;
            let key_hi = *key_hi;
            let stride = value_kind.z3_var_count();
            let curr_vars = &step_vars[step][var_idx];

            match rhs {
                CompiledExpr::FnUpdate {
                    base: _,
                    key,
                    value,
                } if matches!(value_kind.as_ref(), VarKind::Bool | VarKind::Int { .. }) => {
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
                            conjuncts.push(ni.eq(is_updated.ite(&vi, &ci)));
                        } else if let (Some(nb), Some(vb), Some(cb)) = (
                            next_vars[i].as_bool(),
                            val_z3.as_bool(),
                            curr_vars[i].as_bool(),
                        ) {
                            conjuncts.push(nb.eq(is_updated.ite(&vb, &cb)));
                        }
                    }

                    Ok(Bool::and(&conjuncts))
                }
                CompiledExpr::FnLit { domain: _, body }
                    if matches!(value_kind.as_ref(), VarKind::Bool | VarKind::Int { .. }) =>
                {
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
                CompiledExpr::Binary {
                    op: BinOp::Union,
                    left: _,
                    right,
                } => {
                    if matches!(value_kind.as_ref(), VarKind::Bool | VarKind::Int { .. }) {
                        encode_dict_merge(right, enc, next_vars, curr_vars, key_lo, key_hi)
                    } else {
                        encode_dict_merge_compound(
                            right, enc, next_vars, curr_vars, key_lo, key_hi, stride, value_kind,
                            step_vars, step, var_idx,
                        )
                    }
                }
                // FnLit with compound values
                CompiledExpr::FnLit { domain: _, body } => {
                    let mut conjuncts = Vec::new();
                    for (i, k) in (key_lo..=key_hi).enumerate() {
                        let k_val = Dynamic::from_ast(&Int::from_i64(k));
                        enc.locals.push(k_val);
                        let key_offset = i * stride;
                        let key_next = &next_vars[key_offset..key_offset + stride];
                        let key_curr = &curr_vars[key_offset..key_offset + stride];
                        let updated =
                            encode_compound_update_for_slot(enc, body, key_curr, value_kind);
                        match updated {
                            Ok(vals) => {
                                for (j, val) in vals.iter().enumerate() {
                                    let c = eq_dynamic(&key_next[j], val)?;
                                    conjuncts.push(c);
                                }
                            }
                            Err(e) => {
                                enc.locals.pop();
                                return Err(e);
                            }
                        }
                        enc.locals.pop();
                    }
                    Ok(Bool::and(&conjuncts))
                }
                _ => Err(SymbolicError::Encoding(format!(
                    "unsupported dict rhs: {:?}",
                    std::mem::discriminant(rhs)
                ))),
            }
        }
        VarKind::ExplodedSet { lo, hi } => {
            let lo = *lo;
            let hi = *hi;
            let flags = enc.encode_as_set(rhs, lo, hi)?;
            let mut conjuncts = Vec::new();
            for (i, flag) in flags.iter().enumerate() {
                let nb = next_vars[i].as_bool().unwrap();
                conjuncts.push(nb.eq(flag));
            }
            Ok(Bool::and(&conjuncts))
        }
        VarKind::ExplodedSeq { max_len, elem_kind } => {
            let curr_vars = &step_vars[step][var_idx];
            let elem_stride = elem_kind.z3_var_count();

            match rhs {
                CompiledExpr::SeqLit(elems) => {
                    let mut conjuncts = Vec::new();
                    let next_len = next_vars[0].as_int().unwrap();
                    conjuncts.push(next_len.eq(Int::from_i64(elems.len() as i64)));
                    for (i, elem_expr) in elems.iter().enumerate() {
                        if i >= *max_len {
                            break;
                        }
                        let val = enc.encode(elem_expr)?;
                        let offset = 1 + i * elem_stride;
                        if let (Some(ni), Some(ri)) = (next_vars[offset].as_int(), val.as_int()) {
                            conjuncts.push(ni.eq(&ri));
                        } else if let (Some(nb), Some(rb)) =
                            (next_vars[offset].as_bool(), val.as_bool())
                        {
                            conjuncts.push(nb.eq(&rb));
                        }
                    }
                    // Frame remaining slots
                    for i in elems.len()..*max_len {
                        let offset = 1 + i * elem_stride;
                        for j in 0..elem_stride {
                            if let (Some(ni), Some(ci)) = (
                                next_vars[offset + j].as_int(),
                                curr_vars[offset + j].as_int(),
                            ) {
                                conjuncts.push(ni.eq(&ci));
                            } else if let (Some(nb), Some(cb)) = (
                                next_vars[offset + j].as_bool(),
                                curr_vars[offset + j].as_bool(),
                            ) {
                                conjuncts.push(nb.eq(&cb));
                            }
                        }
                    }
                    Ok(Bool::and(&conjuncts))
                }
                // SeqTail: shift left, len - 1
                CompiledExpr::SeqTail(_) => {
                    let mut conjuncts = Vec::new();
                    let curr_len = curr_vars[0].as_int().unwrap();
                    let next_len = next_vars[0].as_int().unwrap();
                    conjuncts.push(next_len.eq(Int::sub(&[&curr_len, &Int::from_i64(1)])));
                    for i in 0..max_len.saturating_sub(1) {
                        let next_offset = 1 + i * elem_stride;
                        let curr_offset = 1 + (i + 1) * elem_stride;
                        for j in 0..elem_stride {
                            if let (Some(ni), Some(ci)) = (
                                next_vars[next_offset + j].as_int(),
                                curr_vars[curr_offset + j].as_int(),
                            ) {
                                conjuncts.push(ni.eq(&ci));
                            } else if let (Some(nb), Some(cb)) = (
                                next_vars[next_offset + j].as_bool(),
                                curr_vars[curr_offset + j].as_bool(),
                            ) {
                                conjuncts.push(nb.eq(&cb));
                            }
                        }
                    }
                    Ok(Bool::and(&conjuncts))
                }
                // Concat: base ++ [val] (append single element)
                CompiledExpr::Binary {
                    op: BinOp::Concat,
                    left: _,
                    right,
                } => match right.as_ref() {
                    CompiledExpr::SeqLit(elems) if elems.len() == 1 => {
                        let mut conjuncts = Vec::new();
                        let curr_len = curr_vars[0].as_int().unwrap();
                        let next_len = next_vars[0].as_int().unwrap();
                        conjuncts.push(next_len.eq(Int::add(&[&curr_len, &Int::from_i64(1)])));
                        let appended = enc.encode(&elems[0])?;
                        for j in 0..*max_len {
                            let offset = 1 + j * elem_stride;
                            let j_z3 = Int::from_i64(j as i64);
                            let is_append_slot = curr_len.eq(&j_z3);
                            for s in 0..elem_stride {
                                if let (Some(ni), Some(ci)) = (
                                    next_vars[offset + s].as_int(),
                                    curr_vars[offset + s].as_int(),
                                ) {
                                    let new_val = if s == 0 {
                                        appended.as_int().unwrap()
                                    } else {
                                        ci.clone()
                                    };
                                    conjuncts.push(ni.eq(is_append_slot.ite(&new_val, &ci)));
                                } else if let (Some(nb), Some(cb)) = (
                                    next_vars[offset + s].as_bool(),
                                    curr_vars[offset + s].as_bool(),
                                ) {
                                    let new_val = if s == 0 {
                                        appended.as_bool().unwrap()
                                    } else {
                                        cb.clone()
                                    };
                                    conjuncts.push(nb.eq(is_append_slot.ite(&new_val, &cb)));
                                }
                            }
                        }
                        Ok(Bool::and(&conjuncts))
                    }
                    _ => Err(SymbolicError::Encoding(
                        "concat in seq effect: only `base ++ [single_elem]` is supported".into(),
                    )),
                },
                // Slice: base[lo..hi]
                CompiledExpr::Slice { base: _, lo, hi } => {
                    let mut conjuncts = Vec::new();
                    let lo_z3 = enc.encode_int(lo)?;
                    let hi_z3 = enc.encode_int(hi)?;
                    let next_len = next_vars[0].as_int().unwrap();
                    conjuncts.push(next_len.eq(Int::sub(&[&hi_z3, &lo_z3])));
                    for i in 0..*max_len {
                        let next_offset = 1 + i * elem_stride;
                        let i_z3 = Int::from_i64(i as i64);
                        let src_idx = Int::add(&[&lo_z3, &i_z3]);
                        // ITE chain over source elements
                        for s in 0..elem_stride {
                            if let Some(ni) = next_vars[next_offset + s].as_int() {
                                let mut val = curr_vars[1 + s].as_int().unwrap().clone(); // default: elem 0
                                for j in (0..*max_len).rev() {
                                    let src_offset = 1 + j * elem_stride;
                                    let cond = src_idx.eq(Int::from_i64(j as i64));
                                    let cv = curr_vars[src_offset + s].as_int().unwrap();
                                    val = cond.ite(&cv, &val);
                                }
                                conjuncts.push(ni.eq(&val));
                            } else if let Some(nb) = next_vars[next_offset + s].as_bool() {
                                let mut val = curr_vars[1 + s].as_bool().unwrap().clone();
                                for j in (0..*max_len).rev() {
                                    let src_offset = 1 + j * elem_stride;
                                    let cond = src_idx.eq(Int::from_i64(j as i64));
                                    let cv = curr_vars[src_offset + s].as_bool().unwrap();
                                    val = cond.ite(&cv, &val);
                                }
                                conjuncts.push(nb.eq(&val));
                            }
                        }
                    }
                    Ok(Bool::and(&conjuncts))
                }
                _ => Err(SymbolicError::Encoding(format!(
                    "unsupported seq effect rhs: {:?}",
                    std::mem::discriminant(rhs)
                ))),
            }
        }
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

/// Dict merge for compound value kinds (e.g., Dict[Range, Seq[T]]).
/// For each key k: if k is updated, encode the seq operation; otherwise frame.
#[allow(clippy::too_many_arguments)]
fn encode_dict_merge_compound(
    merge_expr: &CompiledExpr,
    enc: &mut EncoderCtx,
    next_vars: &[Dynamic],
    curr_vars: &[Dynamic],
    key_lo: i64,
    key_hi: i64,
    stride: usize,
    value_kind: &VarKind,
    _step_vars: &[Vec<Vec<Dynamic>>],
    _step: usize,
    _var_idx: usize,
) -> SymbolicResult<Bool> {
    let pairs: Vec<(&CompiledExpr, &CompiledExpr)> = match merge_expr {
        CompiledExpr::DictLit(ps) => ps.iter().map(|(k, v)| (k, v)).collect(),
        _ => {
            return Err(SymbolicError::Encoding(format!(
                "unsupported compound dict merge rhs: {:?}",
                std::mem::discriminant(merge_expr)
            )));
        }
    };

    // Encode Z3 key expressions for each update pair
    let mut encoded_keys: Vec<(Int, &CompiledExpr)> = Vec::new();
    for (key_expr, val_expr) in &pairs {
        let key_z3 = enc.encode_int(key_expr)?;
        encoded_keys.push((key_z3, val_expr));
    }

    let mut conjuncts = Vec::new();

    for k in key_lo..=key_hi {
        let k_idx = (k - key_lo) as usize;
        let key_offset = k_idx * stride;
        let key_next = &next_vars[key_offset..key_offset + stride];
        let key_curr = &curr_vars[key_offset..key_offset + stride];
        let k_z3 = Int::from_i64(k);

        let frame_elems: Vec<Dynamic> = (0..stride).map(|j| key_curr[j].clone()).collect();

        let mut result_vars: Vec<Dynamic> = frame_elems;
        for (pair_key, val_expr) in encoded_keys.iter().rev() {
            let is_match = pair_key.eq(&k_z3);
            let updated = encode_compound_update_for_slot(enc, val_expr, key_curr, value_kind)?;
            let mut new_result = Vec::with_capacity(stride);
            for j in 0..stride {
                let selected = ite_dynamic(&is_match, &updated[j], &result_vars[j])?;
                new_result.push(selected);
            }
            result_vars = new_result;
        }

        for j in 0..stride {
            let c = eq_dynamic(&key_next[j], &result_vars[j])?;
            conjuncts.push(c);
        }
    }

    Ok(Bool::and(&conjuncts))
}

/// Encode a compound update for a single dict key slot.
/// Handles Seq (append, tail, literal), Dict (inner merge), and Set (union, literal).
fn encode_compound_update_for_slot(
    enc: &mut EncoderCtx,
    val_expr: &CompiledExpr,
    slot_curr: &[Dynamic],
    value_kind: &VarKind,
) -> SymbolicResult<Vec<Dynamic>> {
    let stride = slot_curr.len();

    // Identity/frame patterns (d | {k: d[k]})
    if matches!(
        val_expr,
        CompiledExpr::Index { .. } | CompiledExpr::Local(_)
    ) {
        return Ok(slot_curr.to_vec());
    }

    // If/then/else: recurse on both branches
    if let CompiledExpr::If {
        cond,
        then_branch,
        else_branch,
    } = val_expr
    {
        let cond_z3 = enc.encode_bool(cond)?;
        let then_vars = encode_compound_update_for_slot(enc, then_branch, slot_curr, value_kind)?;
        let else_vars = encode_compound_update_for_slot(enc, else_branch, slot_curr, value_kind)?;
        let mut result = Vec::with_capacity(stride);
        for i in 0..stride {
            result.push(ite_dynamic(&cond_z3, &then_vars[i], &else_vars[i])?);
        }
        return Ok(result);
    }

    match value_kind {
        VarKind::ExplodedSeq { max_len, .. } => {
            let max_len = *max_len;
            let curr_len = slot_curr[0].as_int().unwrap();
            match val_expr {
                CompiledExpr::Binary {
                    op: BinOp::Concat,
                    left: _,
                    right: concat_right,
                } => {
                    if let CompiledExpr::SeqLit(elems) = concat_right.as_ref() {
                        if elems.len() == 1 {
                            let new_len =
                                Dynamic::from_ast(&Int::add(&[&curr_len, &Int::from_i64(1)]));
                            let appended = enc.encode(&elems[0])?;
                            let mut result = vec![new_len];
                            for j in 0..max_len {
                                let j_z3 = Int::from_i64(j as i64);
                                let is_append = curr_len.eq(&j_z3);
                                let updated =
                                    ite_dynamic(&is_append, &appended, &slot_curr[1 + j])?;
                                result.push(updated);
                            }
                            return Ok(result);
                        }
                    }
                    Err(SymbolicError::Encoding(
                        "dict-of-seq merge: only single-element append supported".into(),
                    ))
                }
                CompiledExpr::SeqTail(_) => {
                    let new_len = Dynamic::from_ast(&Int::sub(&[&curr_len, &Int::from_i64(1)]));
                    let mut result = vec![new_len];
                    for i in 0..max_len.saturating_sub(1) {
                        result.push(slot_curr[1 + (i + 1)].clone());
                    }
                    if max_len > 0 {
                        result.push(slot_curr[stride - 1].clone());
                    }
                    Ok(result)
                }
                CompiledExpr::SeqLit(elems) => {
                    let mut result = vec![Dynamic::from_ast(&Int::from_i64(elems.len() as i64))];
                    for (i, elem_expr) in elems.iter().enumerate() {
                        if i >= max_len {
                            break;
                        }
                        result.push(enc.encode(elem_expr)?);
                    }
                    while result.len() < stride {
                        result.push(slot_curr[result.len()].clone());
                    }
                    Ok(result)
                }
                _ => Err(SymbolicError::Encoding(format!(
                    "unsupported seq operation in dict merge: {:?}",
                    std::mem::discriminant(val_expr)
                ))),
            }
        }
        VarKind::ExplodedDict {
            key_lo,
            key_hi,
            value_kind: inner_vk,
        } => {
            let inner_stride = inner_vk.z3_var_count();
            match val_expr {
                // Inner dict merge: val_expr = base | {k: v, ...}
                CompiledExpr::Binary {
                    op: BinOp::Union,
                    left: _,
                    right,
                } => {
                    let inner_pairs: Vec<(&CompiledExpr, &CompiledExpr)> = match right.as_ref() {
                        CompiledExpr::DictLit(ps) => ps.iter().map(|(k, v)| (k, v)).collect(),
                        _ => {
                            return Err(SymbolicError::Encoding(
                                "inner dict merge: expected DictLit on right side".into(),
                            ))
                        }
                    };
                    let mut encoded_inner_keys: Vec<(Int, &CompiledExpr)> = Vec::new();
                    for (key_expr, inner_val_expr) in &inner_pairs {
                        let ik_z3 = enc.encode_int(key_expr)?;
                        encoded_inner_keys.push((ik_z3, inner_val_expr));
                    }

                    let mut result = Vec::new();
                    for j in *key_lo..=*key_hi {
                        let j_idx = (j - key_lo) as usize;
                        let j_offset = j_idx * inner_stride;
                        let j_curr = &slot_curr[j_offset..j_offset + inner_stride];
                        let j_z3 = Int::from_i64(j);

                        let mut j_result: Vec<Dynamic> = j_curr.to_vec();
                        for (ik_z3, inner_val) in encoded_inner_keys.iter().rev() {
                            let is_match = ik_z3.eq(&j_z3);
                            let updated =
                                encode_compound_update_for_slot(enc, inner_val, j_curr, inner_vk)?;
                            let mut new_j = Vec::with_capacity(inner_stride);
                            for s in 0..inner_stride {
                                new_j.push(ite_dynamic(&is_match, &updated[s], &j_result[s])?);
                            }
                            j_result = new_j;
                        }
                        result.extend(j_result);
                    }
                    Ok(result)
                }
                // FnLit (full reassignment of inner dict)
                CompiledExpr::FnLit { domain: _, body } => {
                    let mut result = Vec::new();
                    for j in *key_lo..=*key_hi {
                        let j_val = Dynamic::from_ast(&Int::from_i64(j));
                        enc.locals.push(j_val);
                        let j_idx = (j - key_lo) as usize;
                        let j_offset = j_idx * inner_stride;
                        let j_curr = &slot_curr[j_offset..j_offset + inner_stride];
                        if matches!(inner_vk.as_ref(), VarKind::Bool | VarKind::Int { .. }) {
                            let body_z3 = enc.encode(body)?;
                            result.push(body_z3);
                        } else {
                            let updated =
                                encode_compound_update_for_slot(enc, body, j_curr, inner_vk)?;
                            result.extend(updated);
                        }
                        enc.locals.pop();
                    }
                    Ok(result)
                }
                _ => Err(SymbolicError::Encoding(format!(
                    "unsupported inner dict operation: {:?}",
                    std::mem::discriminant(val_expr)
                ))),
            }
        }
        VarKind::ExplodedSet { lo, hi } => {
            match val_expr {
                // Set union: val_expr = base union {elem, ...}
                CompiledExpr::Binary {
                    op: BinOp::Union,
                    left: _,
                    right,
                } => {
                    let new_flags = enc.encode_as_set(right, *lo, *hi)?;
                    let mut result = Vec::new();
                    for (i, new_flag) in new_flags.iter().enumerate() {
                        let curr_flag = slot_curr[i].as_bool().unwrap();
                        result.push(Dynamic::from_ast(&Bool::or(&[curr_flag, new_flag.clone()])));
                    }
                    Ok(result)
                }
                // Set literal (direct assignment)
                CompiledExpr::SetLit(_) | CompiledExpr::SetComprehension { .. } => {
                    let flags = enc.encode_as_set(val_expr, *lo, *hi)?;
                    Ok(flags.into_iter().map(|b| Dynamic::from_ast(&b)).collect())
                }
                _ => Err(SymbolicError::Encoding(format!(
                    "unsupported set operation in dict merge: {:?}",
                    std::mem::discriminant(val_expr)
                ))),
            }
        }
        _ => {
            // Scalar value: just encode directly
            let val_z3 = enc.encode(val_expr)?;
            Ok(vec![val_z3])
        }
    }
}

/// ITE on Dynamic values (works for both Int and Bool).
fn ite_dynamic(cond: &Bool, then_val: &Dynamic, else_val: &Dynamic) -> SymbolicResult<Dynamic> {
    if let (Some(t), Some(e)) = (then_val.as_int(), else_val.as_int()) {
        Ok(Dynamic::from_ast(&cond.ite(&t, &e)))
    } else if let (Some(t), Some(e)) = (then_val.as_bool(), else_val.as_bool()) {
        Ok(Dynamic::from_ast(&cond.ite(&t, &e)))
    } else {
        Err(SymbolicError::Encoding("ite_dynamic: type mismatch".into()))
    }
}

/// Equality on Dynamic values (works for both Int and Bool).
fn eq_dynamic(a: &Dynamic, b: &Dynamic) -> SymbolicResult<Bool> {
    if let (Some(ai), Some(bi)) = (a.as_int(), b.as_int()) {
        Ok(ai.eq(&bi))
    } else if let (Some(ab), Some(bb)) = (a.as_bool(), b.as_bool()) {
        Ok(ab.eq(&bb))
    } else {
        Err(SymbolicError::Encoding("eq_dynamic: type mismatch".into()))
    }
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

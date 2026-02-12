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
                    compound_locals: Vec::new(),
                    set_locals: Vec::new(),
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
            };
            let rhs_z3 = enc.encode(rhs)?;
            if let (Some(vi), Some(ri)) = (z3_vars[0].as_int(), rhs_z3.as_int()) {
                solver.assert(&vi.eq(&ri));
            } else if let (Some(vb), Some(rb)) = (z3_vars[0].as_bool(), rhs_z3.as_bool()) {
                solver.assert(&vb.eq(&rb));
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
                        };
                        let k_val = Dynamic::from_ast(&Int::from_i64(k));
                        enc.locals.push(k_val);

                        if stride == 1 {
                            let body_z3 = enc.encode(body)?;
                            if let (Some(vi), Some(ri)) = (z3_vars[i].as_int(), body_z3.as_int()) {
                                solver.assert(&vi.eq(&ri));
                            } else if let (Some(vb), Some(rb)) =
                                (z3_vars[i].as_bool(), body_z3.as_bool())
                            {
                                solver.assert(&vb.eq(&rb));
                            }
                        } else {
                            // Compound value: handle SeqLit
                            let key_offset = i * stride;
                            let key_vars = &z3_vars[key_offset..key_offset + stride];
                            if let CompiledExpr::SeqLit(elems) = body.as_ref() {
                                let len_var = key_vars[0].as_int().unwrap();
                                solver.assert(&len_var.eq(&Int::from_i64(elems.len() as i64)));
                                if let VarKind::ExplodedSeq { max_len, .. } = value_kind.as_ref() {
                                    for (ei, elem_expr) in elems.iter().enumerate() {
                                        if ei >= *max_len {
                                            break;
                                        }
                                        let val = enc.encode(elem_expr)?;
                                        let offset = 1 + ei;
                                        if let (Some(vi), Some(ri)) =
                                            (key_vars[offset].as_int(), val.as_int())
                                        {
                                            solver.assert(&vi.eq(&ri));
                                        } else if let (Some(vb), Some(rb)) =
                                            (key_vars[offset].as_bool(), val.as_bool())
                                        {
                                            solver.assert(&vb.eq(&rb));
                                        }
                                    }
                                }
                            } else {
                                return Err(SymbolicError::Encoding(
                                    "Dict[Range, Seq] init body must be SeqLit".into(),
                                ));
                            }
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
            };
            let flags = enc.encode_as_set(rhs, *lo, *hi)?;
            for (i, flag) in flags.iter().enumerate() {
                let vb = z3_vars[i].as_bool().unwrap();
                solver.assert(&vb.eq(flag));
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
            };
            match rhs {
                CompiledExpr::SeqLit(elems) => {
                    // len = elems.len()
                    let len_var = z3_vars[0].as_int().unwrap();
                    solver.assert(&len_var.eq(&Int::from_i64(elems.len() as i64)));
                    // assign each element
                    let elem_stride = elem_kind.z3_var_count();
                    for (i, elem_expr) in elems.iter().enumerate() {
                        if i >= *max_len {
                            break;
                        }
                        let val = enc.encode(elem_expr)?;
                        let offset = 1 + i * elem_stride;
                        if let (Some(vi), Some(ri)) = (z3_vars[offset].as_int(), val.as_int()) {
                            solver.assert(&vi.eq(&ri));
                        } else if let (Some(vb), Some(rb)) =
                            (z3_vars[offset].as_bool(), val.as_bool())
                        {
                            solver.assert(&vb.eq(&rb));
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
                } if stride == 1 => {
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
                CompiledExpr::FnLit { domain: _, body } if stride == 1 => {
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
                    if stride == 1 {
                        encode_dict_merge(right, enc, next_vars, curr_vars, key_lo, key_hi)
                    } else {
                        encode_dict_merge_compound(
                            right, enc, next_vars, curr_vars, key_lo, key_hi, stride, value_kind,
                            step_vars, step, var_idx,
                        )
                    }
                }
                // FnLit with compound values (Dict[Range, Seq[T]] init)
                CompiledExpr::FnLit { domain: _, body } => {
                    // body is evaluated per key, expecting a SeqLit
                    let mut conjuncts = Vec::new();
                    for (i, k) in (key_lo..=key_hi).enumerate() {
                        let k_val = Dynamic::from_ast(&Int::from_i64(k));
                        enc.locals.push(k_val);
                        let key_offset = i * stride;
                        let key_next = &next_vars[key_offset..key_offset + stride];
                        if let CompiledExpr::SeqLit(elems) = body.as_ref() {
                            let next_len = key_next[0].as_int().unwrap();
                            conjuncts.push(next_len.eq(&Int::from_i64(elems.len() as i64)));
                            if let VarKind::ExplodedSeq { max_len, elem_kind } = value_kind.as_ref()
                            {
                                let es = elem_kind.z3_var_count();
                                for (ei, elem_expr) in elems.iter().enumerate() {
                                    if ei >= *max_len {
                                        break;
                                    }
                                    let val = enc.encode(elem_expr)?;
                                    let offset = 1 + ei * es;
                                    if let (Some(ni), Some(ri)) =
                                        (key_next[offset].as_int(), val.as_int())
                                    {
                                        conjuncts.push(ni.eq(&ri));
                                    } else if let (Some(nb), Some(rb)) =
                                        (key_next[offset].as_bool(), val.as_bool())
                                    {
                                        conjuncts.push(nb.eq(&rb));
                                    }
                                }
                            }
                        } else {
                            enc.locals.pop();
                            return Err(SymbolicError::Encoding(
                                "Dict[Range, Seq] init body must be a SeqLit".into(),
                            ));
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
                    conjuncts.push(next_len.eq(&Int::from_i64(elems.len() as i64)));
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
                    conjuncts.push(next_len.eq(&Int::sub(&[&curr_len, &Int::from_i64(1)])));
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
                        conjuncts.push(next_len.eq(&Int::add(&[&curr_len, &Int::from_i64(1)])));
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
                                    conjuncts.push(ni.eq(&is_append_slot.ite(&new_val, &ci)));
                                } else if let (Some(nb), Some(cb)) = (
                                    next_vars[offset + s].as_bool(),
                                    curr_vars[offset + s].as_bool(),
                                ) {
                                    let new_val = if s == 0 {
                                        appended.as_bool().unwrap()
                                    } else {
                                        cb.clone()
                                    };
                                    conjuncts.push(nb.eq(&is_append_slot.ite(&new_val, &cb)));
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
                    conjuncts.push(next_len.eq(&Int::sub(&[&hi_z3, &lo_z3])));
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
                                    let cond = src_idx.eq(&Int::from_i64(j as i64));
                                    let cv = curr_vars[src_offset + s].as_int().unwrap();
                                    val = cond.ite(&cv, &val);
                                }
                                conjuncts.push(ni.eq(&val));
                            } else if let Some(nb) = next_vars[next_offset + s].as_bool() {
                                let mut val = curr_vars[1 + s].as_bool().unwrap().clone();
                                for j in (0..*max_len).rev() {
                                    let src_offset = 1 + j * elem_stride;
                                    let cond = src_idx.eq(&Int::from_i64(j as i64));
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

    let max_len = match value_kind {
        VarKind::ExplodedSeq { max_len, .. } => *max_len,
        _ => {
            return Err(SymbolicError::Encoding(
                "compound dict merge only supports Seq values".into(),
            ));
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

        // Check if any update key matches this slot
        // Build ITE: for each update pair, if key matches → apply operation, else frame
        // With multiple update pairs, later pairs shadow earlier ones (last match wins)
        // We process pairs in reverse to build nested ITEs correctly.

        // First, compute the "framed" values (copy current to next)
        let frame_len = key_curr[0].as_int().unwrap();
        let mut frame_elems: Vec<Dynamic> = Vec::new();
        for j in 0..stride {
            frame_elems.push(key_curr[j].clone());
        }

        // For each update pair, compute what the updated values would be
        // and build ITE selection
        let mut result_vars: Vec<Dynamic> = frame_elems;
        for (pair_key, val_expr) in encoded_keys.iter().rev() {
            let is_match = pair_key.eq(&k_z3);
            let updated =
                encode_seq_update_for_slot(enc, *val_expr, key_curr, max_len, &frame_len)?;
            // ITE per var: if this key matches, use updated; else use previous result
            let mut new_result = Vec::with_capacity(stride);
            for j in 0..stride {
                let selected = ite_dynamic(&is_match, &updated[j], &result_vars[j])?;
                new_result.push(selected);
            }
            result_vars = new_result;
        }

        // Assert next == result
        for j in 0..stride {
            let c = eq_dynamic(&key_next[j], &result_vars[j])?;
            conjuncts.push(c);
        }
    }

    Ok(Bool::and(&conjuncts))
}

/// Encode a seq operation (append, tail, literal) for a single dict key slot.
/// Returns the updated Z3 var values (len + elements).
fn encode_seq_update_for_slot(
    enc: &mut EncoderCtx,
    val_expr: &CompiledExpr,
    key_curr: &[Dynamic],
    max_len: usize,
    curr_len: &Int,
) -> SymbolicResult<Vec<Dynamic>> {
    let stride = key_curr.len();
    match val_expr {
        CompiledExpr::Binary {
            op: BinOp::Concat,
            left: _,
            right: concat_right,
        } => {
            // Append: base ++ [elem]
            if let CompiledExpr::SeqLit(elems) = concat_right.as_ref() {
                if elems.len() == 1 {
                    let new_len = Dynamic::from_ast(&Int::add(&[curr_len, &Int::from_i64(1)]));
                    let appended = enc.encode(&elems[0])?;
                    let mut result = vec![new_len];
                    for j in 0..max_len {
                        let j_z3 = Int::from_i64(j as i64);
                        let is_append = curr_len.eq(&j_z3);
                        let updated = ite_dynamic(&is_append, &appended, &key_curr[1 + j])?;
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
            let new_len = Dynamic::from_ast(&Int::sub(&[curr_len, &Int::from_i64(1)]));
            let mut result = vec![new_len];
            for i in 0..max_len.saturating_sub(1) {
                result.push(key_curr[1 + (i + 1)].clone()); // shift left
            }
            // Last element slot: keep current (doesn't matter, beyond new len)
            if max_len > 0 {
                result.push(key_curr[stride - 1].clone());
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
            // Pad remaining slots with current values
            while result.len() < stride {
                result.push(key_curr[result.len()].clone());
            }
            Ok(result)
        }
        CompiledExpr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            let cond_z3 = enc.encode_bool(cond)?;
            let then_vars =
                encode_seq_update_for_slot(enc, then_branch, key_curr, max_len, curr_len)?;
            let else_vars =
                encode_seq_update_for_slot(enc, else_branch, key_curr, max_len, curr_len)?;
            let mut result = Vec::with_capacity(stride);
            for i in 0..stride {
                result.push(ite_dynamic(&cond_z3, &then_vars[i], &else_vars[i])?);
            }
            Ok(result)
        }
        // Index into same variable (identity/frame): just return current slot values.
        // This handles patterns like `d = d | {i: d[i]}` where the value is unchanged.
        CompiledExpr::Index { .. } | CompiledExpr::Local(_) => Ok(key_curr.to_vec()),
        _ => Err(SymbolicError::Encoding(format!(
            "unsupported seq operation in dict merge: {:?}",
            std::mem::discriminant(val_expr)
        ))),
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

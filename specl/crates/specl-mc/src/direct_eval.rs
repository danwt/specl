//! Direct evaluation for initial states and successors.
//!
//! This module provides efficient state generation by directly evaluating
//! expressions rather than enumerating all type-valid values and filtering.
//!
//! Key insight: Most init/effect expressions are conjunctions of equalities
//! like `x == 0 and y == fn(i in S) => 0`. We can extract these assignments
//! and evaluate them directly.

use specl_eval::bytecode::{vm_eval, vm_eval_reuse, Bytecode, VmBufs};
use specl_eval::{eval, eval_bool, EvalContext, EvalError, Value};
use specl_ir::{BinOp, CompiledAction, CompiledExpr, CompiledSpec};
use tracing::debug;

use crate::state::{hash_var, State};

/// Result of extracting assignments from an expression.
#[derive(Debug, Clone)]
pub enum AssignmentResult {
    /// Direct assignment: var = value
    Direct(Vec<(usize, Value)>),
    /// Expression needs enumeration (can't extract direct assignments)
    NeedsEnumeration,
}

/// Extract variable assignments from an init predicate.
///
/// Handles common patterns like:
/// - `x == 0 and y == {} and z == fn(i in S) => 0`
/// - `(x == 0) and (y == 0)`
pub fn extract_init_assignments(
    init: &CompiledExpr,
    consts: &[Value],
    num_vars: usize,
) -> AssignmentResult {
    let mut assignments: Vec<Option<Value>> = vec![None; num_vars];
    let mut locals = Vec::new();

    if !extract_from_expr(init, consts, &mut assignments, &mut locals) {
        return AssignmentResult::NeedsEnumeration;
    }

    // Check all variables have assignments
    let mut result = Vec::new();
    for (idx, value) in assignments.into_iter().enumerate() {
        match value {
            Some(v) => result.push((idx, v)),
            None => {
                debug!(var_idx = idx, "variable not assigned in init");
                return AssignmentResult::NeedsEnumeration;
            }
        }
    }

    AssignmentResult::Direct(result)
}

/// Extract assignments from an expression recursively.
/// Returns false if the expression can't be analyzed (needs enumeration).
fn extract_from_expr(
    expr: &CompiledExpr,
    consts: &[Value],
    assignments: &mut [Option<Value>],
    locals: &mut Vec<Value>,
) -> bool {
    match expr {
        // Boolean literal true is trivially satisfied (no new assignments)
        CompiledExpr::Bool(true) => true,
        CompiledExpr::Bool(false) => false,

        // Conjunction: extract from both sides
        CompiledExpr::Binary {
            op: BinOp::And,
            left,
            right,
        } => {
            extract_from_expr(left, consts, assignments, locals)
                && extract_from_expr(right, consts, assignments, locals)
        }

        // Let binding: evaluate value, bind as local, extract from body
        CompiledExpr::Let { value, body } => {
            if let Some(val) = try_eval_value(value, consts, assignments, locals) {
                locals.push(val);
                let result = extract_from_expr(body, consts, assignments, locals);
                locals.pop();
                result
            } else {
                false
            }
        }

        // Equality: x == expr where x is a variable
        // In init context, PrimedVar and Var are equivalent (both refer to initial state)
        CompiledExpr::Binary {
            op: BinOp::Eq,
            left,
            right,
        } => {
            // Try left == right (var on left)
            let left_idx = match left.as_ref() {
                CompiledExpr::Var(idx) | CompiledExpr::PrimedVar(idx) => Some(*idx),
                _ => None,
            };
            if let Some(idx) = left_idx {
                if let Some(value) = try_eval_value(right, consts, assignments, locals) {
                    if assignments[idx].is_none() {
                        assignments[idx] = Some(value);
                        return true;
                    } else {
                        // Already assigned - check if same value
                        return assignments[idx].as_ref() == Some(&value);
                    }
                }
            }
            // Try right == left (var on right)
            let right_idx = match right.as_ref() {
                CompiledExpr::Var(idx) | CompiledExpr::PrimedVar(idx) => Some(*idx),
                _ => None,
            };
            if let Some(idx) = right_idx {
                if let Some(value) = try_eval_value(left, consts, assignments, locals) {
                    if assignments[idx].is_none() {
                        assignments[idx] = Some(value);
                        return true;
                    } else {
                        return assignments[idx].as_ref() == Some(&value);
                    }
                }
            }
            // Can't extract assignment
            false
        }

        // Other expressions need enumeration
        _ => false,
    }
}

/// Try to evaluate an expression to a value using already-extracted assignments.
/// Uses partial assignments as variable context so that init expressions like
/// `sigs = {k: {} for k in certs}` can reference previously assigned `certs`.
fn try_eval_value(
    expr: &CompiledExpr,
    consts: &[Value],
    partial_assignments: &[Option<Value>],
    locals: &[Value],
) -> Option<Value> {
    let vars: Vec<Value> = partial_assignments
        .iter()
        .map(|a| a.clone().unwrap_or(Value::none()))
        .collect();
    let mut ctx = EvalContext::new(&vars, &vars, consts, &[]);
    for local in locals {
        ctx.push_local(local.clone());
    }
    eval(expr, &mut ctx).ok()
}

/// Generate initial states by direct evaluation.
pub fn generate_initial_states_direct(
    spec: &CompiledSpec,
    consts: &[Value],
) -> Result<Vec<State>, EvalError> {
    let num_vars = spec.vars.len();

    match extract_init_assignments(&spec.init, consts, num_vars) {
        AssignmentResult::Direct(assignments) => {
            // Build the initial state directly
            let mut vars = vec![Value::none(); num_vars];
            for (idx, value) in assignments {
                vars[idx] = value;
            }
            Ok(vec![State::new(vars)])
        }
        AssignmentResult::NeedsEnumeration => {
            // Fall back to enumeration (handled by caller)
            Err(EvalError::Internal("init requires enumeration".to_string()))
        }
    }
}

/// Result of extracting effect assignments.
pub struct EffectExtraction {
    /// Variable assignments extracted from the effect.
    pub assignments: Vec<(usize, CompiledExpr)>,
    /// Whether the effect contains current-state constraints that require re-verification.
    pub needs_reverify: bool,
}

/// Extract effect assignments from an action.
/// Returns assignments and whether re-verification is needed.
/// Returns None if the effect can't be analyzed directly.
pub fn extract_effect_assignments(effect: &CompiledExpr) -> Option<EffectExtraction> {
    let mut assignments = Vec::new();
    let mut has_constraints = false;

    if !extract_effect_from_expr(effect, &mut assignments, &mut has_constraints) {
        return None;
    }

    Some(EffectExtraction {
        assignments,
        needs_reverify: has_constraints,
    })
}

/// Extract effect assignments from an expression.
fn extract_effect_from_expr(
    expr: &CompiledExpr,
    assignments: &mut Vec<(usize, CompiledExpr)>,
    has_constraints: &mut bool,
) -> bool {
    match expr {
        CompiledExpr::Bool(true) => true,
        CompiledExpr::Bool(false) => false,

        // Conjunction: extract from both sides
        CompiledExpr::Binary {
            op: BinOp::And,
            left,
            right,
        } => {
            extract_effect_from_expr(left, assignments, has_constraints)
                && extract_effect_from_expr(right, assignments, has_constraints)
        }

        // Let binding: extract from body, wrap assignment expressions in the let
        CompiledExpr::Let { value, body } => {
            let mut inner_assignments = Vec::new();
            let mut inner_constraints = false;
            if !extract_effect_from_expr(body, &mut inner_assignments, &mut inner_constraints) {
                return false;
            }
            *has_constraints |= inner_constraints;
            for (idx, inner_expr) in inner_assignments {
                assignments.push((
                    idx,
                    CompiledExpr::Let {
                        value: value.clone(),
                        body: Box::new(inner_expr),
                    },
                ));
            }
            true
        }

        // Primed variable equality: var' == expr
        CompiledExpr::Binary {
            op: BinOp::Eq,
            left,
            right,
        } => {
            // var' == expr
            if let CompiledExpr::PrimedVar(idx) = left.as_ref() {
                assignments.push((*idx, (**right).clone()));
                return true;
            }
            // expr == var'
            if let CompiledExpr::PrimedVar(idx) = right.as_ref() {
                assignments.push((*idx, (**left).clone()));
                return true;
            }
            // Not a primed variable assignment - current state constraint
            *has_constraints = true;
            matches!(
                (left.as_ref(), right.as_ref()),
                (CompiledExpr::Var(_), _)
                    | (_, CompiledExpr::Var(_))
                    | (CompiledExpr::Index { .. }, _)
                    | (_, CompiledExpr::Index { .. })
            )
        }

        // Unchanged constraint
        CompiledExpr::Unchanged(_) => true,

        // Other expressions
        _ => false,
    }
}

/// Apply effects using bytecode-compiled assignments (guard already checked).
/// Uses cached var_hashes from the parent state to avoid rehashing old values.
/// Uses var_hashes_buf as a reusable buffer to avoid per-firing allocation.
pub fn apply_effects_bytecode(
    state: &State,
    params: &[Value],
    consts: &[Value],
    compiled_assignments: &[(usize, Bytecode)],
    needs_reverify: bool,
    next_vars_buf: &mut Vec<Value>,
    effect: &CompiledExpr,
    var_hashes_buf: &mut Vec<u64>,
) -> Result<Option<State>, EvalError> {
    next_vars_buf.clear();
    next_vars_buf.extend_from_slice(&state.vars);
    var_hashes_buf.clear();
    var_hashes_buf.extend_from_slice(&state.var_hashes);
    let mut fp = state.fingerprint().as_u64();

    for (var_idx, bc) in compiled_assignments {
        let value = vm_eval(bc, &state.vars, next_vars_buf, consts, params)?;
        let old_hash = var_hashes_buf[*var_idx];
        let new_hash = hash_var(*var_idx, &value);
        fp ^= old_hash ^ new_hash;
        var_hashes_buf[*var_idx] = new_hash;
        next_vars_buf[*var_idx] = value;
    }

    let fp = crate::state::Fingerprint::from_u64(fp);
    if needs_reverify {
        let mut ctx = EvalContext::new(&state.vars, next_vars_buf, consts, params);
        let result = eval(effect, &mut ctx)?;
        if result.as_bool() == Some(true) {
            Ok(Some(State::with_fingerprint_and_hashes(
                std::mem::take(next_vars_buf),
                fp,
                var_hashes_buf,
            )))
        } else {
            Ok(None)
        }
    } else {
        Ok(Some(State::with_fingerprint_and_hashes(
            std::mem::take(next_vars_buf),
            fp,
            var_hashes_buf,
        )))
    }
}

/// Apply effects using bytecode-compiled assignments with reusable VM buffers.
/// Uses cached var_hashes from the parent state to avoid rehashing old values.
/// Uses var_hashes_buf as a reusable buffer to avoid per-firing allocation.
pub fn apply_effects_bytecode_reuse(
    state: &State,
    params: &[Value],
    consts: &[Value],
    compiled_assignments: &[(usize, Bytecode)],
    needs_reverify: bool,
    next_vars_buf: &mut Vec<Value>,
    effect: &CompiledExpr,
    vm_bufs: &mut VmBufs,
    var_hashes_buf: &mut Vec<u64>,
) -> Result<Option<State>, EvalError> {
    next_vars_buf.clear();
    next_vars_buf.extend_from_slice(&state.vars);
    var_hashes_buf.clear();
    var_hashes_buf.extend_from_slice(&state.var_hashes);
    let mut fp = state.fingerprint().as_u64();

    for (var_idx, bc) in compiled_assignments {
        let value = vm_eval_reuse(bc, &state.vars, next_vars_buf, consts, params, vm_bufs)?;
        let old_hash = var_hashes_buf[*var_idx];
        let new_hash = hash_var(*var_idx, &value);
        fp ^= old_hash ^ new_hash;
        var_hashes_buf[*var_idx] = new_hash;
        next_vars_buf[*var_idx] = value;
    }

    let fp = crate::state::Fingerprint::from_u64(fp);
    if needs_reverify {
        let mut ctx = EvalContext::new(&state.vars, next_vars_buf, consts, params);
        let result = eval(effect, &mut ctx)?;
        if result.as_bool() == Some(true) {
            Ok(Some(State::with_fingerprint_and_hashes(
                std::mem::take(next_vars_buf),
                fp,
                var_hashes_buf,
            )))
        } else {
            Ok(None)
        }
    } else {
        Ok(Some(State::with_fingerprint_and_hashes(
            std::mem::take(next_vars_buf),
            fp,
            var_hashes_buf,
        )))
    }
}

/// Apply an action to a state using precomputed effect assignments.
/// Uses `next_vars_buf` as a reusable buffer to avoid repeated allocation.
/// Uses cached var_hashes from the parent state to avoid rehashing old values.
pub fn apply_action_direct_cached(
    state: &State,
    action: &CompiledAction,
    params: &[Value],
    consts: &[Value],
    assignments: &[(usize, CompiledExpr)],
    needs_reverify: bool,
    next_vars_buf: &mut Vec<Value>,
    var_hashes_buf: &mut Vec<u64>,
) -> Result<Option<State>, EvalError> {
    let mut ctx = EvalContext::new(&state.vars, &state.vars, consts, params);
    if !eval_bool(&action.guard, &mut ctx)? {
        return Ok(None);
    }

    next_vars_buf.clear();
    next_vars_buf.extend_from_slice(&state.vars);
    var_hashes_buf.clear();
    var_hashes_buf.extend_from_slice(&state.var_hashes);
    let mut fp = state.fingerprint().as_u64();

    for (var_idx, expr) in assignments {
        let mut ctx = EvalContext::new(&state.vars, next_vars_buf, consts, params);
        let value = eval(expr, &mut ctx)?;
        let old_hash = var_hashes_buf[*var_idx];
        let new_hash = hash_var(*var_idx, &value);
        fp ^= old_hash ^ new_hash;
        var_hashes_buf[*var_idx] = new_hash;
        next_vars_buf[*var_idx] = value;
    }

    let fp = crate::state::Fingerprint::from_u64(fp);
    if needs_reverify {
        let mut ctx = EvalContext::new(&state.vars, next_vars_buf, consts, params);
        let result = eval(&action.effect, &mut ctx)?;
        if result.as_bool() == Some(true) {
            Ok(Some(State::with_fingerprint_and_hashes(
                std::mem::take(next_vars_buf),
                fp,
                var_hashes_buf,
            )))
        } else {
            Ok(None)
        }
    } else {
        Ok(Some(State::with_fingerprint_and_hashes(
            std::mem::take(next_vars_buf),
            fp,
            var_hashes_buf,
        )))
    }
}

/// Apply an action to a state and compute successor states directly.
pub fn apply_action_direct(
    state: &State,
    action: &CompiledAction,
    params: &[Value],
    consts: &[Value],
    _num_vars: usize,
    next_vars_buf: &mut Vec<Value>,
    var_hashes_buf: &mut Vec<u64>,
) -> Result<Option<State>, EvalError> {
    // Try to extract direct assignments from effect
    if let Some(extraction) = extract_effect_assignments(&action.effect) {
        apply_action_direct_cached(
            state,
            action,
            params,
            consts,
            &extraction.assignments,
            extraction.needs_reverify,
            next_vars_buf,
            var_hashes_buf,
        )
    } else {
        Err(EvalError::Internal(
            "effect requires enumeration".to_string(),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extract_simple_assignment() {
        // x == 0
        let expr = CompiledExpr::Binary {
            op: BinOp::Eq,
            left: Box::new(CompiledExpr::Var(0)),
            right: Box::new(CompiledExpr::Int(0)),
        };

        let mut assignments = vec![None; 1];
        let result = extract_from_expr(&expr, &[], &mut assignments, &mut Vec::new());

        assert!(result);
        assert_eq!(assignments[0], Some(Value::int(0)));
    }

    #[test]
    fn test_extract_conjunction() {
        // x == 0 and y == 1
        let expr = CompiledExpr::Binary {
            op: BinOp::And,
            left: Box::new(CompiledExpr::Binary {
                op: BinOp::Eq,
                left: Box::new(CompiledExpr::Var(0)),
                right: Box::new(CompiledExpr::Int(0)),
            }),
            right: Box::new(CompiledExpr::Binary {
                op: BinOp::Eq,
                left: Box::new(CompiledExpr::Var(1)),
                right: Box::new(CompiledExpr::Int(1)),
            }),
        };

        let mut assignments = vec![None; 2];
        let result = extract_from_expr(&expr, &[], &mut assignments, &mut Vec::new());

        assert!(result);
        assert_eq!(assignments[0], Some(Value::int(0)));
        assert_eq!(assignments[1], Some(Value::int(1)));
    }
}

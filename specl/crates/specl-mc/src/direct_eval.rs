//! Direct evaluation for initial states and successors.
//!
//! This module provides efficient state generation by directly evaluating
//! expressions rather than enumerating all type-valid values and filtering.
//!
//! Key insight: Most init/effect expressions are conjunctions of equalities
//! like `x == 0 and y == fn(i in S) => 0`. We can extract these assignments
//! and evaluate them directly.

use specl_eval::bytecode::{vm_eval_reuse, Bytecode, VmBufs};
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
///
/// Uses a multi-pass approach to handle inter-variable dependencies regardless
/// of conjunction order: `y == x and x == 0` works the same as `x == 0 and y == x`.
pub fn extract_init_assignments(
    init: &CompiledExpr,
    consts: &[Value],
    num_vars: usize,
) -> AssignmentResult {
    // Flatten the And-tree into leaf conjuncts.
    let mut conjuncts = Vec::new();
    if !flatten_init_conjuncts(init, &mut conjuncts) {
        return AssignmentResult::NeedsEnumeration;
    }

    let mut assignments: Vec<Option<Value>> = vec![None; num_vars];
    let mut resolved = vec![false; conjuncts.len()];

    // Fixpoint loop: keep resolving until no more progress.
    loop {
        let mut progress = false;
        for (i, conjunct) in conjuncts.iter().enumerate() {
            if resolved[i] {
                continue;
            }
            let mut locals = Vec::new();
            match try_resolve_conjunct(conjunct, consts, &mut assignments, &mut locals) {
                ResolveResult::Resolved => {
                    resolved[i] = true;
                    progress = true;
                }
                ResolveResult::Deferred => {}
                ResolveResult::Failed => return AssignmentResult::NeedsEnumeration,
            }
        }
        if !progress {
            break;
        }
    }

    // Check that all conjuncts were resolved and all variables assigned.
    if resolved.iter().any(|r| !*r) {
        return AssignmentResult::NeedsEnumeration;
    }

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

/// Result of trying to resolve a single init conjunct.
enum ResolveResult {
    /// Conjunct resolved (assignment extracted or constraint verified).
    Resolved,
    /// Conjunct can't be resolved yet (dependencies not assigned).
    Deferred,
    /// Conjunct is unsatisfiable or unanalyzable.
    Failed,
}

/// Flatten an init expression's And-tree into leaf conjuncts.
/// Returns false if any leaf is unanalyzable (not Bool, Eq, or Let).
fn flatten_init_conjuncts<'a>(expr: &'a CompiledExpr, out: &mut Vec<&'a CompiledExpr>) -> bool {
    match expr {
        CompiledExpr::Bool(true) => true,
        CompiledExpr::Bool(false) => false,
        CompiledExpr::Binary {
            op: BinOp::And,
            left,
            right,
        } => flatten_init_conjuncts(left, out) && flatten_init_conjuncts(right, out),
        CompiledExpr::Binary { op: BinOp::Eq, .. } | CompiledExpr::Let { .. } => {
            out.push(expr);
            true
        }
        _ => false,
    }
}

/// Try to resolve a single init conjunct given current partial assignments.
fn try_resolve_conjunct(
    expr: &CompiledExpr,
    consts: &[Value],
    assignments: &mut [Option<Value>],
    locals: &mut Vec<Value>,
) -> ResolveResult {
    match expr {
        CompiledExpr::Bool(true) => ResolveResult::Resolved,
        CompiledExpr::Bool(false) => ResolveResult::Failed,

        // Conjunction within a Let body: resolve both sides.
        CompiledExpr::Binary {
            op: BinOp::And,
            left,
            right,
        } => {
            let l = try_resolve_conjunct(left, consts, assignments, locals);
            let r = try_resolve_conjunct(right, consts, assignments, locals);
            match (l, r) {
                (ResolveResult::Failed, _) | (_, ResolveResult::Failed) => ResolveResult::Failed,
                (ResolveResult::Deferred, _) | (_, ResolveResult::Deferred) => {
                    ResolveResult::Deferred
                }
                (ResolveResult::Resolved, ResolveResult::Resolved) => ResolveResult::Resolved,
            }
        }

        CompiledExpr::Let { value, body } => {
            if let Some(val) = try_eval_value(value, consts, assignments, locals) {
                locals.push(val);
                let result = try_resolve_conjunct(body, consts, assignments, locals);
                locals.pop();
                result
            } else {
                ResolveResult::Deferred
            }
        }

        CompiledExpr::Binary {
            op: BinOp::Eq,
            left,
            right,
        } => try_resolve_eq(left, right, consts, assignments, locals),

        _ => ResolveResult::Failed,
    }
}

/// Try to resolve a single equality `left == right` as a variable assignment.
fn try_resolve_eq(
    left: &CompiledExpr,
    right: &CompiledExpr,
    consts: &[Value],
    assignments: &mut [Option<Value>],
    locals: &[Value],
) -> ResolveResult {
    // Try left == right (var on left)
    let left_idx = match left {
        CompiledExpr::Var(idx) | CompiledExpr::PrimedVar(idx) => Some(*idx),
        _ => None,
    };
    if let Some(idx) = left_idx {
        if let Some(value) = try_eval_value(right, consts, assignments, locals) {
            if assignments[idx].is_none() {
                assignments[idx] = Some(value);
                return ResolveResult::Resolved;
            } else {
                return if assignments[idx].as_ref() == Some(&value) {
                    ResolveResult::Resolved
                } else {
                    ResolveResult::Failed
                };
            }
        }
    }
    // Try right == left (var on right)
    let right_idx = match right {
        CompiledExpr::Var(idx) | CompiledExpr::PrimedVar(idx) => Some(*idx),
        _ => None,
    };
    if let Some(idx) = right_idx {
        if let Some(value) = try_eval_value(left, consts, assignments, locals) {
            if assignments[idx].is_none() {
                assignments[idx] = Some(value);
                return ResolveResult::Resolved;
            } else {
                return if assignments[idx].as_ref() == Some(&value) {
                    ResolveResult::Resolved
                } else {
                    ResolveResult::Failed
                };
            }
        }
    }
    // Can't resolve yet (dependencies not assigned)
    ResolveResult::Deferred
}

/// Try to evaluate an expression to a value using already-extracted assignments.
/// Uses partial assignments as variable context so that init expressions like
/// `sigs = {k: {} for k in certs}` can reference previously assigned `certs`.
/// Returns None if the expression references any unassigned variable.
fn try_eval_value(
    expr: &CompiledExpr,
    consts: &[Value],
    partial_assignments: &[Option<Value>],
    locals: &[Value],
) -> Option<Value> {
    if refs_unassigned_var(expr, partial_assignments) {
        return None;
    }
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

/// Check if an expression references any variable that is not yet assigned.
fn refs_unassigned_var(expr: &CompiledExpr, partial_assignments: &[Option<Value>]) -> bool {
    match expr {
        CompiledExpr::Var(idx) | CompiledExpr::PrimedVar(idx) => {
            partial_assignments.get(*idx).is_none_or(|a| a.is_none())
        }
        _ => {
            let mut found = false;
            expr.for_each_child(|child| {
                if !found && refs_unassigned_var(child, partial_assignments) {
                    found = true;
                }
            });
            found
        }
    }
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

/// Populate next_vars_buf and var_hashes_buf from a parent state.
/// When the buffer already has the right length (common case: previous call
/// didn't construct a State via take_computed_state), overwrite in a single
/// pass instead of two passes (clear + extend_from_slice).
#[inline]
fn populate_buf_from_state(
    state: &State,
    next_vars_buf: &mut Vec<Value>,
    var_hashes_buf: &mut Vec<u64>,
) {
    let n = state.vars.len();
    if next_vars_buf.len() == n {
        // Single pass: drop old value and clone new value per element.
        for (dst, src) in next_vars_buf.iter_mut().zip(state.vars.iter()) {
            *dst = src.clone();
        }
    } else {
        next_vars_buf.clear();
        next_vars_buf.extend_from_slice(&state.vars);
    }
    if var_hashes_buf.len() == n {
        var_hashes_buf.copy_from_slice(&state.var_hashes);
    } else {
        var_hashes_buf.clear();
        var_hashes_buf.extend_from_slice(&state.var_hashes);
    }
}

/// Compute effects and return the successor fingerprint without constructing a State.
/// Returns Ok(Some(fp)) if the effect succeeded, Ok(None) if guard reverification failed.
/// The computed vars remain in next_vars_buf and hashes in var_hashes_buf.
/// Call `take_computed_state` to construct the State from the buffers.
#[allow(clippy::too_many_arguments)]
pub fn compute_effects_bytecode_reuse(
    state: &State,
    params: &[Value],
    consts: &[Value],
    compiled_assignments: &[(usize, Bytecode)],
    needs_reverify: bool,
    next_vars_buf: &mut Vec<Value>,
    effect: &CompiledExpr,
    vm_bufs: &mut VmBufs,
    var_hashes_buf: &mut Vec<u64>,
    view_mask: Option<&[bool]>,
) -> Result<Option<crate::state::Fingerprint>, EvalError> {
    // Populate buffers from parent state. When the buffer already has the right
    // length (common case: previous call didn't construct a State), overwrite in
    // a single pass instead of two passes (clear + extend_from_slice). This halves
    // the iteration count and improves cache locality.
    populate_buf_from_state(state, next_vars_buf, var_hashes_buf);
    let mut fp = state.fingerprint().as_u64();

    for (var_idx, bc) in compiled_assignments {
        let value = vm_eval_reuse(bc, &state.vars, next_vars_buf, consts, params, vm_bufs)?;
        let old_hash = var_hashes_buf[*var_idx];
        let new_hash = hash_var(*var_idx, &value);
        if view_mask.is_none_or(|m| m[*var_idx]) {
            fp ^= old_hash ^ new_hash;
        }
        var_hashes_buf[*var_idx] = new_hash;
        next_vars_buf[*var_idx] = value;
    }

    let fp = crate::state::Fingerprint::from_u64(fp);
    if needs_reverify {
        let mut ctx = EvalContext::new(&state.vars, next_vars_buf, consts, params);
        let result = eval(effect, &mut ctx)?;
        if result.as_bool() == Some(true) {
            Ok(Some(fp))
        } else {
            Ok(None)
        }
    } else {
        Ok(Some(fp))
    }
}

/// Construct a State from pre-computed effect buffers.
/// Must be called after `compute_effects_bytecode_reuse` returned Some.
#[inline]
pub fn take_computed_state(
    next_vars_buf: &mut Vec<Value>,
    fp: crate::state::Fingerprint,
    var_hashes_buf: &[u64],
) -> State {
    State::with_fingerprint_and_hashes(std::mem::take(next_vars_buf), fp, var_hashes_buf)
}

/// Apply an action to a state using precomputed effect assignments.
/// Uses `next_vars_buf` as a reusable buffer to avoid repeated allocation.
/// Uses cached var_hashes from the parent state to avoid rehashing old values.
#[allow(clippy::too_many_arguments)]
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

    populate_buf_from_state(state, next_vars_buf, var_hashes_buf);
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

        match extract_init_assignments(&expr, &[], 1) {
            AssignmentResult::Direct(assignments) => {
                assert_eq!(assignments, vec![(0, Value::int(0))]);
            }
            AssignmentResult::NeedsEnumeration => panic!("expected Direct"),
        }
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

        match extract_init_assignments(&expr, &[], 2) {
            AssignmentResult::Direct(assignments) => {
                assert_eq!(assignments, vec![(0, Value::int(0)), (1, Value::int(1))]);
            }
            AssignmentResult::NeedsEnumeration => panic!("expected Direct"),
        }
    }

    #[test]
    fn test_extract_conjunction_order_independent() {
        // y == x and x == 0  (dependency on x before x is assigned)
        let expr = CompiledExpr::Binary {
            op: BinOp::And,
            left: Box::new(CompiledExpr::Binary {
                op: BinOp::Eq,
                left: Box::new(CompiledExpr::Var(1)),
                right: Box::new(CompiledExpr::Var(0)),
            }),
            right: Box::new(CompiledExpr::Binary {
                op: BinOp::Eq,
                left: Box::new(CompiledExpr::Var(0)),
                right: Box::new(CompiledExpr::Int(0)),
            }),
        };

        match extract_init_assignments(&expr, &[], 2) {
            AssignmentResult::Direct(assignments) => {
                assert_eq!(assignments, vec![(0, Value::int(0)), (1, Value::int(0))]);
            }
            AssignmentResult::NeedsEnumeration => panic!("expected Direct"),
        }
    }
}

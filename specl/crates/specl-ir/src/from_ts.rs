//! Lower a generic `TransitionSystem` into `CompiledSpec`.
//!
//! This module converts the language-agnostic transition system IR
//! (from `specl_ts`) into the internal `CompiledSpec` representation
//! consumed by the model checker. The lowering is mechanical: types,
//! expressions, and actions are mapped 1:1, with the addition of
//! Specl-specific concepts (PrimedVar, Unchanged, implicit frame).

use crate::ir::{
    BinOp, CompiledAction, CompiledExpr, CompiledInvariant, CompiledSpec, ConstDecl, KeySource,
    SymmetryGroup, UnaryOp, VarDecl,
};
use specl_ts::{TransitionSystem, TsAction, TsBinOp, TsExpr, TsType, TsUnaryOp};
use specl_types::{RecordType, Type};
use std::collections::{HashMap, HashSet};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum LowerError {
    #[error("variable index {0} out of bounds (have {1} variables)")]
    VarIndexOutOfBounds(usize, usize),

    #[error("constant index {0} out of bounds (have {1} constants)")]
    ConstIndexOutOfBounds(usize, usize),

    #[error("init must assign every variable exactly once: missing {missing:?}, duplicated {duplicated:?}")]
    InitAssignmentError {
        missing: Vec<String>,
        duplicated: Vec<String>,
    },

    #[error("action '{action}': variable index {var_idx} assigned multiple times")]
    DuplicateAssignment { action: String, var_idx: usize },

    #[error(
        "action '{action}': assignment references variable index {var_idx} which is out of bounds"
    )]
    ActionVarOutOfBounds { action: String, var_idx: usize },
}

/// Lower a `TransitionSystem` to a `CompiledSpec`.
pub fn lower(ts: &TransitionSystem) -> Result<CompiledSpec, LowerError> {
    validate(ts)?;

    let num_vars = ts.variables.len();

    // Variables
    let vars: Vec<VarDecl> = ts
        .variables
        .iter()
        .enumerate()
        .map(|(i, v)| VarDecl {
            name: v.name.clone(),
            index: i,
            ty: lower_type(&v.ty),
        })
        .collect();

    // Constants
    let consts: Vec<ConstDecl> = ts
        .constants
        .iter()
        .enumerate()
        .map(|(i, c)| ConstDecl {
            name: c.name.clone(),
            index: i,
            ty: lower_type(&c.ty),
            default_value: c.default_value,
        })
        .collect();

    // Init: conjunction of PrimedVar(idx) == value for each assignment.
    // This format is recognized by direct_eval::extract_init_assignments (fast path).
    let init = {
        let mut expr = CompiledExpr::Bool(true);
        for assignment in &ts.init {
            let eq = CompiledExpr::Binary {
                op: BinOp::Eq,
                left: Box::new(CompiledExpr::PrimedVar(assignment.var_idx)),
                right: Box::new(lower_expr(&assignment.value)),
            };
            expr = CompiledExpr::Binary {
                op: BinOp::And,
                left: Box::new(expr),
                right: Box::new(eq),
            };
        }
        expr
    };

    // Actions
    let actions: Vec<CompiledAction> = ts
        .actions
        .iter()
        .map(|a| lower_action(a, num_vars))
        .collect();

    // Invariants
    let invariants: Vec<CompiledInvariant> = ts
        .invariants
        .iter()
        .map(|inv| CompiledInvariant {
            name: inv.name.clone(),
            body: lower_expr(&inv.body),
        })
        .collect();

    let auxiliary_invariants: Vec<CompiledInvariant> = ts
        .auxiliary_invariants
        .iter()
        .map(|inv| CompiledInvariant {
            name: inv.name.clone(),
            body: lower_expr(&inv.body),
        })
        .collect();

    // POR independence matrix
    let n = actions.len();
    let independent = compute_independence_matrix(&actions, n);

    // Symmetry groups
    let symmetry_groups = detect_symmetry_groups(&vars);

    // Refinable pairs
    let refinable_pairs = compute_refinable_pairs(&actions, &independent, n);

    Ok(CompiledSpec {
        vars,
        consts,
        init,
        actions,
        invariants,
        auxiliary_invariants,
        independent,
        refinable_pairs,
        symmetry_groups,
        view_variables: ts.view_variables.clone(),
    })
}

fn validate(ts: &TransitionSystem) -> Result<(), LowerError> {
    let num_vars = ts.variables.len();
    let num_consts = ts.constants.len();

    // Validate init assignments: every variable exactly once
    let mut assigned = HashSet::new();
    let mut duplicated = Vec::new();
    for a in &ts.init {
        if a.var_idx >= num_vars {
            return Err(LowerError::VarIndexOutOfBounds(a.var_idx, num_vars));
        }
        if !assigned.insert(a.var_idx) {
            duplicated.push(ts.variables[a.var_idx].name.clone());
        }
    }
    let missing: Vec<String> = (0..num_vars)
        .filter(|i| !assigned.contains(i))
        .map(|i| ts.variables[i].name.clone())
        .collect();
    if !missing.is_empty() || !duplicated.is_empty() {
        return Err(LowerError::InitAssignmentError {
            missing,
            duplicated,
        });
    }

    // Validate actions
    for action in &ts.actions {
        let mut seen = HashSet::new();
        for a in &action.assignments {
            if a.var_idx >= num_vars {
                return Err(LowerError::ActionVarOutOfBounds {
                    action: action.name.clone(),
                    var_idx: a.var_idx,
                });
            }
            if !seen.insert(a.var_idx) {
                return Err(LowerError::DuplicateAssignment {
                    action: action.name.clone(),
                    var_idx: a.var_idx,
                });
            }
        }
    }

    // Validate expression indices
    validate_exprs(ts, num_vars, num_consts)?;

    Ok(())
}

fn validate_exprs(
    ts: &TransitionSystem,
    num_vars: usize,
    num_consts: usize,
) -> Result<(), LowerError> {
    let check = |expr: &TsExpr| -> Result<(), LowerError> {
        validate_expr_indices(expr, num_vars, num_consts)
    };
    for a in &ts.init {
        check(&a.value)?;
    }
    for action in &ts.actions {
        check(&action.guard)?;
        for a in &action.assignments {
            check(&a.value)?;
        }
    }
    for inv in &ts.invariants {
        check(&inv.body)?;
    }
    for inv in &ts.auxiliary_invariants {
        check(&inv.body)?;
    }
    Ok(())
}

fn validate_expr_indices(
    expr: &TsExpr,
    num_vars: usize,
    num_consts: usize,
) -> Result<(), LowerError> {
    match expr {
        TsExpr::Var { index } => {
            if *index >= num_vars {
                return Err(LowerError::VarIndexOutOfBounds(*index, num_vars));
            }
        }
        TsExpr::Const { index } => {
            if *index >= num_consts {
                return Err(LowerError::ConstIndexOutOfBounds(*index, num_consts));
            }
        }
        TsExpr::Binary { left, right, .. } => {
            validate_expr_indices(left, num_vars, num_consts)?;
            validate_expr_indices(right, num_vars, num_consts)?;
        }
        TsExpr::Unary { operand, .. } => {
            validate_expr_indices(operand, num_vars, num_consts)?;
        }
        TsExpr::SetLit { elements }
        | TsExpr::SeqLit { elements }
        | TsExpr::TupleLit { elements } => {
            for e in elements {
                validate_expr_indices(e, num_vars, num_consts)?;
            }
        }
        TsExpr::DictLit { entries } => {
            for (k, v) in entries {
                validate_expr_indices(k, num_vars, num_consts)?;
                validate_expr_indices(v, num_vars, num_consts)?;
            }
        }
        TsExpr::FnLit { domain, body }
        | TsExpr::Forall { domain, body }
        | TsExpr::Exists { domain, body } => {
            validate_expr_indices(domain, num_vars, num_consts)?;
            validate_expr_indices(body, num_vars, num_consts)?;
        }
        TsExpr::MapUpdate { base, key, value } => {
            validate_expr_indices(base, num_vars, num_consts)?;
            validate_expr_indices(key, num_vars, num_consts)?;
            validate_expr_indices(value, num_vars, num_consts)?;
        }
        TsExpr::Index { base, index } => {
            validate_expr_indices(base, num_vars, num_consts)?;
            validate_expr_indices(index, num_vars, num_consts)?;
        }
        TsExpr::Slice { base, lo, hi } => {
            validate_expr_indices(base, num_vars, num_consts)?;
            validate_expr_indices(lo, num_vars, num_consts)?;
            validate_expr_indices(hi, num_vars, num_consts)?;
        }
        TsExpr::Field { base, .. } => {
            validate_expr_indices(base, num_vars, num_consts)?;
        }
        TsExpr::Len { expr }
        | TsExpr::Keys { expr }
        | TsExpr::Values { expr }
        | TsExpr::SeqHead { expr }
        | TsExpr::SeqTail { expr } => {
            validate_expr_indices(expr, num_vars, num_consts)?;
        }
        TsExpr::SetComprehension {
            element,
            domain,
            filter,
        } => {
            validate_expr_indices(element, num_vars, num_consts)?;
            validate_expr_indices(domain, num_vars, num_consts)?;
            if let Some(f) = filter {
                validate_expr_indices(f, num_vars, num_consts)?;
            }
        }
        TsExpr::Let { value, body } => {
            validate_expr_indices(value, num_vars, num_consts)?;
            validate_expr_indices(body, num_vars, num_consts)?;
        }
        TsExpr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            validate_expr_indices(cond, num_vars, num_consts)?;
            validate_expr_indices(then_branch, num_vars, num_consts)?;
            validate_expr_indices(else_branch, num_vars, num_consts)?;
        }
        TsExpr::Range { lo, hi } => {
            validate_expr_indices(lo, num_vars, num_consts)?;
            validate_expr_indices(hi, num_vars, num_consts)?;
        }
        TsExpr::RecordUpdate { base, updates } => {
            validate_expr_indices(base, num_vars, num_consts)?;
            for (_, v) in updates {
                validate_expr_indices(v, num_vars, num_consts)?;
            }
        }
        // Leaves with no sub-expressions or no indices to validate
        TsExpr::Bool { .. }
        | TsExpr::Int { .. }
        | TsExpr::Str { .. }
        | TsExpr::Local { .. }
        | TsExpr::Param { .. } => {}
    }
    Ok(())
}

// --- Lowering ---

fn lower_action(action: &TsAction, num_vars: usize) -> CompiledAction {
    let guard = lower_expr(&action.guard);

    // Collect changed variable indices
    let mut changes: Vec<usize> = action.assignments.iter().map(|a| a.var_idx).collect();
    changes.sort();
    changes.dedup();

    // Build effect: conjunction of (PrimedVar(idx) == value) for each assignment
    let mut effect = CompiledExpr::Bool(true);
    for assignment in &action.assignments {
        let eq = CompiledExpr::Binary {
            op: BinOp::Eq,
            left: Box::new(CompiledExpr::PrimedVar(assignment.var_idx)),
            right: Box::new(lower_expr(&assignment.value)),
        };
        effect = CompiledExpr::Binary {
            op: BinOp::And,
            left: Box::new(effect),
            right: Box::new(eq),
        };
    }

    // Add implicit frame: Unchanged for all vars NOT assigned
    for var_idx in 0..num_vars {
        if !changes.contains(&var_idx) {
            effect = CompiledExpr::Binary {
                op: BinOp::And,
                left: Box::new(effect),
                right: Box::new(CompiledExpr::Unchanged(var_idx)),
            };
        }
    }

    // Collect reads from guard and assignment values
    let mut reads = collect_reads(&guard);
    for assignment in &action.assignments {
        let lowered = lower_expr(&assignment.value);
        reads.extend(collect_reads(&lowered));
    }
    reads.sort();
    reads.dedup();

    // Key params for instance-level POR (operate on TsExpr before lowering)
    let write_key_params = collect_write_key_params(&action.assignments, &changes);
    let read_key_params = collect_read_key_params(&action.guard, &action.assignments, &reads);

    // Parameters
    let params: Vec<(String, Type)> = action
        .params
        .iter()
        .map(|p| (p.name.clone(), lower_type(&p.ty)))
        .collect();

    let guard_cost = expr_cost(&guard);

    CompiledAction {
        name: action.name.clone(),
        params,
        param_type_exprs: Vec::new(), // empty: explorer falls back to type_domain(ty)
        guard,
        effect,
        changes,
        reads,
        write_key_params,
        read_key_params,
        guard_cost,
    }
}

fn lower_expr(expr: &TsExpr) -> CompiledExpr {
    match expr {
        TsExpr::Bool { value } => CompiledExpr::Bool(*value),
        TsExpr::Int { value } => CompiledExpr::Int(*value),
        TsExpr::Str { value } => CompiledExpr::String(value.clone()),
        TsExpr::Var { index } => CompiledExpr::Var(*index),
        TsExpr::Const { index } => CompiledExpr::Const(*index),
        TsExpr::Local { index } => CompiledExpr::Local(*index),
        TsExpr::Param { index } => CompiledExpr::Param(*index),
        TsExpr::Binary { op, left, right } => CompiledExpr::Binary {
            op: lower_binop(*op),
            left: Box::new(lower_expr(left)),
            right: Box::new(lower_expr(right)),
        },
        TsExpr::Unary { op, operand } => CompiledExpr::Unary {
            op: lower_unaryop(*op),
            operand: Box::new(lower_expr(operand)),
        },
        TsExpr::SetLit { elements } => {
            CompiledExpr::SetLit(elements.iter().map(lower_expr).collect())
        }
        TsExpr::SeqLit { elements } => {
            CompiledExpr::SeqLit(elements.iter().map(lower_expr).collect())
        }
        TsExpr::TupleLit { elements } => {
            CompiledExpr::TupleLit(elements.iter().map(lower_expr).collect())
        }
        TsExpr::DictLit { entries } => CompiledExpr::DictLit(
            entries
                .iter()
                .map(|(k, v)| (lower_expr(k), lower_expr(v)))
                .collect(),
        ),
        TsExpr::FnLit { domain, body } => CompiledExpr::FnLit {
            domain: Box::new(lower_expr(domain)),
            body: Box::new(lower_expr(body)),
        },
        TsExpr::MapUpdate { base, key, value } => CompiledExpr::FnUpdate {
            base: Box::new(lower_expr(base)),
            key: Box::new(lower_expr(key)),
            value: Box::new(lower_expr(value)),
        },
        TsExpr::Index { base, index } => CompiledExpr::Index {
            base: Box::new(lower_expr(base)),
            index: Box::new(lower_expr(index)),
        },
        TsExpr::Slice { base, lo, hi } => CompiledExpr::Slice {
            base: Box::new(lower_expr(base)),
            lo: Box::new(lower_expr(lo)),
            hi: Box::new(lower_expr(hi)),
        },
        TsExpr::Field { base, field } => CompiledExpr::Field {
            base: Box::new(lower_expr(base)),
            field: field.clone(),
        },
        TsExpr::Len { expr } => CompiledExpr::Len(Box::new(lower_expr(expr))),
        TsExpr::Keys { expr } => CompiledExpr::Keys(Box::new(lower_expr(expr))),
        TsExpr::Values { expr } => CompiledExpr::Values(Box::new(lower_expr(expr))),
        TsExpr::SeqHead { expr } => CompiledExpr::SeqHead(Box::new(lower_expr(expr))),
        TsExpr::SeqTail { expr } => CompiledExpr::SeqTail(Box::new(lower_expr(expr))),
        TsExpr::SetComprehension {
            element,
            domain,
            filter,
        } => CompiledExpr::SetComprehension {
            element: Box::new(lower_expr(element)),
            domain: Box::new(lower_expr(domain)),
            filter: filter.as_ref().map(|f| Box::new(lower_expr(f))),
        },
        TsExpr::Forall { domain, body } => CompiledExpr::Forall {
            domain: Box::new(lower_expr(domain)),
            body: Box::new(lower_expr(body)),
        },
        TsExpr::Exists { domain, body } => CompiledExpr::Exists {
            domain: Box::new(lower_expr(domain)),
            body: Box::new(lower_expr(body)),
        },
        TsExpr::Let { value, body } => CompiledExpr::Let {
            value: Box::new(lower_expr(value)),
            body: Box::new(lower_expr(body)),
        },
        TsExpr::If {
            cond,
            then_branch,
            else_branch,
        } => CompiledExpr::If {
            cond: Box::new(lower_expr(cond)),
            then_branch: Box::new(lower_expr(then_branch)),
            else_branch: Box::new(lower_expr(else_branch)),
        },
        TsExpr::Range { lo, hi } => CompiledExpr::Range {
            lo: Box::new(lower_expr(lo)),
            hi: Box::new(lower_expr(hi)),
        },
        TsExpr::RecordUpdate { base, updates } => CompiledExpr::RecordUpdate {
            base: Box::new(lower_expr(base)),
            updates: updates
                .iter()
                .map(|(k, v)| (k.clone(), lower_expr(v)))
                .collect(),
        },
    }
}

pub fn lower_type(ty: &TsType) -> Type {
    match ty {
        TsType::Bool => Type::Bool,
        TsType::Nat => Type::Nat,
        TsType::Int => Type::Int,
        TsType::String => Type::String,
        TsType::Range { lo, hi } => Type::Range(*lo, *hi),
        TsType::Set { element } => Type::Set(Box::new(lower_type(element))),
        TsType::Seq { element } => Type::Seq(Box::new(lower_type(element))),
        TsType::Map { key, value } => {
            Type::Fn(Box::new(lower_type(key)), Box::new(lower_type(value)))
        }
        TsType::Record { fields } => Type::Record(RecordType::from_fields(
            fields.iter().map(|(k, v)| (k.clone(), lower_type(v))),
        )),
        TsType::Tuple { elements } => Type::Tuple(elements.iter().map(lower_type).collect()),
        TsType::Option { inner } => Type::Option(Box::new(lower_type(inner))),
    }
}

fn lower_binop(op: TsBinOp) -> BinOp {
    match op {
        TsBinOp::And => BinOp::And,
        TsBinOp::Or => BinOp::Or,
        TsBinOp::Implies => BinOp::Implies,
        TsBinOp::Iff => BinOp::Iff,
        TsBinOp::Eq => BinOp::Eq,
        TsBinOp::Ne => BinOp::Ne,
        TsBinOp::Lt => BinOp::Lt,
        TsBinOp::Le => BinOp::Le,
        TsBinOp::Gt => BinOp::Gt,
        TsBinOp::Ge => BinOp::Ge,
        TsBinOp::Add => BinOp::Add,
        TsBinOp::Sub => BinOp::Sub,
        TsBinOp::Mul => BinOp::Mul,
        TsBinOp::Div => BinOp::Div,
        TsBinOp::Mod => BinOp::Mod,
        TsBinOp::In => BinOp::In,
        TsBinOp::NotIn => BinOp::NotIn,
        TsBinOp::Union => BinOp::Union,
        TsBinOp::Intersect => BinOp::Intersect,
        TsBinOp::Diff => BinOp::Diff,
        TsBinOp::SubsetOf => BinOp::SubsetOf,
        TsBinOp::Concat => BinOp::Concat,
    }
}

fn lower_unaryop(op: TsUnaryOp) -> UnaryOp {
    match op {
        TsUnaryOp::Not => UnaryOp::Not,
        TsUnaryOp::Neg => UnaryOp::Neg,
    }
}

// --- Analysis helpers (replicated from compile.rs) ---

fn collect_reads(expr: &CompiledExpr) -> Vec<usize> {
    let mut reads = Vec::new();
    collect_reads_impl(expr, &mut reads);
    reads.sort();
    reads.dedup();
    reads
}

fn collect_reads_impl(expr: &CompiledExpr, reads: &mut Vec<usize>) {
    match expr {
        CompiledExpr::Var(idx) => reads.push(*idx),
        CompiledExpr::Binary { left, right, .. } => {
            collect_reads_impl(left, reads);
            collect_reads_impl(right, reads);
        }
        CompiledExpr::Unary { operand, .. } => collect_reads_impl(operand, reads),
        CompiledExpr::SetLit(elems)
        | CompiledExpr::SeqLit(elems)
        | CompiledExpr::TupleLit(elems) => {
            for e in elems {
                collect_reads_impl(e, reads);
            }
        }
        CompiledExpr::DictLit(entries) => {
            for (k, v) in entries {
                collect_reads_impl(k, reads);
                collect_reads_impl(v, reads);
            }
        }
        CompiledExpr::Index { base, index } => {
            collect_reads_impl(base, reads);
            collect_reads_impl(index, reads);
        }
        CompiledExpr::Slice { base, lo, hi } => {
            collect_reads_impl(base, reads);
            collect_reads_impl(lo, reads);
            collect_reads_impl(hi, reads);
        }
        CompiledExpr::Field { base, .. } => collect_reads_impl(base, reads),
        CompiledExpr::Forall { domain, body }
        | CompiledExpr::Exists { domain, body }
        | CompiledExpr::FnLit { domain, body } => {
            collect_reads_impl(domain, reads);
            collect_reads_impl(body, reads);
        }
        CompiledExpr::SetComprehension {
            element,
            domain,
            filter,
        } => {
            collect_reads_impl(element, reads);
            collect_reads_impl(domain, reads);
            if let Some(f) = filter {
                collect_reads_impl(f, reads);
            }
        }
        CompiledExpr::FnUpdate { base, key, value } => {
            collect_reads_impl(base, reads);
            collect_reads_impl(key, reads);
            collect_reads_impl(value, reads);
        }
        CompiledExpr::RecordUpdate { base, updates } => {
            collect_reads_impl(base, reads);
            for (_, v) in updates {
                collect_reads_impl(v, reads);
            }
        }
        CompiledExpr::Let { value, body } => {
            collect_reads_impl(value, reads);
            collect_reads_impl(body, reads);
        }
        CompiledExpr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            collect_reads_impl(cond, reads);
            collect_reads_impl(then_branch, reads);
            collect_reads_impl(else_branch, reads);
        }
        CompiledExpr::Range { lo, hi } => {
            collect_reads_impl(lo, reads);
            collect_reads_impl(hi, reads);
        }
        CompiledExpr::SeqHead(inner)
        | CompiledExpr::SeqTail(inner)
        | CompiledExpr::Len(inner)
        | CompiledExpr::Keys(inner)
        | CompiledExpr::Values(inner) => {
            collect_reads_impl(inner, reads);
        }
        _ => {}
    }
}

fn compute_independence_matrix(actions: &[CompiledAction], n: usize) -> Vec<Vec<bool>> {
    let mut independent = vec![vec![false; n]; n];
    for i in 0..n {
        for j in 0..n {
            if i != j {
                let writes_a = &actions[i].changes;
                let reads_a = &actions[i].reads;
                let writes_b = &actions[j].changes;
                let reads_b = &actions[j].reads;

                let a_interferes_b = writes_a
                    .iter()
                    .any(|w| reads_b.contains(w) || writes_b.contains(w));
                let b_interferes_a = writes_b
                    .iter()
                    .any(|w| reads_a.contains(w) || writes_a.contains(w));

                independent[i][j] = !a_interferes_b && !b_interferes_a;
            }
        }
    }
    independent
}

fn detect_symmetry_groups(vars: &[VarDecl]) -> Vec<SymmetryGroup> {
    let mut groups: HashMap<usize, Vec<usize>> = HashMap::new();

    for var in vars {
        if let Type::Fn(key_ty, _) = &var.ty {
            if let Type::Range(0, hi) = key_ty.as_ref() {
                let domain_size = (*hi + 1) as usize;
                groups.entry(domain_size).or_default().push(var.index);
            }
        }
    }

    groups
        .into_iter()
        .filter(|(_, vars)| !vars.is_empty())
        .map(|(domain_size, variables)| SymmetryGroup {
            domain_size,
            variables,
        })
        .collect()
}

fn compute_refinable_pairs(
    actions: &[CompiledAction],
    independent: &[Vec<bool>],
    n: usize,
) -> Vec<Vec<bool>> {
    let mut rp = vec![vec![false; n]; n];
    for i in 0..n {
        for j in i..n {
            if !independent[i][j] {
                let refinable = check_refinable(&actions[i], &actions[j]);
                rp[i][j] = refinable;
                rp[j][i] = refinable;
            }
        }
    }
    rp
}

fn check_refinable(a: &CompiledAction, b: &CompiledAction) -> bool {
    fn find_key_info(
        key_params: &[(usize, Option<Vec<KeySource>>)],
        var_idx: usize,
    ) -> Option<&Option<Vec<KeySource>>> {
        key_params
            .iter()
            .find(|(v, _)| *v == var_idx)
            .map(|(_, k)| k)
    }

    for &var_idx in &a.changes {
        if b.reads.contains(&var_idx) || b.changes.contains(&var_idx) {
            match find_key_info(&a.write_key_params, var_idx) {
                Some(Some(_)) => {}
                _ => return false,
            }
            if b.changes.contains(&var_idx) {
                match find_key_info(&b.write_key_params, var_idx) {
                    Some(Some(_)) => {}
                    _ => return false,
                }
            }
            if b.reads.contains(&var_idx) {
                match find_key_info(&b.read_key_params, var_idx) {
                    Some(Some(_)) => {}
                    _ => return false,
                }
            }
        }
    }
    for &var_idx in &b.changes {
        if a.reads.contains(&var_idx) && !a.changes.contains(&var_idx) {
            match find_key_info(&b.write_key_params, var_idx) {
                Some(Some(_)) => {}
                _ => return false,
            }
            match find_key_info(&a.read_key_params, var_idx) {
                Some(Some(_)) => {}
                _ => return false,
            }
        }
    }
    true
}

/// Write key params: detect FnUpdate chains keyed by Param in assignments.
fn collect_write_key_params(
    assignments: &[specl_ts::TsAssignment],
    changes: &[usize],
) -> Vec<(usize, Option<Vec<KeySource>>)> {
    let mut result: Vec<(usize, Option<Vec<KeySource>>)> = Vec::new();

    for assignment in assignments {
        if !changes.contains(&assignment.var_idx) {
            continue;
        }
        let keys = extract_map_update_keys(&assignment.value, assignment.var_idx);
        result.push((assignment.var_idx, keys));
    }

    // Any variable in changes not found in assignments is unkeyed
    for &var_idx in changes {
        if !result.iter().any(|(v, _)| *v == var_idx) {
            result.push((var_idx, None));
        }
    }

    result.sort_by_key(|(v, _)| *v);
    result
}

/// Extract key sources from a TsExpr::MapUpdate chain.
fn extract_map_update_keys(expr: &TsExpr, target_var: usize) -> Option<Vec<KeySource>> {
    match expr {
        TsExpr::MapUpdate { base, key, .. } => {
            let mut keys = extract_map_update_keys(base, target_var)?;
            match key.as_ref() {
                TsExpr::Param { index } => keys.push(KeySource::Param(*index)),
                TsExpr::Int { value } => keys.push(KeySource::Literal(*value)),
                _ => return None,
            }
            Some(keys)
        }
        TsExpr::Var { index } if *index == target_var => Some(Vec::new()),
        _ => None,
    }
}

/// Read key params: detect Index(Var(idx), Param(p)) patterns.
fn collect_read_key_params(
    guard: &TsExpr,
    assignments: &[specl_ts::TsAssignment],
    reads: &[usize],
) -> Vec<(usize, Option<Vec<KeySource>>)> {
    let mut info: HashMap<usize, (Vec<KeySource>, bool)> = HashMap::new();
    for &var_idx in reads {
        info.insert(var_idx, (Vec::new(), false));
    }

    collect_ts_read_keys(guard, &mut info);
    for assignment in assignments {
        collect_ts_read_keys(&assignment.value, &mut info);
    }

    let mut pairs: Vec<_> = info
        .into_iter()
        .map(|(var_idx, (keys, has_unkeyed))| {
            if has_unkeyed || keys.is_empty() {
                (var_idx, None)
            } else {
                (var_idx, Some(keys))
            }
        })
        .collect();
    pairs.sort_by_key(|(v, _)| *v);
    pairs
}

fn collect_ts_read_keys(expr: &TsExpr, info: &mut HashMap<usize, (Vec<KeySource>, bool)>) {
    match expr {
        TsExpr::Index { base, index } => {
            if let TsExpr::Var { index: var_idx } = base.as_ref() {
                if let Some((keys, _)) = info.get_mut(var_idx) {
                    match index.as_ref() {
                        TsExpr::Param { index: p } => keys.push(KeySource::Param(*p)),
                        TsExpr::Int { value: k } => keys.push(KeySource::Literal(*k)),
                        _ => {
                            info.get_mut(var_idx).unwrap().1 = true;
                        }
                    }
                }
            } else {
                collect_ts_read_keys(base, info);
            }
            collect_ts_read_keys(index, info);
        }
        TsExpr::Var { index: var_idx } => {
            if let Some((_, has_unkeyed)) = info.get_mut(var_idx) {
                *has_unkeyed = true;
            }
        }
        TsExpr::Binary { left, right, .. } => {
            collect_ts_read_keys(left, info);
            collect_ts_read_keys(right, info);
        }
        TsExpr::Unary { operand, .. } => collect_ts_read_keys(operand, info),
        TsExpr::SetLit { elements }
        | TsExpr::SeqLit { elements }
        | TsExpr::TupleLit { elements } => {
            for e in elements {
                collect_ts_read_keys(e, info);
            }
        }
        TsExpr::DictLit { entries } => {
            for (k, v) in entries {
                collect_ts_read_keys(k, info);
                collect_ts_read_keys(v, info);
            }
        }
        TsExpr::FnLit { domain, body }
        | TsExpr::Forall { domain, body }
        | TsExpr::Exists { domain, body } => {
            collect_ts_read_keys(domain, info);
            collect_ts_read_keys(body, info);
        }
        TsExpr::MapUpdate { base, key, value } => {
            if !matches!(base.as_ref(), TsExpr::Var { .. }) {
                collect_ts_read_keys(base, info);
            }
            collect_ts_read_keys(key, info);
            collect_ts_read_keys(value, info);
        }
        TsExpr::SetComprehension {
            element,
            domain,
            filter,
        } => {
            collect_ts_read_keys(element, info);
            collect_ts_read_keys(domain, info);
            if let Some(f) = filter {
                collect_ts_read_keys(f, info);
            }
        }
        TsExpr::Slice { base, lo, hi } => {
            collect_ts_read_keys(base, info);
            collect_ts_read_keys(lo, info);
            collect_ts_read_keys(hi, info);
        }
        TsExpr::Field { base, .. } => collect_ts_read_keys(base, info),
        TsExpr::Len { expr }
        | TsExpr::Keys { expr }
        | TsExpr::Values { expr }
        | TsExpr::SeqHead { expr }
        | TsExpr::SeqTail { expr } => {
            if let TsExpr::Var { index: var_idx } = expr.as_ref() {
                if let Some((_, has_unkeyed)) = info.get_mut(var_idx) {
                    *has_unkeyed = true;
                }
            } else {
                collect_ts_read_keys(expr, info);
            }
        }
        TsExpr::Let { value, body } => {
            collect_ts_read_keys(value, info);
            collect_ts_read_keys(body, info);
        }
        TsExpr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            collect_ts_read_keys(cond, info);
            collect_ts_read_keys(then_branch, info);
            collect_ts_read_keys(else_branch, info);
        }
        TsExpr::Range { lo, hi } => {
            collect_ts_read_keys(lo, info);
            collect_ts_read_keys(hi, info);
        }
        TsExpr::RecordUpdate { base, updates } => {
            collect_ts_read_keys(base, info);
            for (_, v) in updates {
                collect_ts_read_keys(v, info);
            }
        }
        // Leaves
        TsExpr::Bool { .. }
        | TsExpr::Int { .. }
        | TsExpr::Str { .. }
        | TsExpr::Const { .. }
        | TsExpr::Local { .. }
        | TsExpr::Param { .. } => {}
    }
}

fn expr_cost(expr: &CompiledExpr) -> u32 {
    match expr {
        CompiledExpr::Bool(_)
        | CompiledExpr::Int(_)
        | CompiledExpr::String(_)
        | CompiledExpr::Var(_)
        | CompiledExpr::PrimedVar(_)
        | CompiledExpr::Const(_)
        | CompiledExpr::Local(_)
        | CompiledExpr::Param(_)
        | CompiledExpr::Changes(_)
        | CompiledExpr::Unchanged(_)
        | CompiledExpr::Enabled(_) => 1,
        CompiledExpr::Binary { left, right, .. } => 1 + expr_cost(left) + expr_cost(right),
        CompiledExpr::Unary { operand, .. } => 1 + expr_cost(operand),
        CompiledExpr::Index { base, index } => 2 + expr_cost(base) + expr_cost(index),
        CompiledExpr::Let { value, body } => 1 + expr_cost(value) + expr_cost(body),
        CompiledExpr::If {
            cond,
            then_branch,
            else_branch,
        } => 1 + expr_cost(cond) + expr_cost(then_branch).max(expr_cost(else_branch)),
        CompiledExpr::SetLit(elems)
        | CompiledExpr::SeqLit(elems)
        | CompiledExpr::TupleLit(elems) => elems.iter().map(expr_cost).sum::<u32>() + 1,
        CompiledExpr::DictLit(pairs) => {
            pairs
                .iter()
                .map(|(k, v)| expr_cost(k) + expr_cost(v))
                .sum::<u32>()
                + 1
        }
        CompiledExpr::Forall { domain, body }
        | CompiledExpr::Exists { domain, body }
        | CompiledExpr::FnLit { domain, body } => 10 + expr_cost(domain) * expr_cost(body),
        CompiledExpr::Fix { domain, predicate } => {
            let domain_cost = domain.as_ref().map_or(1, |d| expr_cost(d));
            10 + domain_cost * expr_cost(predicate)
        }
        CompiledExpr::SetComprehension {
            domain,
            filter: Some(predicate),
            ..
        } => 10 + expr_cost(domain) * expr_cost(predicate),
        CompiledExpr::SetComprehension {
            domain,
            element,
            filter: None,
        } => 10 + expr_cost(domain) * expr_cost(element),
        CompiledExpr::Slice { base, lo, hi } => 3 + expr_cost(base) + expr_cost(lo) + expr_cost(hi),
        CompiledExpr::Field { base, .. } => 1 + expr_cost(base),
        CompiledExpr::SeqHead(inner) | CompiledExpr::SeqTail(inner) => 2 + expr_cost(inner),
        CompiledExpr::Len(inner) | CompiledExpr::Keys(inner) | CompiledExpr::Values(inner) => {
            2 + expr_cost(inner)
        }
        CompiledExpr::BigUnion(inner) | CompiledExpr::Powerset(inner) => 10 + expr_cost(inner),
        CompiledExpr::FnUpdate { base, key, value } => {
            2 + expr_cost(base) + expr_cost(key) + expr_cost(value)
        }
        CompiledExpr::RecordUpdate { base, updates } => {
            2 + expr_cost(base) + updates.iter().map(|(_, v)| expr_cost(v)).sum::<u32>()
        }
        CompiledExpr::Call { args, .. } => args.iter().map(expr_cost).sum::<u32>() + 5,
        CompiledExpr::ActionCall { args, .. } => args.iter().map(expr_cost).sum::<u32>() + 10,
        CompiledExpr::Range { lo, hi } => 2 + expr_cost(lo) + expr_cost(hi),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use specl_ts::*;

    fn counter_ts(max: i64) -> TransitionSystem {
        TransitionSystem {
            name: "Counter".to_string(),
            variables: vec![TsVariable {
                name: "count".to_string(),
                ty: TsType::Nat,
            }],
            constants: vec![TsConstant {
                name: "MAX".to_string(),
                ty: TsType::Nat,
                default_value: Some(max),
            }],
            init: vec![TsAssignment {
                var_idx: 0,
                value: TsExpr::Int { value: 0 },
            }],
            actions: vec![TsAction {
                name: "Inc".to_string(),
                params: vec![],
                guard: TsExpr::Binary {
                    op: TsBinOp::Lt,
                    left: Box::new(TsExpr::Var { index: 0 }),
                    right: Box::new(TsExpr::Const { index: 0 }),
                },
                assignments: vec![TsAssignment {
                    var_idx: 0,
                    value: TsExpr::Binary {
                        op: TsBinOp::Add,
                        left: Box::new(TsExpr::Var { index: 0 }),
                        right: Box::new(TsExpr::Int { value: 1 }),
                    },
                }],
            }],
            invariants: vec![TsInvariant {
                name: "Bounded".to_string(),
                body: TsExpr::Binary {
                    op: TsBinOp::Le,
                    left: Box::new(TsExpr::Var { index: 0 }),
                    right: Box::new(TsExpr::Const { index: 0 }),
                },
            }],
            auxiliary_invariants: vec![],
            view_variables: None,
        }
    }

    #[test]
    fn test_lower_counter() {
        let ts = counter_ts(5);
        let spec = lower(&ts).unwrap();
        assert_eq!(spec.vars.len(), 1);
        assert_eq!(spec.vars[0].name, "count");
        assert_eq!(spec.consts.len(), 1);
        assert_eq!(spec.consts[0].name, "MAX");
        assert_eq!(spec.actions.len(), 1);
        assert_eq!(spec.actions[0].name, "Inc");
        assert_eq!(spec.invariants.len(), 1);
        assert_eq!(spec.invariants[0].name, "Bounded");
        // Only one var, one action → 1x1 independence matrix, all false (self)
        assert_eq!(spec.independent, vec![vec![false]]);
    }

    #[test]
    fn test_lower_type_mapping() {
        assert_eq!(lower_type(&TsType::Bool), Type::Bool);
        assert_eq!(lower_type(&TsType::Nat), Type::Nat);
        assert_eq!(lower_type(&TsType::Int), Type::Int);
        assert_eq!(lower_type(&TsType::String), Type::String);
        assert_eq!(
            lower_type(&TsType::Range { lo: 0, hi: 5 }),
            Type::Range(0, 5)
        );
        assert_eq!(
            lower_type(&TsType::Set {
                element: Box::new(TsType::Nat)
            }),
            Type::Set(Box::new(Type::Nat))
        );
        assert_eq!(
            lower_type(&TsType::Map {
                key: Box::new(TsType::Range { lo: 0, hi: 2 }),
                value: Box::new(TsType::Int)
            }),
            Type::Fn(Box::new(Type::Range(0, 2)), Box::new(Type::Int))
        );
    }

    #[test]
    fn test_validation_missing_init() {
        let mut ts = counter_ts(5);
        ts.variables.push(TsVariable {
            name: "extra".to_string(),
            ty: TsType::Nat,
        });
        let err = lower(&ts).unwrap_err();
        assert!(matches!(err, LowerError::InitAssignmentError { .. }));
    }

    #[test]
    fn test_validation_duplicate_init() {
        let mut ts = counter_ts(5);
        ts.init.push(TsAssignment {
            var_idx: 0,
            value: TsExpr::Int { value: 1 },
        });
        let err = lower(&ts).unwrap_err();
        assert!(matches!(err, LowerError::InitAssignmentError { .. }));
    }

    #[test]
    fn test_validation_var_out_of_bounds() {
        let mut ts = counter_ts(5);
        ts.init[0].var_idx = 99;
        let err = lower(&ts).unwrap_err();
        assert!(matches!(err, LowerError::VarIndexOutOfBounds(99, 1)));
    }

    #[test]
    fn test_validation_duplicate_action_assignment() {
        let mut ts = counter_ts(5);
        ts.actions[0].assignments.push(TsAssignment {
            var_idx: 0,
            value: TsExpr::Int { value: 2 },
        });
        let err = lower(&ts).unwrap_err();
        assert!(matches!(err, LowerError::DuplicateAssignment { .. }));
    }

    #[test]
    fn test_serde_roundtrip() {
        let ts = counter_ts(5);
        let json = serde_json::to_string(&ts).unwrap();
        let ts2: TransitionSystem = serde_json::from_str(&json).unwrap();
        assert_eq!(ts, ts2);
    }

    #[test]
    fn test_two_variable_independence() {
        // Two vars: x and y, two actions: IncX (changes x), IncY (changes y)
        // They should be independent.
        let ts = TransitionSystem {
            name: "TwoCounters".to_string(),
            variables: vec![
                TsVariable {
                    name: "x".to_string(),
                    ty: TsType::Nat,
                },
                TsVariable {
                    name: "y".to_string(),
                    ty: TsType::Nat,
                },
            ],
            constants: vec![],
            init: vec![
                TsAssignment {
                    var_idx: 0,
                    value: TsExpr::Int { value: 0 },
                },
                TsAssignment {
                    var_idx: 1,
                    value: TsExpr::Int { value: 0 },
                },
            ],
            actions: vec![
                TsAction {
                    name: "IncX".to_string(),
                    params: vec![],
                    guard: TsExpr::Bool { value: true },
                    assignments: vec![TsAssignment {
                        var_idx: 0,
                        value: TsExpr::Binary {
                            op: TsBinOp::Add,
                            left: Box::new(TsExpr::Var { index: 0 }),
                            right: Box::new(TsExpr::Int { value: 1 }),
                        },
                    }],
                },
                TsAction {
                    name: "IncY".to_string(),
                    params: vec![],
                    guard: TsExpr::Bool { value: true },
                    assignments: vec![TsAssignment {
                        var_idx: 1,
                        value: TsExpr::Binary {
                            op: TsBinOp::Add,
                            left: Box::new(TsExpr::Var { index: 1 }),
                            right: Box::new(TsExpr::Int { value: 1 }),
                        },
                    }],
                },
            ],
            invariants: vec![],
            auxiliary_invariants: vec![],
            view_variables: None,
        };

        let spec = lower(&ts).unwrap();
        // IncX reads/writes x only, IncY reads/writes y only → independent
        assert!(spec.independent[0][1]);
        assert!(spec.independent[1][0]);
    }
}

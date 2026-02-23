//! Variable layout analysis: maps specl state variables to Z3 variables.

use specl_eval::Value;
use specl_ir::{CompiledExpr, CompiledSpec};
use specl_syntax::{ExprKind, TypeExpr};
use specl_types::Type;

use crate::SymbolicResult;

/// Layout of Z3 variables for a specl specification.
#[derive(Debug)]
pub struct VarLayout {
    /// One entry per specl state variable.
    pub entries: Vec<VarEntry>,
    /// String interning table: maps string literals to integer IDs.
    pub string_table: Vec<String>,
    /// Maximum sequence length for ExplodedSeq variables.
    pub seq_bound: usize,
}

/// How a single specl variable maps to Z3 variables.
#[derive(Debug, Clone)]
pub struct VarEntry {
    /// Index in CompiledSpec.vars.
    pub specl_var_idx: usize,
    /// Variable name.
    pub name: String,
    /// What kind of Z3 encoding to use.
    pub kind: VarKind,
}

/// Z3 encoding strategy for a variable.
#[derive(Debug, Clone)]
pub enum VarKind {
    /// Single Z3 Bool.
    Bool,
    /// Single Z3 Int, optionally bounded.
    Int { lo: Option<i64>, hi: Option<i64> },
    /// Dict exploded into individual Z3 variables per key.
    ExplodedDict {
        key_lo: i64,
        key_hi: i64,
        value_kind: Box<VarKind>,
    },
    /// Set over bounded domain: one Z3 Bool per element.
    ExplodedSet { lo: i64, hi: i64 },
    /// Bounded sequence: len_var (Int) + max_len element variables.
    /// Z3 layout: [len, elem_0, elem_1, ..., elem_{max_len-1}]
    ExplodedSeq {
        max_len: usize,
        elem_kind: Box<VarKind>,
    },
    /// Option[T]: present Bool + inner value.
    /// Z3 layout: [present, inner_0, inner_1, ...]
    ExplodedOption { inner_kind: Box<VarKind> },
    /// Tuple: flattened element variables.
    /// Z3 layout: [elem_0_vars..., elem_1_vars..., ...]
    ExplodedTuple { element_kinds: Vec<VarKind> },
}

impl VarLayout {
    /// Analyze a compiled spec and compute the Z3 variable layout.
    pub fn from_spec(
        spec: &CompiledSpec,
        consts: &[Value],
        seq_bound: usize,
    ) -> SymbolicResult<Self> {
        let string_table = build_string_table(spec);
        let mut entries = Vec::new();
        for var in &spec.vars {
            let kind = type_to_kind(&var.ty, var.index, spec, consts, &string_table, seq_bound)?;
            entries.push(VarEntry {
                specl_var_idx: var.index,
                name: var.name.clone(),
                kind,
            });
        }
        Ok(VarLayout {
            entries,
            string_table,
            seq_bound,
        })
    }

    /// Look up a string literal's integer ID.
    pub fn string_id(&self, s: &str) -> Option<i64> {
        self.string_table
            .iter()
            .position(|t| t == s)
            .map(|i| i as i64)
    }
}

fn type_to_kind(
    ty: &Type,
    var_idx: usize,
    spec: &CompiledSpec,
    consts: &[Value],
    string_table: &[String],
    seq_bound: usize,
) -> SymbolicResult<VarKind> {
    match ty {
        Type::Bool => Ok(VarKind::Bool),
        Type::Int => Ok(VarKind::Int { lo: None, hi: None }),
        Type::Nat => Ok(VarKind::Int {
            lo: Some(0),
            hi: None,
        }),
        Type::String => {
            if string_table.is_empty() {
                Ok(VarKind::Int { lo: None, hi: None })
            } else {
                Ok(VarKind::Int {
                    lo: Some(0),
                    hi: Some(string_table.len() as i64 - 1),
                })
            }
        }
        Type::Range(lo, hi) => Ok(VarKind::Int {
            lo: Some(*lo),
            hi: Some(*hi),
        }),
        Type::Fn(key_ty, val_ty) => {
            // Reject Dict with Seq keys (e.g., Dict[Seq[Int], V])
            if matches!(key_ty.as_ref(), Type::Seq(_)) {
                return Err(crate::SymbolicError::Unsupported(
                    "Dict with sequence keys requires enumerating all possible sequences; \
                     use Dict[Int, V] with an integer key instead"
                        .into(),
                ));
            }
            let key_range = if let Type::Range(lo, hi) = key_ty.as_ref() {
                (*lo, *hi)
            } else if matches!(key_ty.as_ref(), Type::Int | Type::Nat) {
                infer_dict_range(var_idx, spec, consts).ok_or_else(|| {
                    crate::SymbolicError::Unsupported(format!(
                        "Dict with unbounded key type {:?} (cannot infer range from init).\n  \
                         Fix: use a bounded key type, e.g. change 'Dict[Int, T]' to \
                         'Dict[0..N, T]' where N is a const",
                        key_ty
                    ))
                })?
            } else {
                return Err(crate::SymbolicError::Unsupported(format!(
                    "Dict with non-range key type: {:?}",
                    key_ty
                )));
            };
            let init_rhs = find_init_rhs(var_idx, spec);
            let init_body = init_rhs.and_then(extract_fn_body);
            let value_kind = type_to_kind_value(
                val_ty,
                var_idx,
                spec,
                consts,
                string_table,
                seq_bound,
                init_body,
            )?;
            Ok(VarKind::ExplodedDict {
                key_lo: key_range.0,
                key_hi: key_range.1,
                value_kind: Box::new(value_kind),
            })
        }
        Type::Set(elem_ty) => {
            if matches!(elem_ty.as_ref(), Type::Seq(_)) {
                return Err(crate::SymbolicError::Unsupported(
                    "Set[Seq[T]] requires exponential encoding (tracks membership of every \
                     possible sequence). Workaround: model messages as Dict[Int, Seq[Int]] \
                     with a message counter instead of Set[Seq[Int]]"
                        .into(),
                ));
            }
            if let Type::Range(lo, hi) = elem_ty.as_ref() {
                Ok(VarKind::ExplodedSet { lo: *lo, hi: *hi })
            } else if matches!(elem_ty.as_ref(), Type::Int | Type::Nat) {
                if let Some((lo, hi)) = infer_set_range_from_actions(var_idx, spec, consts) {
                    Ok(VarKind::ExplodedSet { lo, hi })
                } else {
                    Err(crate::SymbolicError::Unsupported(format!(
                        "Set with unbounded element type {:?} (cannot infer range).\n  \
                         Fix: use a bounded set type, e.g. change 'var x: Set[Int]' to \
                         'var x: Set[0..N]' where N is a const",
                        elem_ty
                    )))
                }
            } else {
                Err(crate::SymbolicError::Unsupported(format!(
                    "Set with non-range element type: {:?}",
                    elem_ty
                )))
            }
        }
        Type::Seq(elem_ty) => {
            let elem_kind = type_to_kind_simple(elem_ty, seq_bound)?;
            let max_len = infer_seq_max_len(var_idx, spec, consts).unwrap_or(seq_bound);
            Ok(VarKind::ExplodedSeq {
                max_len,
                elem_kind: Box::new(elem_kind),
            })
        }
        Type::Option(inner) => {
            let inner_kind = type_to_kind(inner, var_idx, spec, consts, string_table, seq_bound)?;
            Ok(VarKind::ExplodedOption {
                inner_kind: Box::new(inner_kind),
            })
        }
        _ => Err(crate::SymbolicError::Unsupported(format!(
            "variable type: {:?}",
            ty
        ))),
    }
}

/// Resolve value types within containers, with full spec context for range inference.
/// The `init_body` parameter is the FnLit body at this nesting level, used to infer
/// inner dict key ranges and set element ranges from init expressions.
fn type_to_kind_value(
    ty: &Type,
    var_idx: usize,
    spec: &CompiledSpec,
    consts: &[Value],
    string_table: &[String],
    seq_bound: usize,
    init_body: Option<&CompiledExpr>,
) -> SymbolicResult<VarKind> {
    match ty {
        Type::Bool => Ok(VarKind::Bool),
        Type::Int => Ok(VarKind::Int { lo: None, hi: None }),
        Type::String => {
            if string_table.is_empty() {
                Ok(VarKind::Int { lo: None, hi: None })
            } else {
                Ok(VarKind::Int {
                    lo: Some(0),
                    hi: Some(string_table.len() as i64 - 1),
                })
            }
        }
        Type::Nat => Ok(VarKind::Int {
            lo: Some(0),
            hi: None,
        }),
        Type::Range(lo, hi) => Ok(VarKind::Int {
            lo: Some(*lo),
            hi: Some(*hi),
        }),
        Type::Seq(elem_ty) => {
            let elem_kind = type_to_kind_simple(elem_ty, seq_bound)?;
            Ok(VarKind::ExplodedSeq {
                max_len: seq_bound,
                elem_kind: Box::new(elem_kind),
            })
        }
        Type::Fn(key_ty, val_ty) => {
            if matches!(key_ty.as_ref(), Type::Seq(_)) {
                return Err(crate::SymbolicError::Unsupported(
                    "Dict with sequence keys requires enumerating all possible sequences".into(),
                ));
            }
            let key_range = if let Type::Range(lo, hi) = key_ty.as_ref() {
                (*lo, *hi)
            } else if matches!(key_ty.as_ref(), Type::Int | Type::Nat) {
                // Infer from init body's FnLit domain
                if let Some(body) = init_body {
                    extract_domain_range(body, consts).ok_or_else(|| {
                        crate::SymbolicError::Unsupported(format!(
                            "nested Dict with unbounded key type {:?} \
                             (cannot infer range from init body)",
                            key_ty
                        ))
                    })?
                } else {
                    // Fall back to action parameter inference
                    infer_dict_range(var_idx, spec, consts).ok_or_else(|| {
                        crate::SymbolicError::Unsupported(format!(
                            "nested Dict with unbounded key type {:?} (cannot infer range)",
                            key_ty
                        ))
                    })?
                }
            } else {
                return Err(crate::SymbolicError::Unsupported(format!(
                    "Dict with non-range key type in value context: {:?}",
                    key_ty
                )));
            };
            let inner_init_body = init_body.and_then(extract_fn_body);
            let value_kind = type_to_kind_value(
                val_ty,
                var_idx,
                spec,
                consts,
                string_table,
                seq_bound,
                inner_init_body,
            )?;
            Ok(VarKind::ExplodedDict {
                key_lo: key_range.0,
                key_hi: key_range.1,
                value_kind: Box::new(value_kind),
            })
        }
        Type::Set(elem_ty) => {
            if matches!(elem_ty.as_ref(), Type::Seq(_)) {
                return Err(crate::SymbolicError::Unsupported(
                    "Set[Seq[T]] in value context requires exponential encoding".into(),
                ));
            }
            if let Type::Range(lo, hi) = elem_ty.as_ref() {
                Ok(VarKind::ExplodedSet { lo: *lo, hi: *hi })
            } else if matches!(elem_ty.as_ref(), Type::Int | Type::Nat) {
                // Try action parameter inference (works for inner sets too)
                if let Some((lo, hi)) = infer_set_range_from_actions(var_idx, spec, consts) {
                    Ok(VarKind::ExplodedSet { lo, hi })
                } else {
                    Err(crate::SymbolicError::Unsupported(format!(
                        "Set with unbounded element type {:?} (cannot infer range).\n  \
                         Fix: use a bounded set type, e.g. change 'var x: Set[Int]' to \
                         'var x: Set[0..N]' where N is a const",
                        elem_ty
                    )))
                }
            } else {
                Err(crate::SymbolicError::Unsupported(format!(
                    "Set with non-range element type: {:?}",
                    elem_ty
                )))
            }
        }
        _ => type_to_kind_simple(ty, seq_bound),
    }
}

/// Simple type_to_kind without spec/const context (for value types within containers).
fn type_to_kind_simple(ty: &Type, seq_bound: usize) -> SymbolicResult<VarKind> {
    match ty {
        Type::Bool => Ok(VarKind::Bool),
        Type::Int | Type::String => Ok(VarKind::Int { lo: None, hi: None }),
        Type::Nat => Ok(VarKind::Int {
            lo: Some(0),
            hi: None,
        }),
        Type::Range(lo, hi) => Ok(VarKind::Int {
            lo: Some(*lo),
            hi: Some(*hi),
        }),
        Type::Seq(elem_ty) => {
            let elem_kind = type_to_kind_simple(elem_ty, seq_bound)?;
            Ok(VarKind::ExplodedSeq {
                max_len: seq_bound,
                elem_kind: Box::new(elem_kind),
            })
        }
        Type::Option(inner) => {
            let inner_kind = type_to_kind_simple(inner, seq_bound)?;
            Ok(VarKind::ExplodedOption {
                inner_kind: Box::new(inner_kind),
            })
        }
        _ => Err(crate::SymbolicError::Unsupported(format!(
            "value type in container: {:?}",
            ty
        ))),
    }
}

/// Extract the init RHS expression for a variable (e.g., for `x = FnLit{...}` returns the FnLit).
fn find_init_rhs(var_idx: usize, spec: &CompiledSpec) -> Option<&CompiledExpr> {
    find_init_rhs_in(var_idx, &spec.init)
}

fn find_init_rhs_in(var_idx: usize, expr: &CompiledExpr) -> Option<&CompiledExpr> {
    match expr {
        CompiledExpr::Binary {
            op: specl_ir::BinOp::And,
            left,
            right,
        } => find_init_rhs_in(var_idx, left).or_else(|| find_init_rhs_in(var_idx, right)),
        CompiledExpr::Binary {
            op: specl_ir::BinOp::Eq,
            left,
            right,
        } => match left.as_ref() {
            CompiledExpr::PrimedVar(idx) | CompiledExpr::Var(idx) if *idx == var_idx => {
                Some(right.as_ref())
            }
            _ => None,
        },
        _ => None,
    }
}

/// Extract the body from a FnLit expression.
fn extract_fn_body(expr: &CompiledExpr) -> Option<&CompiledExpr> {
    if let CompiledExpr::FnLit { body, .. } = expr {
        Some(body.as_ref())
    } else {
        None
    }
}

/// Infer dict key range from init expression or action parameters.
fn infer_dict_range(var_idx: usize, spec: &CompiledSpec, consts: &[Value]) -> Option<(i64, i64)> {
    if let Some(range) = find_var_init_range(var_idx, &spec.init, consts) {
        return Some(range);
    }
    // Fall through to AST type expressions on actions that modify this variable
    for action in &spec.actions {
        if !action.changes.contains(&var_idx) {
            continue;
        }
        for type_expr in &action.param_type_exprs {
            if let Some(range) = eval_type_expr_range(type_expr, spec, consts) {
                return Some(range);
            }
        }
    }
    None
}

/// Infer set element range from action parameters that add to this set.
fn infer_set_range_from_actions(
    var_idx: usize,
    spec: &CompiledSpec,
    consts: &[Value],
) -> Option<(i64, i64)> {
    // First try init expression
    if let Some(range) = find_var_init_range(var_idx, &spec.init, consts) {
        return Some(range);
    }
    // Try to find from action parameter types that reference this set
    for action in &spec.actions {
        if !action.changes.contains(&var_idx) {
            continue;
        }
        // Try compiled param types first (works when type checker resolved the range)
        for (_, param_ty) in &action.params {
            if let Type::Range(lo, hi) = param_ty {
                return Some((*lo, *hi));
            }
        }
        // Fall through to AST type expressions (works when consts aren't resolved by type checker)
        for type_expr in &action.param_type_exprs {
            if let Some(range) = eval_type_expr_range(type_expr, spec, consts) {
                return Some(range);
            }
        }
    }
    None
}

/// Walk the init expression to find a FnLit/SetComprehension domain for a variable.
fn find_var_init_range(
    var_idx: usize,
    expr: &CompiledExpr,
    consts: &[Value],
) -> Option<(i64, i64)> {
    match expr {
        CompiledExpr::Binary {
            op: specl_ir::BinOp::And,
            left,
            right,
        } => find_var_init_range(var_idx, left, consts)
            .or_else(|| find_var_init_range(var_idx, right, consts)),
        CompiledExpr::Binary {
            op: specl_ir::BinOp::Eq,
            left,
            right,
        } => {
            let target_idx = match left.as_ref() {
                CompiledExpr::PrimedVar(idx) | CompiledExpr::Var(idx) => Some(*idx),
                _ => None,
            };
            if target_idx == Some(var_idx) {
                extract_domain_range(right, consts)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Extract domain range from a FnLit or SetComprehension RHS.
fn extract_domain_range(expr: &CompiledExpr, consts: &[Value]) -> Option<(i64, i64)> {
    match expr {
        CompiledExpr::FnLit { domain, .. } | CompiledExpr::SetComprehension { domain, .. } => {
            extract_range_bounds(domain, consts)
        }
        _ => None,
    }
}

fn extract_range_bounds(expr: &CompiledExpr, consts: &[Value]) -> Option<(i64, i64)> {
    if let CompiledExpr::Range { lo, hi } = expr {
        let lo_val = eval_const_int(lo, consts)?;
        let hi_val = eval_const_int(hi, consts)?;
        Some((lo_val, hi_val))
    } else {
        None
    }
}

fn eval_const_int(expr: &CompiledExpr, consts: &[Value]) -> Option<i64> {
    match expr {
        CompiledExpr::Int(n) => Some(*n),
        CompiledExpr::Const(idx) => consts[*idx].as_int(),
        _ => None,
    }
}

/// Evaluate an AST TypeExpr::Range to a concrete (lo, hi) using const values.
pub fn eval_type_expr_range(
    type_expr: &TypeExpr,
    spec: &CompiledSpec,
    consts: &[Value],
) -> Option<(i64, i64)> {
    if let TypeExpr::Range(lo_expr, hi_expr, _) = type_expr {
        let lo = eval_ast_expr_int(lo_expr, spec, consts)?;
        let hi = eval_ast_expr_int(hi_expr, spec, consts)?;
        Some((lo, hi))
    } else {
        None
    }
}

/// Evaluate a simple AST Expr to an i64 (handles int literals and const identifiers).
fn eval_ast_expr_int(
    expr: &specl_syntax::Expr,
    spec: &CompiledSpec,
    consts: &[Value],
) -> Option<i64> {
    match &expr.kind {
        ExprKind::Int(n) => Some(*n),
        ExprKind::Ident(name) => {
            let const_decl = spec.consts.iter().find(|c| c.name == *name)?;
            consts[const_decl.index].as_int()
        }
        _ => None,
    }
}

/// Scan all expressions in the spec for string literals and build a deduped table.
fn build_string_table(spec: &CompiledSpec) -> Vec<String> {
    let mut strings = Vec::new();
    collect_strings_from_expr(&spec.init, &mut strings);
    for action in &spec.actions {
        collect_strings_from_expr(&action.guard, &mut strings);
        collect_strings_from_expr(&action.effect, &mut strings);
    }
    for inv in &spec.invariants {
        collect_strings_from_expr(&inv.body, &mut strings);
    }
    strings.sort();
    strings.dedup();
    strings
}

fn collect_strings_from_expr(expr: &CompiledExpr, out: &mut Vec<String>) {
    match expr {
        CompiledExpr::String(s) => out.push(s.clone()),
        CompiledExpr::Binary { left, right, .. } => {
            collect_strings_from_expr(left, out);
            collect_strings_from_expr(right, out);
        }
        CompiledExpr::Unary { operand, .. } => collect_strings_from_expr(operand, out),
        CompiledExpr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            collect_strings_from_expr(cond, out);
            collect_strings_from_expr(then_branch, out);
            collect_strings_from_expr(else_branch, out);
        }
        CompiledExpr::Let { value, body, .. } => {
            collect_strings_from_expr(value, out);
            collect_strings_from_expr(body, out);
        }
        CompiledExpr::Forall { body, domain, .. } | CompiledExpr::Exists { body, domain, .. } => {
            collect_strings_from_expr(domain, out);
            collect_strings_from_expr(body, out);
        }
        CompiledExpr::FnLit { domain, body, .. } => {
            collect_strings_from_expr(domain, out);
            collect_strings_from_expr(body, out);
        }
        CompiledExpr::Index { base, index } => {
            collect_strings_from_expr(base, out);
            collect_strings_from_expr(index, out);
        }
        CompiledExpr::SetComprehension {
            element,
            domain,
            filter,
            ..
        } => {
            collect_strings_from_expr(element, out);
            collect_strings_from_expr(domain, out);
            if let Some(f) = filter {
                collect_strings_from_expr(f, out);
            }
        }
        CompiledExpr::SetLit(elems) | CompiledExpr::SeqLit(elems) => {
            for e in elems {
                collect_strings_from_expr(e, out);
            }
        }
        CompiledExpr::Range { lo, hi } => {
            collect_strings_from_expr(lo, out);
            collect_strings_from_expr(hi, out);
        }
        CompiledExpr::DictLit(pairs) => {
            for (k, v) in pairs {
                collect_strings_from_expr(k, out);
                collect_strings_from_expr(v, out);
            }
        }
        CompiledExpr::Fix {
            domain, predicate, ..
        } => {
            if let Some(domain) = domain {
                collect_strings_from_expr(domain, out);
            }
            collect_strings_from_expr(predicate, out);
        }
        _ => {}
    }
}

impl VarKind {
    /// Number of Z3 variables needed for this kind.
    pub fn z3_var_count(&self) -> usize {
        match self {
            VarKind::Bool | VarKind::Int { .. } => 1,
            VarKind::ExplodedDict {
                key_lo,
                key_hi,
                value_kind,
            } => {
                let num_keys = (*key_hi - *key_lo + 1) as usize;
                num_keys * value_kind.z3_var_count()
            }
            VarKind::ExplodedSet { lo, hi } => (*hi - *lo + 1) as usize,
            VarKind::ExplodedSeq { max_len, elem_kind } => 1 + max_len * elem_kind.z3_var_count(),
            VarKind::ExplodedOption { inner_kind } => 1 + inner_kind.z3_var_count(),
            VarKind::ExplodedTuple { element_kinds } => {
                element_kinds.iter().map(|k| k.z3_var_count()).sum()
            }
        }
    }
}

/// Infer max sequence length from action guards (look for len(var) < K patterns).
fn infer_seq_max_len(var_idx: usize, spec: &CompiledSpec, consts: &[Value]) -> Option<usize> {
    for action in &spec.actions {
        if let Some(bound) = find_len_bound(&action.guard, var_idx, consts) {
            return Some(bound);
        }
    }
    None
}

/// Walk an expression looking for `Len(Var(var_idx)) < K` or `Len(Var(var_idx)) <= K`.
fn find_len_bound(expr: &CompiledExpr, var_idx: usize, consts: &[Value]) -> Option<usize> {
    match expr {
        CompiledExpr::Binary {
            op: specl_ir::BinOp::And,
            left,
            right,
        } => {
            find_len_bound(left, var_idx, consts).or_else(|| find_len_bound(right, var_idx, consts))
        }
        // len(var) < K → max_len = K
        CompiledExpr::Binary {
            op: specl_ir::BinOp::Lt,
            left,
            right,
        } => {
            if is_len_of_var(left, var_idx) {
                eval_const_int(right, consts).map(|k| k as usize)
            } else {
                None
            }
        }
        // len(var) <= K → max_len = K + 1
        CompiledExpr::Binary {
            op: specl_ir::BinOp::Le,
            left,
            right,
        } => {
            if is_len_of_var(left, var_idx) {
                eval_const_int(right, consts).map(|k| (k + 1) as usize)
            } else {
                None
            }
        }
        _ => None,
    }
}

fn is_len_of_var(expr: &CompiledExpr, var_idx: usize) -> bool {
    matches!(expr, CompiledExpr::Len(inner) if matches!(inner.as_ref(), CompiledExpr::Var(idx) if *idx == var_idx))
}

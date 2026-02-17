//! Expression encoder: translates CompiledExpr to Z3 AST.

use crate::state_vars::{VarEntry, VarKind, VarLayout};
use crate::{SymbolicError, SymbolicResult};
use specl_eval::Value;
use specl_ir::{BinOp, CompiledExpr, UnaryOp};
use z3::ast::{Bool, Dynamic, Int};
use z3::Solver;

/// Encoding context for translating expressions to Z3.
pub struct EncoderCtx<'a> {
    pub layout: &'a VarLayout,
    pub consts: &'a [Value],
    /// Z3 variables for each step. step_vars[step][specl_var_idx] = list of Z3 Dynamics.
    pub step_vars: &'a [Vec<Vec<Dynamic>>],
    /// Current step index (for Var references).
    pub current_step: usize,
    /// Next step index (for PrimedVar references).
    pub next_step: usize,
    /// Action parameters (if encoding an action).
    pub params: &'a [Dynamic],
    /// Local variable stack (for Let/Forall/Exists bindings).
    pub locals: Vec<Dynamic>,
    /// Compound locals: tracks locals bound to compound dict values (e.g., d[k] where d is Dict[Range, Seq]).
    /// Each entry: (abs_depth, var_idx, step, key_z3) where abs_depth is the locals stack position.
    pub compound_locals: Vec<(usize, usize, usize, Int)>,
    /// Set locals: maps absolute locals stack position → concrete set members.
    /// Used for powerset quantifier bindings where the local represents a concrete subset.
    pub set_locals: Vec<(usize, Vec<i64>)>,
    /// Whole-var locals: locals that alias an entire compound variable.
    /// Each entry: (abs_depth, var_idx, step).
    pub whole_var_locals: Vec<(usize, usize, usize)>,
}

impl<'a> EncoderCtx<'a> {
    /// Encode a CompiledExpr as a Z3 Bool (for guards, invariants, effects).
    pub fn encode_bool(&mut self, expr: &CompiledExpr) -> SymbolicResult<Bool> {
        let dyn_val = self.encode(expr)?;
        dyn_val.as_bool().ok_or_else(|| {
            SymbolicError::Encoding(format!("expected Bool expression, got: {:?}", expr))
        })
    }

    /// Encode a CompiledExpr as a Z3 Int.
    pub fn encode_int(&mut self, expr: &CompiledExpr) -> SymbolicResult<Int> {
        let dyn_val = self.encode(expr)?;
        dyn_val.as_int().ok_or_else(|| {
            SymbolicError::Encoding(format!("expected Int expression, got: {:?}", expr))
        })
    }

    /// Encode a CompiledExpr as a Z3 Dynamic value.
    pub fn encode(&mut self, expr: &CompiledExpr) -> SymbolicResult<Dynamic> {
        match expr {
            // === Literals ===
            CompiledExpr::Bool(b) => Ok(Dynamic::from_ast(&Bool::from_bool(*b))),
            CompiledExpr::Int(n) => Ok(Dynamic::from_ast(&Int::from_i64(*n))),
            CompiledExpr::String(s) => {
                let id = self.layout.string_id(s).ok_or_else(|| {
                    SymbolicError::Encoding(format!("string literal not in table: {:?}", s))
                })?;
                Ok(Dynamic::from_ast(&Int::from_i64(id)))
            }

            // === Variables ===
            CompiledExpr::Var(idx) => self.encode_var(*idx, self.current_step),
            CompiledExpr::PrimedVar(idx) => self.encode_var(*idx, self.next_step),
            CompiledExpr::Const(idx) => self.encode_const(*idx),
            CompiledExpr::Local(idx) => {
                let depth = self.locals.len();
                if *idx < depth {
                    Ok(self.locals[depth - 1 - *idx].clone())
                } else {
                    Err(SymbolicError::Encoding(format!(
                        "local index {} out of range (depth {})",
                        idx, depth
                    )))
                }
            }
            CompiledExpr::Param(idx) => {
                if *idx < self.params.len() {
                    Ok(self.params[*idx].clone())
                } else {
                    Err(SymbolicError::Encoding(format!(
                        "param index {} out of range",
                        idx
                    )))
                }
            }

            // === Binary operations ===
            CompiledExpr::Binary { op, left, right } => self.encode_binary(*op, left, right),

            // === Unary operations ===
            CompiledExpr::Unary { op, operand } => self.encode_unary(*op, operand),

            // === Conditional ===
            CompiledExpr::If {
                cond,
                then_branch,
                else_branch,
            } => {
                let c = self.encode_bool(cond)?;
                let t = self.encode(then_branch)?;
                let e = self.encode(else_branch)?;
                if let (Some(ti), Some(ei)) = (t.as_int(), e.as_int()) {
                    Ok(Dynamic::from_ast(&c.ite(&ti, &ei)))
                } else if let (Some(tb), Some(eb)) = (t.as_bool(), e.as_bool()) {
                    Ok(Dynamic::from_ast(&c.ite(&tb, &eb)))
                } else {
                    Err(SymbolicError::Encoding(
                        "if-then-else branches have incompatible types".into(),
                    ))
                }
            }

            // === Let binding ===
            CompiledExpr::Let { value, body } => {
                // Try to encode the value as a scalar
                match self.encode(value) {
                    Ok(val) => {
                        self.locals.push(val);
                        let result = self.encode(body);
                        self.locals.pop();
                        result
                    }
                    Err(_) => {
                        // Value might be a compound expression (e.g., d[k] where d is Dict[Range, Seq]).
                        // Track as a compound local.
                        if let Some((var_idx, step, key_z3)) =
                            self.try_resolve_compound_local(value)
                        {
                            // Push a dummy value to maintain local index alignment
                            let abs_depth = self.locals.len();
                            self.locals.push(Dynamic::from_ast(&Int::from_i64(0)));
                            self.compound_locals
                                .push((abs_depth, var_idx, step, key_z3));
                            let result = self.encode(body);
                            self.compound_locals.pop();
                            self.locals.pop();
                            result
                        } else if let CompiledExpr::Var(var_idx)
                        | CompiledExpr::PrimedVar(var_idx) = value.as_ref()
                        {
                            // Bare compound variable alias (e.g., inlined function arg)
                            let step = if matches!(value.as_ref(), CompiledExpr::Var(_)) {
                                self.current_step
                            } else {
                                self.next_step
                            };
                            let entry = &self.layout.entries[*var_idx];
                            if entry.kind.z3_var_count() > 1 {
                                let abs_depth = self.locals.len();
                                self.locals.push(Dynamic::from_ast(&Int::from_i64(0)));
                                self.whole_var_locals.push((abs_depth, *var_idx, step));
                                let result = self.encode(body);
                                self.whole_var_locals.pop();
                                self.locals.pop();
                                return result;
                            }
                            // Re-raise the original error
                            self.encode(value).and_then(|_| unreachable!())
                        } else {
                            // Re-raise the original error
                            self.encode(value).and_then(|_| unreachable!())
                        }
                    }
                }
            }

            // === Quantifiers ===
            CompiledExpr::Forall { domain, body } => self.encode_quantifier(domain, body, true),
            CompiledExpr::Exists { domain, body } => self.encode_quantifier(domain, body, false),

            // === Dict/Fn operations ===
            CompiledExpr::Index { base, index } => self.encode_index(base, index),
            CompiledExpr::FnUpdate { .. } => Err(SymbolicError::Encoding(
                "FnUpdate should be handled at the effect level".into(),
            )),
            CompiledExpr::FnLit { .. } => Err(SymbolicError::Encoding(
                "FnLit should be handled at the init/effect level".into(),
            )),
            CompiledExpr::DictLit(_) => Err(SymbolicError::Encoding(
                "DictLit should be handled at the init/effect level".into(),
            )),

            // === Set operations (handled as expressions for equality/assignment) ===
            CompiledExpr::SetLit(_) | CompiledExpr::SetComprehension { .. } => {
                Err(SymbolicError::Encoding(
                    "set expression used in non-set context (use in equality, membership, or len)"
                        .into(),
                ))
            }

            // === Len ===
            CompiledExpr::Len(inner) => self.encode_len(inner),

            // === Frame ===
            CompiledExpr::Unchanged(var_idx) => self.encode_unchanged(*var_idx),

            // === Range ===
            CompiledExpr::Range { .. } => Err(SymbolicError::Encoding(
                "Range expression used outside quantifier context".into(),
            )),

            // === Seq operations ===
            CompiledExpr::SeqHead(inner) => self.encode_seq_head(inner),
            CompiledExpr::SeqTail(_) => Err(SymbolicError::Encoding(
                "SeqTail should be handled at the effect level".into(),
            )),
            CompiledExpr::SeqLit(_) => Err(SymbolicError::Encoding(
                "SeqLit should be handled at the init/effect level".into(),
            )),
            CompiledExpr::Slice { .. } => Err(SymbolicError::Encoding(
                "Slice should be handled at the effect level".into(),
            )),

            // === Fix ===
            CompiledExpr::Fix {
                domain: Some(domain),
                predicate,
            } => self.encode_choose(domain, predicate),
            CompiledExpr::Fix { domain: None, .. } => Err(SymbolicError::Encoding(
                "fix without domain not supported in symbolic mode".into(),
            )),

            // === Keys/Values (set-returning — error in scalar context) ===
            CompiledExpr::Keys(_) => Err(SymbolicError::Encoding(
                "keys() returns a set; use in set context (in, len, quantifier)".into(),
            )),
            CompiledExpr::Values(_) => Err(SymbolicError::Encoding(
                "values() returns a set; use in set context (in, len, quantifier)".into(),
            )),

            // === Unsupported ===
            CompiledExpr::Powerset(_) => Err(SymbolicError::Unsupported(
                "powerset() as a value; use in quantifier context (any Q in powerset(S): ...)"
                    .into(),
            )),
            CompiledExpr::BigUnion(_) => Err(SymbolicError::Unsupported(
                "union_all requires set-of-sets encoding".into(),
            )),
            CompiledExpr::Changes(_) => Err(SymbolicError::Unsupported(
                "changes() is a temporal operator".into(),
            )),
            CompiledExpr::Enabled(_) => Err(SymbolicError::Unsupported(
                "enabled() is a temporal operator".into(),
            )),
            CompiledExpr::ActionCall { .. } => Err(SymbolicError::Unsupported(
                "action calls in expressions not supported".into(),
            )),
            CompiledExpr::Call { .. } => Err(SymbolicError::Unsupported(
                "function calls should be inlined by the compiler; this is a bug".into(),
            )),
            CompiledExpr::Field { base, field } => self.encode_field_access(base, field),
            CompiledExpr::RecordUpdate { .. } => Err(SymbolicError::Encoding(
                "RecordUpdate should be handled at the effect level".into(),
            )),
            CompiledExpr::TupleLit(_) => Err(SymbolicError::Encoding(
                "TupleLit should be handled at the init/effect level".into(),
            )),
        }
    }

    fn encode_var(&self, specl_var_idx: usize, step: usize) -> SymbolicResult<Dynamic> {
        let entry = &self.layout.entries[specl_var_idx];
        match &entry.kind {
            VarKind::Bool | VarKind::Int { .. } => {
                Ok(self.step_vars[step][specl_var_idx][0].clone())
            }
            VarKind::ExplodedDict { .. }
            | VarKind::ExplodedSet { .. }
            | VarKind::ExplodedSeq { .. }
            | VarKind::ExplodedOption { .. }
            | VarKind::ExplodedTuple { .. }
            | VarKind::ExplodedRecord { .. } => Err(SymbolicError::Encoding(format!(
                "compound variable '{}' accessed directly (use field/option operator)",
                entry.name
            ))),
        }
    }

    fn encode_field_access(&mut self, base: &CompiledExpr, field: &str) -> SymbolicResult<Dynamic> {
        let (specl_var_idx, step) = self.extract_var_step(base)?;
        let entry = &self.layout.entries[specl_var_idx];
        let z3_vars = &self.step_vars[step][specl_var_idx];

        match &entry.kind {
            VarKind::ExplodedTuple { element_kinds } => {
                let idx: usize = field.parse().map_err(|_| {
                    SymbolicError::Encoding(format!("invalid tuple field: {}", field))
                })?;
                if idx >= element_kinds.len() {
                    return Err(SymbolicError::Encoding(format!(
                        "tuple index {} out of bounds (tuple has {} elements)",
                        idx,
                        element_kinds.len()
                    )));
                }
                let mut offset = 0;
                for kind in &element_kinds[..idx] {
                    offset += kind.z3_var_count();
                }
                let stride = element_kinds[idx].z3_var_count();
                if stride == 1 {
                    Ok(z3_vars[offset].clone())
                } else {
                    Err(SymbolicError::Encoding(
                        "tuple element is compound; use nested field access".into(),
                    ))
                }
            }
            VarKind::ExplodedRecord {
                field_names,
                field_kinds,
            } => {
                let field_idx = field_names.iter().position(|n| n == field).ok_or_else(|| {
                    SymbolicError::Encoding(format!(
                        "unknown record field '{}' (available: {:?})",
                        field, field_names
                    ))
                })?;
                let mut offset = 0;
                for kind in &field_kinds[..field_idx] {
                    offset += kind.z3_var_count();
                }
                let stride = field_kinds[field_idx].z3_var_count();
                if stride == 1 {
                    Ok(z3_vars[offset].clone())
                } else {
                    Err(SymbolicError::Encoding(
                        "record field is compound; use nested field access".into(),
                    ))
                }
            }
            _ => Err(SymbolicError::Encoding(format!(
                "field access on non-record/tuple variable '{}'",
                entry.name
            ))),
        }
    }

    fn encode_const(&self, const_idx: usize) -> SymbolicResult<Dynamic> {
        use specl_eval::VK;
        let val = &self.consts[const_idx];
        match val.kind() {
            VK::Bool(b) => Ok(Dynamic::from_ast(&Bool::from_bool(b))),
            VK::Int(n) => Ok(Dynamic::from_ast(&Int::from_i64(n))),
            VK::String(s) => {
                let id = self.layout.string_id(s).ok_or_else(|| {
                    SymbolicError::Encoding(format!("string constant not in table: {:?}", s))
                })?;
                Ok(Dynamic::from_ast(&Int::from_i64(id)))
            }
            _ => Err(SymbolicError::Unsupported(format!(
                "constant type: {:?}",
                val
            ))),
        }
    }

    fn encode_binary(
        &mut self,
        op: BinOp,
        left: &CompiledExpr,
        right: &CompiledExpr,
    ) -> SymbolicResult<Dynamic> {
        match op {
            // Logical
            BinOp::And => {
                let l = self.encode_bool(left)?;
                let r = self.encode_bool(right)?;
                Ok(Dynamic::from_ast(&Bool::and(&[l, r])))
            }
            BinOp::Or => {
                let l = self.encode_bool(left)?;
                let r = self.encode_bool(right)?;
                Ok(Dynamic::from_ast(&Bool::or(&[l, r])))
            }
            BinOp::Implies => {
                let l = self.encode_bool(left)?;
                let r = self.encode_bool(right)?;
                Ok(Dynamic::from_ast(&l.implies(&r)))
            }
            BinOp::Iff => {
                let l = self.encode_bool(left)?;
                let r = self.encode_bool(right)?;
                Ok(Dynamic::from_ast(&l.iff(&r)))
            }

            // Comparison
            BinOp::Eq => self.encode_eq(left, right),
            BinOp::Ne => {
                let eq = self.encode_eq(left, right)?;
                let eq_bool = eq.as_bool().unwrap();
                Ok(Dynamic::from_ast(&eq_bool.not()))
            }
            BinOp::Lt => {
                let l = self.encode_int(left)?;
                let r = self.encode_int(right)?;
                Ok(Dynamic::from_ast(&l.lt(&r)))
            }
            BinOp::Le => {
                let l = self.encode_int(left)?;
                let r = self.encode_int(right)?;
                Ok(Dynamic::from_ast(&l.le(&r)))
            }
            BinOp::Gt => {
                let l = self.encode_int(left)?;
                let r = self.encode_int(right)?;
                Ok(Dynamic::from_ast(&l.gt(&r)))
            }
            BinOp::Ge => {
                let l = self.encode_int(left)?;
                let r = self.encode_int(right)?;
                Ok(Dynamic::from_ast(&l.ge(&r)))
            }

            // Arithmetic
            BinOp::Add => {
                let l = self.encode_int(left)?;
                let r = self.encode_int(right)?;
                Ok(Dynamic::from_ast(&Int::add(&[l, r])))
            }
            BinOp::Sub => {
                let l = self.encode_int(left)?;
                let r = self.encode_int(right)?;
                Ok(Dynamic::from_ast(&Int::sub(&[l, r])))
            }
            BinOp::Mul => {
                let l = self.encode_int(left)?;
                let r = self.encode_int(right)?;
                Ok(Dynamic::from_ast(&Int::mul(&[l, r])))
            }
            BinOp::Div => {
                let l = self.encode_int(left)?;
                let r = self.encode_int(right)?;
                Ok(Dynamic::from_ast(&l.div(&r)))
            }
            BinOp::Mod => {
                let l = self.encode_int(left)?;
                let r = self.encode_int(right)?;
                Ok(Dynamic::from_ast(&l.modulo(&r)))
            }

            // Set membership
            BinOp::In => self.encode_set_membership(left, right, false),
            BinOp::NotIn => self.encode_set_membership(left, right, true),

            // Set operations on ExplodedSet
            BinOp::Union | BinOp::Intersect | BinOp::Diff => {
                // These produce a set — cannot be used as a scalar expression.
                // They are handled at the effect/equality level via encode_as_set.
                Err(SymbolicError::Encoding(format!(
                    "set operation {:?} used in scalar context (handled in effects/equality)",
                    op
                )))
            }
            BinOp::SubsetOf => {
                // subset_of returns a Bool: for all elements, left[i] implies right[i]
                let (lo, hi) = self.infer_set_bounds(left, right)?;
                let l_set = self.encode_as_set(left, lo, hi)?;
                let r_set = self.encode_as_set(right, lo, hi)?;
                let mut conjuncts = Vec::new();
                for (lb, rb) in l_set.iter().zip(r_set.iter()) {
                    conjuncts.push(lb.implies(rb));
                }
                Ok(Dynamic::from_ast(&Bool::and(&conjuncts)))
            }

            BinOp::Concat => Err(SymbolicError::Encoding(
                "sequence concat (++) should be handled at the effect level".into(),
            )),
        }
    }

    fn encode_eq(&mut self, left: &CompiledExpr, right: &CompiledExpr) -> SymbolicResult<Dynamic> {
        // Check if either side is a set expression — use per-element equality
        if self.is_set_expr(left) || self.is_set_expr(right) {
            let (lo, hi) = self.infer_set_bounds(left, right)?;
            let l_set = self.encode_as_set(left, lo, hi)?;
            let r_set = self.encode_as_set(right, lo, hi)?;
            let mut conjuncts = Vec::new();
            for (lb, rb) in l_set.iter().zip(r_set.iter()) {
                conjuncts.push(lb.eq(rb));
            }
            return Ok(Dynamic::from_ast(&Bool::and(&conjuncts)));
        }

        // Check if either side is a seq expression — compare len + elements
        if self.is_seq_expr(left) || self.is_seq_expr(right) {
            return self.encode_seq_eq(left, right);
        }

        let l = self.encode(left)?;
        let r = self.encode(right)?;
        if let (Some(li), Some(ri)) = (l.as_int(), r.as_int()) {
            Ok(Dynamic::from_ast(&li.eq(&ri)))
        } else if let (Some(lb), Some(rb)) = (l.as_bool(), r.as_bool()) {
            Ok(Dynamic::from_ast(&lb.eq(&rb)))
        } else {
            Err(SymbolicError::Encoding(
                "equality between incompatible types".into(),
            ))
        }
    }

    fn encode_unary(&mut self, op: UnaryOp, operand: &CompiledExpr) -> SymbolicResult<Dynamic> {
        match op {
            UnaryOp::Not => {
                let v = self.encode_bool(operand)?;
                Ok(Dynamic::from_ast(&v.not()))
            }
            UnaryOp::Neg => {
                let v = self.encode_int(operand)?;
                Ok(Dynamic::from_ast(&v.unary_minus()))
            }
        }
    }

    fn encode_quantifier(
        &mut self,
        domain: &CompiledExpr,
        body: &CompiledExpr,
        is_forall: bool,
    ) -> SymbolicResult<Dynamic> {
        // Powerset domain: enumerate all subsets
        if let CompiledExpr::Powerset(inner) = domain {
            return self.encode_powerset_quantifier(inner, body, is_forall);
        }

        // Set local domain (e.g., `all a in Q` where Q is a powerset-bound local)
        if let CompiledExpr::Local(idx) = domain {
            if let Some(members) = self.resolve_set_local(*idx) {
                let members = members.clone();
                return self.encode_set_local_quantifier(&members, body, is_forall);
            }
        }

        let (lo, hi) = self.extract_range(domain)?;
        let mut conjuncts = Vec::new();

        for val in lo..=hi {
            let z3_val = Dynamic::from_ast(&Int::from_i64(val));
            self.locals.push(z3_val);
            let body_encoded = self.encode_bool(body)?;
            self.locals.pop();
            conjuncts.push(body_encoded);
        }

        if is_forall {
            Ok(Dynamic::from_ast(&Bool::and(&conjuncts)))
        } else {
            Ok(Dynamic::from_ast(&Bool::or(&conjuncts)))
        }
    }

    fn encode_powerset_quantifier(
        &mut self,
        inner: &CompiledExpr,
        body: &CompiledExpr,
        is_forall: bool,
    ) -> SymbolicResult<Dynamic> {
        let (lo, hi) = self.extract_range(inner)?;
        let n = (hi - lo + 1) as u32;
        if n > 20 {
            return Err(SymbolicError::Encoding(format!(
                "powerset too large: 2^{} subsets",
                n
            )));
        }
        let num_subsets = 1u32 << n;
        let mut results = Vec::new();

        for mask in 0..num_subsets {
            let members: Vec<i64> = (0..n)
                .filter(|bit| mask & (1 << bit) != 0)
                .map(|bit| lo + bit as i64)
                .collect();

            // Push a dummy local for the set variable
            let abs_depth = self.locals.len();
            self.locals.push(Dynamic::from_ast(&Int::from_i64(0)));
            self.set_locals.push((abs_depth, members));
            let result = self.encode_bool(body)?;
            self.set_locals.pop();
            self.locals.pop();
            results.push(result);
        }

        if is_forall {
            Ok(Dynamic::from_ast(&Bool::and(&results)))
        } else {
            Ok(Dynamic::from_ast(&Bool::or(&results)))
        }
    }

    fn encode_set_local_quantifier(
        &mut self,
        members: &[i64],
        body: &CompiledExpr,
        is_forall: bool,
    ) -> SymbolicResult<Dynamic> {
        if members.is_empty() {
            return Ok(Dynamic::from_ast(&Bool::from_bool(is_forall)));
        }
        let mut results = Vec::new();
        for &val in members {
            let z3_val = Dynamic::from_ast(&Int::from_i64(val));
            self.locals.push(z3_val);
            let result = self.encode_bool(body)?;
            self.locals.pop();
            results.push(result);
        }
        if is_forall {
            Ok(Dynamic::from_ast(&Bool::and(&results)))
        } else {
            Ok(Dynamic::from_ast(&Bool::or(&results)))
        }
    }

    /// Resolve a Local(idx) as a set local, returning its concrete members.
    fn resolve_set_local(&self, local_idx: usize) -> Option<&Vec<i64>> {
        let depth = self.locals.len();
        let abs_idx = depth - 1 - local_idx;
        for (abs_depth, members) in self.set_locals.iter().rev() {
            if *abs_depth == abs_idx {
                return Some(members);
            }
        }
        None
    }

    fn encode_choose(
        &mut self,
        domain: &CompiledExpr,
        predicate: &CompiledExpr,
    ) -> SymbolicResult<Dynamic> {
        let values = self.resolve_domain_values(domain)?;
        // Build ITE chain: if P(first) then first else if P(second) then second else ... else first
        let fallback = *values
            .first()
            .ok_or_else(|| SymbolicError::Encoding("empty domain in choose".into()))?;
        let mut result = Dynamic::from_ast(&Int::from_i64(fallback));
        for val in values.into_iter().rev() {
            let z3_val = Dynamic::from_ast(&Int::from_i64(val));
            self.locals.push(z3_val);
            let pred = self.encode_bool(predicate)?;
            self.locals.pop();
            let val_int = Int::from_i64(val);
            if let Some(ri) = result.as_int() {
                result = Dynamic::from_ast(&pred.ite(&val_int, &ri));
            }
        }
        Ok(result)
    }

    fn encode_index(
        &mut self,
        base: &CompiledExpr,
        index: &CompiledExpr,
    ) -> SymbolicResult<Dynamic> {
        // Flatten index chain: d[k1][k2][k3] → (base_expr, [k1, k2, k3])
        let mut keys: Vec<&CompiledExpr> = vec![index];
        let mut current: &CompiledExpr = base;
        while let CompiledExpr::Index {
            base: inner,
            index: inner_key,
        } = current
        {
            keys.push(inner_key.as_ref());
            current = inner.as_ref();
        }
        keys.reverse();

        // Handle compound Local(n)[keys...]: local is bound to a dict slot
        if let CompiledExpr::Local(local_idx) = current {
            if let Some((var_idx, step, key_z3)) = self
                .resolve_compound_local(*local_idx)
                .map(|(v, s, k)| (*v, *s, k.clone()))
            {
                return self.encode_compound_local_chain(var_idx, step, &key_z3, &keys);
            }
            // Whole-var alias: redirect to the original compound variable
            if let Some((var_idx, step)) = self.resolve_whole_var_local(*local_idx) {
                let entry = &self.layout.entries[var_idx];
                let z3_vars = &self.step_vars[step][var_idx];
                return self.resolve_index_chain(&entry.kind, z3_vars, &keys);
            }
        }

        let (specl_var_idx, step) = self.extract_var_step(current)?;
        let entry = &self.layout.entries[specl_var_idx];
        let z3_vars = &self.step_vars[step][specl_var_idx];
        self.resolve_index_chain(&entry.kind, z3_vars, &keys)
    }

    /// Recursively resolve an index chain on a compound VarKind.
    fn resolve_index_chain(
        &mut self,
        kind: &VarKind,
        vars: &[Dynamic],
        keys: &[&CompiledExpr],
    ) -> SymbolicResult<Dynamic> {
        if keys.is_empty() {
            return if vars.len() == 1 {
                Ok(vars[0].clone())
            } else {
                Err(SymbolicError::Encoding(
                    "index chain incomplete: compound value requires more indices".into(),
                ))
            };
        }

        match kind {
            VarKind::ExplodedDict {
                key_lo,
                key_hi,
                value_kind,
            } => {
                let stride = value_kind.z3_var_count();
                let key_lo = *key_lo;
                let key_hi = *key_hi;
                let remaining = &keys[1..];

                // Last key and scalar value: simple access
                if remaining.is_empty() && stride == 1 {
                    if let Some(concrete_key) = self.try_concrete_int(keys[0]) {
                        let offset = (concrete_key - key_lo) as usize;
                        return if offset < vars.len() {
                            Ok(vars[offset].clone())
                        } else {
                            Err(SymbolicError::Encoding(format!(
                                "dict key {} out of range [{}, {}]",
                                concrete_key, key_lo, key_hi
                            )))
                        };
                    } else {
                        let key_z3 = self.encode_int(keys[0])?;
                        return self.build_ite_chain(&key_z3, vars, key_lo);
                    }
                }

                // Compound value needs more indices
                if remaining.is_empty() {
                    return Err(SymbolicError::Encoding(
                        "dict has compound values; use nested index (d[k1][k2]) or len(d[k])"
                            .into(),
                    ));
                }

                // Descend into value_kind with remaining keys
                if let Some(concrete_key) = self.try_concrete_int(keys[0]) {
                    let offset = (concrete_key - key_lo) as usize * stride;
                    let slot_vars = &vars[offset..offset + stride];
                    self.resolve_index_chain(value_kind, slot_vars, remaining)
                } else {
                    let key_z3 = self.encode_int(keys[0])?;
                    let num_keys = (key_hi - key_lo + 1) as usize;
                    let mut result: Option<Dynamic> = None;
                    for k in (0..num_keys).rev() {
                        let offset = k * stride;
                        let slot_vars = &vars[offset..offset + stride];
                        let val = self.resolve_index_chain(value_kind, slot_vars, remaining)?;
                        let k_z3 = Int::from_i64(key_lo + k as i64);
                        let cond = key_z3.eq(&k_z3);
                        result = Some(match result {
                            None => val,
                            Some(prev) => {
                                if let (Some(vi), Some(pi)) = (val.as_int(), prev.as_int()) {
                                    Dynamic::from_ast(&cond.ite(&vi, &pi))
                                } else if let (Some(vb), Some(pb)) = (val.as_bool(), prev.as_bool())
                                {
                                    Dynamic::from_ast(&cond.ite(&vb, &pb))
                                } else {
                                    prev
                                }
                            }
                        });
                    }
                    result
                        .ok_or_else(|| SymbolicError::Encoding("empty dict for index chain".into()))
                }
            }
            VarKind::ExplodedSeq { max_len, .. } => {
                if keys.len() != 1 {
                    return Err(SymbolicError::Encoding(
                        "cannot index deeper into sequence elements".into(),
                    ));
                }
                let max_len = *max_len;
                let elem_vars = &vars[1..1 + max_len];
                if let Some(concrete_idx) = self.try_concrete_int(keys[0]) {
                    let idx = concrete_idx as usize;
                    if idx < max_len {
                        Ok(elem_vars[idx].clone())
                    } else {
                        Err(SymbolicError::Encoding(format!(
                            "seq index {} out of bounds (max_len {})",
                            concrete_idx, max_len
                        )))
                    }
                } else {
                    let idx_z3 = self.encode_int(keys[0])?;
                    self.build_ite_chain(&idx_z3, elem_vars, 0)
                }
            }
            VarKind::ExplodedSet { lo, .. } => {
                if keys.len() != 1 {
                    return Err(SymbolicError::Encoding(
                        "cannot index deeper into set elements".into(),
                    ));
                }
                let lo = *lo;
                if let Some(concrete_key) = self.try_concrete_int(keys[0]) {
                    let offset = (concrete_key - lo) as usize;
                    if offset < vars.len() {
                        Ok(vars[offset].clone())
                    } else {
                        Ok(Dynamic::from_ast(&Bool::from_bool(false)))
                    }
                } else {
                    let key_z3 = self.encode_int(keys[0])?;
                    self.build_ite_chain(&key_z3, vars, lo)
                }
            }
            VarKind::Bool | VarKind::Int { .. } => {
                Err(SymbolicError::Encoding("index on scalar variable".into()))
            }
            VarKind::ExplodedOption { .. } => Err(SymbolicError::Encoding(
                "cannot index into Option (use field access)".into(),
            )),
            VarKind::ExplodedTuple { .. } => Err(SymbolicError::Encoding(
                "cannot index into Tuple (use field access, e.g. t.0)".into(),
            )),
            VarKind::ExplodedRecord { .. } => Err(SymbolicError::Encoding(
                "cannot index into Record (use field access, e.g. r.field)".into(),
            )),
        }
    }

    /// Resolve index chain for a compound local (d[outer_key][keys...]).
    fn encode_compound_local_chain(
        &mut self,
        var_idx: usize,
        step: usize,
        outer_key_z3: &Int,
        keys: &[&CompiledExpr],
    ) -> SymbolicResult<Dynamic> {
        let entry = &self.layout.entries[var_idx];
        let (key_lo, key_hi, value_kind) = match &entry.kind {
            VarKind::ExplodedDict {
                key_lo,
                key_hi,
                value_kind,
            } => (*key_lo, *key_hi, value_kind.as_ref()),
            _ => return Err(SymbolicError::Encoding("compound local on non-dict".into())),
        };
        let stride = value_kind.z3_var_count();
        let z3_vars = &self.step_vars[step][var_idx];
        let num_keys = (key_hi - key_lo + 1) as usize;
        let mut result: Option<Dynamic> = None;
        for k in (0..num_keys).rev() {
            let offset = k * stride;
            let slot_vars = &z3_vars[offset..offset + stride];
            let val = self.resolve_index_chain(value_kind, slot_vars, keys)?;
            let k_z3 = Int::from_i64(key_lo + k as i64);
            let cond = outer_key_z3.eq(&k_z3);
            result = Some(match result {
                None => val,
                Some(prev) => {
                    if let (Some(vi), Some(pi)) = (val.as_int(), prev.as_int()) {
                        Dynamic::from_ast(&cond.ite(&vi, &pi))
                    } else if let (Some(vb), Some(pb)) = (val.as_bool(), prev.as_bool()) {
                        Dynamic::from_ast(&cond.ite(&vb, &pb))
                    } else {
                        prev
                    }
                }
            });
        }
        result.ok_or_else(|| SymbolicError::Encoding("empty compound local".into()))
    }

    /// Compute len of a VarKind from its Z3 vars.
    fn len_of_kind(&self, kind: &VarKind, vars: &[Dynamic]) -> SymbolicResult<Dynamic> {
        match kind {
            VarKind::ExplodedSeq { .. } => Ok(vars[0].clone()),
            VarKind::ExplodedSet { .. } => {
                let one = Int::from_i64(1);
                let zero = Int::from_i64(0);
                let terms: Vec<Int> = vars
                    .iter()
                    .map(|v| v.as_bool().unwrap().ite(&one, &zero))
                    .collect();
                Ok(Dynamic::from_ast(&Int::add(&terms)))
            }
            VarKind::ExplodedDict { key_lo, key_hi, .. } => {
                Ok(Dynamic::from_ast(&Int::from_i64(key_hi - key_lo + 1)))
            }
            _ => Err(SymbolicError::Encoding("len on scalar".into())),
        }
    }

    /// Recursively resolve len(d[k1][k2]...) for nested compounds.
    fn resolve_nested_len(
        &mut self,
        kind: &VarKind,
        vars: &[Dynamic],
        keys: &[&CompiledExpr],
    ) -> SymbolicResult<Dynamic> {
        if keys.is_empty() {
            return self.len_of_kind(kind, vars);
        }

        match kind {
            VarKind::ExplodedDict {
                key_lo,
                key_hi,
                value_kind,
            } => {
                let stride = value_kind.z3_var_count();
                let key_lo = *key_lo;
                let key_hi = *key_hi;
                let remaining = &keys[1..];

                if let Some(concrete_key) = self.try_concrete_int(keys[0]) {
                    let offset = (concrete_key - key_lo) as usize * stride;
                    let slot_vars = &vars[offset..offset + stride];
                    if remaining.is_empty() {
                        self.len_of_kind(value_kind, slot_vars)
                    } else {
                        self.resolve_nested_len(value_kind, slot_vars, remaining)
                    }
                } else {
                    let key_z3 = self.encode_int(keys[0])?;
                    let num_keys = (key_hi - key_lo + 1) as usize;
                    let mut len_vals = Vec::new();
                    for k in 0..num_keys {
                        let offset = k * stride;
                        let slot_vars = &vars[offset..offset + stride];
                        let len = if remaining.is_empty() {
                            self.len_of_kind(value_kind, slot_vars)?
                        } else {
                            self.resolve_nested_len(value_kind, slot_vars, remaining)?
                        };
                        len_vals.push(len);
                    }
                    self.build_ite_chain(&key_z3, &len_vals, key_lo)
                }
            }
            _ => Err(SymbolicError::Encoding(
                "nested len on non-dict kind".into(),
            )),
        }
    }

    fn encode_len(&mut self, inner: &CompiledExpr) -> SymbolicResult<Dynamic> {
        if let CompiledExpr::SetComprehension {
            element: _,
            domain,
            filter,
        } = inner
        {
            let values = self.resolve_domain_values(domain)?;
            let one = Int::from_i64(1);
            let zero = Int::from_i64(0);
            let mut sum_terms = Vec::new();

            for val in values {
                let z3_val = Dynamic::from_ast(&Int::from_i64(val));
                self.locals.push(z3_val);
                let included = if let Some(f) = filter {
                    self.encode_bool(f)?
                } else {
                    Bool::from_bool(true)
                };
                self.locals.pop();
                sum_terms.push(included.ite(&one, &zero));
            }

            if sum_terms.is_empty() {
                Ok(Dynamic::from_ast(&Int::from_i64(0)))
            } else {
                Ok(Dynamic::from_ast(&Int::add(&sum_terms)))
            }
        } else {
            match inner {
                CompiledExpr::Var(idx) | CompiledExpr::PrimedVar(idx) => {
                    let step = match inner {
                        CompiledExpr::Var(_) => self.current_step,
                        _ => self.next_step,
                    };
                    let entry = &self.layout.entries[*idx];
                    match &entry.kind {
                        VarKind::ExplodedSet { .. } => {
                            let z3_vars = &self.step_vars[step][*idx];
                            let one = Int::from_i64(1);
                            let zero = Int::from_i64(0);
                            let terms: Vec<Int> = z3_vars
                                .iter()
                                .map(|v| v.as_bool().unwrap().ite(&one, &zero))
                                .collect();
                            Ok(Dynamic::from_ast(&Int::add(&terms)))
                        }
                        VarKind::ExplodedSeq { .. } => {
                            // len is the first var (offset 0)
                            Ok(self.step_vars[step][*idx][0].clone())
                        }
                        _ => Err(SymbolicError::Unsupported(
                            "len() on non-set/seq variable".into(),
                        )),
                    }
                }
                // len(d[k]) or len(d[k1][k2]) for nested compounds
                CompiledExpr::Index { .. } => {
                    let mut keys: Vec<&CompiledExpr> = Vec::new();
                    let mut cur = inner;
                    while let CompiledExpr::Index {
                        base: ib,
                        index: ik,
                    } = cur
                    {
                        keys.push(ik.as_ref());
                        cur = ib.as_ref();
                    }
                    keys.reverse();

                    // Handle compound local len
                    if let CompiledExpr::Local(local_idx) = cur {
                        if let Some((var_idx, step, key_z3)) = self
                            .resolve_compound_local(*local_idx)
                            .map(|(v, s, k)| (*v, *s, k.clone()))
                        {
                            return self
                                .encode_compound_local_nested_len(var_idx, step, &key_z3, &keys);
                        }
                    }

                    let (var_idx, step) = self.extract_var_step(cur)?;
                    let entry = &self.layout.entries[var_idx];
                    let z3_vars = &self.step_vars[step][var_idx];
                    self.resolve_nested_len(&entry.kind, z3_vars, &keys)
                }
                // len(Local(n)) for compound locals or set locals
                CompiledExpr::Local(idx) => {
                    if let Some((var_idx, step, key_z3)) = self
                        .resolve_compound_local(*idx)
                        .map(|(v, s, k)| (*v, *s, k.clone()))
                    {
                        self.encode_compound_local_nested_len(var_idx, step, &key_z3, &[])
                    } else if let Some(members) = self.resolve_set_local(*idx) {
                        Ok(Dynamic::from_ast(&Int::from_i64(members.len() as i64)))
                    } else {
                        Err(SymbolicError::Unsupported(
                            "len() on non-compound/non-set local".into(),
                        ))
                    }
                }
                // len(keys(d)) = number of keys in dict
                CompiledExpr::Keys(inner) => {
                    if let CompiledExpr::Var(idx) | CompiledExpr::PrimedVar(idx) = inner.as_ref() {
                        let entry = &self.layout.entries[*idx];
                        if let VarKind::ExplodedDict { key_lo, key_hi, .. } = &entry.kind {
                            return Ok(Dynamic::from_ast(&Int::from_i64(key_hi - key_lo + 1)));
                        }
                    }
                    Err(SymbolicError::Encoding(
                        "len(keys()) requires a dict variable".into(),
                    ))
                }
                _ => {
                    // Try encoding as a set expression
                    if self.is_set_expr(inner) {
                        if let Some((lo, hi)) = self.try_set_bounds(inner) {
                            let flags = self.encode_as_set(inner, lo, hi)?;
                            let one = Int::from_i64(1);
                            let zero = Int::from_i64(0);
                            let terms: Vec<Int> =
                                flags.iter().map(|b| b.ite(&one, &zero)).collect();
                            return Ok(Dynamic::from_ast(&Int::add(&terms)));
                        }
                    }
                    Err(SymbolicError::Unsupported(
                        "len() on complex expression".into(),
                    ))
                }
            }
        }
    }

    fn encode_set_membership(
        &mut self,
        elem: &CompiledExpr,
        set: &CompiledExpr,
        negate: bool,
    ) -> SymbolicResult<Dynamic> {
        match set {
            CompiledExpr::Var(idx) | CompiledExpr::PrimedVar(idx) => {
                let step = match set {
                    CompiledExpr::Var(_) => self.current_step,
                    _ => self.next_step,
                };
                let entry = &self.layout.entries[*idx];
                if let VarKind::ExplodedSet { lo, .. } = &entry.kind {
                    let lo = *lo;
                    let z3_vars = &self.step_vars[step][*idx];
                    if let Some(concrete_elem) = self.try_concrete_int(elem) {
                        let offset = (concrete_elem - lo) as usize;
                        let result = if offset < z3_vars.len() {
                            z3_vars[offset].as_bool().unwrap()
                        } else {
                            Bool::from_bool(false)
                        };
                        let final_val = if negate { result.not() } else { result };
                        Ok(Dynamic::from_ast(&final_val))
                    } else {
                        let elem_z3 = self.encode_int(elem)?;
                        let result = self.build_ite_chain(&elem_z3, z3_vars, lo)?;
                        let result_bool = result.as_bool().unwrap();
                        let final_val = if negate {
                            result_bool.not()
                        } else {
                            result_bool
                        };
                        Ok(Dynamic::from_ast(&final_val))
                    }
                } else if let VarKind::ExplodedDict { key_lo, key_hi, .. } = &entry.kind {
                    let key_lo = *key_lo;
                    let key_hi = *key_hi;
                    let elem_z3 = self.encode_int(elem)?;
                    let lo_z3 = Int::from_i64(key_lo);
                    let hi_z3 = Int::from_i64(key_hi);
                    let in_range = Bool::and(&[elem_z3.ge(&lo_z3), elem_z3.le(&hi_z3)]);
                    let final_val = if negate { in_range.not() } else { in_range };
                    Ok(Dynamic::from_ast(&final_val))
                } else {
                    Err(SymbolicError::Encoding(format!(
                        "'in' on non-set/dict variable '{}'",
                        entry.name
                    )))
                }
            }
            CompiledExpr::Range { lo, hi } => {
                let elem_z3 = self.encode_int(elem)?;
                let lo_z3 = self.encode_int(lo)?;
                let hi_z3 = self.encode_int(hi)?;
                let in_range = Bool::and(&[elem_z3.ge(&lo_z3), elem_z3.le(&hi_z3)]);
                let final_val = if negate { in_range.not() } else { in_range };
                Ok(Dynamic::from_ast(&final_val))
            }
            CompiledExpr::SetComprehension {
                element: _,
                domain,
                filter,
            } => {
                let values = self.resolve_domain_values(domain)?;
                let elem_z3 = self.encode_int(elem)?;
                let eqs: Vec<Bool> = values
                    .iter()
                    .map(|v| elem_z3.eq(Int::from_i64(*v)))
                    .collect();
                let eq_refs: Vec<&Bool> = eqs.iter().collect();
                let in_domain = if eq_refs.is_empty() {
                    Bool::from_bool(false)
                } else {
                    Bool::or(&eq_refs)
                };

                let result = if let Some(f) = filter {
                    let elem_encoded = self.encode(elem)?;
                    self.locals.push(elem_encoded);
                    let pred = self.encode_bool(f)?;
                    self.locals.pop();
                    Bool::and(&[in_domain, pred])
                } else {
                    in_domain
                };

                let final_val = if negate { result.not() } else { result };
                Ok(Dynamic::from_ast(&final_val))
            }
            CompiledExpr::SetLit(elements) => {
                let elem_z3 = self.encode(elem)?;
                let mut disjuncts = Vec::new();
                for set_elem in elements {
                    let set_elem_z3 = self.encode(set_elem)?;
                    if let (Some(ei), Some(si)) = (elem_z3.as_int(), set_elem_z3.as_int()) {
                        disjuncts.push(ei.eq(&si));
                    } else if let (Some(eb), Some(sb)) = (elem_z3.as_bool(), set_elem_z3.as_bool())
                    {
                        disjuncts.push(eb.eq(&sb));
                    }
                }
                let result = if disjuncts.is_empty() {
                    Bool::from_bool(false)
                } else {
                    Bool::or(&disjuncts)
                };
                let final_val = if negate { result.not() } else { result };
                Ok(Dynamic::from_ast(&final_val))
            }
            // Set local membership (e.g., `a in Q` where Q is powerset-bound)
            CompiledExpr::Local(idx) => {
                if let Some(members) = self.resolve_set_local(*idx) {
                    let members = members.clone();
                    let elem_z3 = self.encode_int(elem)?;
                    let mut disjuncts = Vec::new();
                    for m in &members {
                        disjuncts.push(elem_z3.eq(Int::from_i64(*m)));
                    }
                    let result = if disjuncts.is_empty() {
                        Bool::from_bool(false)
                    } else {
                        Bool::or(&disjuncts)
                    };
                    let final_val = if negate { result.not() } else { result };
                    Ok(Dynamic::from_ast(&final_val))
                } else {
                    Err(SymbolicError::Encoding(format!(
                        "'in' with Local({}) is not a set local",
                        idx
                    )))
                }
            }
            // Powerset membership (e.g., `s in powerset({1,2,3})`)
            CompiledExpr::Powerset(inner) => {
                // A set is always in the powerset of its superset — encode as subset check
                let (lo, hi) = self.extract_range(inner)?;
                if let CompiledExpr::Var(var_idx) | CompiledExpr::PrimedVar(var_idx) = elem {
                    let step = match elem {
                        CompiledExpr::Var(_) => self.current_step,
                        _ => self.next_step,
                    };
                    let entry = &self.layout.entries[*var_idx];
                    if let VarKind::ExplodedSet {
                        lo: set_lo,
                        hi: set_hi,
                    } = &entry.kind
                    {
                        let z3_vars = &self.step_vars[step][*var_idx];
                        // s in powerset(lo..hi) iff all members of s are in lo..hi
                        // Since s is ExplodedSet over set_lo..set_hi, check that flags
                        // outside lo..hi are false
                        let mut constraints = Vec::new();
                        for (i, k) in (*set_lo..=*set_hi).enumerate() {
                            if k < lo || k > hi {
                                // This element is outside powerset range — must not be member
                                if let Some(b) = z3_vars[i].as_bool() {
                                    constraints.push(b.not());
                                }
                            }
                        }
                        let result = if constraints.is_empty() {
                            Bool::from_bool(true)
                        } else {
                            Bool::and(&constraints)
                        };
                        let final_val = if negate { result.not() } else { result };
                        return Ok(Dynamic::from_ast(&final_val));
                    }
                }
                // For set locals bound by outer powerset quantifier
                // `s in powerset(R)` where s is a set local is always true by construction
                if let CompiledExpr::Local(idx) = elem {
                    if self.resolve_set_local(*idx).is_some() {
                        let result = Bool::from_bool(!negate);
                        return Ok(Dynamic::from_ast(&result));
                    }
                }
                Err(SymbolicError::Encoding(
                    "'in' powerset: unsupported element expression".into(),
                ))
            }
            // keys(d): for ExplodedDict, keys is always the full range
            CompiledExpr::Keys(inner) => {
                if let CompiledExpr::Var(idx) | CompiledExpr::PrimedVar(idx) = inner.as_ref() {
                    let entry = &self.layout.entries[*idx];
                    if let VarKind::ExplodedDict { key_lo, key_hi, .. } = &entry.kind {
                        let elem_z3 = self.encode_int(elem)?;
                        let lo_z3 = Int::from_i64(*key_lo);
                        let hi_z3 = Int::from_i64(*key_hi);
                        let in_range = Bool::and(&[elem_z3.ge(&lo_z3), elem_z3.le(&hi_z3)]);
                        let final_val = if negate { in_range.not() } else { in_range };
                        return Ok(Dynamic::from_ast(&final_val));
                    }
                }
                Err(SymbolicError::Encoding(
                    "keys() requires a dict variable".into(),
                ))
            }
            // values(d): v in values(d) iff exists k in key_range: d[k] == v
            CompiledExpr::Values(inner) => {
                if let CompiledExpr::Var(idx) | CompiledExpr::PrimedVar(idx) = inner.as_ref() {
                    let step = match inner.as_ref() {
                        CompiledExpr::Var(_) => self.current_step,
                        _ => self.next_step,
                    };
                    let entry = &self.layout.entries[*idx];
                    if let VarKind::ExplodedDict {
                        key_lo,
                        key_hi,
                        value_kind,
                    } = &entry.kind
                    {
                        if value_kind.z3_var_count() == 1 {
                            let elem_z3 = self.encode(elem)?;
                            let z3_vars = &self.step_vars[step][*idx];
                            let mut disjuncts = Vec::new();
                            for (i, _k) in (*key_lo..=*key_hi).enumerate() {
                                if let (Some(ei), Some(vi)) =
                                    (elem_z3.as_int(), z3_vars[i].as_int())
                                {
                                    disjuncts.push(ei.eq(&vi));
                                } else if let (Some(eb), Some(vb)) =
                                    (elem_z3.as_bool(), z3_vars[i].as_bool())
                                {
                                    disjuncts.push(eb.eq(&vb));
                                }
                            }
                            let result = if disjuncts.is_empty() {
                                Bool::from_bool(false)
                            } else {
                                Bool::or(&disjuncts)
                            };
                            let final_val = if negate { result.not() } else { result };
                            return Ok(Dynamic::from_ast(&final_val));
                        }
                    }
                }
                Err(SymbolicError::Encoding(
                    "values() requires a simple-valued dict variable".into(),
                ))
            }
            // x in d[k] where d is Dict[Range, Set[Range]]
            CompiledExpr::Index { .. } => {
                let mut keys: Vec<&CompiledExpr> = Vec::new();
                let mut cur = set;
                while let CompiledExpr::Index {
                    base: ib,
                    index: ik,
                } = cur
                {
                    keys.push(ik.as_ref());
                    cur = ib.as_ref();
                }
                keys.reverse();

                let (var_idx, step) = self.extract_var_step(cur)?;
                let entry = &self.layout.entries[var_idx];
                let z3_vars = &self.step_vars[step][var_idx];

                // Walk the VarKind to find the Set slot
                let (set_vars, set_kind) = self.resolve_set_slot(&entry.kind, z3_vars, &keys)?;

                if let VarKind::ExplodedSet { lo, .. } = set_kind {
                    let lo = *lo;
                    if let Some(concrete_elem) = self.try_concrete_int(elem) {
                        let offset = (concrete_elem - lo) as usize;
                        let result = if offset < set_vars.len() {
                            set_vars[offset].as_bool().unwrap()
                        } else {
                            Bool::from_bool(false)
                        };
                        let final_val = if negate { result.not() } else { result };
                        Ok(Dynamic::from_ast(&final_val))
                    } else {
                        let elem_z3 = self.encode_int(elem)?;
                        let result = self.build_ite_chain(&elem_z3, set_vars, lo)?;
                        let result_bool = result.as_bool().unwrap();
                        let final_val = if negate {
                            result_bool.not()
                        } else {
                            result_bool
                        };
                        Ok(Dynamic::from_ast(&final_val))
                    }
                } else {
                    Err(SymbolicError::Encoding(
                        "'in' on nested index: inner value is not a set".into(),
                    ))
                }
            }
            _ => {
                // Try as a set expression with known bounds (union, intersect, etc.)
                if self.is_set_expr(set) {
                    if let Some((lo, hi)) = self.try_set_bounds(set) {
                        let flags = self.encode_as_set(set, lo, hi)?;
                        if let Some(concrete_elem) = self.try_concrete_int(elem) {
                            let offset = (concrete_elem - lo) as usize;
                            let result = if offset < flags.len() {
                                flags[offset].clone()
                            } else {
                                Bool::from_bool(false)
                            };
                            let final_val = if negate { result.not() } else { result };
                            return Ok(Dynamic::from_ast(&final_val));
                        } else {
                            let elem_z3 = self.encode_int(elem)?;
                            let z3_vars: Vec<Dynamic> =
                                flags.iter().map(|b| Dynamic::from_ast(b)).collect();
                            let result = self.build_ite_chain(&elem_z3, &z3_vars, lo)?;
                            let result_bool = result.as_bool().unwrap();
                            let final_val = if negate {
                                result_bool.not()
                            } else {
                                result_bool
                            };
                            return Ok(Dynamic::from_ast(&final_val));
                        }
                    }
                }
                Err(SymbolicError::Unsupported(format!(
                    "'in' operator with set expression: {:?}",
                    std::mem::discriminant(set)
                )))
            }
        }
    }

    pub fn encode_unchanged(&self, var_idx: usize) -> SymbolicResult<Dynamic> {
        let curr_vars = &self.step_vars[self.current_step][var_idx];
        let next_vars = &self.step_vars[self.next_step][var_idx];
        let mut eqs = Vec::new();
        for (c, n) in curr_vars.iter().zip(next_vars.iter()) {
            if let (Some(ci), Some(ni)) = (c.as_int(), n.as_int()) {
                eqs.push(ci.eq(&ni));
            } else if let (Some(cb), Some(nb)) = (c.as_bool(), n.as_bool()) {
                eqs.push(cb.eq(&nb));
            } else {
                return Err(SymbolicError::Encoding(
                    "unchanged: mismatched types".into(),
                ));
            }
        }
        Ok(Dynamic::from_ast(&Bool::and(&eqs)))
    }

    // === Compound local helpers ===

    /// Try to resolve an expression as a compound local (d[k] where d is Dict[Range, Seq]).
    /// Returns Some((var_idx, step, key_z3)) on success.
    fn try_resolve_compound_local(&mut self, expr: &CompiledExpr) -> Option<(usize, usize, Int)> {
        if let CompiledExpr::Index { base, index } = expr {
            let (var_idx, step) = match base.as_ref() {
                CompiledExpr::Var(idx) => (*idx, self.current_step),
                CompiledExpr::PrimedVar(idx) => (*idx, self.next_step),
                _ => return None,
            };
            let entry = &self.layout.entries[var_idx];
            if let VarKind::ExplodedDict { value_kind, .. } = &entry.kind {
                let stride = value_kind.z3_var_count();
                if stride > 1 {
                    let key_z3 = self.encode_int(index).ok()?;
                    return Some((var_idx, step, key_z3));
                }
            }
        }
        None
    }

    /// Check if a Local(idx) resolves to a compound local.
    /// Returns (var_idx, step, key_z3) if so.
    fn resolve_compound_local(&self, local_idx: usize) -> Option<(&usize, &usize, &Int)> {
        let depth = self.locals.len();
        let abs_idx = depth - 1 - local_idx;
        for (abs_depth, var_idx, step, key_z3) in self.compound_locals.iter().rev() {
            if *abs_depth == abs_idx {
                return Some((var_idx, step, key_z3));
            }
        }
        None
    }

    /// Check if a Local(idx) resolves to a whole-variable alias.
    /// Returns (var_idx, step) if so.
    fn resolve_whole_var_local(&self, local_idx: usize) -> Option<(usize, usize)> {
        let abs_idx = self.locals.len() - 1 - local_idx;
        for &(abs_depth, var_idx, step) in self.whole_var_locals.iter().rev() {
            if abs_depth == abs_idx {
                return Some((var_idx, step));
            }
        }
        None
    }

    /// Resolve nested len for a compound local: len(Local(n)[k1][k2]...).
    fn encode_compound_local_nested_len(
        &mut self,
        var_idx: usize,
        step: usize,
        outer_key_z3: &Int,
        keys: &[&CompiledExpr],
    ) -> SymbolicResult<Dynamic> {
        let entry = &self.layout.entries[var_idx];
        let (key_lo, key_hi, value_kind) = match &entry.kind {
            VarKind::ExplodedDict {
                key_lo,
                key_hi,
                value_kind,
            } => (*key_lo, *key_hi, value_kind.as_ref()),
            _ => {
                return Err(SymbolicError::Encoding(
                    "compound local len on non-dict".into(),
                ))
            }
        };
        let stride = value_kind.z3_var_count();
        let z3_vars = &self.step_vars[step][var_idx];
        let num_keys = (key_hi - key_lo + 1) as usize;
        let mut len_vals = Vec::new();
        for k in 0..num_keys {
            let offset = k * stride;
            let slot_vars = &z3_vars[offset..offset + stride];
            let len = if keys.is_empty() {
                self.len_of_kind(value_kind, slot_vars)?
            } else {
                self.resolve_nested_len(value_kind, slot_vars, keys)?
            };
            len_vals.push(len);
        }
        self.build_ite_chain(outer_key_z3, &len_vals, key_lo)
    }

    /// Resolve an index chain to find the Set slot vars and kind.
    fn resolve_set_slot<'b>(
        &mut self,
        kind: &'b VarKind,
        vars: &'b [Dynamic],
        keys: &[&CompiledExpr],
    ) -> SymbolicResult<(&'b [Dynamic], &'b VarKind)> {
        if keys.is_empty() {
            return Ok((vars, kind));
        }
        match kind {
            VarKind::ExplodedDict {
                key_lo,
                key_hi: _,
                value_kind,
            } => {
                let stride = value_kind.z3_var_count();
                let key_lo = *key_lo;
                let remaining = &keys[1..];

                if let Some(concrete_key) = self.try_concrete_int(keys[0]) {
                    let offset = (concrete_key - key_lo) as usize * stride;
                    let slot_vars = &vars[offset..offset + stride];
                    if remaining.is_empty() {
                        Ok((slot_vars, value_kind.as_ref()))
                    } else {
                        self.resolve_set_slot(value_kind, slot_vars, remaining)
                    }
                } else {
                    Err(SymbolicError::Encoding(
                        "set membership with symbolic dict key in nested index".into(),
                    ))
                }
            }
            _ => Err(SymbolicError::Encoding(
                "resolve_set_slot: unexpected kind".into(),
            )),
        }
    }

    /// Get head (first element) of a compound local (seq within dict).
    fn encode_compound_local_head(
        &self,
        var_idx: usize,
        step: usize,
        key_z3: &Int,
    ) -> SymbolicResult<Dynamic> {
        let entry = &self.layout.entries[var_idx];
        if let VarKind::ExplodedDict {
            key_lo,
            key_hi,
            value_kind,
        } = &entry.kind
        {
            let stride = value_kind.z3_var_count();
            let z3_vars = &self.step_vars[step][var_idx];
            let num_keys = (*key_hi - *key_lo + 1) as usize;
            // elem 0 is at offset 1 within each key's stride
            let head_vars: Vec<Dynamic> = (0..num_keys)
                .map(|k| z3_vars[k * stride + 1].clone())
                .collect();
            return self.build_ite_chain(key_z3, &head_vars, *key_lo);
        }
        Err(SymbolicError::Encoding(
            "compound local head on non-dict".into(),
        ))
    }

    // === Seq helpers ===

    fn encode_seq_head(&mut self, inner: &CompiledExpr) -> SymbolicResult<Dynamic> {
        // Handle head(d[k]) or head(d[k1][k2]) for nested compounds
        if let CompiledExpr::Index { .. } = inner {
            let mut keys: Vec<&CompiledExpr> = Vec::new();
            let mut cur = inner;
            while let CompiledExpr::Index {
                base: ib,
                index: ik,
            } = cur
            {
                keys.push(ik.as_ref());
                cur = ib.as_ref();
            }
            keys.reverse();
            let zero = CompiledExpr::Int(0);
            keys.push(&zero);
            let (var_idx, step) = self.extract_var_step(cur)?;
            let entry = &self.layout.entries[var_idx];
            let z3_vars = &self.step_vars[step][var_idx];
            return self.resolve_index_chain(&entry.kind, z3_vars, &keys);
        }
        // Handle head(Local(n)) for compound local
        if let CompiledExpr::Local(idx) = inner {
            if let Some((var_idx, step, key_z3)) = self
                .resolve_compound_local(*idx)
                .map(|(v, s, k)| (*v, *s, k.clone()))
            {
                return self.encode_compound_local_head(var_idx, step, &key_z3);
            }
        }
        let (var_idx, step) = self.extract_var_step(inner)?;
        let entry = &self.layout.entries[var_idx];
        if !matches!(entry.kind, VarKind::ExplodedSeq { .. }) {
            return Err(SymbolicError::Encoding(format!(
                "head() on non-seq variable '{}'",
                entry.name
            )));
        }
        Ok(self.step_vars[step][var_idx][1].clone())
    }

    // === Set helpers ===

    /// Check if an expression represents a set (for equality routing).
    fn is_set_expr(&self, expr: &CompiledExpr) -> bool {
        match expr {
            CompiledExpr::SetLit(_) | CompiledExpr::SetComprehension { .. } => true,
            CompiledExpr::Binary { op, .. } => {
                matches!(op, BinOp::Union | BinOp::Intersect | BinOp::Diff)
            }
            CompiledExpr::Var(idx) | CompiledExpr::PrimedVar(idx) => {
                matches!(self.layout.entries[*idx].kind, VarKind::ExplodedSet { .. })
            }
            _ => false,
        }
    }

    // === Seq helpers ===

    fn is_seq_expr(&self, expr: &CompiledExpr) -> bool {
        match expr {
            CompiledExpr::SeqLit(_) => true,
            CompiledExpr::Var(idx) | CompiledExpr::PrimedVar(idx) => {
                matches!(self.layout.entries[*idx].kind, VarKind::ExplodedSeq { .. })
            }
            _ => false,
        }
    }

    /// Encode seq equality: `seq == []` → `len == 0`; general: `len1 == len2 ∧ elem-wise eq`.
    fn encode_seq_eq(
        &mut self,
        left: &CompiledExpr,
        right: &CompiledExpr,
    ) -> SymbolicResult<Dynamic> {
        // Detect seq == [] or [] == seq
        if let CompiledExpr::SeqLit(elems) = right {
            if elems.is_empty() {
                let len = self.encode_len(left)?;
                return Ok(Dynamic::from_ast(&len.eq(Int::from_i64(0))));
            }
        }
        if let CompiledExpr::SeqLit(elems) = left {
            if elems.is_empty() {
                let len = self.encode_len(right)?;
                return Ok(Dynamic::from_ast(&len.eq(Int::from_i64(0))));
            }
        }

        // General case: get both seq vars and compare len + elements
        let (l_idx, l_step) = self.extract_var_step(left)?;
        let (r_idx, r_step) = self.extract_var_step(right)?;
        let l_kind = &self.layout.entries[l_idx].kind;
        let r_kind = &self.layout.entries[r_idx].kind;
        let max_len = match (l_kind, r_kind) {
            (
                VarKind::ExplodedSeq { max_len: ml, .. },
                VarKind::ExplodedSeq { max_len: mr, .. },
            ) => (*ml).min(*mr),
            _ => {
                return Err(SymbolicError::Encoding(
                    "seq equality requires two sequence variables".into(),
                ));
            }
        };

        let l_vars = &self.step_vars[l_step][l_idx];
        let r_vars = &self.step_vars[r_step][r_idx];

        let mut conjuncts = Vec::new();
        // len equality
        let l_len = l_vars[0].as_int().unwrap();
        let r_len = r_vars[0].as_int().unwrap();
        conjuncts.push(l_len.eq(&r_len));
        // element equality (for all positions up to max_len)
        for i in 0..max_len {
            let l_elem = &l_vars[1 + i];
            let r_elem = &r_vars[1 + i];
            if let (Some(li), Some(ri)) = (l_elem.as_int(), r_elem.as_int()) {
                conjuncts.push(li.eq(&ri));
            } else if let (Some(lb), Some(rb)) = (l_elem.as_bool(), r_elem.as_bool()) {
                conjuncts.push(lb.eq(&rb));
            }
        }
        Ok(Dynamic::from_ast(&Bool::and(&conjuncts)))
    }

    fn extract_var_step(&self, expr: &CompiledExpr) -> SymbolicResult<(usize, usize)> {
        match expr {
            CompiledExpr::Var(idx) => Ok((*idx, self.current_step)),
            CompiledExpr::PrimedVar(idx) => Ok((*idx, self.next_step)),
            _ => Err(SymbolicError::Encoding(
                "expected state variable in seq equality".into(),
            )),
        }
    }

    /// Infer set bounds from two operands (at least one must reveal bounds).
    fn infer_set_bounds(
        &mut self,
        left: &CompiledExpr,
        right: &CompiledExpr,
    ) -> SymbolicResult<(i64, i64)> {
        self.try_set_bounds(left)
            .or_else(|| self.try_set_bounds(right))
            .ok_or_else(|| SymbolicError::Encoding("cannot infer set bounds from operands".into()))
    }

    fn try_set_bounds(&self, expr: &CompiledExpr) -> Option<(i64, i64)> {
        match expr {
            CompiledExpr::Var(idx) | CompiledExpr::PrimedVar(idx) => {
                if let VarKind::ExplodedSet { lo, hi } = &self.layout.entries[*idx].kind {
                    Some((*lo, *hi))
                } else {
                    None
                }
            }
            CompiledExpr::SetComprehension { domain, .. } => {
                if let CompiledExpr::Range { lo, hi } = domain.as_ref() {
                    let lo_val = self.extract_concrete_int(lo).ok()?;
                    let hi_val = self.extract_concrete_int(hi).ok()?;
                    Some((lo_val, hi_val))
                } else {
                    None
                }
            }
            CompiledExpr::Binary { left, right, .. } => self
                .try_set_bounds(left)
                .or_else(|| self.try_set_bounds(right)),
            _ => None,
        }
    }

    /// Encode a set expression as a Vec<Bool> of per-element membership flags.
    pub fn encode_as_set(
        &mut self,
        expr: &CompiledExpr,
        lo: i64,
        hi: i64,
    ) -> SymbolicResult<Vec<Bool>> {
        let count = (hi - lo + 1) as usize;
        match expr {
            CompiledExpr::Var(idx) | CompiledExpr::PrimedVar(idx) => {
                let step = match expr {
                    CompiledExpr::Var(_) => self.current_step,
                    _ => self.next_step,
                };
                let z3_vars = &self.step_vars[step][*idx];
                Ok(z3_vars.iter().map(|v| v.as_bool().unwrap()).collect())
            }
            CompiledExpr::SetLit(elements) => {
                let mut flags = vec![Bool::from_bool(false); count];
                for elem in elements {
                    if let Some(val) = self.try_concrete_int(elem) {
                        let offset = (val - lo) as usize;
                        if offset < count {
                            flags[offset] = Bool::from_bool(true);
                        }
                    } else {
                        // Symbolic element: set the flag at the symbolic index
                        let elem_z3 = self.encode_int(elem)?;
                        for (i, k) in (lo..=hi).enumerate() {
                            let k_z3 = Int::from_i64(k);
                            let is_match = elem_z3.eq(&k_z3);
                            flags[i] = Bool::or(&[flags[i].clone(), is_match]);
                        }
                    }
                }
                Ok(flags)
            }
            CompiledExpr::SetComprehension {
                element: _,
                domain,
                filter,
            } => {
                let values = self.resolve_domain_values(domain)?;
                let mut flags = vec![Bool::from_bool(false); count];
                for val in values {
                    let offset = (val - lo) as usize;
                    if offset >= count {
                        continue;
                    }
                    let z3_val = Dynamic::from_ast(&Int::from_i64(val));
                    self.locals.push(z3_val);
                    let included = if let Some(f) = filter {
                        self.encode_bool(f)?
                    } else {
                        Bool::from_bool(true)
                    };
                    self.locals.pop();
                    flags[offset] = included;
                }
                Ok(flags)
            }
            CompiledExpr::Binary {
                op: BinOp::Union,
                left,
                right,
            } => {
                let l = self.encode_as_set(left, lo, hi)?;
                let r = self.encode_as_set(right, lo, hi)?;
                Ok(l.iter()
                    .zip(r.iter())
                    .map(|(a, b)| Bool::or(&[a.clone(), b.clone()]))
                    .collect())
            }
            CompiledExpr::Binary {
                op: BinOp::Intersect,
                left,
                right,
            } => {
                let l = self.encode_as_set(left, lo, hi)?;
                let r = self.encode_as_set(right, lo, hi)?;
                Ok(l.iter()
                    .zip(r.iter())
                    .map(|(a, b)| Bool::and(&[a.clone(), b.clone()]))
                    .collect())
            }
            CompiledExpr::Binary {
                op: BinOp::Diff,
                left,
                right,
            } => {
                let l = self.encode_as_set(left, lo, hi)?;
                let r = self.encode_as_set(right, lo, hi)?;
                Ok(l.iter()
                    .zip(r.iter())
                    .map(|(a, b)| Bool::and(&[a.clone(), b.not()]))
                    .collect())
            }
            _ => Err(SymbolicError::Encoding(format!(
                "cannot encode as set: {:?}",
                std::mem::discriminant(expr)
            ))),
        }
    }

    // === Helpers ===

    fn try_concrete_int(&self, expr: &CompiledExpr) -> Option<i64> {
        match expr {
            CompiledExpr::Int(n) => Some(*n),
            CompiledExpr::Const(idx) => self.consts[*idx].as_int(),
            CompiledExpr::Local(idx) => {
                let depth = self.locals.len();
                if *idx < depth {
                    let local = &self.locals[depth - 1 - *idx];
                    local.as_int().and_then(|i| i.as_i64())
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Resolve a domain to concrete values, handling both Range and set-local domains.
    fn resolve_domain_values(&mut self, domain: &CompiledExpr) -> SymbolicResult<Vec<i64>> {
        if let CompiledExpr::Local(idx) = domain {
            if let Some(members) = self.resolve_set_local(*idx) {
                return Ok(members.clone());
            }
        }
        let (lo, hi) = self.extract_range(domain)?;
        Ok((lo..=hi).collect())
    }

    pub fn extract_range(&mut self, domain: &CompiledExpr) -> SymbolicResult<(i64, i64)> {
        match domain {
            CompiledExpr::Range { lo, hi } => {
                let lo_val = self.extract_concrete_int(lo)?;
                let hi_val = self.extract_concrete_int(hi)?;
                Ok((lo_val, hi_val))
            }
            _ => Err(SymbolicError::Unsupported(format!(
                "non-range domain: {:?}",
                std::mem::discriminant(domain)
            ))),
        }
    }

    fn extract_concrete_int(&self, expr: &CompiledExpr) -> SymbolicResult<i64> {
        match expr {
            CompiledExpr::Int(n) => Ok(*n),
            CompiledExpr::Const(idx) => self.consts[*idx]
                .as_int()
                .ok_or_else(|| SymbolicError::Encoding("expected integer constant".into())),
            _ => Err(SymbolicError::Encoding(format!(
                "expected concrete integer, got {:?}",
                std::mem::discriminant(expr)
            ))),
        }
    }

    /// Build an ITE chain for symbolic key lookup.
    fn build_ite_chain(&self, key: &Int, vars: &[Dynamic], base: i64) -> SymbolicResult<Dynamic> {
        if vars.is_empty() {
            return Err(SymbolicError::Encoding("empty ITE chain".into()));
        }
        let mut result = vars.last().unwrap().clone();
        for (i, var) in vars.iter().enumerate().rev().skip(1) {
            let idx_val = Int::from_i64(base + i as i64);
            let cond = key.eq(&idx_val);
            if let (Some(vi), Some(ri)) = (var.as_int(), result.as_int()) {
                result = Dynamic::from_ast(&cond.ite(&vi, &ri));
            } else if let (Some(vb), Some(rb)) = (var.as_bool(), result.as_bool()) {
                result = Dynamic::from_ast(&cond.ite(&vb, &rb));
            }
        }
        Ok(result)
    }

    /// Helper to extract concrete int (used by transition encoder).
    pub fn extract_concrete_int_helper(&self, expr: &CompiledExpr) -> SymbolicResult<i64> {
        self.extract_concrete_int(expr)
    }
}

/// Create Z3 variables for a given step.
pub fn create_step_vars(layout: &VarLayout, step: usize) -> Vec<Vec<Dynamic>> {
    layout
        .entries
        .iter()
        .map(|entry| create_var_z3(entry, step))
        .collect()
}

fn create_var_z3(entry: &VarEntry, step: usize) -> Vec<Dynamic> {
    match &entry.kind {
        VarKind::Bool => {
            vec![Dynamic::from_ast(&Bool::new_const(format!(
                "{}_s{}",
                entry.name, step
            )))]
        }
        VarKind::Int { .. } => {
            vec![Dynamic::from_ast(&Int::new_const(format!(
                "{}_s{}",
                entry.name, step
            )))]
        }
        VarKind::ExplodedDict {
            key_lo,
            key_hi,
            value_kind,
        } => {
            let mut vars = Vec::new();
            for k in *key_lo..=*key_hi {
                create_vars_for_kind(
                    value_kind,
                    &format!("{}_{}", entry.name, k),
                    step,
                    &mut vars,
                );
            }
            vars
        }
        VarKind::ExplodedSet { lo, hi } => {
            let mut vars = Vec::new();
            for k in *lo..=*hi {
                vars.push(Dynamic::from_ast(&Bool::new_const(format!(
                    "{}_{}_s{}",
                    entry.name, k, step
                ))));
            }
            vars
        }
        VarKind::ExplodedSeq { max_len, elem_kind } => {
            let mut vars = Vec::new();
            // First var: length
            vars.push(Dynamic::from_ast(&Int::new_const(format!(
                "{}_len_s{}",
                entry.name, step
            ))));
            // Element vars
            for i in 0..*max_len {
                create_vars_for_kind(elem_kind, &format!("{}_{}", entry.name, i), step, &mut vars);
            }
            vars
        }
        VarKind::ExplodedOption { inner_kind } => {
            let mut vars = Vec::new();
            // present flag
            vars.push(Dynamic::from_ast(&Bool::new_const(format!(
                "{}_present_s{}",
                entry.name, step
            ))));
            // inner value vars
            create_vars_for_kind(inner_kind, &format!("{}_val", entry.name), step, &mut vars);
            vars
        }
        VarKind::ExplodedTuple { element_kinds } => {
            let mut vars = Vec::new();
            for (i, kind) in element_kinds.iter().enumerate() {
                create_vars_for_kind(kind, &format!("{}_{}", entry.name, i), step, &mut vars);
            }
            vars
        }
        VarKind::ExplodedRecord {
            field_names,
            field_kinds,
        } => {
            let mut vars = Vec::new();
            for (name, kind) in field_names.iter().zip(field_kinds.iter()) {
                create_vars_for_kind(kind, &format!("{}_{}", entry.name, name), step, &mut vars);
            }
            vars
        }
    }
}

/// Recursively create Z3 variables for a VarKind (used for compound value kinds).
fn create_vars_for_kind(kind: &VarKind, prefix: &str, step: usize, out: &mut Vec<Dynamic>) {
    match kind {
        VarKind::Bool => {
            out.push(Dynamic::from_ast(&Bool::new_const(format!(
                "{}_s{}",
                prefix, step
            ))));
        }
        VarKind::Int { .. } => {
            out.push(Dynamic::from_ast(&Int::new_const(format!(
                "{}_s{}",
                prefix, step
            ))));
        }
        VarKind::ExplodedSeq { max_len, elem_kind } => {
            out.push(Dynamic::from_ast(&Int::new_const(format!(
                "{}_len_s{}",
                prefix, step
            ))));
            for i in 0..*max_len {
                create_vars_for_kind(elem_kind, &format!("{}_{}", prefix, i), step, out);
            }
        }
        VarKind::ExplodedDict {
            key_lo,
            key_hi,
            value_kind,
        } => {
            for k in *key_lo..=*key_hi {
                create_vars_for_kind(value_kind, &format!("{}_{}", prefix, k), step, out);
            }
        }
        VarKind::ExplodedSet { lo, hi } => {
            for k in *lo..=*hi {
                out.push(Dynamic::from_ast(&Bool::new_const(format!(
                    "{}_{}_s{}",
                    prefix, k, step
                ))));
            }
        }
        VarKind::ExplodedOption { inner_kind } => {
            out.push(Dynamic::from_ast(&Bool::new_const(format!(
                "{}_present_s{}",
                prefix, step
            ))));
            create_vars_for_kind(inner_kind, &format!("{}_val", prefix), step, out);
        }
        VarKind::ExplodedTuple { element_kinds } => {
            for (i, kind) in element_kinds.iter().enumerate() {
                create_vars_for_kind(kind, &format!("{}_{}", prefix, i), step, out);
            }
        }
        VarKind::ExplodedRecord {
            field_names,
            field_kinds,
        } => {
            for (name, kind) in field_names.iter().zip(field_kinds.iter()) {
                create_vars_for_kind(kind, &format!("{}_{}", prefix, name), step, out);
            }
        }
    }
}

/// Assert range constraints for all variables at a given step.
pub fn assert_range_constraints(
    solver: &Solver,
    layout: &VarLayout,
    step_vars: &[Vec<Vec<Dynamic>>],
    step: usize,
) {
    for (var_idx, entry) in layout.entries.iter().enumerate() {
        assert_var_range(solver, &entry.kind, &step_vars[step][var_idx]);
    }
}

fn assert_var_range(solver: &Solver, kind: &VarKind, z3_vars: &[Dynamic]) {
    match kind {
        VarKind::Int { lo, hi } => {
            if let Some(lo) = lo {
                let z3_lo = Int::from_i64(*lo);
                solver.assert(z3_vars[0].as_int().unwrap().ge(&z3_lo));
            }
            if let Some(hi) = hi {
                let z3_hi = Int::from_i64(*hi);
                solver.assert(z3_vars[0].as_int().unwrap().le(&z3_hi));
            }
        }
        VarKind::ExplodedDict {
            key_lo,
            key_hi,
            value_kind,
        } => {
            let stride = value_kind.z3_var_count();
            let num_keys = (*key_hi - *key_lo + 1) as usize;
            for k in 0..num_keys {
                let start = k * stride;
                assert_var_range(solver, value_kind, &z3_vars[start..start + stride]);
            }
        }
        VarKind::ExplodedSeq { max_len, elem_kind } => {
            // len bounded: 0 <= len <= max_len
            let len_var = z3_vars[0].as_int().unwrap();
            solver.assert(len_var.ge(Int::from_i64(0)));
            solver.assert(len_var.le(Int::from_i64(*max_len as i64)));
            // Element range constraints
            let elem_stride = elem_kind.z3_var_count();
            for i in 0..*max_len {
                let start = 1 + i * elem_stride;
                assert_var_range(solver, elem_kind, &z3_vars[start..start + elem_stride]);
            }
        }
        VarKind::Bool | VarKind::ExplodedSet { .. } => {}
        VarKind::ExplodedOption { inner_kind } => {
            // No range constraint on the present Bool (vars[0]).
            // Apply range constraints to inner value.
            let inner_stride = inner_kind.z3_var_count();
            assert_var_range(solver, inner_kind, &z3_vars[1..1 + inner_stride]);
        }
        VarKind::ExplodedTuple { element_kinds } => {
            let mut offset = 0;
            for kind in element_kinds {
                let stride = kind.z3_var_count();
                assert_var_range(solver, kind, &z3_vars[offset..offset + stride]);
                offset += stride;
            }
        }
        VarKind::ExplodedRecord { field_kinds, .. } => {
            let mut offset = 0;
            for kind in field_kinds {
                let stride = kind.z3_var_count();
                assert_var_range(solver, kind, &z3_vars[offset..offset + stride]);
                offset += stride;
            }
        }
    }
}

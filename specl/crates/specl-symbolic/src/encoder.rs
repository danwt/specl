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
                let val = self.encode(value)?;
                self.locals.push(val);
                let result = self.encode(body);
                self.locals.pop();
                result
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

            // === Unsupported ===
            CompiledExpr::SeqLit(_)
            | CompiledExpr::SeqHead(_)
            | CompiledExpr::SeqTail(_)
            | CompiledExpr::Slice { .. }
            | CompiledExpr::Powerset(_)
            | CompiledExpr::BigUnion(_)
            | CompiledExpr::Fix { .. }
            | CompiledExpr::Keys(_)
            | CompiledExpr::Values(_)
            | CompiledExpr::Changes(_)
            | CompiledExpr::Enabled(_)
            | CompiledExpr::ActionCall { .. }
            | CompiledExpr::Field { .. }
            | CompiledExpr::RecordUpdate { .. }
            | CompiledExpr::TupleLit(_)
            | CompiledExpr::Call { .. }
            | CompiledExpr::Choose { .. } => Err(SymbolicError::Unsupported(format!(
                "{:?}",
                std::mem::discriminant(expr)
            ))),
        }
    }

    fn encode_var(&self, specl_var_idx: usize, step: usize) -> SymbolicResult<Dynamic> {
        let entry = &self.layout.entries[specl_var_idx];
        match &entry.kind {
            VarKind::Bool | VarKind::Int { .. } => {
                Ok(self.step_vars[step][specl_var_idx][0].clone())
            }
            VarKind::ExplodedDict { .. } | VarKind::ExplodedSet { .. } => {
                Err(SymbolicError::Encoding(format!(
                    "dict/set variable '{}' accessed directly (use index operator)",
                    entry.name
                )))
            }
        }
    }

    fn encode_const(&self, const_idx: usize) -> SymbolicResult<Dynamic> {
        let val = &self.consts[const_idx];
        match val {
            Value::Bool(b) => Ok(Dynamic::from_ast(&Bool::from_bool(*b))),
            Value::Int(n) => Ok(Dynamic::from_ast(&Int::from_i64(*n))),
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

            BinOp::Concat => Err(SymbolicError::Unsupported("sequence concat".into())),
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

    fn encode_index(
        &mut self,
        base: &CompiledExpr,
        index: &CompiledExpr,
    ) -> SymbolicResult<Dynamic> {
        let (specl_var_idx, step) = match base {
            CompiledExpr::Var(idx) => (*idx, self.current_step),
            CompiledExpr::PrimedVar(idx) => (*idx, self.next_step),
            _ => {
                return Err(SymbolicError::Encoding(
                    "index base must be a state variable".into(),
                ))
            }
        };

        let entry = &self.layout.entries[specl_var_idx];
        match &entry.kind {
            VarKind::ExplodedDict { key_lo, key_hi, .. } => {
                let key_lo = *key_lo;
                let key_hi = *key_hi;
                let z3_vars = &self.step_vars[step][specl_var_idx];

                if let Some(concrete_key) = self.try_concrete_int(index) {
                    let offset = (concrete_key - key_lo) as usize;
                    if offset < z3_vars.len() {
                        Ok(z3_vars[offset].clone())
                    } else {
                        Err(SymbolicError::Encoding(format!(
                            "dict key {} out of range [{}, {}]",
                            concrete_key, key_lo, key_hi
                        )))
                    }
                } else {
                    let key_z3 = self.encode_int(index)?;
                    self.build_ite_chain(&key_z3, z3_vars, key_lo)
                }
            }
            VarKind::ExplodedSet { lo, .. } => {
                let lo = *lo;
                let z3_vars = &self.step_vars[step][specl_var_idx];
                if let Some(concrete_key) = self.try_concrete_int(index) {
                    let offset = (concrete_key - lo) as usize;
                    if offset < z3_vars.len() {
                        Ok(z3_vars[offset].clone())
                    } else {
                        Ok(Dynamic::from_ast(&Bool::from_bool(false)))
                    }
                } else {
                    let key_z3 = self.encode_int(index)?;
                    self.build_ite_chain(&key_z3, z3_vars, lo)
                }
            }
            _ => Err(SymbolicError::Encoding(format!(
                "index on non-dict/set variable '{}'",
                entry.name
            ))),
        }
    }

    fn encode_len(&mut self, inner: &CompiledExpr) -> SymbolicResult<Dynamic> {
        if let CompiledExpr::SetComprehension {
            element: _,
            domain,
            filter,
        } = inner
        {
            let (lo, hi) = self.extract_range(domain)?;
            let one = Int::from_i64(1);
            let zero = Int::from_i64(0);
            let mut sum_terms = Vec::new();

            for val in lo..=hi {
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

            Ok(Dynamic::from_ast(&Int::add(&sum_terms)))
        } else {
            match inner {
                CompiledExpr::Var(idx) | CompiledExpr::PrimedVar(idx) => {
                    let step = match inner {
                        CompiledExpr::Var(_) => self.current_step,
                        _ => self.next_step,
                    };
                    let entry = &self.layout.entries[*idx];
                    if let VarKind::ExplodedSet { .. } = &entry.kind {
                        let z3_vars = &self.step_vars[step][*idx];
                        let one = Int::from_i64(1);
                        let zero = Int::from_i64(0);
                        let terms: Vec<Int> = z3_vars
                            .iter()
                            .map(|v| v.as_bool().unwrap().ite(&one, &zero))
                            .collect();
                        Ok(Dynamic::from_ast(&Int::add(&terms)))
                    } else {
                        Err(SymbolicError::Unsupported(
                            "len() on non-set variable".into(),
                        ))
                    }
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
                let (lo, hi) = self.extract_range(domain)?;
                let elem_z3 = self.encode_int(elem)?;
                let lo_z3 = Int::from_i64(lo);
                let hi_z3 = Int::from_i64(hi);
                let in_domain = Bool::and(&[elem_z3.ge(&lo_z3), elem_z3.le(&hi_z3)]);

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
                let (dom_lo, dom_hi) = self.extract_range(domain)?;
                let mut flags = vec![Bool::from_bool(false); count];
                for val in dom_lo..=dom_hi {
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
            CompiledExpr::Const(idx) => {
                if let Value::Int(n) = &self.consts[*idx] {
                    Some(*n)
                } else {
                    None
                }
            }
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
            CompiledExpr::Const(idx) => {
                if let Value::Int(n) = &self.consts[*idx] {
                    Ok(*n)
                } else {
                    Err(SymbolicError::Encoding("expected integer constant".into()))
                }
            }
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
                match value_kind.as_ref() {
                    VarKind::Bool => {
                        vars.push(Dynamic::from_ast(&Bool::new_const(format!(
                            "{}_{}_s{}",
                            entry.name, k, step
                        ))));
                    }
                    _ => {
                        vars.push(Dynamic::from_ast(&Int::new_const(format!(
                            "{}_{}_s{}",
                            entry.name, k, step
                        ))));
                    }
                }
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
                solver.assert(&z3_vars[0].as_int().unwrap().ge(&z3_lo));
            }
            if let Some(hi) = hi {
                let z3_hi = Int::from_i64(*hi);
                solver.assert(&z3_vars[0].as_int().unwrap().le(&z3_hi));
            }
        }
        VarKind::ExplodedDict { value_kind, .. } => {
            for var in z3_vars {
                assert_var_range(solver, value_kind, &[var.clone()]);
            }
        }
        VarKind::Bool | VarKind::ExplodedSet { .. } => {}
    }
}

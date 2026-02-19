//! Type checker implementation.

use crate::env::{ActionSig, TypeEnv};
use crate::error::{TypeError, TypeResult};
use crate::types::{Substitution, Type, TypeVarGen};
use specl_syntax::*;

/// Type check a module.
pub fn check_module(module: &Module) -> TypeResult<TypeEnv> {
    let mut checker = TypeChecker::new();
    checker.check_module(module)?;
    Ok(checker.env)
}

/// The type checker.
pub struct TypeChecker {
    /// Type environment.
    pub env: TypeEnv,
    /// Type variable generator.
    var_gen: TypeVarGen,
}

impl TypeChecker {
    /// Create a new type checker.
    pub fn new() -> Self {
        Self {
            env: TypeEnv::new(),
            var_gen: TypeVarGen::new(),
        }
    }

    /// Check a complete module.
    pub fn check_module(&mut self, module: &Module) -> TypeResult<()> {
        // First pass: collect all declarations
        for decl in &module.decls {
            self.collect_decl(decl)?;
        }

        // Second pass: check bodies
        for decl in &module.decls {
            self.check_decl(decl)?;
        }

        Ok(())
    }

    /// Collect declaration signatures (first pass).
    fn collect_decl(&mut self, decl: &Decl) -> TypeResult<()> {
        match decl {
            Decl::Const(d) => {
                let ty = match &d.value {
                    specl_syntax::ConstValue::Type(type_expr) => {
                        self.convert_type_expr(type_expr)?
                    }
                    specl_syntax::ConstValue::Scalar(n) => {
                        // Scalar constants have type Int (or Nat if non-negative)
                        if *n >= 0 {
                            Type::Nat
                        } else {
                            Type::Int
                        }
                    }
                };
                self.env.define_const(d.name.name.clone(), ty);
            }
            Decl::Var(d) => {
                let ty = self.convert_type_expr(&d.ty)?;
                self.env.define_var(d.name.name.clone(), ty);
            }
            Decl::Type(d) => {
                let ty = self.convert_type_expr(&d.ty)?;
                self.env.define_type_alias(d.name.name.clone(), ty);
            }
            Decl::Action(d) => {
                let params: Vec<(String, Type)> = d
                    .params
                    .iter()
                    .map(|p| {
                        let ty = self.convert_type_expr(&p.ty)?;
                        Ok((p.name.name.clone(), ty))
                    })
                    .collect::<TypeResult<_>>()?;
                self.env
                    .define_action(d.name.name.clone(), ActionSig { params });
            }
            Decl::Func(d) => {
                // Functions have polymorphic types - we use fresh type vars for params
                let param_types: Vec<Type> =
                    d.params.iter().map(|_| self.var_gen.fresh_type()).collect();
                self.env.define_func(
                    d.name.name.clone(),
                    d.params.iter().map(|p| p.name.name.clone()).collect(),
                    param_types,
                );
            }
            _ => {}
        }
        Ok(())
    }

    /// Check declaration bodies (second pass).
    fn check_decl(&mut self, decl: &Decl) -> TypeResult<()> {
        match decl {
            Decl::Init(d) => {
                let ty = self.infer_expr(&d.body)?;
                self.expect_bool(&ty, d.body.span)?;
            }
            Decl::Action(d) => {
                self.env.push_scope();

                // Bind parameters
                for param in &d.params {
                    let ty = self.convert_type_expr(&param.ty)?;
                    self.env.bind_local(param.name.name.clone(), ty);
                }

                // Check requires
                for req in &d.body.requires {
                    let ty = self.infer_expr(req)?;
                    self.expect_bool(&ty, req.span)?;
                }

                // Check effect
                if let Some(effect) = &d.body.effect {
                    let ty = self.infer_expr(effect)?;
                    self.expect_bool(&ty, effect.span)?;
                }

                self.env.pop_scope();
            }
            Decl::Invariant(d) => {
                let ty = self.infer_expr(&d.body)?;
                self.expect_bool(&ty, d.body.span)?;
            }
            Decl::Property(d) => {
                let ty = self.infer_expr(&d.body)?;
                self.expect_bool(&ty, d.body.span)?;
            }
            Decl::Func(d) => {
                self.env.push_scope();
                // Bind parameters with fresh type variables
                let param_types = self
                    .env
                    .lookup_func(&d.name.name)
                    .map(|f| f.param_types.clone())
                    .unwrap_or_default();
                for (param, ty) in d.params.iter().zip(param_types.iter()) {
                    self.env.bind_local(param.name.name.clone(), ty.clone());
                }
                // Infer body type (don't constrain it - functions can return anything)
                let _body_ty = self.infer_expr(&d.body)?;
                self.env.pop_scope();
            }
            _ => {}
        }
        Ok(())
    }

    /// Convert an AST type expression to a Type.
    fn convert_type_expr(&mut self, ty_expr: &TypeExpr) -> TypeResult<Type> {
        match ty_expr {
            TypeExpr::Named(id) => {
                let name = &id.name;
                match name.as_str() {
                    "Bool" => Ok(Type::Bool),
                    "Nat" => Ok(Type::Nat),
                    "Int" => Ok(Type::Int),
                    "String" => Ok(Type::String),
                    // Special marker for inferred types (used by TLA+ translator for empty domains)
                    "_" | "Inferred" => Ok(self.var_gen.fresh_type()),
                    _ => {
                        // Check if it's a defined type alias
                        if self.env.lookup_type_alias(name).is_some() {
                            Ok(Type::Named(name.clone()))
                        } else {
                            Err(TypeError::UndefinedType {
                                name: name.clone(),
                                span: id.span,
                            })
                        }
                    }
                }
            }
            TypeExpr::Set(inner, _) => {
                let inner_ty = self.convert_type_expr(inner)?;
                Ok(Type::Set(Box::new(inner_ty)))
            }
            TypeExpr::Seq(inner, _) => {
                let inner_ty = self.convert_type_expr(inner)?;
                Ok(Type::Seq(Box::new(inner_ty)))
            }
            TypeExpr::Dict(key, value, _) => {
                let key_ty = self.convert_type_expr(key)?;
                let value_ty = self.convert_type_expr(value)?;
                Ok(Type::Fn(Box::new(key_ty), Box::new(value_ty)))
            }
            TypeExpr::Option(inner, _) => {
                let inner_ty = self.convert_type_expr(inner)?;
                Ok(Type::Option(Box::new(inner_ty)))
            }
            TypeExpr::Range(lo, hi, _span) => {
                // Check that both bounds are numeric
                let lo_ty = self.infer_expr(lo)?;
                let hi_ty = self.infer_expr(hi)?;

                if !lo_ty.is_numeric() {
                    return Err(TypeError::ExpectedNumeric {
                        found: lo_ty,
                        span: lo.span,
                    });
                }
                if !hi_ty.is_numeric() {
                    return Err(TypeError::ExpectedNumeric {
                        found: hi_ty,
                        span: hi.span,
                    });
                }

                // Extract literal values if possible
                let lo_val = self.extract_int_literal(lo);
                let hi_val = self.extract_int_literal(hi);

                match (lo_val, hi_val) {
                    (Some(lo), Some(hi)) => Ok(Type::Range(lo, hi)),
                    _ => Ok(Type::Int), // Fallback to Int if bounds aren't literals
                }
            }
            TypeExpr::Tuple(elems, _) => {
                let elem_types: Vec<Type> = elems
                    .iter()
                    .map(|ty| self.convert_type_expr(ty))
                    .collect::<TypeResult<_>>()?;
                Ok(Type::Tuple(elem_types))
            }
        }
    }

    /// Extract an integer literal value from an expression.
    fn extract_int_literal(&self, expr: &Expr) -> Option<i64> {
        match &expr.kind {
            ExprKind::Int(n) => Some(*n),
            ExprKind::Ident(_name) => {
                // Check if it's a constant with a known value
                // For now, we can't resolve constant values at type-checking time
                None
            }
            _ => None,
        }
    }

    /// Infer the type of an expression.
    pub fn infer_expr(&mut self, expr: &Expr) -> TypeResult<Type> {
        let ty = match &expr.kind {
            ExprKind::Bool(_) => Type::Bool,
            ExprKind::Int(_) => Type::Int,
            ExprKind::String(_) => Type::String,

            ExprKind::Ident(name) => {
                // None → Option[T] where T is a fresh type variable
                if name == "None" {
                    let inner = self.var_gen.fresh_type();
                    Type::Option(Box::new(inner))
                } else if let Some(ty) = self.env.lookup_ident(name) {
                    ty.clone()
                } else {
                    return Err(TypeError::UndefinedVariable {
                        name: name.clone(),
                        span: expr.span,
                    });
                }
            }

            ExprKind::Primed(name) => {
                // Must be a state variable
                if let Some(ty) = self.env.lookup_var(name) {
                    ty.clone()
                } else {
                    return Err(TypeError::InvalidPrime { span: expr.span });
                }
            }

            ExprKind::Binary { op, left, right } => {
                // Flatten left spine of binary expressions to iterate instead of recurse.
                // The parser builds left-leaning trees for left-associative operators,
                // so `a and b and c and ...` with 80+ conjuncts would overflow the stack
                // in debug builds without this.
                let mut chain: Vec<(BinOp, &Expr)> = vec![(*op, right)];
                let mut leftmost: &Expr = left;
                while let ExprKind::Binary {
                    op: inner_op,
                    left: inner_left,
                    right: inner_right,
                } = &leftmost.kind
                {
                    chain.push((*inner_op, inner_right));
                    leftmost = inner_left;
                }
                let mut result_ty = self.infer_expr(leftmost)?;
                for (op, right_expr) in chain.into_iter().rev() {
                    let right_ty = self.infer_expr(right_expr)?;
                    result_ty = self.check_binary_types(
                        op,
                        &result_ty,
                        leftmost.span,
                        &right_ty,
                        right_expr.span,
                    )?;
                }
                result_ty
            }

            ExprKind::Unary { op, operand } => self.infer_unary(*op, operand)?,

            ExprKind::Index { base, index } => {
                // Check if this is actually a slice (Seq indexed by Range)
                // The parser parses `seq[1..3]` as Index with a Range expression
                if let ExprKind::Range { lo, hi } = &index.kind {
                    let base_ty_raw = self.infer_expr(base)?;
                    let base_ty = self.env.resolve_type(&base_ty_raw);
                    let lo_ty = self.infer_expr(lo)?;
                    let hi_ty = self.infer_expr(hi)?;

                    self.expect_numeric(&lo_ty, lo.span)?;
                    self.expect_numeric(&hi_ty, hi.span)?;

                    match base_ty {
                        Type::Seq(_) => base_ty, // Slice returns same Seq type
                        Type::Var(_) => self.var_gen.fresh_type(),
                        _ => {
                            return Err(TypeError::NotIndexable {
                                ty: base_ty,
                                span: base.span,
                            });
                        }
                    }
                } else {
                    let base_ty_raw = self.infer_expr(base)?;
                    let base_ty = self.env.resolve_type(&base_ty_raw);
                    let index_ty = self.infer_expr(index)?;

                    match base_ty {
                        Type::Seq(elem_ty) => {
                            self.expect_numeric(&index_ty, index.span)?;
                            *elem_ty
                        }
                        Type::Fn(key_ty, value_ty) => {
                            self.unify(&key_ty, &index_ty, index.span)?;
                            *value_ty
                        }
                        // Accept type variables for polymorphic funcs
                        Type::Var(_) => self.var_gen.fresh_type(),
                        _ => {
                            return Err(TypeError::NotIndexable {
                                ty: base_ty,
                                span: base.span,
                            });
                        }
                    }
                }
            }

            ExprKind::Slice { base, lo, hi } => {
                let base_ty_raw = self.infer_expr(base)?;
                let base_ty = self.env.resolve_type(&base_ty_raw);
                let lo_ty = self.infer_expr(lo)?;
                let hi_ty = self.infer_expr(hi)?;

                self.expect_numeric(&lo_ty, lo.span)?;
                self.expect_numeric(&hi_ty, hi.span)?;

                match base_ty {
                    Type::Seq(_) => base_ty,
                    _ => {
                        return Err(TypeError::NotIndexable {
                            ty: base_ty,
                            span: base.span,
                        });
                    }
                }
            }

            ExprKind::Field { base, field } => {
                let base_ty_raw = self.infer_expr(base)?;
                let base_ty = self.env.resolve_type(&base_ty_raw);

                match &base_ty {
                    Type::Record(rec) => {
                        if let Some(field_ty) = rec.get_field(&field.name) {
                            field_ty.clone()
                        } else {
                            return Err(TypeError::InvalidField {
                                ty: base_ty,
                                field: field.name.clone(),
                                span: field.span,
                            });
                        }
                    }
                    Type::Tuple(elems) => {
                        if let Ok(idx) = field.name.parse::<usize>() {
                            if idx < elems.len() {
                                elems[idx].clone()
                            } else {
                                return Err(TypeError::InvalidField {
                                    ty: base_ty,
                                    field: field.name.clone(),
                                    span: field.span,
                                });
                            }
                        } else {
                            return Err(TypeError::InvalidField {
                                ty: base_ty,
                                field: field.name.clone(),
                                span: field.span,
                            });
                        }
                    }
                    // MVP: Allow field access on Int (for TLA+ specs where elements are records
                    // but type inference defaults to Int). Return Int as the field type.
                    Type::Int => Type::Int,
                    // Allow field access on type variables (for TLA+ specs with inferred types).
                    // Return a fresh type variable for the field type.
                    Type::Var(_) => self.var_gen.fresh_type(),
                    _ => {
                        return Err(TypeError::InvalidField {
                            ty: base_ty,
                            field: field.name.clone(),
                            span: field.span,
                        });
                    }
                }
            }

            ExprKind::Call { func, args } => {
                // Check if it's a built-in function or an action call
                if let ExprKind::Ident(name) = &func.kind {
                    // Check for action call
                    if let Some(sig) = self.env.lookup_action(name).cloned() {
                        if args.len() != sig.params.len() {
                            return Err(TypeError::ArityMismatch {
                                expected: sig.params.len(),
                                found: args.len(),
                                span: expr.span,
                            });
                        }

                        for (arg, (_, param_ty)) in args.iter().zip(sig.params.iter()) {
                            let arg_ty = self.infer_expr(arg)?;
                            self.unify(param_ty, &arg_ty, arg.span)?;
                        }

                        return Ok(Type::Bool); // Actions are predicates
                    }

                    // Some(x) → Option[T]
                    if name == "Some" && args.len() == 1 {
                        let inner_ty = self.infer_expr(&args[0])?;
                        return Ok(Type::Option(Box::new(inner_ty)));
                    }

                    // Check for user-defined function call
                    if let Some(func_info) = self.env.lookup_func(name).cloned() {
                        if args.len() != func_info.param_names.len() {
                            return Err(TypeError::ArityMismatch {
                                expected: func_info.param_names.len(),
                                found: args.len(),
                                span: expr.span,
                            });
                        }

                        // Unify argument types with parameter types
                        for (arg, param_ty) in args.iter().zip(func_info.param_types.iter()) {
                            let arg_ty = self.infer_expr(arg)?;
                            self.unify(param_ty, &arg_ty, arg.span)?;
                        }

                        // User-defined functions return a fresh type (polymorphic)
                        return Ok(self.var_gen.fresh_type());
                    }
                }

                // Generic function call
                let func_ty = self.infer_expr(func)?;
                let arg_types: Vec<Type> = args
                    .iter()
                    .map(|a| self.infer_expr(a))
                    .collect::<TypeResult<_>>()?;

                // For now, just return a fresh type variable
                // Full inference would need to track function types
                let _ = (func_ty, arg_types);
                self.var_gen.fresh_type()
            }

            ExprKind::SetLit(elements) => {
                if elements.is_empty() {
                    // Empty set has a polymorphic element type
                    Type::Set(Box::new(self.var_gen.fresh_type()))
                } else {
                    let elem_ty = self.infer_expr(&elements[0])?;
                    for elem in elements.iter().skip(1) {
                        let ty = self.infer_expr(elem)?;
                        self.unify(&elem_ty, &ty, elem.span)?;
                    }
                    Type::Set(Box::new(elem_ty))
                }
            }

            ExprKind::SeqLit(elements) => {
                if elements.is_empty() {
                    Type::Seq(Box::new(self.var_gen.fresh_type()))
                } else {
                    let elem_ty = self.infer_expr(&elements[0])?;
                    for elem in elements.iter().skip(1) {
                        let ty = self.infer_expr(elem)?;
                        self.unify(&elem_ty, &ty, elem.span)?;
                    }
                    Type::Seq(Box::new(elem_ty))
                }
            }

            ExprKind::TupleLit(elements) => {
                // Each element can have a different type
                let elem_types: Vec<Type> = elements
                    .iter()
                    .map(|e| self.infer_expr(e))
                    .collect::<TypeResult<_>>()?;
                Type::Tuple(elem_types)
            }

            ExprKind::DictLit(entries) => {
                if entries.is_empty() {
                    // Empty dict - use fresh type variables
                    Type::Fn(
                        Box::new(self.var_gen.fresh_type()),
                        Box::new(self.var_gen.fresh_type()),
                    )
                } else {
                    // Infer from first entry, unify with rest
                    let (first_key, first_val) = &entries[0];
                    let key_ty = self.infer_expr(first_key)?;
                    let val_ty = self.infer_expr(first_val)?;

                    for (key, val) in entries.iter().skip(1) {
                        let k_ty = self.infer_expr(key)?;
                        let v_ty = self.infer_expr(val)?;
                        self.unify(&key_ty, &k_ty, key.span)?;
                        self.unify(&val_ty, &v_ty, val.span)?;
                    }

                    Type::Fn(Box::new(key_ty), Box::new(val_ty))
                }
            }

            ExprKind::FnLit { var, domain, body } => {
                let domain_ty = self.infer_expr(domain)?;
                let elem_ty = self.element_type(&domain_ty, domain.span)?;

                self.env.push_scope();
                self.env.bind_local(var.name.clone(), elem_ty.clone());
                let body_ty = self.infer_expr(body)?;
                self.env.pop_scope();

                Type::Fn(Box::new(elem_ty), Box::new(body_ty))
            }

            ExprKind::SetComprehension {
                element,
                var,
                domain,
                filter,
            } => {
                let domain_ty = self.infer_expr(domain)?;
                let elem_ty = self.element_type(&domain_ty, domain.span)?;

                self.env.push_scope();
                self.env.bind_local(var.name.clone(), elem_ty);

                if let Some(f) = filter {
                    let filter_ty = self.infer_expr(f)?;
                    self.expect_bool(&filter_ty, f.span)?;
                }

                let element_ty = self.infer_expr(element)?;
                self.env.pop_scope();

                Type::Set(Box::new(element_ty))
            }

            ExprKind::RecordUpdate { base, updates } => {
                let base_ty_raw = self.infer_expr(base)?;
                let base_ty = self.env.resolve_type(&base_ty_raw);

                match &base_ty {
                    Type::Record(rec) => {
                        for update in updates {
                            match update {
                                RecordFieldUpdate::Field { name, value } => {
                                    let expected = rec.get_field(&name.name).ok_or_else(|| {
                                        TypeError::InvalidField {
                                            ty: base_ty.clone(),
                                            field: name.name.clone(),
                                            span: name.span,
                                        }
                                    })?;
                                    let value_ty = self.infer_expr(value)?;
                                    self.unify(expected, &value_ty, value.span)?;
                                }
                                RecordFieldUpdate::Dynamic { key, value } => {
                                    let _ = self.infer_expr(key)?;
                                    let _ = self.infer_expr(value)?;
                                }
                            }
                        }
                        base_ty
                    }
                    Type::Fn(key_ty, value_ty) => {
                        // Function update { f with [k]: v }
                        for update in updates {
                            match update {
                                RecordFieldUpdate::Dynamic { key, value } => {
                                    let key_actual = self.infer_expr(key)?;
                                    let value_actual = self.infer_expr(value)?;
                                    self.unify(key_ty, &key_actual, key.span)?;
                                    self.unify(value_ty, &value_actual, value.span)?;
                                }
                                RecordFieldUpdate::Field { name, .. } => {
                                    return Err(TypeError::InvalidField {
                                        ty: base_ty.clone(),
                                        field: name.name.clone(),
                                        span: name.span,
                                    });
                                }
                            }
                        }
                        base_ty
                    }
                    _ => {
                        return Err(TypeError::InvalidField {
                            ty: base_ty,
                            field: "<update>".to_string(),
                            span: expr.span,
                        });
                    }
                }
            }

            ExprKind::Quantifier {
                kind: _,
                bindings,
                body,
            } => {
                self.env.push_scope();

                for binding in bindings {
                    let domain_ty = self.infer_expr(&binding.domain)?;
                    let elem_ty = self.element_type(&domain_ty, binding.domain.span)?;
                    self.env.bind_local(binding.var.name.clone(), elem_ty);
                }

                let body_ty = self.infer_expr(body)?;
                self.expect_bool(&body_ty, body.span)?;

                self.env.pop_scope();
                Type::Bool
            }

            ExprKind::Fix {
                var,
                domain,
                predicate,
            } => {
                let elem_ty = if let Some(domain) = domain {
                    let domain_ty = self.infer_expr(domain)?;
                    self.element_type(&domain_ty, domain.span)?
                } else {
                    Type::Int
                };

                self.env.push_scope();
                self.env.bind_local(var.name.clone(), elem_ty.clone());

                let pred_ty = self.infer_expr(predicate)?;
                self.expect_bool(&pred_ty, predicate.span)?;

                self.env.pop_scope();
                elem_ty
            }

            ExprKind::Let { var, value, body } => {
                let value_ty = self.infer_expr(value)?;

                self.env.push_scope();
                self.env.bind_local(var.name.clone(), value_ty);

                let body_ty = self.infer_expr(body)?;
                self.env.pop_scope();

                body_ty
            }

            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                let cond_ty = self.infer_expr(cond)?;
                self.expect_bool(&cond_ty, cond.span)?;

                let then_ty = self.infer_expr(then_branch)?;
                let else_ty = self.infer_expr(else_branch)?;
                self.unify(&then_ty, &else_ty, else_branch.span)?;

                then_ty
            }

            ExprKind::Require(inner) => {
                let inner_ty = self.infer_expr(inner)?;
                self.expect_bool(&inner_ty, inner.span)?;
                Type::Bool
            }

            ExprKind::Changes(_var) => {
                // changes(v) is a boolean predicate
                Type::Bool
            }

            ExprKind::Enabled(action) => {
                // Check that action exists
                if self.env.lookup_action(&action.name).is_none() {
                    return Err(TypeError::UndefinedAction {
                        name: action.name.clone(),
                        span: action.span,
                    });
                }
                Type::Bool
            }

            ExprKind::SeqHead(seq_expr) => {
                let seq_ty_raw = self.infer_expr(seq_expr)?;
                let seq_ty = self.env.resolve_type(&seq_ty_raw);
                match seq_ty {
                    Type::Seq(elem_ty) => *elem_ty,
                    // TLA+ sequences are functions with domain 1..n; accept Fn[Int, T] as sequence-like.
                    Type::Fn(key_ty, val_ty) => {
                        self.unify(key_ty.as_ref(), &Type::Int, seq_expr.span)?;
                        *val_ty
                    }
                    _ => {
                        return Err(TypeError::TypeMismatch {
                            expected: Type::Seq(Box::new(self.var_gen.fresh_type())),
                            found: seq_ty,
                            span: seq_expr.span,
                        });
                    }
                }
            }

            ExprKind::SeqTail(seq_expr) => {
                let seq_ty_raw = self.infer_expr(seq_expr)?;
                let seq_ty = self.env.resolve_type(&seq_ty_raw);
                match seq_ty {
                    Type::Seq(_) => seq_ty,
                    // Keep function form for sequence-like TLA+ functions.
                    Type::Fn(key_ty, val_ty) => {
                        self.unify(key_ty.as_ref(), &Type::Int, seq_expr.span)?;
                        Type::Fn(key_ty, val_ty)
                    }
                    _ => {
                        return Err(TypeError::TypeMismatch {
                            expected: Type::Seq(Box::new(self.var_gen.fresh_type())),
                            found: seq_ty,
                            span: seq_expr.span,
                        });
                    }
                }
            }

            ExprKind::Len(expr) => {
                let ty_raw = self.infer_expr(expr)?;
                let ty = self.env.resolve_type(&ty_raw);
                match ty {
                    // Accept Seq, Set, Fn, or type variables (for polymorphic funcs)
                    Type::Seq(_) | Type::Set(_) | Type::Fn(_, _) | Type::Var(_) => Type::Nat,
                    _ => {
                        return Err(TypeError::TypeMismatch {
                            expected: Type::Seq(Box::new(self.var_gen.fresh_type())),
                            found: ty,
                            span: expr.span,
                        });
                    }
                }
            }

            ExprKind::Keys(expr) => {
                let ty_raw = self.infer_expr(expr)?;
                let ty = self.env.resolve_type(&ty_raw);
                match ty {
                    Type::Fn(key_ty, _) => Type::Set(key_ty),
                    // For sequences, keys returns 1..len(seq), which is Set[Int]
                    Type::Seq(_) => Type::Set(Box::new(Type::Int)),
                    _ => {
                        return Err(TypeError::TypeMismatch {
                            expected: Type::Fn(
                                Box::new(self.var_gen.fresh_type()),
                                Box::new(self.var_gen.fresh_type()),
                            ),
                            found: ty,
                            span: expr.span,
                        });
                    }
                }
            }

            ExprKind::Values(expr) => {
                let ty_raw = self.infer_expr(expr)?;
                let ty = self.env.resolve_type(&ty_raw);
                match ty {
                    Type::Fn(_, val_ty) => Type::Set(val_ty),
                    _ => {
                        return Err(TypeError::TypeMismatch {
                            expected: Type::Fn(
                                Box::new(self.var_gen.fresh_type()),
                                Box::new(self.var_gen.fresh_type()),
                            ),
                            found: ty,
                            span: expr.span,
                        });
                    }
                }
            }

            ExprKind::BigUnion(expr) => {
                let ty_raw = self.infer_expr(expr)?;
                let ty = self.env.resolve_type(&ty_raw);
                // BigUnion takes Set[Set[T]] and returns Set[T]
                match ty {
                    Type::Set(inner) => match *inner {
                        Type::Set(elem_ty) => Type::Set(elem_ty),
                        _ => {
                            return Err(TypeError::TypeMismatch {
                                expected: Type::Set(Box::new(self.var_gen.fresh_type())),
                                found: *inner,
                                span: expr.span,
                            });
                        }
                    },
                    _ => {
                        return Err(TypeError::TypeMismatch {
                            expected: Type::Set(Box::new(Type::Set(Box::new(
                                self.var_gen.fresh_type(),
                            )))),
                            found: ty,
                            span: expr.span,
                        });
                    }
                }
            }

            ExprKind::Powerset(expr) => {
                let ty_raw = self.infer_expr(expr)?;
                let ty = self.env.resolve_type(&ty_raw);
                // Powerset takes Set[T] and returns Set[Set[T]]
                match ty {
                    Type::Set(elem_ty) => Type::Set(Box::new(Type::Set(elem_ty))),
                    _ => {
                        return Err(TypeError::TypeMismatch {
                            expected: Type::Set(Box::new(self.var_gen.fresh_type())),
                            found: ty,
                            span: expr.span,
                        });
                    }
                }
            }

            ExprKind::Always(inner) | ExprKind::Eventually(inner) => {
                let inner_ty = self.infer_expr(inner)?;
                self.expect_bool(&inner_ty, inner.span)?;
                Type::Bool
            }

            ExprKind::LeadsTo { left, right } => {
                let left_ty = self.infer_expr(left)?;
                let right_ty = self.infer_expr(right)?;
                self.expect_bool(&left_ty, left.span)?;
                self.expect_bool(&right_ty, right.span)?;
                Type::Bool
            }

            ExprKind::Range { lo, hi } => {
                let lo_ty = self.infer_expr(lo)?;
                let hi_ty = self.infer_expr(hi)?;
                self.expect_numeric(&lo_ty, lo.span)?;
                self.expect_numeric(&hi_ty, hi.span)?;
                // A range expression is a set of integers
                Type::Set(Box::new(Type::Int))
            }

            ExprKind::Paren(inner) => self.infer_expr(inner)?,
        };

        Ok(ty)
    }

    /// Check types of a binary operation given already-inferred operand types.
    fn check_binary_types(
        &mut self,
        op: BinOp,
        left_ty: &Type,
        left_span: Span,
        right_ty: &Type,
        right_span: Span,
    ) -> TypeResult<Type> {
        match op {
            // Logical operators
            BinOp::And | BinOp::Or | BinOp::Implies | BinOp::Iff => {
                self.expect_bool(left_ty, left_span)?;
                self.expect_bool(right_ty, right_span)?;
                Ok(Type::Bool)
            }

            // Comparison operators
            BinOp::Eq | BinOp::Ne => {
                self.unify(left_ty, right_ty, right_span)?;
                Ok(Type::Bool)
            }

            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                self.expect_numeric(left_ty, left_span)?;
                self.expect_numeric(right_ty, right_span)?;
                Ok(Type::Bool)
            }

            // Arithmetic operators
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => {
                self.expect_numeric(left_ty, left_span)?;
                self.expect_numeric(right_ty, right_span)?;
                // Return the more general numeric type
                if matches!(left_ty, Type::Int) || matches!(right_ty, Type::Int) {
                    Ok(Type::Int)
                } else {
                    Ok(Type::Nat)
                }
            }

            // Set membership
            BinOp::In | BinOp::NotIn => {
                let resolved = self.env.resolve_type(right_ty);
                match resolved {
                    Type::Set(elem_ty) => {
                        self.unify(left_ty, &elem_ty, left_span)?;
                        Ok(Type::Bool)
                    }
                    Type::Fn(key_ty, _val_ty) => {
                        self.unify(left_ty, &key_ty, left_span)?;
                        Ok(Type::Bool)
                    }
                    _ => Err(TypeError::NotIterable {
                        ty: right_ty.clone(),
                        span: right_span,
                    }),
                }
            }

            // Set and dict operations
            BinOp::Union | BinOp::Intersect | BinOp::Diff => {
                let resolved_left = self.env.resolve_type(left_ty);
                let resolved_right = self.env.resolve_type(right_ty);

                match (&resolved_left, &resolved_right) {
                    (Type::Set(_), Type::Set(_)) => {
                        self.unify(left_ty, right_ty, right_span)?;
                        Ok(left_ty.clone())
                    }
                    (Type::Fn(_, _), Type::Fn(_, _)) => {
                        // Dict merge with | operator
                        self.unify(left_ty, right_ty, right_span)?;
                        Ok(left_ty.clone())
                    }
                    _ => Err(TypeError::TypeMismatch {
                        expected: Type::Set(Box::new(self.var_gen.fresh_type())),
                        found: left_ty.clone(),
                        span: left_span,
                    }),
                }
            }

            BinOp::SubsetOf => {
                let resolved_left = self.env.resolve_type(left_ty);
                let resolved_right = self.env.resolve_type(right_ty);

                match (&resolved_left, &resolved_right) {
                    (Type::Set(_), Type::Set(_)) => {
                        self.unify(left_ty, right_ty, right_span)?;
                        Ok(Type::Bool)
                    }
                    _ => Err(TypeError::TypeMismatch {
                        expected: Type::Set(Box::new(self.var_gen.fresh_type())),
                        found: left_ty.clone(),
                        span: left_span,
                    }),
                }
            }

            // Sequence concatenation
            BinOp::Concat => {
                let resolved_left = self.env.resolve_type(left_ty);
                let resolved_right = self.env.resolve_type(right_ty);

                match (&resolved_left, &resolved_right) {
                    (Type::Seq(_), Type::Seq(_)) => {
                        self.unify(left_ty, right_ty, right_span)?;
                        Ok(left_ty.clone())
                    }
                    _ => Err(TypeError::TypeMismatch {
                        expected: Type::Seq(Box::new(self.var_gen.fresh_type())),
                        found: left_ty.clone(),
                        span: left_span,
                    }),
                }
            }
        }
    }

    /// Infer type of unary operation.
    fn infer_unary(&mut self, op: UnaryOp, operand: &Expr) -> TypeResult<Type> {
        let operand_ty = self.infer_expr(operand)?;

        match op {
            UnaryOp::Not => {
                self.expect_bool(&operand_ty, operand.span)?;
                Ok(Type::Bool)
            }
            UnaryOp::Neg => {
                self.expect_numeric(&operand_ty, operand.span)?;
                Ok(Type::Int) // Negation produces Int even from Nat
            }
        }
    }

    /// Get the element type of a collection or set.
    fn element_type(&mut self, ty: &Type, span: Span) -> TypeResult<Type> {
        let resolved = self.env.resolve_type(ty);
        match resolved {
            Type::Set(elem) | Type::Seq(elem) => Ok(*elem),
            Type::Fn(key, _) => Ok(*key), // Iterating over function yields keys
            Type::Range(_, _) => Ok(Type::Int),
            Type::Var(_) => {
                // Type variable used as iterable - assume it's a collection
                // and return a fresh element type for polymorphism
                Ok(self.var_gen.fresh_type())
            }
            _ => Err(TypeError::NotIterable { ty: resolved, span }),
        }
    }

    /// Unify two types.
    fn unify(&mut self, a: &Type, b: &Type, span: Span) -> TypeResult<Substitution> {
        let a = self.env.resolve_type(a);
        let b = self.env.resolve_type(b);

        if a == b {
            return Ok(Substitution::new());
        }

        match (&a, &b) {
            // Type variables unify with anything
            (Type::Var(v), _) => {
                if b.has_vars() && matches!(b, Type::Var(v2) if *v == v2) {
                    // Same variable
                    Ok(Substitution::new())
                } else if self.occurs_in(v, &b) {
                    Err(TypeError::OccursCheck { span })
                } else {
                    let mut subst = Substitution::new();
                    subst.insert(*v, b.clone());
                    Ok(subst)
                }
            }
            (_, Type::Var(v)) => {
                if self.occurs_in(v, &a) {
                    Err(TypeError::OccursCheck { span })
                } else {
                    let mut subst = Substitution::new();
                    subst.insert(*v, a.clone());
                    Ok(subst)
                }
            }

            // Structural unification
            (Type::Set(a_elem), Type::Set(b_elem)) => self.unify(a_elem, b_elem, span),
            (Type::Seq(a_elem), Type::Seq(b_elem)) => self.unify(a_elem, b_elem, span),
            (Type::Option(a_elem), Type::Option(b_elem)) => self.unify(a_elem, b_elem, span),
            (Type::Fn(a_key, a_val), Type::Fn(b_key, b_val)) => {
                let s1 = self.unify(a_key, b_key, span)?;
                let a_val = a_val.substitute(&s1);
                let b_val = b_val.substitute(&s1);
                let s2 = self.unify(&a_val, &b_val, span)?;
                Ok(s1.compose(&s2))
            }
            (Type::Record(a_rec), Type::Record(b_rec)) => {
                if a_rec.fields.keys().collect::<Vec<_>>()
                    != b_rec.fields.keys().collect::<Vec<_>>()
                {
                    return Err(TypeError::UnificationFailure {
                        a: a.clone(),
                        b: b.clone(),
                        span,
                    });
                }

                let mut subst = Substitution::new();
                for (name, a_ty) in &a_rec.fields {
                    let b_ty = b_rec.fields.get(name).unwrap();
                    let a_ty = a_ty.substitute(&subst);
                    let b_ty = b_ty.substitute(&subst);
                    let s = self.unify(&a_ty, &b_ty, span)?;
                    subst = subst.compose(&s);
                }
                Ok(subst)
            }
            (Type::Tuple(a_elems), Type::Tuple(b_elems)) => {
                if a_elems.len() != b_elems.len() {
                    return Err(TypeError::UnificationFailure {
                        a: a.clone(),
                        b: b.clone(),
                        span,
                    });
                }

                let mut subst = Substitution::new();
                for (a_ty, b_ty) in a_elems.iter().zip(b_elems.iter()) {
                    let a_ty = a_ty.substitute(&subst);
                    let b_ty = b_ty.substitute(&subst);
                    let s = self.unify(&a_ty, &b_ty, span)?;
                    subst = subst.compose(&s);
                }
                Ok(subst)
            }

            // Numeric types: Int subsumes Nat and Range
            (Type::Int, Type::Nat) | (Type::Nat, Type::Int) => Ok(Substitution::new()),
            (Type::Int, Type::Range(_, _)) | (Type::Range(_, _), Type::Int) => {
                Ok(Substitution::new())
            }
            (Type::Nat, Type::Range(lo, _)) | (Type::Range(lo, _), Type::Nat) if *lo >= 0 => {
                Ok(Substitution::new())
            }
            (Type::Range(a_lo, a_hi), Type::Range(b_lo, b_hi)) if a_lo == b_lo && a_hi == b_hi => {
                Ok(Substitution::new())
            }

            // Error type unifies with anything (for error recovery)
            (Type::Error, _) | (_, Type::Error) => Ok(Substitution::new()),

            // MVP: Allow Int and Bool to unify (for TLA+ specs that mix Nil with true/false)
            (Type::Int, Type::Bool) | (Type::Bool, Type::Int) => Ok(Substitution::new()),

            _ => Err(TypeError::UnificationFailure {
                a: a.clone(),
                b: b.clone(),
                span,
            }),
        }
    }

    /// Check if a type variable occurs in a type.
    fn occurs_in(&self, var: &crate::types::TypeVar, ty: &Type) -> bool {
        Self::occurs_in_impl(var, ty)
    }

    fn occurs_in_impl(var: &crate::types::TypeVar, ty: &Type) -> bool {
        match ty {
            Type::Var(v) => v == var,
            Type::Set(t) | Type::Seq(t) | Type::Option(t) => Self::occurs_in_impl(var, t),
            Type::Fn(k, v) => Self::occurs_in_impl(var, k) || Self::occurs_in_impl(var, v),
            Type::Record(r) => r.fields.values().any(|t| Self::occurs_in_impl(var, t)),
            Type::Tuple(elems) => elems.iter().any(|t| Self::occurs_in_impl(var, t)),
            _ => false,
        }
    }

    /// Expect a boolean type.
    fn expect_bool(&self, ty: &Type, span: Span) -> TypeResult<()> {
        let resolved = self.env.resolve_type(ty);
        match resolved {
            Type::Bool | Type::Var(_) | Type::Error => Ok(()),
            _ => Err(TypeError::ExpectedBool {
                found: resolved,
                span,
            }),
        }
    }

    /// Expect a numeric type.
    fn expect_numeric(&self, ty: &Type, span: Span) -> TypeResult<()> {
        let resolved = self.env.resolve_type(ty);
        match resolved {
            Type::Nat | Type::Int | Type::Range(_, _) | Type::Var(_) | Type::Error => Ok(()),
            _ => Err(TypeError::ExpectedNumeric {
                found: resolved,
                span,
            }),
        }
    }
}

impl Default for TypeChecker {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use specl_syntax::parse;

    fn check(source: &str) -> TypeResult<TypeEnv> {
        let module = parse(source).expect("parse error");
        check_module(&module)
    }

    #[test]
    fn test_simple_types() {
        let source = r#"
module Test
var x: Nat
var y: Bool
init { x == 0 and y == true }
"#;
        assert!(check(source).is_ok());
    }

    #[test]
    fn test_type_mismatch() {
        let source = r#"
module Test
var x: Nat
init { x == true }
"#;
        let result = check(source);
        assert!(result.is_err());
    }

    #[test]
    fn test_undefined_variable() {
        let source = r#"
module Test
init { undefined_var == 0 }
"#;
        let result = check(source);
        assert!(matches!(result, Err(TypeError::UndefinedVariable { .. })));
    }

    #[test]
    fn test_set_operations() {
        let source = r#"
module Test
var s: Set[Nat]
init { 1 in s and s union {} == s }
"#;
        assert!(check(source).is_ok());
    }

    #[test]
    fn test_quantifier() {
        let source = r#"
module Test
var s: Set[Nat]
init { all x in s: x >= 0 }
"#;
        assert!(check(source).is_ok());
    }

    #[test]
    fn test_action_type_check() {
        let source = r#"
module Test
var x: Nat
const MAX: Nat
action Inc() {
    require x < MAX
    x = x + 1
}
"#;
        assert!(check(source).is_ok());
    }

    #[test]
    fn test_dict_access() {
        let source = r#"
module Test
var d: Dict[Nat, Bool]
init { d[0] == false and d[1] == true }
"#;
        assert!(check(source).is_ok());
    }

    #[test]
    fn test_dict_comprehension() {
        let source = r#"
module Test
var d: Dict[0..2, Nat]
init { d == {x: 0 for x in 0..2} }
"#;
        assert!(check(source).is_ok());
    }
}

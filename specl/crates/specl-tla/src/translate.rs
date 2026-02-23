//! Translate TLA+ AST to Specl AST.

use crate::ast::*;
use crate::parser::Parser;
use specl_syntax::ast as specl;
use specl_syntax::token::Span;
use thiserror::Error;

/// Translation error.
#[derive(Debug, Error)]
pub enum TranslateError {
    #[error("parse error: {0}")]
    Parse(#[from] crate::parser::ParseError),
    #[error("unsupported construct: {message}")]
    Unsupported { message: String },
    #[error("translation error: {message}")]
    Translation { message: String },
}

/// Translate TLA+ source to Specl source.
pub fn translate(source: &str) -> Result<String, TranslateError> {
    let mut parser = Parser::new(source);
    let tla_module = parser.parse_module()?;

    let translator = Translator::new();
    let specl_module = translator.translate_module(&tla_module)?;

    Ok(specl_syntax::pretty::pretty_print(&specl_module))
}

/// TLA+ to Specl translator.
struct Translator {
    /// Variables that have been identified as state variables.
    state_vars: Vec<String>,
    /// Operator definitions that are pure constants (for inlining).
    constant_ops: std::collections::HashMap<String, TlaExpr>,
    /// Parameterized helper operators (pure functions to be inlined).
    helper_ops: std::collections::HashMap<String, (Vec<String>, TlaExpr)>,
    /// Init predicate operators (no params, conjunctions of var = expr, for inlining in Init).
    init_predicates: std::collections::HashMap<String, TlaExpr>,
    /// Zero-arg non-primed operators (including stateful predicates) to inline at use sites.
    zero_arg_ops: std::collections::HashMap<String, TlaExpr>,
    /// Inferred types for variables from Init expression.
    var_types: std::collections::HashMap<String, specl::TypeExpr>,
    /// Constants that are used as set domains (e.g., Server, Value).
    set_constants: std::collections::HashSet<String>,
    /// Stateful predicates: operators with params that reference state vars but don't modify state.
    /// These need to be inlined at call sites since they can't be pure funcs.
    stateful_predicates: std::collections::HashMap<String, (Vec<String>, TlaExpr)>,
    /// Action helpers: operators with params that modify state (have primed vars).
    /// These need to be inlined at call sites when called from other actions.
    action_helpers: std::collections::HashMap<String, (Vec<String>, TlaExpr)>,
    /// Operators that are recursive (their body references themselves).
    /// These must not be inlined — emit as function calls instead.
    recursive_ops: std::collections::HashSet<String>,
}

impl Translator {
    fn new() -> Self {
        Self {
            state_vars: Vec::new(),
            constant_ops: std::collections::HashMap::new(),
            helper_ops: std::collections::HashMap::new(),
            init_predicates: std::collections::HashMap::new(),
            zero_arg_ops: std::collections::HashMap::new(),
            var_types: std::collections::HashMap::new(),
            set_constants: std::collections::HashSet::new(),
            stateful_predicates: std::collections::HashMap::new(),
            action_helpers: std::collections::HashMap::new(),
            recursive_ops: std::collections::HashSet::new(),
        }
    }

    /// Check if an expression contains a call (OpApp) to the given operator name.
    fn body_references_self(name: &str, expr: &TlaExpr) -> bool {
        match &expr.kind {
            TlaExprKind::OpApp {
                name: call_name,
                args,
            } => {
                if call_name == name {
                    return true;
                }
                args.iter().any(|a| Self::body_references_self(name, a))
            }
            TlaExprKind::Ident(n) => n == name,
            TlaExprKind::Binary { left, right, .. } => {
                Self::body_references_self(name, left) || Self::body_references_self(name, right)
            }
            TlaExprKind::Unary { operand, .. } => Self::body_references_self(name, operand),
            TlaExprKind::SetEnum { elements } | TlaExprKind::Tuple { elements } => {
                elements.iter().any(|e| Self::body_references_self(name, e))
            }
            TlaExprKind::Record { fields } => fields
                .iter()
                .any(|(_, e)| Self::body_references_self(name, e)),
            TlaExprKind::FieldAccess { base, .. } => Self::body_references_self(name, base),
            TlaExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => {
                Self::body_references_self(name, cond)
                    || Self::body_references_self(name, then_branch)
                    || Self::body_references_self(name, else_branch)
            }
            TlaExprKind::Paren(inner) | TlaExprKind::Primed(inner) => {
                Self::body_references_self(name, inner)
            }
            TlaExprKind::Range { lo, hi } => {
                Self::body_references_self(name, lo) || Self::body_references_self(name, hi)
            }
            TlaExprKind::FunctionApp { func, args } => {
                Self::body_references_self(name, func)
                    || args.iter().any(|a| Self::body_references_self(name, a))
            }
            TlaExprKind::FunctionDef { domain, body, .. } => {
                Self::body_references_self(name, domain) || Self::body_references_self(name, body)
            }
            TlaExprKind::FunctionSet { domain, range } => {
                Self::body_references_self(name, domain) || Self::body_references_self(name, range)
            }
            TlaExprKind::RecordSet { fields } => fields
                .iter()
                .any(|(_, e)| Self::body_references_self(name, e)),
            TlaExprKind::LetIn { defs, body } => {
                defs.iter()
                    .any(|d| Self::body_references_self(name, &d.body))
                    || Self::body_references_self(name, body)
            }
            TlaExprKind::Forall { body, bindings, .. }
            | TlaExprKind::Exists { body, bindings, .. } => {
                Self::body_references_self(name, body)
                    || bindings
                        .iter()
                        .any(|b| Self::body_references_self(name, &b.domain))
            }
            TlaExprKind::SetMap {
                element, domain, ..
            } => {
                Self::body_references_self(name, element)
                    || Self::body_references_self(name, domain)
            }
            TlaExprKind::SetFilter {
                predicate, domain, ..
            } => {
                Self::body_references_self(name, predicate)
                    || Self::body_references_self(name, domain)
            }
            TlaExprKind::Choose {
                predicate, domain, ..
            } => {
                Self::body_references_self(name, predicate)
                    || domain
                        .as_ref()
                        .is_some_and(|d| Self::body_references_self(name, d))
            }
            TlaExprKind::Except { base, updates } => {
                Self::body_references_self(name, base)
                    || updates.iter().any(|u| {
                        u.path.iter().any(|p| Self::body_references_self(name, p))
                            || Self::body_references_self(name, &u.value)
                    })
            }
            TlaExprKind::Domain(inner)
            | TlaExprKind::PowerSet(inner)
            | TlaExprKind::BigUnion(inner)
            | TlaExprKind::Always(inner)
            | TlaExprKind::Eventually(inner)
            | TlaExprKind::Enabled(inner) => Self::body_references_self(name, inner),
            TlaExprKind::LeadsTo { left, right }
            | TlaExprKind::BoxAction {
                action: left,
                vars: right,
            }
            | TlaExprKind::AngleAction {
                action: left,
                vars: right,
            } => Self::body_references_self(name, left) || Self::body_references_self(name, right),
            TlaExprKind::WeakFairness { vars, action }
            | TlaExprKind::StrongFairness { vars, action } => {
                Self::body_references_self(name, vars) || Self::body_references_self(name, action)
            }
            TlaExprKind::Unchanged(vars) => vars.iter().any(|v| v.name == name),
            TlaExprKind::Case { arms, other } => {
                arms.iter().any(|(cond, body)| {
                    Self::body_references_self(name, cond) || Self::body_references_self(name, body)
                }) || other
                    .as_ref()
                    .is_some_and(|e| Self::body_references_self(name, e))
            }
            TlaExprKind::InstanceOp { instance, args, .. } => {
                Self::body_references_self(name, instance)
                    || args.iter().any(|a| Self::body_references_self(name, a))
            }
            _ => false,
        }
    }

    /// Check if an expression references any state variables.
    fn references_state_vars(&self, expr: &TlaExpr) -> bool {
        match &expr.kind {
            TlaExprKind::Ident(name) => self.state_vars.contains(name),
            TlaExprKind::Primed(inner) => self.references_state_vars(inner),
            TlaExprKind::Binary { left, right, .. } => {
                self.references_state_vars(left) || self.references_state_vars(right)
            }
            TlaExprKind::Unary { operand, .. } => self.references_state_vars(operand),
            TlaExprKind::Forall { bindings, body } | TlaExprKind::Exists { bindings, body } => {
                bindings
                    .iter()
                    .any(|b| self.references_state_vars(&b.domain))
                    || self.references_state_vars(body)
            }
            TlaExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => {
                self.references_state_vars(cond)
                    || self.references_state_vars(then_branch)
                    || self.references_state_vars(else_branch)
            }
            TlaExprKind::SetEnum { elements } | TlaExprKind::Tuple { elements } => {
                elements.iter().any(|e| self.references_state_vars(e))
            }
            TlaExprKind::SetMap {
                element, domain, ..
            }
            | TlaExprKind::SetFilter {
                domain,
                predicate: element,
                ..
            } => self.references_state_vars(element) || self.references_state_vars(domain),
            TlaExprKind::FunctionApp { func, args } => {
                self.references_state_vars(func)
                    || args.iter().any(|a| self.references_state_vars(a))
            }
            TlaExprKind::OpApp { name, args } => {
                // Check if the operator being called is known to reference state
                if self.stateful_predicates.contains_key(name)
                    || self.action_helpers.contains_key(name)
                {
                    return true;
                }
                args.iter().any(|a| self.references_state_vars(a))
            }
            TlaExprKind::Record { fields } => {
                fields.iter().any(|(_, e)| self.references_state_vars(e))
            }
            TlaExprKind::FieldAccess { base, .. } => self.references_state_vars(base),
            TlaExprKind::FunctionDef { domain, body, .. } => {
                self.references_state_vars(domain) || self.references_state_vars(body)
            }
            TlaExprKind::Except { base, updates } => {
                self.references_state_vars(base)
                    || updates.iter().any(|u| {
                        u.path.iter().any(|p| self.references_state_vars(p))
                            || self.references_state_vars(&u.value)
                    })
            }
            TlaExprKind::LetIn { defs, body } => {
                defs.iter().any(|d| self.references_state_vars(&d.body))
                    || self.references_state_vars(body)
            }
            TlaExprKind::Range { lo, hi } => {
                self.references_state_vars(lo) || self.references_state_vars(hi)
            }
            TlaExprKind::Paren(inner) => self.references_state_vars(inner),
            TlaExprKind::Choose {
                domain, predicate, ..
            } => {
                domain
                    .as_ref()
                    .is_some_and(|d| self.references_state_vars(d))
                    || self.references_state_vars(predicate)
            }
            TlaExprKind::FunctionSet { domain, range } => {
                self.references_state_vars(domain) || self.references_state_vars(range)
            }
            TlaExprKind::RecordSet { fields } => {
                fields.iter().any(|(_, e)| self.references_state_vars(e))
            }
            TlaExprKind::Domain(e)
            | TlaExprKind::PowerSet(e)
            | TlaExprKind::BigUnion(e)
            | TlaExprKind::Always(e)
            | TlaExprKind::Eventually(e)
            | TlaExprKind::Enabled(e) => self.references_state_vars(e),
            TlaExprKind::LeadsTo { left, right }
            | TlaExprKind::BoxAction {
                action: left,
                vars: right,
            }
            | TlaExprKind::AngleAction {
                action: left,
                vars: right,
            } => self.references_state_vars(left) || self.references_state_vars(right),
            TlaExprKind::WeakFairness { vars, action }
            | TlaExprKind::StrongFairness { vars, action } => {
                self.references_state_vars(vars) || self.references_state_vars(action)
            }
            TlaExprKind::Unchanged(vars) => vars.iter().any(|v| self.state_vars.contains(&v.name)),
            _ => false,
        }
    }

    /// Check if an operator is a pure constant (no params, doesn't reference state vars).
    fn is_constant_operator(&self, params: &[TlaIdent], body: &TlaExpr) -> bool {
        params.is_empty() && !self.references_state_vars(body)
    }

    /// Check if an operator is a helper function (has params but is pure - no state refs, no primed vars).
    fn is_helper_operator(&self, params: &[TlaIdent], body: &TlaExpr) -> bool {
        !params.is_empty() && !self.references_state_vars(body) && !self.contains_primed_var(body)
    }

    /// Check if an operator is a stateful predicate (has params, references state, but no primed vars).
    /// These are read-only predicates that can be inlined at call sites.
    fn is_stateful_predicate(&self, params: &[TlaIdent], body: &TlaExpr) -> bool {
        !params.is_empty() && self.references_state_vars(body) && !self.contains_primed_var(body)
    }

    /// Collect constants that are used as set domains in expressions.
    fn collect_set_constants(&mut self, expr: &TlaExpr) {
        let mark_set_ident =
            |e: &TlaExpr, set_constants: &mut std::collections::HashSet<String>| {
                if let TlaExprKind::Ident(name) = &e.kind {
                    set_constants.insert(name.clone());
                }
            };
        match &expr.kind {
            TlaExprKind::FunctionDef { domain, body, .. } => {
                // [x \in S |-> e] - S is used as a set domain
                if let TlaExprKind::Ident(name) = &domain.kind {
                    self.set_constants.insert(name.clone());
                }
                self.collect_set_constants(domain);
                self.collect_set_constants(body);
            }
            TlaExprKind::Forall { bindings, body } | TlaExprKind::Exists { bindings, body } => {
                for binding in bindings {
                    if let TlaExprKind::Ident(name) = &binding.domain.kind {
                        self.set_constants.insert(name.clone());
                    }
                    self.collect_set_constants(&binding.domain);
                }
                self.collect_set_constants(body);
            }
            TlaExprKind::SetMap {
                domain, element, ..
            }
            | TlaExprKind::SetFilter {
                domain,
                predicate: element,
                ..
            } => {
                if let TlaExprKind::Ident(name) = &domain.kind {
                    self.set_constants.insert(name.clone());
                }
                self.collect_set_constants(domain);
                self.collect_set_constants(element);
            }
            TlaExprKind::Choose {
                domain, predicate, ..
            } => {
                if let Some(dom) = domain {
                    if let TlaExprKind::Ident(name) = &dom.kind {
                        self.set_constants.insert(name.clone());
                    }
                    self.collect_set_constants(dom);
                }
                self.collect_set_constants(predicate);
            }
            TlaExprKind::Binary { op, left, right } => {
                match op {
                    TlaBinOp::Cup | TlaBinOp::Cap | TlaBinOp::SetDiff | TlaBinOp::SubsetEq => {
                        mark_set_ident(left, &mut self.set_constants);
                        mark_set_ident(right, &mut self.set_constants);
                    }
                    TlaBinOp::In | TlaBinOp::NotIn => {
                        // x \in S => S is a set.
                        mark_set_ident(right, &mut self.set_constants);
                    }
                    _ => {}
                }
                self.collect_set_constants(left);
                self.collect_set_constants(right);
            }
            TlaExprKind::Unary { operand, .. } => self.collect_set_constants(operand),
            TlaExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => {
                self.collect_set_constants(cond);
                self.collect_set_constants(then_branch);
                self.collect_set_constants(else_branch);
            }
            TlaExprKind::SetEnum { elements } | TlaExprKind::Tuple { elements } => {
                for e in elements {
                    self.collect_set_constants(e);
                }
            }
            TlaExprKind::FunctionApp { func, args } => {
                self.collect_set_constants(func);
                for a in args {
                    self.collect_set_constants(a);
                }
            }
            TlaExprKind::OpApp { args, .. } => {
                for a in args {
                    self.collect_set_constants(a);
                }
            }
            TlaExprKind::Record { fields } => {
                for (_, e) in fields {
                    self.collect_set_constants(e);
                }
            }
            TlaExprKind::RecordSet { fields } => {
                for (_, domain) in fields {
                    if let TlaExprKind::Ident(name) = &domain.kind {
                        self.set_constants.insert(name.clone());
                    }
                    self.collect_set_constants(domain);
                }
            }
            TlaExprKind::FieldAccess { base, .. } => self.collect_set_constants(base),
            TlaExprKind::Except { base, updates } => {
                self.collect_set_constants(base);
                for u in updates {
                    for p in &u.path {
                        self.collect_set_constants(p);
                    }
                    self.collect_set_constants(&u.value);
                }
            }
            TlaExprKind::LetIn { defs, body } => {
                for d in defs {
                    self.collect_set_constants(&d.body);
                }
                self.collect_set_constants(body);
            }
            TlaExprKind::Paren(inner) | TlaExprKind::Primed(inner) => {
                self.collect_set_constants(inner);
            }
            TlaExprKind::Range { lo, hi } => {
                self.collect_set_constants(lo);
                self.collect_set_constants(hi);
            }
            TlaExprKind::Domain(inner)
            | TlaExprKind::PowerSet(inner)
            | TlaExprKind::BigUnion(inner) => {
                mark_set_ident(inner, &mut self.set_constants);
                self.collect_set_constants(inner);
            }
            _ => {}
        }
    }

    /// Infer variable types from Init expression.
    fn infer_types_from_init(&mut self, init_body: &TlaExpr) {
        self.extract_var_types(init_body);
    }

    /// Extract variable types from an init expression.
    fn extract_var_types(&mut self, expr: &TlaExpr) {
        match &expr.kind {
            TlaExprKind::Binary {
                op: TlaBinOp::And,
                left,
                right,
            } => {
                self.extract_var_types(left);
                self.extract_var_types(right);
            }
            TlaExprKind::Binary {
                op: TlaBinOp::Eq,
                left,
                right,
            } => {
                // var = expr pattern
                if let TlaExprKind::Ident(var_name) = &left.kind {
                    if self.state_vars.contains(var_name) {
                        if let Some(ty) = self.infer_type_from_expr(right) {
                            self.var_types.insert(var_name.clone(), ty);
                        }
                    }
                }
            }
            TlaExprKind::Binary {
                op: TlaBinOp::In,
                left,
                right,
            } => {
                // var \in S pattern - infer type from S
                if let TlaExprKind::Ident(var_name) = &left.kind {
                    if self.state_vars.contains(var_name) {
                        if let Some(ty) = self.infer_type_from_set_expr(right) {
                            self.var_types.insert(var_name.clone(), ty);
                        }
                    }
                }
            }
            TlaExprKind::Ident(name) => {
                // Inline init predicates (e.g., InitServerVars)
                if let Some(body) = self.init_predicates.get(name).cloned() {
                    self.extract_var_types(&body);
                }
            }
            TlaExprKind::OpApp { name, args } if args.is_empty() => {
                // Inline init predicates called without args
                if let Some(body) = self.init_predicates.get(name).cloned() {
                    self.extract_var_types(&body);
                }
            }
            _ => {}
        }
    }

    /// Infer Specl type from a TLA+ expression.
    fn infer_type_from_expr(&self, expr: &TlaExpr) -> Option<specl::TypeExpr> {
        let default_span = Span::default();
        match &expr.kind {
            TlaExprKind::FunctionDef { domain, body, .. } => {
                // [x \in S |-> e] - infer Dict[element_type_of(S), type_of(e)]
                // Use infer_type_from_set_expr for domain since it's a set expression
                // For empty domains {}, use "_" (inferred) type for the key
                let domain_ty = if let TlaExprKind::SetEnum { elements } = &domain.kind {
                    if elements.is_empty() {
                        // Empty domain - use inferred type for key
                        specl::TypeExpr::Named(specl::Ident::new("_", default_span))
                    } else {
                        self.infer_type_from_set_expr(domain).unwrap_or_else(|| {
                            specl::TypeExpr::Named(specl::Ident::new("_", default_span))
                        })
                    }
                } else {
                    self.infer_type_from_set_expr(domain).unwrap_or_else(|| {
                        specl::TypeExpr::Named(specl::Ident::new("_", default_span))
                    })
                };
                let body_ty = self.infer_type_from_expr(body).unwrap_or_else(|| {
                    specl::TypeExpr::Named(specl::Ident::new("_", default_span))
                });
                Some(specl::TypeExpr::Dict(
                    Box::new(domain_ty),
                    Box::new(body_ty),
                    default_span,
                ))
            }
            TlaExprKind::Range { lo, hi } => {
                // lo..hi - use as type directly
                let lo_expr = self.translate_expr(lo, false).ok()?;
                let hi_expr = self.translate_expr(hi, false).ok()?;
                Some(specl::TypeExpr::Range(
                    Box::new(lo_expr),
                    Box::new(hi_expr),
                    default_span,
                ))
            }
            TlaExprKind::Ident(name) => {
                // Try to resolve constant operators
                if let Some(body) = self.constant_ops.get(name) {
                    return self.infer_type_from_expr(body);
                }
                if self.set_constants.contains(name) {
                    return Some(specl::TypeExpr::Set(
                        Box::new(specl::TypeExpr::Named(specl::Ident::new("_", default_span))),
                        default_span,
                    ));
                }
                // For unresolved identifiers (TLA+ model values like Nil, Follower, Server, etc.),
                // use Int since model values are represented as integers
                Some(specl::TypeExpr::Named(specl::Ident::new(
                    "Int",
                    default_span,
                )))
            }
            TlaExprKind::Bool(_) => Some(specl::TypeExpr::Named(specl::Ident::new(
                "Bool",
                default_span,
            ))),
            TlaExprKind::Int(_) => Some(specl::TypeExpr::Named(specl::Ident::new(
                "Int",
                default_span,
            ))),
            TlaExprKind::String(_) => Some(specl::TypeExpr::Named(specl::Ident::new(
                "String",
                default_span,
            ))),
            TlaExprKind::SetEnum { elements } if !elements.is_empty() => {
                // For enum sets like {0, 1, 2}, try to infer element type
                self.infer_type_from_expr(&elements[0])
            }
            TlaExprKind::SetEnum { .. } => {
                // Empty set {} - keep element type inferred.
                Some(specl::TypeExpr::Set(
                    Box::new(specl::TypeExpr::Named(specl::Ident::new("_", default_span))),
                    default_span,
                ))
            }
            TlaExprKind::Tuple { elements } if elements.is_empty() => {
                // Empty sequence [] - use inferred type for elements
                Some(specl::TypeExpr::Seq(
                    Box::new(specl::TypeExpr::Named(specl::Ident::new("_", default_span))),
                    default_span,
                ))
            }
            TlaExprKind::Tuple { elements } => {
                // Non-empty sequence
                if let Some(elem_ty) = self.infer_type_from_expr(&elements[0]) {
                    Some(specl::TypeExpr::Seq(Box::new(elem_ty), default_span))
                } else {
                    Some(specl::TypeExpr::Seq(
                        Box::new(specl::TypeExpr::Named(specl::Ident::new(
                            "Int",
                            default_span,
                        ))),
                        default_span,
                    ))
                }
            }
            _ => None,
        }
    }

    /// Infer element type from a set expression (for x \in S patterns).
    fn infer_type_from_set_expr(&self, expr: &TlaExpr) -> Option<specl::TypeExpr> {
        let default_span = Span::default();
        match &expr.kind {
            TlaExprKind::FunctionSet { domain, range } => {
                // [S -> T] - element type is Fn[S, T]
                let domain_ty = self.infer_type_from_set_expr(domain)?;
                let range_ty = self.infer_type_from_set_expr(range)?;
                Some(specl::TypeExpr::Dict(
                    Box::new(domain_ty),
                    Box::new(range_ty),
                    default_span,
                ))
            }
            TlaExprKind::Range { lo, hi } => {
                let lo_expr = self.translate_expr(lo, false).ok()?;
                let hi_expr = self.translate_expr(hi, false).ok()?;
                Some(specl::TypeExpr::Range(
                    Box::new(lo_expr),
                    Box::new(hi_expr),
                    default_span,
                ))
            }
            TlaExprKind::SetEnum { elements } if !elements.is_empty() => {
                // Infer from first element
                self.infer_type_from_expr(&elements[0])
            }
            TlaExprKind::OpApp { name, .. } if name == "BOOLEAN" => Some(specl::TypeExpr::Named(
                specl::Ident::new("Bool", default_span),
            )),
            TlaExprKind::Ident(name) if name == "BOOLEAN" => Some(specl::TypeExpr::Named(
                specl::Ident::new("Bool", default_span),
            )),
            TlaExprKind::Ident(name) if name == "Nat" || name == "Int" => Some(
                specl::TypeExpr::Named(specl::Ident::new("Int", default_span)),
            ),
            TlaExprKind::Ident(_) => {
                // For abstract set identifiers (Server, Value, etc.), keep element type inferred.
                Some(specl::TypeExpr::Named(specl::Ident::new("_", default_span)))
            }
            _ => {
                // Default to Int if we can't infer
                None
            }
        }
    }

    /// Substitute parameter names in an expression with argument expressions.
    fn substitute_params(
        &self,
        expr: &TlaExpr,
        params: &[String],
        args: &[TlaExpr],
    ) -> Result<TlaExpr, TranslateError> {
        let substitutions: std::collections::HashMap<&str, &TlaExpr> =
            params.iter().map(|s| s.as_str()).zip(args.iter()).collect();
        self.substitute_in_expr(expr, &substitutions)
    }

    /// Inline local operator calls in an expression.
    /// local_ops maps operator names to (param_names, body).
    fn inline_local_ops(
        &self,
        expr: &TlaExpr,
        local_ops: &std::collections::HashMap<String, (Vec<String>, &TlaExpr)>,
    ) -> Result<TlaExpr, TranslateError> {
        let span = expr.span;
        let kind = match &expr.kind {
            TlaExprKind::OpApp { name, args } => {
                // Check if this is a call to a local operator
                if let Some((params, body)) = local_ops.get(name) {
                    if args.len() == params.len() {
                        // Inline: substitute params with args in body
                        let inlined_args: Vec<TlaExpr> = args
                            .iter()
                            .map(|a| self.inline_local_ops(a, local_ops))
                            .collect::<Result<_, _>>()?;
                        let subs: std::collections::HashMap<&str, &TlaExpr> = params
                            .iter()
                            .map(|s| s.as_str())
                            .zip(inlined_args.iter())
                            .collect();
                        let inlined = self.substitute_in_expr(body, &subs)?;
                        // Recursively inline any nested local op calls
                        return self.inline_local_ops(&inlined, local_ops);
                    }
                }
                // Not a local op call - recurse into args
                let new_args: Vec<TlaExpr> = args
                    .iter()
                    .map(|a| self.inline_local_ops(a, local_ops))
                    .collect::<Result<_, _>>()?;
                TlaExprKind::OpApp {
                    name: name.clone(),
                    args: new_args,
                }
            }
            // Recurse into subexpressions
            TlaExprKind::Binary { op, left, right } => TlaExprKind::Binary {
                op: *op,
                left: Box::new(self.inline_local_ops(left, local_ops)?),
                right: Box::new(self.inline_local_ops(right, local_ops)?),
            },
            TlaExprKind::Unary { op, operand } => TlaExprKind::Unary {
                op: *op,
                operand: Box::new(self.inline_local_ops(operand, local_ops)?),
            },
            TlaExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => TlaExprKind::IfThenElse {
                cond: Box::new(self.inline_local_ops(cond, local_ops)?),
                then_branch: Box::new(self.inline_local_ops(then_branch, local_ops)?),
                else_branch: Box::new(self.inline_local_ops(else_branch, local_ops)?),
            },
            TlaExprKind::FunctionApp { func, args } => {
                let new_args: Vec<TlaExpr> = args
                    .iter()
                    .map(|a| self.inline_local_ops(a, local_ops))
                    .collect::<Result<_, _>>()?;
                TlaExprKind::FunctionApp {
                    func: Box::new(self.inline_local_ops(func, local_ops)?),
                    args: new_args,
                }
            }
            TlaExprKind::Forall { bindings, body } => {
                let new_bindings: Vec<TlaBinding> = bindings
                    .iter()
                    .map(|b| {
                        Ok(TlaBinding {
                            var: b.var.clone(),
                            domain: self.inline_local_ops(&b.domain, local_ops)?,
                            span: b.span,
                        })
                    })
                    .collect::<Result<_, TranslateError>>()?;
                TlaExprKind::Forall {
                    bindings: new_bindings,
                    body: Box::new(self.inline_local_ops(body, local_ops)?),
                }
            }
            TlaExprKind::Exists { bindings, body } => {
                let new_bindings: Vec<TlaBinding> = bindings
                    .iter()
                    .map(|b| {
                        Ok(TlaBinding {
                            var: b.var.clone(),
                            domain: self.inline_local_ops(&b.domain, local_ops)?,
                            span: b.span,
                        })
                    })
                    .collect::<Result<_, TranslateError>>()?;
                TlaExprKind::Exists {
                    bindings: new_bindings,
                    body: Box::new(self.inline_local_ops(body, local_ops)?),
                }
            }
            TlaExprKind::SetMap {
                element,
                var,
                domain,
            } => TlaExprKind::SetMap {
                element: Box::new(self.inline_local_ops(element, local_ops)?),
                var: var.clone(),
                domain: Box::new(self.inline_local_ops(domain, local_ops)?),
            },
            TlaExprKind::SetFilter {
                var,
                domain,
                predicate,
            } => TlaExprKind::SetFilter {
                var: var.clone(),
                domain: Box::new(self.inline_local_ops(domain, local_ops)?),
                predicate: Box::new(self.inline_local_ops(predicate, local_ops)?),
            },
            TlaExprKind::Paren(inner) => {
                TlaExprKind::Paren(Box::new(self.inline_local_ops(inner, local_ops)?))
            }
            TlaExprKind::RecordSet { fields } => {
                let new_fields: Vec<(TlaIdent, TlaExpr)> = fields
                    .iter()
                    .map(|(name, domain)| {
                        Ok((name.clone(), self.inline_local_ops(domain, local_ops)?))
                    })
                    .collect::<Result<_, TranslateError>>()?;
                TlaExprKind::RecordSet { fields: new_fields }
            }
            // Pass through other expressions unchanged
            _ => expr.kind.clone(),
        };
        Ok(TlaExpr { kind, span })
    }

    fn substitute_in_expr(
        &self,
        expr: &TlaExpr,
        subs: &std::collections::HashMap<&str, &TlaExpr>,
    ) -> Result<TlaExpr, TranslateError> {
        let span = expr.span;
        let kind = match &expr.kind {
            TlaExprKind::Ident(name) => {
                if let Some(replacement) = subs.get(name.as_str()) {
                    return Ok((*replacement).clone());
                }
                TlaExprKind::Ident(name.clone())
            }
            TlaExprKind::Binary { op, left, right } => TlaExprKind::Binary {
                op: *op,
                left: Box::new(self.substitute_in_expr(left, subs)?),
                right: Box::new(self.substitute_in_expr(right, subs)?),
            },
            TlaExprKind::Unary { op, operand } => TlaExprKind::Unary {
                op: *op,
                operand: Box::new(self.substitute_in_expr(operand, subs)?),
            },
            TlaExprKind::FunctionApp { func, args } => TlaExprKind::FunctionApp {
                func: Box::new(self.substitute_in_expr(func, subs)?),
                args: args
                    .iter()
                    .map(|a| self.substitute_in_expr(a, subs))
                    .collect::<Result<Vec<_>, _>>()?,
            },
            TlaExprKind::OpApp { name, args } => TlaExprKind::OpApp {
                name: name.clone(),
                args: args
                    .iter()
                    .map(|a| self.substitute_in_expr(a, subs))
                    .collect::<Result<Vec<_>, _>>()?,
            },
            TlaExprKind::Paren(inner) => {
                TlaExprKind::Paren(Box::new(self.substitute_in_expr(inner, subs)?))
            }
            TlaExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => TlaExprKind::IfThenElse {
                cond: Box::new(self.substitute_in_expr(cond, subs)?),
                then_branch: Box::new(self.substitute_in_expr(then_branch, subs)?),
                else_branch: Box::new(self.substitute_in_expr(else_branch, subs)?),
            },
            // CHOOSE: substitute in domain and predicate (but not the bound var)
            TlaExprKind::Choose {
                var,
                domain,
                predicate,
            } => {
                // Remove the bound variable from substitutions to avoid capture
                let mut inner_subs = subs.clone();
                inner_subs.remove(var.name.as_str());
                let new_domain = match domain {
                    Some(d) => Some(Box::new(self.substitute_in_expr(d, subs)?)),
                    None => None,
                };
                TlaExprKind::Choose {
                    var: var.clone(),
                    domain: new_domain,
                    predicate: Box::new(self.substitute_in_expr(predicate, &inner_subs)?),
                }
            }
            // Quantifiers: substitute in bindings' domains and body
            TlaExprKind::Forall { bindings, body } => {
                let mut inner_subs = subs.clone();
                let new_bindings: Vec<TlaBinding> = bindings
                    .iter()
                    .map(|b| {
                        inner_subs.remove(b.var.name.as_str());
                        let binding = TlaBinding {
                            var: b.var.clone(),
                            domain: self.substitute_in_expr(&b.domain, subs)?,
                            span: b.span,
                        };
                        Ok::<_, TranslateError>(binding)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                TlaExprKind::Forall {
                    bindings: new_bindings,
                    body: Box::new(self.substitute_in_expr(body, &inner_subs)?),
                }
            }
            TlaExprKind::Exists { bindings, body } => {
                let mut inner_subs = subs.clone();
                let new_bindings: Vec<TlaBinding> = bindings
                    .iter()
                    .map(|b| {
                        inner_subs.remove(b.var.name.as_str());
                        let binding = TlaBinding {
                            var: b.var.clone(),
                            domain: self.substitute_in_expr(&b.domain, subs)?,
                            span: b.span,
                        };
                        Ok::<_, TranslateError>(binding)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                TlaExprKind::Exists {
                    bindings: new_bindings,
                    body: Box::new(self.substitute_in_expr(body, &inner_subs)?),
                }
            }
            // Set comprehensions
            TlaExprKind::SetMap {
                element,
                var,
                domain,
            } => {
                let mut inner_subs = subs.clone();
                inner_subs.remove(var.name.as_str());
                TlaExprKind::SetMap {
                    element: Box::new(self.substitute_in_expr(element, &inner_subs)?),
                    var: var.clone(),
                    domain: Box::new(self.substitute_in_expr(domain, subs)?),
                }
            }
            TlaExprKind::SetFilter {
                var,
                domain,
                predicate,
            } => {
                let mut inner_subs = subs.clone();
                inner_subs.remove(var.name.as_str());
                TlaExprKind::SetFilter {
                    var: var.clone(),
                    domain: Box::new(self.substitute_in_expr(domain, subs)?),
                    predicate: Box::new(self.substitute_in_expr(predicate, &inner_subs)?),
                }
            }
            // Function definition
            TlaExprKind::FunctionDef { var, domain, body } => {
                let mut inner_subs = subs.clone();
                inner_subs.remove(var.name.as_str());
                TlaExprKind::FunctionDef {
                    var: var.clone(),
                    domain: Box::new(self.substitute_in_expr(domain, subs)?),
                    body: Box::new(self.substitute_in_expr(body, &inner_subs)?),
                }
            }
            // Set enumeration
            TlaExprKind::SetEnum { elements } => TlaExprKind::SetEnum {
                elements: elements
                    .iter()
                    .map(|e| self.substitute_in_expr(e, subs))
                    .collect::<Result<Vec<_>, _>>()?,
            },
            // Tuple
            TlaExprKind::Tuple { elements } => TlaExprKind::Tuple {
                elements: elements
                    .iter()
                    .map(|e| self.substitute_in_expr(e, subs))
                    .collect::<Result<Vec<_>, _>>()?,
            },
            // Record
            TlaExprKind::Record { fields } => {
                let new_fields: Vec<(TlaIdent, TlaExpr)> = fields
                    .iter()
                    .map(|(name, e)| {
                        let new_e = self.substitute_in_expr(e, subs)?;
                        Ok::<_, TranslateError>((name.clone(), new_e))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                TlaExprKind::Record { fields: new_fields }
            }
            // Field access
            TlaExprKind::FieldAccess { base, field } => TlaExprKind::FieldAccess {
                base: Box::new(self.substitute_in_expr(base, subs)?),
                field: field.clone(),
            },
            // EXCEPT
            TlaExprKind::Except { base, updates } => {
                let new_updates: Vec<TlaExceptUpdate> = updates
                    .iter()
                    .map(|u| {
                        let new_path = u
                            .path
                            .iter()
                            .map(|k| self.substitute_in_expr(k, subs))
                            .collect::<Result<Vec<_>, _>>()?;
                        Ok::<_, TranslateError>(TlaExceptUpdate {
                            path: new_path,
                            value: self.substitute_in_expr(&u.value, subs)?,
                            span: u.span,
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                TlaExprKind::Except {
                    base: Box::new(self.substitute_in_expr(base, subs)?),
                    updates: new_updates,
                }
            }
            // Case
            TlaExprKind::Case { arms, other } => {
                let new_arms: Vec<(TlaExpr, TlaExpr)> = arms
                    .iter()
                    .map(|(cond, body)| {
                        let new_cond = self.substitute_in_expr(cond, subs)?;
                        let new_body = self.substitute_in_expr(body, subs)?;
                        Ok::<_, TranslateError>((new_cond, new_body))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                TlaExprKind::Case {
                    arms: new_arms,
                    other: other
                        .as_ref()
                        .map(|o| self.substitute_in_expr(o, subs))
                        .transpose()?
                        .map(Box::new),
                }
            }
            // Primed
            TlaExprKind::Primed(inner) => {
                TlaExprKind::Primed(Box::new(self.substitute_in_expr(inner, subs)?))
            }
            // SingletonFunction: k :> v
            TlaExprKind::SingletonFunction { key, value } => TlaExprKind::SingletonFunction {
                key: Box::new(self.substitute_in_expr(key, subs)?),
                value: Box::new(self.substitute_in_expr(value, subs)?),
            },
            // FunctionCombine: f @@ g
            TlaExprKind::FunctionCombine { left, right } => TlaExprKind::FunctionCombine {
                left: Box::new(self.substitute_in_expr(left, subs)?),
                right: Box::new(self.substitute_in_expr(right, subs)?),
            },
            // Domain (DOMAIN f)
            TlaExprKind::Domain(inner) => {
                TlaExprKind::Domain(Box::new(self.substitute_in_expr(inner, subs)?))
            }
            // Range: lo..hi
            TlaExprKind::Range { lo, hi } => TlaExprKind::Range {
                lo: Box::new(self.substitute_in_expr(lo, subs)?),
                hi: Box::new(self.substitute_in_expr(hi, subs)?),
            },
            // Pass through literals unchanged
            TlaExprKind::Int(n) => TlaExprKind::Int(*n),
            TlaExprKind::Bool(b) => TlaExprKind::Bool(*b),
            TlaExprKind::String(s) => TlaExprKind::String(s.clone()),
            // ExceptAt: @
            TlaExprKind::ExceptAt => TlaExprKind::ExceptAt,
            // RecordSet: [field: Domain, ...]
            TlaExprKind::RecordSet { fields } => {
                let new_fields: Vec<(TlaIdent, TlaExpr)> = fields
                    .iter()
                    .map(|(name, domain)| {
                        let new_domain = self.substitute_in_expr(domain, subs)?;
                        Ok::<_, TranslateError>((name.clone(), new_domain))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                TlaExprKind::RecordSet { fields: new_fields }
            }
            // LetIn: substitute in definitions and body, respecting scoping
            TlaExprKind::LetIn { defs, body } => {
                let mut inner_subs = subs.clone();
                let new_defs: Vec<TlaLetDef> = defs
                    .iter()
                    .map(|def| {
                        // Remove the defined name from substitutions to avoid capture
                        inner_subs.remove(def.name.name.as_str());
                        // Also remove params from substitutions for the body
                        let mut body_subs = inner_subs.clone();
                        for p in &def.params {
                            body_subs.remove(p.name.as_str());
                        }
                        // For recursive binding, remove the bound var too
                        if let Some(binding) = &def.recursive_binding {
                            body_subs.remove(binding.var.name.as_str());
                        }
                        // Substitute in recursive binding domain
                        let new_recursive_binding = match &def.recursive_binding {
                            Some(binding) => Some(TlaBinding {
                                var: binding.var.clone(),
                                domain: self.substitute_in_expr(&binding.domain, &inner_subs)?,
                                span: binding.span,
                            }),
                            None => None,
                        };
                        Ok::<_, TranslateError>(TlaLetDef {
                            name: def.name.clone(),
                            params: def.params.clone(),
                            recursive_binding: new_recursive_binding,
                            body: self.substitute_in_expr(&def.body, &body_subs)?,
                            span: def.span,
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                TlaExprKind::LetIn {
                    defs: new_defs,
                    body: Box::new(self.substitute_in_expr(body, &inner_subs)?),
                }
            }
            // For any remaining constructs, clone them
            other => other.clone(),
        };
        Ok(TlaExpr { kind, span })
    }

    /// Infer types for action parameters from their usage in the body.
    fn infer_param_types(
        &self,
        params: &[TlaIdent],
        body: &TlaExpr,
    ) -> std::collections::HashMap<String, specl::TypeExpr> {
        let mut types = std::collections::HashMap::new();
        let param_names: std::collections::HashSet<_> =
            params.iter().map(|p| p.name.as_str()).collect();
        self.collect_param_types_from_expr(body, &param_names, &mut types);
        types
    }

    fn maybe_set_param_type(
        &self,
        param_names: &std::collections::HashSet<&str>,
        types: &mut std::collections::HashMap<String, specl::TypeExpr>,
        name: &str,
        ty: specl::TypeExpr,
    ) {
        if param_names.contains(name) && !types.contains_key(name) {
            types.insert(name.to_string(), ty);
        }
    }

    /// Recursively collect type information for parameters from expression usage.
    fn collect_param_types_from_expr(
        &self,
        expr: &TlaExpr,
        param_names: &std::collections::HashSet<&str>,
        types: &mut std::collections::HashMap<String, specl::TypeExpr>,
    ) {
        let default_span = Span::default();
        match &expr.kind {
            // If a parameter is used as a quantifier domain, it's a Set
            TlaExprKind::Forall { bindings, body } | TlaExprKind::Exists { bindings, body } => {
                for binding in bindings {
                    if let TlaExprKind::Ident(name) = &binding.domain.kind {
                        if param_names.contains(name.as_str()) && !types.contains_key(name) {
                            types.insert(
                                name.clone(),
                                specl::TypeExpr::Set(
                                    Box::new(specl::TypeExpr::Named(specl::Ident::new(
                                        "_",
                                        default_span,
                                    ))),
                                    default_span,
                                ),
                            );
                        }
                    }
                    self.collect_param_types_from_expr(&binding.domain, param_names, types);
                }
                self.collect_param_types_from_expr(body, param_names, types);
            }
            // If a parameter is used in a function definition domain, it's a Set
            TlaExprKind::FunctionDef {
                var: _,
                domain,
                body,
            } => {
                if let TlaExprKind::Ident(name) = &domain.kind {
                    if param_names.contains(name.as_str()) && !types.contains_key(name) {
                        types.insert(
                            name.clone(),
                            specl::TypeExpr::Set(
                                Box::new(specl::TypeExpr::Named(specl::Ident::new(
                                    "_",
                                    default_span,
                                ))),
                                default_span,
                            ),
                        );
                    }
                }
                self.collect_param_types_from_expr(domain, param_names, types);
                self.collect_param_types_from_expr(body, param_names, types);
            }
            // If a parameter is used as a CHOOSE domain, it's a Set
            TlaExprKind::Choose {
                var: _,
                domain,
                predicate,
            } => {
                if let Some(dom) = domain {
                    if let TlaExprKind::Ident(name) = &dom.kind {
                        if param_names.contains(name.as_str()) && !types.contains_key(name) {
                            types.insert(
                                name.clone(),
                                specl::TypeExpr::Set(
                                    Box::new(specl::TypeExpr::Named(specl::Ident::new(
                                        "_",
                                        default_span,
                                    ))),
                                    default_span,
                                ),
                            );
                        }
                    }
                    self.collect_param_types_from_expr(dom, param_names, types);
                }
                self.collect_param_types_from_expr(predicate, param_names, types);
            }
            // Infer from binary operator contexts, then recurse.
            TlaExprKind::Binary { op, left, right } => {
                // Set-like contexts.
                if matches!(
                    op,
                    TlaBinOp::Cup | TlaBinOp::Cap | TlaBinOp::SetDiff | TlaBinOp::SubsetEq
                ) {
                    if let TlaExprKind::Ident(name) = &left.kind {
                        self.maybe_set_param_type(
                            param_names,
                            types,
                            name,
                            specl::TypeExpr::Set(
                                Box::new(specl::TypeExpr::Named(specl::Ident::new(
                                    "_",
                                    default_span,
                                ))),
                                default_span,
                            ),
                        );
                    }
                    if let TlaExprKind::Ident(name) = &right.kind {
                        self.maybe_set_param_type(
                            param_names,
                            types,
                            name,
                            specl::TypeExpr::Set(
                                Box::new(specl::TypeExpr::Named(specl::Ident::new(
                                    "_",
                                    default_span,
                                ))),
                                default_span,
                            ),
                        );
                    }
                }
                if matches!(op, TlaBinOp::In | TlaBinOp::NotIn) {
                    if let TlaExprKind::Ident(name) = &right.kind {
                        self.maybe_set_param_type(
                            param_names,
                            types,
                            name,
                            specl::TypeExpr::Set(
                                Box::new(specl::TypeExpr::Named(specl::Ident::new(
                                    "_",
                                    default_span,
                                ))),
                                default_span,
                            ),
                        );
                    }
                }
                // String equality/comparison contexts.
                if matches!(
                    op,
                    TlaBinOp::Eq
                        | TlaBinOp::Ne
                        | TlaBinOp::Lt
                        | TlaBinOp::Le
                        | TlaBinOp::Gt
                        | TlaBinOp::Ge
                ) {
                    if let (TlaExprKind::Ident(name), TlaExprKind::String(_)) =
                        (&left.kind, &right.kind)
                    {
                        self.maybe_set_param_type(
                            param_names,
                            types,
                            name,
                            specl::TypeExpr::Named(specl::Ident::new("String", default_span)),
                        );
                    }
                    if let (TlaExprKind::String(_), TlaExprKind::Ident(name)) =
                        (&left.kind, &right.kind)
                    {
                        self.maybe_set_param_type(
                            param_names,
                            types,
                            name,
                            specl::TypeExpr::Named(specl::Ident::new("String", default_span)),
                        );
                    }
                }
                self.collect_param_types_from_expr(left, param_names, types);
                self.collect_param_types_from_expr(right, param_names, types);
            }
            TlaExprKind::Unary { operand, .. } => {
                self.collect_param_types_from_expr(operand, param_names, types);
            }
            TlaExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => {
                self.collect_param_types_from_expr(cond, param_names, types);
                self.collect_param_types_from_expr(then_branch, param_names, types);
                self.collect_param_types_from_expr(else_branch, param_names, types);
            }
            TlaExprKind::LetIn { defs, body } => {
                for def in defs {
                    self.collect_param_types_from_expr(&def.body, param_names, types);
                }
                self.collect_param_types_from_expr(body, param_names, types);
            }
            TlaExprKind::FunctionApp { func, args } => {
                // If p appears as index in dict_var[p], infer key type from dict_var.
                if args.len() == 1 {
                    if let TlaExprKind::Ident(arg_name) = &args[0].kind {
                        if let TlaExprKind::Ident(func_name) = &func.kind {
                            if let Some(specl::TypeExpr::Dict(key_ty, _, _)) =
                                self.var_types.get(func_name)
                            {
                                self.maybe_set_param_type(
                                    param_names,
                                    types,
                                    arg_name,
                                    (*key_ty.clone()).clone(),
                                );
                            }
                        }
                    }
                }
                self.collect_param_types_from_expr(func, param_names, types);
                for arg in args {
                    self.collect_param_types_from_expr(arg, param_names, types);
                }
            }
            TlaExprKind::OpApp { args, .. } => {
                for arg in args {
                    self.collect_param_types_from_expr(arg, param_names, types);
                }
            }
            TlaExprKind::SetEnum { elements } | TlaExprKind::Tuple { elements } => {
                for elem in elements {
                    self.collect_param_types_from_expr(elem, param_names, types);
                }
            }
            TlaExprKind::Record { fields } => {
                for (_, e) in fields {
                    self.collect_param_types_from_expr(e, param_names, types);
                }
            }
            TlaExprKind::Except { base, updates } => {
                self.collect_param_types_from_expr(base, param_names, types);
                for update in updates {
                    for p in &update.path {
                        self.collect_param_types_from_expr(p, param_names, types);
                    }
                    self.collect_param_types_from_expr(&update.value, param_names, types);
                }
            }
            TlaExprKind::Paren(inner) | TlaExprKind::Primed(inner) => {
                self.collect_param_types_from_expr(inner, param_names, types);
            }
            _ => {}
        }
    }

    fn translate_module(&self, module: &TlaModule) -> Result<specl::Module, TranslateError> {
        let mut translator = Translator::new();

        // First pass: collect state variables
        for decl in &module.declarations {
            if let TlaDecl::Variable { names, .. } = decl {
                for name in names {
                    translator.state_vars.push(name.name.clone());
                }
            }
        }

        // Select the module's init predicate operator.
        // Prefer a canonical `Init`; otherwise fall back to a single no-arg `*Init` operator.
        let mut init_operator_name: Option<String> = None;
        for decl in &module.declarations {
            if let TlaDecl::Operator { name, params, .. } = decl {
                if params.is_empty() && name.name == "Init" {
                    init_operator_name = Some(name.name.clone());
                    break;
                }
            }
        }
        if init_operator_name.is_none() {
            for decl in &module.declarations {
                if let TlaDecl::Operator { name, params, .. } = decl {
                    if params.is_empty() && name.name.ends_with("Init") {
                        init_operator_name = Some(name.name.clone());
                        break;
                    }
                }
            }
        }

        // Second pass: collect constant, helper, and init predicate operators (for inlining)
        for decl in &module.declarations {
            if let TlaDecl::Operator {
                name, params, body, ..
            } = decl
            {
                // Track recursive operators — these must not be inlined
                if Translator::body_references_self(&name.name, body) {
                    translator.recursive_ops.insert(name.name.clone());
                }
                if params.is_empty()
                    && !translator.contains_primed_var(body)
                    && !translator.recursive_ops.contains(&name.name)
                {
                    translator
                        .zero_arg_ops
                        .insert(name.name.clone(), body.clone());
                }
                if translator.is_constant_operator(params, body) {
                    translator
                        .constant_ops
                        .insert(name.name.clone(), body.clone());
                } else if translator.is_helper_operator(params, body) {
                    // Helper operators: have params but are pure (no state refs, no primed vars)
                    let param_names: Vec<String> = params.iter().map(|p| p.name.clone()).collect();
                    translator
                        .helper_ops
                        .insert(name.name.clone(), (param_names, body.clone()));
                } else if translator.is_stateful_predicate(params, body) {
                    // Stateful predicates: have params, reference state, but don't modify state
                    let param_names: Vec<String> = params.iter().map(|p| p.name.clone()).collect();
                    translator
                        .stateful_predicates
                        .insert(name.name.clone(), (param_names, body.clone()));
                } else if !params.is_empty() && translator.contains_primed_var(body) {
                    // Action helpers with params: modify state (primed vars)
                    // These should be inlined at call sites rather than emitted as actions
                    let param_names: Vec<String> = params.iter().map(|p| p.name.clone()).collect();
                    translator
                        .action_helpers
                        .insert(name.name.clone(), (param_names, body.clone()));
                } else if params.is_empty() && name.name.starts_with("Init") {
                    // Init predicate operators: no params, used for inlining in Init
                    translator
                        .init_predicates
                        .insert(name.name.clone(), body.clone());
                }
            }
        }

        // Third pass: infer variable types from the selected init operator, and collect set constants
        for decl in &module.declarations {
            if let TlaDecl::Operator { name, body, .. } = decl {
                if init_operator_name
                    .as_ref()
                    .is_some_and(|init_name| init_name == &name.name)
                {
                    translator.infer_types_from_init(body);
                    translator.collect_set_constants(body);
                }
            }
        }

        // Also scan all operator bodies for set constant usage
        for decl in &module.declarations {
            if let TlaDecl::Operator { body, .. } = decl {
                translator.collect_set_constants(body);
            }
        }

        // Fourth pass: translate declarations
        let mut decls = Vec::new();

        // Translate constants
        for decl in &module.declarations {
            if let TlaDecl::Constant { names, span } = decl {
                for name in names {
                    let ty = if translator.set_constants.contains(&name.name) {
                        // Constants used as set domains are sets of model values.
                        specl::TypeExpr::Set(
                            Box::new(specl::TypeExpr::Named(specl::Ident::new(
                                "_",
                                translate_span(name.span),
                            ))),
                            translate_span(name.span),
                        )
                    } else {
                        // Other constants are Int (model values)
                        specl::TypeExpr::Named(specl::Ident::new("Int", translate_span(name.span)))
                    };
                    decls.push(specl::Decl::Const(specl::ConstDecl {
                        name: specl::Ident::new(
                            escape_ident(&name.name),
                            translate_span(name.span),
                        ),
                        value: specl::ConstValue::Type(ty),
                        default_value: None,
                        span: translate_span(*span),
                    }));
                }
            }
        }

        // Translate variables with inferred types
        for decl in &module.declarations {
            if let TlaDecl::Variable { names, span } = decl {
                for name in names {
                    let ty = translator
                        .var_types
                        .get(&name.name)
                        .cloned()
                        .unwrap_or_else(|| {
                            specl::TypeExpr::Named(specl::Ident::new(
                                "Int",
                                translate_span(name.span),
                            ))
                        });
                    decls.push(specl::Decl::Var(specl::VarDecl {
                        name: specl::Ident::new(
                            escape_ident(&name.name),
                            translate_span(name.span),
                        ),
                        ty,
                        span: translate_span(*span),
                    }));
                }
            }
        }

        // Find and translate Init
        for decl in &module.declarations {
            if let TlaDecl::Operator {
                name, body, span, ..
            } = decl
            {
                if init_operator_name
                    .as_ref()
                    .is_some_and(|init_name| init_name == &name.name)
                {
                    let init_expr = translator.translate_init_expr(body)?;
                    decls.push(specl::Decl::Init(specl::InitDecl {
                        body: init_expr,
                        span: translate_span(*span),
                    }));
                }
            }
        }

        // Translate other operators as actions
        let mut actions = Vec::new();

        for decl in &module.declarations {
            if let TlaDecl::Operator {
                name,
                params,
                body,
                span,
            } = decl
            {
                if init_operator_name
                    .as_ref()
                    .is_some_and(|init_name| init_name == &name.name)
                {
                    continue;
                }
                match name.name.as_str() {
                    // Skip Init, Spec, vars, and Next - Specl auto-generates next from actions
                    "Init" | "Spec" | "vars" | "Next" => continue,
                    // Skip operators ending in Vars (variable groupings for UNCHANGED/VIEW)
                    n if n.ends_with("Vars") => continue,
                    // Skip operators starting with Init (init helper predicates)
                    n if n.starts_with("Init") => continue,
                    // Skip view and symmetry definitions
                    "view" | "symmServers" | "symmValues" => continue,
                    // Skip liveness-related operators
                    n if n.contains("Stuck")
                        || n.contains("Liveness")
                        || n == "NoStuttering"
                        || n == "LivenessSpec" =>
                    {
                        continue
                    }
                    _ => {
                        // Skip constant operators - they'll be inlined when referenced
                        if translator.is_constant_operator(params, body) {
                            continue;
                        }
                        // Skip helper operators - they'll be inlined when referenced
                        if translator.is_helper_operator(params, body) {
                            continue;
                        }
                        // Check if this looks like an action (has primed variables in body)
                        if translator.is_action_body(body) {
                            let action = translator.translate_action(name, params, body, *span)?;
                            actions.push(action);
                        } else if params.is_empty() && translator.is_invariant(body) {
                            // Translate as invariant (only if no params)
                            let inv = translator.translate_invariant(name, body, *span)?;
                            decls.push(specl::Decl::Invariant(inv));
                        }
                    }
                }
            }
        }

        // Add actions to declarations
        for action in actions {
            decls.push(specl::Decl::Action(action));
        }

        // Emit helper/stateful funcs only when there is executable/checkable behavior in the module.
        // Some corpus modules are pure ASSUME/definition files; emitting unused helpers there can
        // introduce translator-only artifacts that fail Specl type checking.
        // Exception: recursive operators are always emitted (they cannot be inlined).
        let has_behavioral_decl = decls.iter().any(|d| {
            matches!(
                d,
                specl::Decl::Init(_)
                    | specl::Decl::Action(_)
                    | specl::Decl::Invariant(_)
                    | specl::Decl::Property(_)
            )
        });
        // Always emit recursive operators as func declarations
        for (name, (params, body)) in &translator.helper_ops {
            if translator.recursive_ops.contains(name) {
                let func_decl = translator.translate_func(name, params, body)?;
                decls.push(specl::Decl::Func(func_decl));
            }
        }
        if has_behavioral_decl {
            // Emit non-recursive helper operators as func declarations
            for (name, (params, body)) in &translator.helper_ops {
                if !translator.recursive_ops.contains(name) {
                    let func_decl = translator.translate_func(name, params, body)?;
                    decls.push(specl::Decl::Func(func_decl));
                }
            }

            // Also emit stateful predicates as func declarations (they reference state but don't modify it)
            for (name, (params, body)) in &translator.stateful_predicates {
                let func_decl = translator.translate_func(name, params, body)?;
                decls.push(specl::Decl::Func(func_decl));
            }
        }

        // Note: Specl auto-generates next from all actions, so we don't emit a next block

        Ok(specl::Module {
            name: specl::Ident::new(escape_ident(&module.name), translate_span(module.span)),
            decls,
            span: translate_span(module.span),
        })
    }

    fn is_action_body(&self, expr: &TlaExpr) -> bool {
        self.contains_primed_var(expr)
    }

    fn is_and_expr(&self, expr: &TlaExpr) -> bool {
        matches!(
            &expr.kind,
            TlaExprKind::Binary {
                op: TlaBinOp::And,
                ..
            }
        )
    }

    fn collect_and_conjuncts(expr: &TlaExpr, out: &mut Vec<TlaExpr>) {
        match &expr.kind {
            TlaExprKind::Binary {
                op: TlaBinOp::And,
                left,
                right,
            } => {
                Self::collect_and_conjuncts(left, out);
                Self::collect_and_conjuncts(right, out);
            }
            _ => out.push(expr.clone()),
        }
    }

    /// Extract the guard (precondition) from an action body.
    /// Returns only the parts that don't contain primed variables.
    fn extract_guard(&self, expr: &TlaExpr) -> Result<TlaExpr, TranslateError> {
        let span = expr.span;
        match &expr.kind {
            TlaExprKind::Binary {
                op: TlaBinOp::And,
                left,
                right,
            } => {
                let left_has_primed = self.contains_primed_var(left);
                let right_has_primed = self.contains_primed_var(right);

                match (left_has_primed, right_has_primed) {
                    (false, false) => {
                        // Both sides are guards
                        Ok(expr.clone())
                    }
                    (false, true) => {
                        // Left is guard, right contains effects
                        Ok((**left).clone())
                    }
                    (true, false) => {
                        // Left contains effects, right is guard
                        Ok((**right).clone())
                    }
                    (true, true) => {
                        // Both sides contain effects - try to extract guards from each
                        let left_guard = self.extract_guard(left)?;
                        let right_guard = self.extract_guard(right)?;
                        // Combine non-trivial guards
                        if let TlaExprKind::Bool(true) = &left_guard.kind {
                            Ok(right_guard)
                        } else if let TlaExprKind::Bool(true) = &right_guard.kind {
                            Ok(left_guard)
                        } else {
                            Ok(TlaExpr {
                                kind: TlaExprKind::Binary {
                                    op: TlaBinOp::And,
                                    left: Box::new(left_guard),
                                    right: Box::new(right_guard),
                                },
                                span,
                            })
                        }
                    }
                }
            }
            _ => {
                // Non-And expression: if it has primed vars, return true (no guard)
                // Otherwise return the expression itself
                if self.contains_primed_var(expr) {
                    Ok(TlaExpr {
                        kind: TlaExprKind::Bool(true),
                        span,
                    })
                } else {
                    Ok(expr.clone())
                }
            }
        }
    }

    fn needs_parens_in_range(&self, expr: &TlaExpr) -> bool {
        // Field access needs parens: 1..m.field -> 1..(m.field)
        // Other complex expressions also need parens to be safe
        matches!(
            &expr.kind,
            TlaExprKind::FieldAccess { .. }
                | TlaExprKind::FunctionApp { .. }
                | TlaExprKind::Binary { .. }
        )
    }

    fn contains_primed_var(&self, expr: &TlaExpr) -> bool {
        match &expr.kind {
            TlaExprKind::Primed(_) => true,
            TlaExprKind::Binary { left, right, .. } => {
                self.contains_primed_var(left) || self.contains_primed_var(right)
            }
            TlaExprKind::Unary { operand, .. } => self.contains_primed_var(operand),
            TlaExprKind::Forall { body, .. } => self.contains_primed_var(body),
            TlaExprKind::Exists { body, .. } => self.contains_primed_var(body),
            TlaExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => {
                self.contains_primed_var(cond)
                    || self.contains_primed_var(then_branch)
                    || self.contains_primed_var(else_branch)
            }
            TlaExprKind::Unchanged(_) => true,
            TlaExprKind::LetIn { defs, body } => {
                defs.iter().any(|d| self.contains_primed_var(&d.body))
                    || self.contains_primed_var(body)
            }
            TlaExprKind::Paren(inner) => self.contains_primed_var(inner),
            TlaExprKind::FunctionApp { func, args } => {
                self.contains_primed_var(func) || args.iter().any(|a| self.contains_primed_var(a))
            }
            TlaExprKind::OpApp { name, args } => {
                // Check if the operator being called is an action helper (has primed vars in body)
                if self.action_helpers.contains_key(name) {
                    return true;
                }
                args.iter().any(|a| self.contains_primed_var(a))
            }
            TlaExprKind::Except { base, updates } => {
                self.contains_primed_var(base)
                    || updates.iter().any(|u| {
                        u.path.iter().any(|p| self.contains_primed_var(p))
                            || self.contains_primed_var(&u.value)
                    })
            }
            _ => false,
        }
    }

    fn is_invariant(&self, expr: &TlaExpr) -> bool {
        // An invariant is a predicate that:
        // - References state variables (otherwise it's a constant)
        // - Has no primed variables
        // - Has no temporal operators
        // - Is not just a tuple/sequence definition (variable grouping)
        // - Is not an Init-style assignment predicate
        self.references_state_vars(expr)
            && !self.contains_primed_var(expr)
            && !self.contains_temporal_or_spec_refs(expr)
            && !self.is_tuple_definition(expr)
            && !self.is_init_style_predicate(expr)
    }

    /// Check if expression is just a tuple definition (used for variable groupings).
    fn is_tuple_definition(&self, expr: &TlaExpr) -> bool {
        matches!(&expr.kind, TlaExprKind::Tuple { .. })
    }

    /// Check if expression looks like an Init predicate (conjunction of assignments).
    /// Init predicates are /\ var = expr patterns without quantifiers over state.
    fn is_init_style_predicate(&self, expr: &TlaExpr) -> bool {
        self.is_all_equality_assignments(expr)
    }

    /// Check if expression is a conjunction of simple equality assignments.
    fn is_all_equality_assignments(&self, expr: &TlaExpr) -> bool {
        match &expr.kind {
            TlaExprKind::Binary {
                op: TlaBinOp::And,
                left,
                right,
            } => self.is_all_equality_assignments(left) && self.is_all_equality_assignments(right),
            TlaExprKind::Binary {
                op: TlaBinOp::Eq,
                left,
                ..
            } => {
                // var = expr pattern
                if let TlaExprKind::Ident(name) = &left.kind {
                    self.state_vars.contains(name)
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    /// Check if expression contains temporal operators or references to Init/Next/Spec
    fn contains_temporal_or_spec_refs(&self, expr: &TlaExpr) -> bool {
        match &expr.kind {
            TlaExprKind::Always(_)
            | TlaExprKind::Eventually(_)
            | TlaExprKind::LeadsTo { .. }
            | TlaExprKind::BoxAction { .. }
            | TlaExprKind::AngleAction { .. }
            | TlaExprKind::WeakFairness { .. }
            | TlaExprKind::StrongFairness { .. }
            | TlaExprKind::Enabled(_) => true,
            TlaExprKind::Ident(name) => {
                matches!(name.as_str(), "Init" | "Next" | "Spec" | "vars")
            }
            TlaExprKind::OpApp { name, args } => {
                matches!(name.as_str(), "Init" | "Next" | "Spec" | "vars")
                    || args.iter().any(|a| self.contains_temporal_or_spec_refs(a))
            }
            TlaExprKind::Binary { left, right, .. } => {
                self.contains_temporal_or_spec_refs(left)
                    || self.contains_temporal_or_spec_refs(right)
            }
            TlaExprKind::Unary { operand, .. } => self.contains_temporal_or_spec_refs(operand),
            TlaExprKind::Forall { bindings, body } | TlaExprKind::Exists { bindings, body } => {
                bindings
                    .iter()
                    .any(|b| self.contains_temporal_or_spec_refs(&b.domain))
                    || self.contains_temporal_or_spec_refs(body)
            }
            TlaExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => {
                self.contains_temporal_or_spec_refs(cond)
                    || self.contains_temporal_or_spec_refs(then_branch)
                    || self.contains_temporal_or_spec_refs(else_branch)
            }
            TlaExprKind::Paren(inner) => self.contains_temporal_or_spec_refs(inner),
            _ => false,
        }
    }

    fn translate_init_expr(&self, expr: &TlaExpr) -> Result<specl::Expr, TranslateError> {
        // In Init, translate x = e as x == e (equality constraint)
        self.translate_expr(expr, false)
    }

    fn translate_action(
        &self,
        name: &TlaIdent,
        params: &[TlaIdent],
        body: &TlaExpr,
        span: crate::token::Span,
    ) -> Result<specl::ActionDecl, TranslateError> {
        // Pre-inline action helpers at TLA AST level
        // This ensures that all assignments (including those in helpers) are visible
        // for primed variable substitution
        let inlined_body = self.inline_action_helpers(body)?;

        // First pass: collect all assignments x' = E to build substitution map
        let mut assignment_map: std::collections::HashMap<String, TlaExpr> =
            std::collections::HashMap::new();
        self.collect_assignments(&inlined_body, &mut assignment_map);

        // Second pass: collect guards and effects, substituting primed vars on RHS
        let mut requires = Vec::new();
        let mut effects = Vec::new();

        self.extract_action_parts_with_subs(
            &inlined_body,
            &mut requires,
            &mut effects,
            &assignment_map,
        )?;

        // Build the action body
        let effect = if effects.is_empty() {
            None
        } else if effects.len() == 1 {
            Some(effects.remove(0))
        } else {
            // Combine effects with 'and'
            let mut combined = effects.remove(0);
            for eff in effects {
                combined = specl::Expr::new(
                    specl::ExprKind::Binary {
                        op: specl::BinOp::And,
                        left: Box::new(combined.clone()),
                        right: Box::new(eff),
                    },
                    translate_span(span),
                );
            }
            Some(combined)
        };

        // Infer parameter types from usage in the inlined body
        let param_types = self.infer_param_types(params, &inlined_body);
        let specl_params: Vec<specl::Param> = params
            .iter()
            .map(|p| {
                let ty = param_types.get(&p.name).cloned().unwrap_or_else(|| {
                    specl::TypeExpr::Named(specl::Ident::new("Int", translate_span(p.span)))
                });
                specl::Param {
                    name: specl::Ident::new(escape_ident(&p.name), translate_span(p.span)),
                    ty,
                    span: translate_span(p.span),
                }
            })
            .collect();

        Ok(specl::ActionDecl {
            name: specl::Ident::new(escape_ident(&name.name), translate_span(name.span)),
            params: specl_params,
            body: specl::ActionBody {
                requires,
                effect,
                span: translate_span(span),
            },
            span: translate_span(span),
        })
    }

    /// Collect all assignments x' = E from an action body.
    fn collect_assignments(
        &self,
        expr: &TlaExpr,
        assignments: &mut std::collections::HashMap<String, TlaExpr>,
    ) {
        match &expr.kind {
            TlaExprKind::Binary {
                op: TlaBinOp::And,
                left,
                right,
            } => {
                self.collect_assignments(left, assignments);
                self.collect_assignments(right, assignments);
            }
            TlaExprKind::Binary {
                op: TlaBinOp::Eq,
                left,
                right,
            } => {
                if let TlaExprKind::Primed(inner) = &left.kind {
                    if let TlaExprKind::Ident(var_name) = &inner.kind {
                        assignments.insert(var_name.clone(), (**right).clone());
                    }
                }
            }
            _ => {}
        }
    }

    /// Substitute primed variables on RHS with their assignment expressions.
    fn substitute_primed_vars(
        &self,
        expr: &TlaExpr,
        assignments: &std::collections::HashMap<String, TlaExpr>,
    ) -> TlaExpr {
        let span = expr.span;
        let kind = match &expr.kind {
            TlaExprKind::Primed(inner) => {
                if let TlaExprKind::Ident(var_name) = &inner.kind {
                    if let Some(replacement) = assignments.get(var_name) {
                        // Recursively substitute in the replacement, then wrap in parens
                        let substituted = self.substitute_primed_vars(replacement, assignments);
                        // Wrap in parens to ensure correct precedence
                        return TlaExpr {
                            kind: TlaExprKind::Paren(Box::new(substituted)),
                            span,
                        };
                    }
                }
                expr.kind.clone()
            }
            TlaExprKind::Binary { op, left, right } => TlaExprKind::Binary {
                op: *op,
                left: Box::new(self.substitute_primed_vars(left, assignments)),
                right: Box::new(self.substitute_primed_vars(right, assignments)),
            },
            TlaExprKind::Unary { op, operand } => TlaExprKind::Unary {
                op: *op,
                operand: Box::new(self.substitute_primed_vars(operand, assignments)),
            },
            TlaExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => TlaExprKind::IfThenElse {
                cond: Box::new(self.substitute_primed_vars(cond, assignments)),
                then_branch: Box::new(self.substitute_primed_vars(then_branch, assignments)),
                else_branch: Box::new(self.substitute_primed_vars(else_branch, assignments)),
            },
            TlaExprKind::FunctionApp { func, args } => TlaExprKind::FunctionApp {
                func: Box::new(self.substitute_primed_vars(func, assignments)),
                args: args
                    .iter()
                    .map(|a| self.substitute_primed_vars(a, assignments))
                    .collect(),
            },
            TlaExprKind::Paren(inner) => {
                TlaExprKind::Paren(Box::new(self.substitute_primed_vars(inner, assignments)))
            }
            _ => expr.kind.clone(),
        };
        TlaExpr { kind, span }
    }

    /// Inline action helper calls at the TLA AST level.
    /// This is needed to properly collect assignments from action helpers
    /// so that primed variables on RHS can be substituted correctly.
    fn inline_action_helpers(&self, expr: &TlaExpr) -> Result<TlaExpr, TranslateError> {
        let span = expr.span;
        let kind = match &expr.kind {
            // Handle bare identifier that might be a no-param action helper
            TlaExprKind::Ident(name) => {
                if let Some((params, body)) = self.action_helpers.get(name).cloned() {
                    if params.is_empty() {
                        // Inline the no-param action helper
                        let fully_inlined = self.inline_action_helpers(&body)?;
                        return Ok(TlaExpr {
                            kind: TlaExprKind::Paren(Box::new(fully_inlined)),
                            span,
                        });
                    }
                }
                expr.kind.clone()
            }
            TlaExprKind::OpApp { name, args } => {
                // First inline in arguments
                let inlined_args: Vec<TlaExpr> = args
                    .iter()
                    .map(|a| self.inline_action_helpers(a))
                    .collect::<Result<_, _>>()?;

                // Check if this is an action helper
                if let Some((params, body)) = self.action_helpers.get(name).cloned() {
                    if inlined_args.len() == params.len() {
                        // Substitute params with args in the helper body
                        let substituted = self.substitute_params(&body, &params, &inlined_args)?;
                        // Recursively inline any nested action helper calls
                        let fully_inlined = self.inline_action_helpers(&substituted)?;
                        return Ok(TlaExpr {
                            kind: TlaExprKind::Paren(Box::new(fully_inlined)),
                            span,
                        });
                    }
                }
                TlaExprKind::OpApp {
                    name: name.clone(),
                    args: inlined_args,
                }
            }
            TlaExprKind::Binary { op, left, right } => TlaExprKind::Binary {
                op: *op,
                left: Box::new(self.inline_action_helpers(left)?),
                right: Box::new(self.inline_action_helpers(right)?),
            },
            TlaExprKind::Unary { op, operand } => TlaExprKind::Unary {
                op: *op,
                operand: Box::new(self.inline_action_helpers(operand)?),
            },
            TlaExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => TlaExprKind::IfThenElse {
                cond: Box::new(self.inline_action_helpers(cond)?),
                then_branch: Box::new(self.inline_action_helpers(then_branch)?),
                else_branch: Box::new(self.inline_action_helpers(else_branch)?),
            },
            TlaExprKind::FunctionApp { func, args } => TlaExprKind::FunctionApp {
                func: Box::new(self.inline_action_helpers(func)?),
                args: args
                    .iter()
                    .map(|a| self.inline_action_helpers(a))
                    .collect::<Result<Vec<_>, _>>()?,
            },
            TlaExprKind::Paren(inner) => {
                TlaExprKind::Paren(Box::new(self.inline_action_helpers(inner)?))
            }
            TlaExprKind::LetIn { defs, body } => {
                let new_defs: Vec<TlaLetDef> = defs
                    .iter()
                    .map(|d| {
                        Ok(TlaLetDef {
                            name: d.name.clone(),
                            params: d.params.clone(),
                            recursive_binding: d.recursive_binding.clone(),
                            body: self.inline_action_helpers(&d.body)?,
                            span: d.span,
                        })
                    })
                    .collect::<Result<_, TranslateError>>()?;
                TlaExprKind::LetIn {
                    defs: new_defs,
                    body: Box::new(self.inline_action_helpers(body)?),
                }
            }
            TlaExprKind::Forall { bindings, body } => {
                let new_bindings: Vec<TlaBinding> = bindings
                    .iter()
                    .map(|b| {
                        Ok(TlaBinding {
                            var: b.var.clone(),
                            domain: self.inline_action_helpers(&b.domain)?,
                            span: b.span,
                        })
                    })
                    .collect::<Result<_, TranslateError>>()?;
                TlaExprKind::Forall {
                    bindings: new_bindings,
                    body: Box::new(self.inline_action_helpers(body)?),
                }
            }
            TlaExprKind::Exists { bindings, body } => {
                let new_bindings: Vec<TlaBinding> = bindings
                    .iter()
                    .map(|b| {
                        Ok(TlaBinding {
                            var: b.var.clone(),
                            domain: self.inline_action_helpers(&b.domain)?,
                            span: b.span,
                        })
                    })
                    .collect::<Result<_, TranslateError>>()?;
                TlaExprKind::Exists {
                    bindings: new_bindings,
                    body: Box::new(self.inline_action_helpers(body)?),
                }
            }
            TlaExprKind::SetMap {
                element,
                var,
                domain,
            } => TlaExprKind::SetMap {
                element: Box::new(self.inline_action_helpers(element)?),
                var: var.clone(),
                domain: Box::new(self.inline_action_helpers(domain)?),
            },
            TlaExprKind::SetFilter {
                var,
                domain,
                predicate,
            } => TlaExprKind::SetFilter {
                var: var.clone(),
                domain: Box::new(self.inline_action_helpers(domain)?),
                predicate: Box::new(self.inline_action_helpers(predicate)?),
            },
            TlaExprKind::FunctionDef { var, domain, body } => TlaExprKind::FunctionDef {
                var: var.clone(),
                domain: Box::new(self.inline_action_helpers(domain)?),
                body: Box::new(self.inline_action_helpers(body)?),
            },
            TlaExprKind::Choose {
                var,
                domain,
                predicate,
            } => TlaExprKind::Choose {
                var: var.clone(),
                domain: domain
                    .as_ref()
                    .map(|d| self.inline_action_helpers(d))
                    .transpose()?
                    .map(Box::new),
                predicate: Box::new(self.inline_action_helpers(predicate)?),
            },
            _ => expr.kind.clone(),
        };
        Ok(TlaExpr { kind, span })
    }

    fn extract_action_parts_with_subs(
        &self,
        expr: &TlaExpr,
        requires: &mut Vec<specl::Expr>,
        effects: &mut Vec<specl::Expr>,
        assignments: &std::collections::HashMap<String, TlaExpr>,
    ) -> Result<(), TranslateError> {
        match &expr.kind {
            TlaExprKind::LetIn { defs, body } => {
                if matches!(
                    &body.kind,
                    TlaExprKind::Binary {
                        op: TlaBinOp::And,
                        ..
                    }
                ) {
                    let mut conjuncts = Vec::new();
                    Self::collect_and_conjuncts(body, &mut conjuncts);
                    for conjunct in conjuncts {
                        let wrapped = TlaExpr {
                            kind: TlaExprKind::LetIn {
                                defs: defs.clone(),
                                body: Box::new(conjunct),
                            },
                            span: expr.span,
                        };
                        self.extract_action_parts_with_subs(
                            &wrapped,
                            requires,
                            effects,
                            assignments,
                        )?;
                    }
                    return Ok(());
                }
                if self.contains_primed_var(expr) {
                    effects.push(self.translate_effect_with_subs(expr, assignments)?);
                } else {
                    requires.push(self.translate_expr(expr, false)?);
                }
                return Ok(());
            }
            TlaExprKind::Binary {
                op: TlaBinOp::And,
                left,
                right,
            } => {
                self.extract_action_parts_with_subs(left, requires, effects, assignments)?;
                self.extract_action_parts_with_subs(right, requires, effects, assignments)?;
            }
            TlaExprKind::Unchanged(_) => {
                // Skip UNCHANGED - Specl uses implicit frame
            }
            _ => {
                if self.contains_primed_var(expr) {
                    // This is an effect - substitute primed vars on RHS
                    effects.push(self.translate_effect_with_subs(expr, assignments)?);
                } else {
                    // This is a guard
                    requires.push(self.translate_expr(expr, false)?);
                }
            }
        }
        Ok(())
    }

    fn translate_effect_with_subs(
        &self,
        expr: &TlaExpr,
        assignments: &std::collections::HashMap<String, TlaExpr>,
    ) -> Result<specl::Expr, TranslateError> {
        // Translate x' = e to x = e (Specl assignment syntax in actions)
        // In Specl AST, assignments are represented as Primed(x) == e
        // The pretty printer converts this to the syntactic sugar `x = e`
        match &expr.kind {
            // Handle Paren by unwrapping
            TlaExprKind::Paren(inner) => {
                return self.translate_effect_with_subs(inner, assignments);
            }
            // Handle compound effects (from inlined action helpers)
            TlaExprKind::Binary {
                op: TlaBinOp::And,
                left,
                right,
            } => {
                let left_expr = self.translate_effect_with_subs(left, assignments)?;
                let right_expr = self.translate_effect_with_subs(right, assignments)?;
                return Ok(specl::Expr::new(
                    specl::ExprKind::Binary {
                        op: specl::BinOp::And,
                        left: Box::new(left_expr),
                        right: Box::new(right_expr),
                    },
                    translate_span(expr.span),
                ));
            }
            TlaExprKind::Binary {
                op: TlaBinOp::Eq,
                left,
                right,
            } => {
                if let TlaExprKind::Primed(inner) = &left.kind {
                    if let TlaExprKind::Ident(var_name) = &inner.kind {
                        // x' = e becomes Primed(x) == e in Specl AST
                        // which the pretty printer outputs as `x = e`
                        let var_expr = specl::Expr::new(
                            specl::ExprKind::Primed(var_name.clone()),
                            translate_span(left.span),
                        );
                        // Substitute any primed vars in RHS with their assignment expressions
                        let substituted_rhs = self.substitute_primed_vars(right, assignments);
                        let value_expr = self.translate_expr(&substituted_rhs, true)?;
                        return Ok(specl::Expr::new(
                            specl::ExprKind::Binary {
                                op: specl::BinOp::Eq,
                                left: Box::new(var_expr),
                                right: Box::new(value_expr),
                            },
                            translate_span(expr.span),
                        ));
                    }
                }
            }
            _ => {}
        }

        // Fall back to general translation
        self.translate_expr(expr, true)
    }

    fn translate_invariant(
        &self,
        name: &TlaIdent,
        body: &TlaExpr,
        span: crate::token::Span,
    ) -> Result<specl::InvariantDecl, TranslateError> {
        let body_expr = self.translate_expr(body, false)?;
        Ok(specl::InvariantDecl {
            name: specl::Ident::new(escape_ident(&name.name), translate_span(name.span)),
            body: body_expr,
            span: translate_span(span),
            is_auxiliary: false,
        })
    }

    /// Translate a helper operator to a func declaration.
    fn translate_func(
        &self,
        name: &str,
        params: &[String],
        body: &TlaExpr,
    ) -> Result<specl::FuncDecl, TranslateError> {
        let default_span = Span::default();
        let body_expr = self.translate_expr(body, false)?;

        let specl_params: Vec<specl::FuncParam> = params
            .iter()
            .map(|p| specl::FuncParam {
                name: specl::Ident::new(escape_ident(p), default_span),
                span: default_span,
            })
            .collect();

        Ok(specl::FuncDecl {
            name: specl::Ident::new(escape_ident(name), default_span),
            params: specl_params,
            body: body_expr,
            span: default_span,
        })
    }

    /// Translate an expression inside an EXCEPT value, replacing @ with at_replacement.
    fn translate_except_value(
        &self,
        expr: &TlaExpr,
        in_action: bool,
        at_replacement: &specl::Expr,
    ) -> Result<specl::Expr, TranslateError> {
        let span = translate_span(expr.span);

        match &expr.kind {
            TlaExprKind::ExceptAt => {
                // Replace @ with the precomputed replacement expression
                Ok(at_replacement.clone())
            }

            // Recursively handle expressions that might contain @
            TlaExprKind::Binary { op, left, right } => {
                let left_expr = self.translate_except_value(left, in_action, at_replacement)?;
                let right_expr = self.translate_except_value(right, in_action, at_replacement)?;
                Ok(specl::Expr::new(
                    specl::ExprKind::Binary {
                        op: translate_binop(*op),
                        left: Box::new(left_expr),
                        right: Box::new(right_expr),
                    },
                    span,
                ))
            }

            TlaExprKind::Unary { op, operand } => {
                let operand_expr =
                    self.translate_except_value(operand, in_action, at_replacement)?;
                let specl_op = match op {
                    TlaUnaryOp::Not => specl::UnaryOp::Not,
                    TlaUnaryOp::Neg => specl::UnaryOp::Neg,
                };
                Ok(specl::Expr::new(
                    specl::ExprKind::Unary {
                        op: specl_op,
                        operand: Box::new(operand_expr),
                    },
                    span,
                ))
            }

            TlaExprKind::OpApp { name, args } => {
                // Handle standard library operators within EXCEPT context
                let kind = match name.as_str() {
                    "Head" => {
                        let arg =
                            self.translate_except_value(&args[0], in_action, at_replacement)?;
                        specl::ExprKind::SeqHead(Box::new(arg))
                    }
                    "Tail" => {
                        let arg =
                            self.translate_except_value(&args[0], in_action, at_replacement)?;
                        specl::ExprKind::SeqTail(Box::new(arg))
                    }
                    "Len" | "Cardinality" => {
                        let arg =
                            self.translate_except_value(&args[0], in_action, at_replacement)?;
                        specl::ExprKind::Len(Box::new(arg))
                    }
                    "Append" => {
                        let seq =
                            self.translate_except_value(&args[0], in_action, at_replacement)?;
                        let elem =
                            self.translate_except_value(&args[1], in_action, at_replacement)?;
                        specl::ExprKind::Binary {
                            op: specl::BinOp::Concat,
                            left: Box::new(seq),
                            right: Box::new(specl::Expr::new(
                                specl::ExprKind::SeqLit(vec![elem]),
                                span,
                            )),
                        }
                    }
                    "SubSeq" => {
                        let seq =
                            self.translate_except_value(&args[0], in_action, at_replacement)?;
                        let lo =
                            self.translate_except_value(&args[1], in_action, at_replacement)?;
                        let hi =
                            self.translate_except_value(&args[2], in_action, at_replacement)?;
                        specl::ExprKind::Slice {
                            base: Box::new(seq),
                            lo: Box::new(lo),
                            hi: Box::new(hi),
                        }
                    }
                    _ => {
                        let translated_args: Result<Vec<_>, _> = args
                            .iter()
                            .map(|a| self.translate_except_value(a, in_action, at_replacement))
                            .collect();
                        specl::ExprKind::Call {
                            func: Box::new(specl::Expr::new(
                                specl::ExprKind::Ident(name.clone()),
                                span,
                            )),
                            args: translated_args?,
                        }
                    }
                };
                Ok(specl::Expr::new(kind, span))
            }

            TlaExprKind::FunctionApp { func, args } => {
                let func_expr = self.translate_except_value(func, in_action, at_replacement)?;
                if args.len() == 1 {
                    let arg_expr =
                        self.translate_except_value(&args[0], in_action, at_replacement)?;
                    Ok(specl::Expr::new(
                        specl::ExprKind::Index {
                            base: Box::new(func_expr),
                            index: Box::new(arg_expr),
                        },
                        span,
                    ))
                } else {
                    // Multi-arg function application - use tuple index
                    let tuple_args: Result<Vec<_>, _> = args
                        .iter()
                        .map(|a| self.translate_except_value(a, in_action, at_replacement))
                        .collect();
                    Ok(specl::Expr::new(
                        specl::ExprKind::Index {
                            base: Box::new(func_expr),
                            index: Box::new(specl::Expr::new(
                                specl::ExprKind::TupleLit(tuple_args?),
                                span,
                            )),
                        },
                        span,
                    ))
                }
            }

            TlaExprKind::Tuple { elements } => {
                let elems: Result<Vec<_>, _> = elements
                    .iter()
                    .map(|e| self.translate_except_value(e, in_action, at_replacement))
                    .collect();
                Ok(specl::Expr::new(specl::ExprKind::SeqLit(elems?), span))
            }

            TlaExprKind::SetEnum { elements } => {
                let elems: Result<Vec<_>, _> = elements
                    .iter()
                    .map(|e| self.translate_except_value(e, in_action, at_replacement))
                    .collect();
                Ok(specl::Expr::new(specl::ExprKind::SetLit(elems?), span))
            }

            TlaExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => {
                let cond_expr = self.translate_except_value(cond, in_action, at_replacement)?;
                let then_expr =
                    self.translate_except_value(then_branch, in_action, at_replacement)?;
                let else_expr =
                    self.translate_except_value(else_branch, in_action, at_replacement)?;
                Ok(specl::Expr::new(
                    specl::ExprKind::If {
                        cond: Box::new(cond_expr),
                        then_branch: Box::new(then_expr),
                        else_branch: Box::new(else_expr),
                    },
                    span,
                ))
            }

            TlaExprKind::Paren(inner) => {
                self.translate_except_value(inner, in_action, at_replacement)
            }

            TlaExprKind::Forall { bindings, body } => {
                let bindings_specl: Result<Vec<_>, _> =
                    bindings.iter().map(|b| self.translate_binding(b)).collect();
                let body_expr = self.translate_except_value(body, in_action, at_replacement)?;
                let wrapped_body =
                    specl::Expr::new(specl::ExprKind::Paren(Box::new(body_expr)), span);
                Ok(specl::Expr::new(
                    specl::ExprKind::Quantifier {
                        kind: specl::QuantifierKind::Forall,
                        bindings: bindings_specl?,
                        body: Box::new(wrapped_body),
                    },
                    span,
                ))
            }

            TlaExprKind::Exists { bindings, body } => {
                let bindings_specl: Result<Vec<_>, _> =
                    bindings.iter().map(|b| self.translate_binding(b)).collect();
                let body_expr = self.translate_except_value(body, in_action, at_replacement)?;
                let wrapped_body =
                    specl::Expr::new(specl::ExprKind::Paren(Box::new(body_expr)), span);
                Ok(specl::Expr::new(
                    specl::ExprKind::Quantifier {
                        kind: specl::QuantifierKind::Exists,
                        bindings: bindings_specl?,
                        body: Box::new(wrapped_body),
                    },
                    span,
                ))
            }

            TlaExprKind::Except { base, updates } => {
                // Nested EXCEPT — translate with its own @ context
                let mut result = self.translate_except_value(base, in_action, at_replacement)?;
                let base_for_at = result.clone();
                for update in updates {
                    if update.path.len() == 1 {
                        let key = self.translate_except_value(
                            &update.path[0],
                            in_action,
                            at_replacement,
                        )?;
                        let inner_at = specl::Expr::new(
                            specl::ExprKind::Index {
                                base: Box::new(base_for_at.clone()),
                                index: Box::new(key.clone()),
                            },
                            span,
                        );
                        let value =
                            self.translate_except_value(&update.value, in_action, &inner_at)?;
                        result = specl::Expr::new(
                            specl::ExprKind::RecordUpdate {
                                base: Box::new(result),
                                updates: vec![specl::RecordFieldUpdate::Dynamic { key, value }],
                            },
                            span,
                        );
                    } else {
                        // Fall back to normal translation for nested multi-key EXCEPT
                        return self.translate_expr(expr, in_action);
                    }
                }
                Ok(result)
            }

            TlaExprKind::LetIn { defs, body } => {
                // Translate LET-IN, propagating @ context into the body
                let body_expr = self.translate_except_value(body, in_action, at_replacement)?;
                let translated_defs = defs
                    .iter()
                    .map(|d| {
                        let def_body = self.translate_expr(&d.body, in_action)?;
                        Ok((d.name.name.clone(), def_body))
                    })
                    .collect::<Result<Vec<_>, TranslateError>>()?;
                let mut result = body_expr;
                for (name, def_body) in translated_defs.into_iter().rev() {
                    result = specl::Expr::new(
                        specl::ExprKind::Let {
                            var: specl::Ident::new(&name, span),
                            value: Box::new(def_body),
                            body: Box::new(result),
                        },
                        span,
                    );
                }
                Ok(result)
            }

            // Expressions that don't contain @ - delegate to normal translation
            TlaExprKind::Bool(_)
            | TlaExprKind::Int(_)
            | TlaExprKind::String(_)
            | TlaExprKind::Ident(_)
            | TlaExprKind::Primed(_) => self.translate_expr(expr, in_action),

            // For other complex expressions, fall back to normal translation
            // (This may fail if they contain @, but handles most common cases)
            _ => self.translate_expr(expr, in_action),
        }
    }

    /// Try to inline one level of an operator reference.
    ///
    /// Returns the inlined body and whether the result needs Paren wrapping
    /// (OpApp inlinings need Paren for precedence safety; Ident inlinings do not).
    /// Returns None when the expression is not an inlinable reference.
    fn try_inline(&self, expr: &TlaExpr) -> Result<Option<(TlaExpr, bool)>, TranslateError> {
        match &expr.kind {
            TlaExprKind::Ident(name) => Ok(self
                .constant_ops
                .get(name)
                .or_else(|| self.init_predicates.get(name))
                .or_else(|| self.zero_arg_ops.get(name))
                .cloned()
                .map(|body| (body, false))),
            TlaExprKind::OpApp { name, args } if !self.recursive_ops.contains(name) => {
                if args.is_empty() {
                    if let Some(body) = self.constant_ops.get(name) {
                        return Ok(Some((body.clone(), true)));
                    }
                }
                if let Some((params, body)) = self.helper_ops.get(name) {
                    if args.len() == params.len() {
                        return Ok(Some((self.substitute_params(body, params, args)?, true)));
                    }
                }
                if let Some((params, body)) = self.stateful_predicates.get(name) {
                    if args.len() == params.len() {
                        return Ok(Some((self.substitute_params(body, params, args)?, true)));
                    }
                }
                if let Some((params, body)) = self.action_helpers.get(name) {
                    if args.len() == params.len() {
                        return Ok(Some((self.substitute_params(body, params, args)?, true)));
                    }
                }
                Ok(None)
            }
            _ => Ok(None),
        }
    }

    /// Translate a TLA+ expression to a Specl expression.
    ///
    /// Iteratively resolves operator inlining (constant_ops, zero_arg_ops, helper_ops,
    /// stateful_predicates, action_helpers) before delegating to translate_expr_impl.
    /// This avoids deep recursion from chained inlining and keeps the recursion depth
    /// bounded by the structural AST tree depth (≤ ~9 after the balanced-tree parser fix).
    fn translate_expr(
        &self,
        expr: &TlaExpr,
        in_action: bool,
    ) -> Result<specl::Expr, TranslateError> {
        // `owned` holds the latest inlined body so `current` can borrow from it.
        // The initial None is a placeholder; it's always overwritten before being read.
        #[allow(unused_assignments)]
        let mut owned: Option<TlaExpr> = None;
        let mut current: &TlaExpr = expr;
        let mut wrap_paren = false;

        while let Some((body, needs_paren)) = self.try_inline(current)? {
            if needs_paren {
                wrap_paren = true;
            }
            owned = Some(body);
            current = owned.as_ref().unwrap();
        }

        let result = self.translate_expr_impl(current, in_action)?;
        if wrap_paren {
            let span = translate_span(current.span);
            Ok(specl::Expr::new(
                specl::ExprKind::Paren(Box::new(result)),
                span,
            ))
        } else {
            Ok(result)
        }
    }

    fn translate_expr_impl(
        &self,
        expr: &TlaExpr,
        in_action: bool,
    ) -> Result<specl::Expr, TranslateError> {
        let span = translate_span(expr.span);
        let kind = match &expr.kind {
            TlaExprKind::Bool(b) => specl::ExprKind::Bool(*b),
            TlaExprKind::Int(n) => specl::ExprKind::Int(*n),
            TlaExprKind::String(s) => specl::ExprKind::String(s.clone()),
            TlaExprKind::Ident(name) => {
                // Inlining is handled by the translate_expr trampoline; this arm sees
                // only identifiers that are not in any inline map.
                specl::ExprKind::Ident(escape_ident(name))
            }

            TlaExprKind::Primed(inner) => {
                if let TlaExprKind::Ident(name) = &inner.kind {
                    specl::ExprKind::Primed(escape_ident(name))
                } else {
                    return Err(TranslateError::Unsupported {
                        message: "complex primed expression".to_string(),
                    });
                }
            }

            TlaExprKind::Binary { op, left, right } => {
                // Special case: x \in [S -> T] (membership in function set)
                if *op == TlaBinOp::In {
                    if let TlaExprKind::FunctionSet { domain, range } = &right.kind {
                        return self.translate_in_fn_set(left, domain, range, in_action, span);
                    }

                    // Special case: x \in Nat  --> x >= 0
                    if let TlaExprKind::Ident(name) = &right.kind {
                        if name == "Nat" {
                            let x = self.translate_expr(left, in_action)?;
                            return Ok(specl::Expr::new(
                                specl::ExprKind::Binary {
                                    op: specl::BinOp::Ge,
                                    left: Box::new(x),
                                    right: Box::new(specl::Expr::new(
                                        specl::ExprKind::Int(0),
                                        span,
                                    )),
                                },
                                span,
                            ));
                        }
                        // x \in Int --> true (all values are integers in Specl)
                        if name == "Int" {
                            return Ok(specl::Expr::new(specl::ExprKind::Bool(true), span));
                        }
                        // x \in BOOLEAN --> x in {true, false}
                        if name == "BOOLEAN" {
                            let x = self.translate_expr(left, in_action)?;
                            return Ok(specl::Expr::new(
                                specl::ExprKind::Binary {
                                    op: specl::BinOp::In,
                                    left: Box::new(x),
                                    right: Box::new(specl::Expr::new(
                                        specl::ExprKind::SetLit(vec![
                                            specl::Expr::new(specl::ExprKind::Bool(true), span),
                                            specl::Expr::new(specl::ExprKind::Bool(false), span),
                                        ]),
                                        span,
                                    )),
                                },
                                span,
                            ));
                        }
                    }

                    // Special case: x \in Seq(S) (membership in sequence set)
                    if let TlaExprKind::OpApp { name, args } = &right.kind {
                        if name == "Seq" && args.len() == 1 {
                            return self.translate_in_seq(left, &args[0], in_action, span);
                        }
                    }
                }

                // Special case: NotIn is translated to not (x in S) since Specl
                // parser doesn't understand "x not in S" syntax
                if *op == TlaBinOp::NotIn {
                    let left_expr = self.translate_expr(left, in_action)?;
                    let right_expr = self.translate_expr(right, in_action)?;
                    let in_expr = specl::Expr::new(
                        specl::ExprKind::Binary {
                            op: specl::BinOp::In,
                            left: Box::new(left_expr),
                            right: Box::new(right_expr),
                        },
                        span,
                    );
                    return Ok(specl::Expr::new(
                        specl::ExprKind::Unary {
                            op: specl::UnaryOp::Not,
                            operand: Box::new(in_expr),
                        },
                        span,
                    ));
                }

                let left_expr = self.translate_expr(left, in_action)?;
                let right_expr = self.translate_expr(right, in_action)?;
                let specl_op = translate_binop(*op);

                // In TLA+, /\ and \/ have the SAME precedence (unlike most languages).
                // TLA+ uses indentation (bullet point notation) to disambiguate.
                // In Specl, `and` binds tighter than `or`, so `A and B or C and D`
                // parses as `(A and B) or (C and D)` which matches TLA's indented form.
                // We wrap AND operands in parens when inside OR for clarity.
                let final_left = if *op == TlaBinOp::Or && self.is_and_expr(left) {
                    specl::Expr::new(specl::ExprKind::Paren(Box::new(left_expr)), span)
                } else {
                    left_expr
                };
                let final_right = if *op == TlaBinOp::Or && self.is_and_expr(right) {
                    specl::Expr::new(specl::ExprKind::Paren(Box::new(right_expr)), span)
                } else {
                    right_expr
                };

                specl::ExprKind::Binary {
                    op: specl_op,
                    left: Box::new(final_left),
                    right: Box::new(final_right),
                }
            }

            TlaExprKind::Unary { op, operand } => {
                let operand_expr = self.translate_expr(operand, in_action)?;
                let specl_op = match op {
                    TlaUnaryOp::Not => specl::UnaryOp::Not,
                    TlaUnaryOp::Neg => specl::UnaryOp::Neg,
                };
                specl::ExprKind::Unary {
                    op: specl_op,
                    operand: Box::new(operand_expr),
                }
            }

            TlaExprKind::Forall { bindings, body } => {
                let bindings_specl: Result<Vec<_>, _> =
                    bindings.iter().map(|b| self.translate_binding(b)).collect();
                let body_expr = self.translate_expr(body, in_action)?;
                // Wrap body in parentheses to avoid `in` ambiguity with let...in
                let wrapped_body =
                    specl::Expr::new(specl::ExprKind::Paren(Box::new(body_expr)), span);
                specl::ExprKind::Quantifier {
                    kind: specl::QuantifierKind::Forall,
                    bindings: bindings_specl?,
                    body: Box::new(wrapped_body),
                }
            }

            TlaExprKind::Exists { bindings, body } => {
                let bindings_specl: Result<Vec<_>, _> =
                    bindings.iter().map(|b| self.translate_binding(b)).collect();
                let body_expr = self.translate_expr(body, in_action)?;
                // Wrap body in parentheses to avoid `in` ambiguity with let...in
                let wrapped_body =
                    specl::Expr::new(specl::ExprKind::Paren(Box::new(body_expr)), span);
                specl::ExprKind::Quantifier {
                    kind: specl::QuantifierKind::Exists,
                    bindings: bindings_specl?,
                    body: Box::new(wrapped_body),
                }
            }

            TlaExprKind::Choose {
                var,
                domain,
                predicate,
            } => {
                // Handle CHOOSE without domain: CHOOSE x : P(x)
                // We need to find a sensible domain from the predicate
                // For now, translate to a CHOOSE with an explicit check expression
                let pred_expr = self.translate_expr(predicate, in_action)?;
                // Wrap predicate in parentheses to avoid `in` ambiguity with let...in
                let wrapped_pred =
                    specl::Expr::new(specl::ExprKind::Paren(Box::new(pred_expr)), span);

                let domain_expr = domain
                    .as_ref()
                    .map(|dom| self.translate_expr(dom, in_action))
                    .transpose()?;
                specl::ExprKind::Fix {
                    var: specl::Ident::new(escape_ident(&var.name), translate_span(var.span)),
                    domain: domain_expr.map(Box::new),
                    predicate: Box::new(wrapped_pred),
                }
            }

            TlaExprKind::FunctionDef { var, domain, body } => {
                // Detect pattern: [index \in 1..n |-> seq[index]]
                // This is semantically a slice: seq[1..n]
                if let TlaExprKind::Range { lo, hi } = &domain.kind {
                    // Check if lo is 1 (integer literal)
                    if let TlaExprKind::Int(1) = &lo.kind {
                        // Check if body is seq[var] where var is the bound variable
                        if let TlaExprKind::FunctionApp { func, args } = &body.kind {
                            if args.len() == 1 {
                                if let TlaExprKind::Ident(arg_name) = &args[0].kind {
                                    if arg_name == &var.name {
                                        // Pattern matched! Emit slice: func[1..hi]
                                        let base_expr = self.translate_expr(func, in_action)?;
                                        let lo_expr =
                                            specl::Expr::new(specl::ExprKind::Int(1), span);
                                        let hi_expr = self.translate_expr(hi, in_action)?;
                                        return Ok(specl::Expr::new(
                                            specl::ExprKind::Slice {
                                                base: Box::new(base_expr),
                                                lo: Box::new(lo_expr),
                                                hi: Box::new(hi_expr),
                                            },
                                            span,
                                        ));
                                    }
                                }
                            }
                        }
                    }
                }
                // Default: translate as function literal
                let domain_expr = self.translate_expr(domain, in_action)?;
                let body_expr = self.translate_expr(body, in_action)?;
                specl::ExprKind::FnLit {
                    var: specl::Ident::new(escape_ident(&var.name), translate_span(var.span)),
                    domain: Box::new(domain_expr),
                    body: Box::new(body_expr),
                }
            }

            TlaExprKind::FunctionSet { domain, range } => {
                // Handle [S -> {e}] as a singleton containing the constant function
                if let TlaExprKind::SetEnum { elements } = &range.kind {
                    if elements.len() == 1 {
                        // [S -> {e}] = { fn(i in S) => e }
                        let domain_expr = self.translate_expr(domain, in_action)?;
                        let elem_expr = self.translate_expr(&elements[0], in_action)?;
                        let var = specl::Ident::new("__x", span);
                        let fn_expr = specl::Expr::new(
                            specl::ExprKind::FnLit {
                                var: var.clone(),
                                domain: Box::new(domain_expr),
                                body: Box::new(elem_expr),
                            },
                            span,
                        );
                        return Ok(specl::Expr::new(
                            specl::ExprKind::SetLit(vec![fn_expr]),
                            span,
                        ));
                    }
                }
                // General case: [S -> T] - emit a warning since this is infinite
                // For now, translate as a call to fn_set which should be defined in prelude
                let domain_expr = self.translate_expr(domain, in_action)?;
                let range_expr = self.translate_expr(range, in_action)?;
                specl::ExprKind::Call {
                    func: Box::new(specl::Expr::new(
                        specl::ExprKind::Ident("fn_set".to_string()),
                        span,
                    )),
                    args: vec![domain_expr, range_expr],
                }
            }

            TlaExprKind::FunctionApp { func, args } => {
                let func_expr = self.translate_expr(func, in_action)?;
                if args.len() == 1 {
                    let arg_expr = self.translate_expr(&args[0], in_action)?;
                    specl::ExprKind::Index {
                        base: Box::new(func_expr),
                        index: Box::new(arg_expr),
                    }
                } else {
                    // Multiple args - use tuple index
                    let args_translated: Result<Vec<_>, _> = args
                        .iter()
                        .map(|a| self.translate_expr(a, in_action))
                        .collect();
                    let tuple = specl::Expr::new(
                        specl::ExprKind::TupleLit(args_translated?),
                        translate_span(expr.span),
                    );
                    specl::ExprKind::Index {
                        base: Box::new(func_expr),
                        index: Box::new(tuple),
                    }
                }
            }

            TlaExprKind::OpApp { name, args } => {
                // Translate standard library operators
                match name.as_str() {
                    "Head" => {
                        let arg = self.translate_expr(&args[0], in_action)?;
                        specl::ExprKind::SeqHead(Box::new(arg))
                    }
                    "Tail" => {
                        let arg = self.translate_expr(&args[0], in_action)?;
                        specl::ExprKind::SeqTail(Box::new(arg))
                    }
                    "Len" | "Cardinality" => {
                        let arg = self.translate_expr(&args[0], in_action)?;
                        specl::ExprKind::Len(Box::new(arg))
                    }
                    "Append" => {
                        let seq = self.translate_expr(&args[0], in_action)?;
                        let elem = self.translate_expr(&args[1], in_action)?;
                        // s ++ [e]
                        specl::ExprKind::Binary {
                            op: specl::BinOp::Concat,
                            left: Box::new(seq),
                            right: Box::new(specl::Expr::new(
                                specl::ExprKind::SeqLit(vec![elem]),
                                span,
                            )),
                        }
                    }
                    "SubSeq" => {
                        // SubSeq(s, m, n) -> s[m..n] (slice)
                        let seq = self.translate_expr(&args[0], in_action)?;
                        let lo = self.translate_expr(&args[1], in_action)?;
                        let hi = self.translate_expr(&args[2], in_action)?;
                        specl::ExprKind::Slice {
                            base: Box::new(seq),
                            lo: Box::new(lo),
                            hi: Box::new(hi),
                        }
                    }
                    "IsPrefix" => {
                        // IsPrefix(a, b) means a is a prefix of b
                        // Translate to: len(a) <= len(b) and forall i in 0..(len(a)-1): a[i] == b[i]
                        // For now, just emit a call - it can be defined in Specl prelude
                        let a = self.translate_expr(&args[0], in_action)?;
                        let b = self.translate_expr(&args[1], in_action)?;
                        specl::ExprKind::Call {
                            func: Box::new(specl::Expr::new(
                                specl::ExprKind::Ident("is_prefix".to_string()),
                                span,
                            )),
                            args: vec![a, b],
                        }
                    }
                    "Seq" => {
                        // Seq(S) is the set of all sequences over S
                        // For model checking, we'll use a finite approximation
                        // Just pass through as a call for now
                        let arg = self.translate_expr(&args[0], in_action)?;
                        specl::ExprKind::Call {
                            func: Box::new(specl::Expr::new(
                                specl::ExprKind::Ident("Seq".to_string()),
                                span,
                            )),
                            args: vec![arg],
                        }
                    }
                    "Range" => {
                        // Range(f) is like DOMAIN
                        let arg = self.translate_expr(&args[0], in_action)?;
                        specl::ExprKind::Values(Box::new(arg))
                    }
                    "DOMAIN" => {
                        let arg = self.translate_expr(&args[0], in_action)?;
                        specl::ExprKind::Keys(Box::new(arg))
                    }
                    _ => {
                        // Inlining is handled by the translate_expr trampoline; this arm sees
                        // only operators not in any inline map (regular calls, recursive ops).
                        let func_expr =
                            specl::Expr::new(specl::ExprKind::Ident(escape_ident(name)), span);
                        let args_translated: Result<Vec<_>, _> = args
                            .iter()
                            .map(|a| self.translate_expr(a, in_action))
                            .collect();
                        specl::ExprKind::Call {
                            func: Box::new(func_expr),
                            args: args_translated?,
                        }
                    }
                }
            }

            TlaExprKind::Except { base, updates } => {
                return self.translate_except_arm(base, updates, in_action, span);
            }

            TlaExprKind::ExceptAt => {
                return Err(TranslateError::Unsupported {
                    message: "@ outside of EXCEPT context".to_string(),
                });
            }

            TlaExprKind::FunctionCombine { left, right } => {
                // f @@ g translates to: f | g (dict union, right takes precedence)
                let left_expr = self.translate_expr(left, in_action)?;
                let right_expr = self.translate_expr(right, in_action)?;
                specl::ExprKind::Binary {
                    op: specl::BinOp::Union,
                    left: Box::new(left_expr),
                    right: Box::new(right_expr),
                }
            }

            TlaExprKind::SingletonFunction { key, value } => {
                // k :> v translates to: {k: v} (singleton dict)
                let key_expr = self.translate_expr(key, in_action)?;
                let value_expr = self.translate_expr(value, in_action)?;
                specl::ExprKind::DictLit(vec![(key_expr, value_expr)])
            }

            TlaExprKind::SetEnum { elements } => {
                let elems: Result<Vec<_>, _> = elements
                    .iter()
                    .map(|e| self.translate_expr(e, in_action))
                    .collect();
                specl::ExprKind::SetLit(elems?)
            }

            TlaExprKind::SetMap {
                element,
                var,
                domain,
            } => {
                let elem_expr = self.translate_expr(element, in_action)?;
                let domain_expr = self.translate_expr(domain, in_action)?;
                specl::ExprKind::SetComprehension {
                    element: Box::new(elem_expr),
                    var: specl::Ident::new(escape_ident(&var.name), translate_span(var.span)),
                    domain: Box::new(domain_expr),
                    filter: None,
                }
            }

            TlaExprKind::SetFilter {
                var,
                domain,
                predicate,
            } => {
                let var_expr = specl::Expr::new(
                    specl::ExprKind::Ident(escape_ident(&var.name)),
                    translate_span(var.span),
                );
                let domain_expr = self.translate_expr(domain, in_action)?;
                let pred_expr = self.translate_expr(predicate, in_action)?;
                specl::ExprKind::SetComprehension {
                    element: Box::new(var_expr),
                    var: specl::Ident::new(escape_ident(&var.name), translate_span(var.span)),
                    domain: Box::new(domain_expr),
                    filter: Some(Box::new(pred_expr)),
                }
            }

            TlaExprKind::Tuple { elements } => {
                let elems: Result<Vec<_>, _> = elements
                    .iter()
                    .map(|e| self.translate_expr(e, in_action))
                    .collect();
                specl::ExprKind::SeqLit(elems?) // Tuples become sequences in Specl
            }

            TlaExprKind::Record { fields } => {
                let entries: Result<Vec<(specl::Expr, specl::Expr)>, TranslateError> = fields
                    .iter()
                    .map(|(k, v)| {
                        let key = specl::Expr::new(
                            specl::ExprKind::String(k.name.clone()),
                            translate_span(k.span),
                        );
                        let value = self.translate_expr(v, in_action)?;
                        Ok((key, value))
                    })
                    .collect();
                specl::ExprKind::DictLit(entries?)
            }

            TlaExprKind::FieldAccess { base, field } => {
                let base_expr = self.translate_expr(base, in_action)?;
                specl::ExprKind::Field {
                    base: Box::new(base_expr),
                    field: specl::Ident::new(escape_ident(&field.name), translate_span(field.span)),
                }
            }

            TlaExprKind::IfThenElse {
                cond,
                then_branch,
                else_branch,
            } => {
                let cond_expr = self.translate_expr(cond, in_action)?;
                let then_expr = self.translate_expr(then_branch, in_action)?;
                let else_expr = self.translate_expr(else_branch, in_action)?;
                // Wrap in parens to avoid precedence issues with following `and`
                specl::ExprKind::Paren(Box::new(specl::Expr::new(
                    specl::ExprKind::If {
                        cond: Box::new(cond_expr),
                        then_branch: Box::new(then_expr),
                        else_branch: Box::new(else_expr),
                    },
                    span,
                )))
            }

            TlaExprKind::LetIn { defs, body } => {
                return self.translate_let_in(defs, body, in_action, span);
            }

            TlaExprKind::Always(inner) => {
                let inner_expr = self.translate_expr(inner, in_action)?;
                specl::ExprKind::Always(Box::new(inner_expr))
            }

            TlaExprKind::Eventually(inner) => {
                let inner_expr = self.translate_expr(inner, in_action)?;
                specl::ExprKind::Eventually(Box::new(inner_expr))
            }

            TlaExprKind::LeadsTo { left, right } => {
                let left_expr = self.translate_expr(left, in_action)?;
                let right_expr = self.translate_expr(right, in_action)?;
                specl::ExprKind::LeadsTo {
                    left: Box::new(left_expr),
                    right: Box::new(right_expr),
                }
            }

            TlaExprKind::Enabled(inner) => {
                return self.translate_enabled_expr(inner, in_action);
            }

            TlaExprKind::Unchanged(_) => {
                // UNCHANGED translates to true (frame is implicit in Specl)
                specl::ExprKind::Bool(true)
            }

            TlaExprKind::Domain(inner) => {
                let inner_expr = self.translate_expr(inner, in_action)?;
                specl::ExprKind::Keys(Box::new(inner_expr))
            }

            TlaExprKind::Range { lo, hi } => {
                let lo_expr = self.translate_expr(lo, in_action)?;
                let hi_expr = self.translate_expr(hi, in_action)?;
                // Wrap hi in parentheses if it's a complex expression (e.g., field access)
                // to avoid ambiguity: 1..m.field should be 1..(m.field), not (1..m).field
                let hi_wrapped = if self.needs_parens_in_range(hi) {
                    specl::Expr::new(specl::ExprKind::Paren(Box::new(hi_expr)), span)
                } else {
                    hi_expr
                };
                specl::ExprKind::Range {
                    lo: Box::new(lo_expr),
                    hi: Box::new(hi_wrapped),
                }
            }

            TlaExprKind::Paren(inner) => {
                let inner_expr = self.translate_expr(inner, in_action)?;
                specl::ExprKind::Paren(Box::new(inner_expr))
            }

            TlaExprKind::PowerSet(inner) => {
                let inner_expr = self.translate_expr(inner, in_action)?;
                specl::ExprKind::Powerset(Box::new(inner_expr))
            }

            TlaExprKind::BigUnion(inner) => {
                let inner_expr = self.translate_expr(inner, in_action)?;
                specl::ExprKind::BigUnion(Box::new(inner_expr))
            }

            TlaExprKind::Case { arms, other } => {
                // Translate CASE to nested if-then-else:
                // CASE p1 -> e1 [] p2 -> e2 [] OTHER -> e3
                // becomes:
                // if p1 then e1 else if p2 then e2 else e3

                if arms.is_empty() {
                    return Err(TranslateError::Unsupported {
                        message: "empty CASE expression".to_string(),
                    });
                }

                // Start with the OTHER clause or a placeholder
                let mut result = if let Some(other_expr) = other {
                    self.translate_expr(other_expr, in_action)?
                } else {
                    // No OTHER clause - use FALSE as placeholder (will cause runtime error)
                    specl::Expr::new(specl::ExprKind::Bool(false), span)
                };

                // Build nested if-then-else from last to first
                for (cond, body) in arms.iter().rev() {
                    let cond_expr = self.translate_expr(cond, in_action)?;
                    let body_expr = self.translate_expr(body, in_action)?;
                    result = specl::Expr::new(
                        specl::ExprKind::If {
                            cond: Box::new(cond_expr),
                            then_branch: Box::new(body_expr),
                            else_branch: Box::new(result),
                        },
                        span,
                    );
                }

                // Wrap in parens to avoid precedence issues
                specl::ExprKind::Paren(Box::new(result))
            }

            TlaExprKind::RecordSet { fields } => {
                // [a: S, b: T] -> set of all records with field a from S and field b from T
                // Translate to: union_all({ { {"a": _a, "b": _b} for _b in T } for _a in S })
                if fields.is_empty() {
                    // Empty record set []: just the set containing the empty record
                    return Ok(specl::Expr::new(
                        specl::ExprKind::SetLit(vec![specl::Expr::new(
                            specl::ExprKind::DictLit(vec![]),
                            span,
                        )]),
                        span,
                    ));
                }

                // Generate unique variable names for iteration
                let var_names: Vec<String> = fields
                    .iter()
                    .map(|(field, _)| format!("_rs_{}", escape_ident(&field.name)))
                    .collect();

                // Translate all domain expressions
                let domains: Vec<specl::Expr> = fields
                    .iter()
                    .map(|(_, domain)| self.translate_expr(domain, in_action))
                    .collect::<Result<Vec<_>, _>>()?;

                // Build the innermost record literal: {"f1": _rs_f1, "f2": _rs_f2, ...}
                let record_entries: Vec<(specl::Expr, specl::Expr)> = fields
                    .iter()
                    .zip(var_names.iter())
                    .map(|((field, _), var_name)| {
                        let key = specl::Expr::new(
                            specl::ExprKind::String(field.name.clone()),
                            translate_span(field.span),
                        );
                        let value = specl::Expr::new(
                            specl::ExprKind::Ident(var_name.clone()),
                            translate_span(field.span),
                        );
                        (key, value)
                    })
                    .collect();

                let record_literal =
                    specl::Expr::new(specl::ExprKind::DictLit(record_entries), span);

                // Build nested comprehensions from innermost to outermost
                let n = fields.len();

                // Start with innermost: { record for _rs_fn in Sn }
                let mut result = specl::Expr::new(
                    specl::ExprKind::SetComprehension {
                        element: Box::new(record_literal),
                        var: specl::Ident::new(
                            &var_names[n - 1],
                            translate_span(fields[n - 1].0.span),
                        ),
                        domain: Box::new(domains[n - 1].clone()),
                        filter: None,
                    },
                    span,
                );

                // Wrap in outer comprehensions with union_all (from second-to-last to first)
                for i in (0..n - 1).rev() {
                    let inner_comprehension = specl::Expr::new(
                        specl::ExprKind::SetComprehension {
                            element: Box::new(result),
                            var: specl::Ident::new(&var_names[i], translate_span(fields[i].0.span)),
                            domain: Box::new(domains[i].clone()),
                            filter: None,
                        },
                        span,
                    );

                    result = specl::Expr::new(
                        specl::ExprKind::BigUnion(Box::new(inner_comprehension)),
                        span,
                    );
                }

                return Ok(result);
            }

            TlaExprKind::BoxAction { action, .. } => {
                // [A]_v means "either A or vars unchanged"
                // For model checking, we translate to just the action part
                // The stuttering allowance is implicit in the model checker
                return self.translate_expr(action, in_action);
            }

            TlaExprKind::AngleAction { action, .. } => {
                // <A>_v means "A and vars changed" (no stuttering allowed)
                // For model checking, we just use the action part
                return self.translate_expr(action, in_action);
            }

            TlaExprKind::InstanceOp {
                instance,
                name,
                args,
            } => {
                // Instance!Operator(args) - translate as a qualified operator call
                // The instance should be an identifier (the instance name)
                let instance_name = if let TlaExprKind::Ident(n) = &instance.kind {
                    n.clone()
                } else {
                    return Err(TranslateError::Unsupported {
                        message: "complex instance expression in Instance!Operator".to_string(),
                    });
                };

                // Create a qualified name like "Instance_Operator"
                let qualified_name = format!(
                    "{}_{}",
                    escape_ident(&instance_name),
                    escape_ident(&name.name)
                );
                let args_translated: Vec<specl::Expr> = args
                    .iter()
                    .map(|a| self.translate_expr(a, in_action))
                    .collect::<Result<Vec<_>, _>>()?;

                let func_ident = specl::Expr::new(specl::ExprKind::Ident(qualified_name), span);
                specl::ExprKind::Call {
                    func: Box::new(func_ident),
                    args: args_translated,
                }
            }

            TlaExprKind::WeakFairness { .. } | TlaExprKind::StrongFairness { .. } => {
                return Err(TranslateError::Unsupported {
                    message: "fairness conditions (translate manually)".to_string(),
                });
            }
        };

        Ok(specl::Expr::new(kind, span))
    }

    /// Translate `x \in [S -> T]` (function-set membership).
    ///
    /// Extracted from translate_expr_impl to reduce its stack frame size.
    /// `x \in [S -> T]` expands to: `keys(x) == S and forall k in keys(x): x[k] in T`
    #[inline(never)]
    fn translate_in_fn_set(
        &self,
        left: &TlaExpr,
        domain: &TlaExpr,
        range: &TlaExpr,
        in_action: bool,
        span: Span,
    ) -> Result<specl::Expr, TranslateError> {
        let x = self.translate_expr(left, in_action)?;
        let s = self.translate_expr(domain, in_action)?;

        let keys_eq = specl::Expr::new(
            specl::ExprKind::Binary {
                op: specl::BinOp::Eq,
                left: Box::new(specl::Expr::new(
                    specl::ExprKind::Keys(Box::new(x.clone())),
                    span,
                )),
                right: Box::new(s),
            },
            span,
        );

        let k_var = specl::Ident::new("__k", span);
        let x_k = specl::Expr::new(
            specl::ExprKind::Index {
                base: Box::new(x.clone()),
                index: Box::new(specl::Expr::new(
                    specl::ExprKind::Ident("__k".to_string()),
                    span,
                )),
            },
            span,
        );

        let body = if let TlaExprKind::OpApp { name, args } = &range.kind {
            if name == "Seq" && args.len() == 1 {
                let elem_set = self.translate_expr(&args[0], in_action)?;
                let i_var = specl::Ident::new("__i", span);
                let len_xk = specl::Expr::new(specl::ExprKind::Len(Box::new(x_k.clone())), span);
                let i_domain = specl::Expr::new(
                    specl::ExprKind::Range {
                        lo: Box::new(specl::Expr::new(specl::ExprKind::Int(1), span)),
                        hi: Box::new(len_xk),
                    },
                    span,
                );
                specl::Expr::new(
                    specl::ExprKind::Quantifier {
                        kind: specl::QuantifierKind::Forall,
                        bindings: vec![specl::Binding {
                            var: i_var.clone(),
                            domain: i_domain,
                            span,
                        }],
                        body: Box::new(specl::Expr::new(
                            specl::ExprKind::Paren(Box::new(specl::Expr::new(
                                specl::ExprKind::Binary {
                                    op: specl::BinOp::In,
                                    left: Box::new(specl::Expr::new(
                                        specl::ExprKind::Index {
                                            base: Box::new(x_k),
                                            index: Box::new(specl::Expr::new(
                                                specl::ExprKind::Ident("__i".to_string()),
                                                span,
                                            )),
                                        },
                                        span,
                                    )),
                                    right: Box::new(elem_set),
                                },
                                span,
                            ))),
                            span,
                        )),
                    },
                    span,
                )
            } else {
                let t = self.translate_expr(range, in_action)?;
                specl::Expr::new(
                    specl::ExprKind::Binary {
                        op: specl::BinOp::In,
                        left: Box::new(x_k),
                        right: Box::new(t),
                    },
                    span,
                )
            }
        } else if let TlaExprKind::Ident(name) = &range.kind {
            match name.as_str() {
                "Nat" => specl::Expr::new(
                    specl::ExprKind::Binary {
                        op: specl::BinOp::Ge,
                        left: Box::new(x_k),
                        right: Box::new(specl::Expr::new(specl::ExprKind::Int(0), span)),
                    },
                    span,
                ),
                "Int" => specl::Expr::new(specl::ExprKind::Bool(true), span),
                "BOOLEAN" => specl::Expr::new(
                    specl::ExprKind::Binary {
                        op: specl::BinOp::In,
                        left: Box::new(x_k),
                        right: Box::new(specl::Expr::new(
                            specl::ExprKind::SetLit(vec![
                                specl::Expr::new(specl::ExprKind::Bool(true), span),
                                specl::Expr::new(specl::ExprKind::Bool(false), span),
                            ]),
                            span,
                        )),
                    },
                    span,
                ),
                _ => {
                    let t = self.translate_expr(range, in_action)?;
                    specl::Expr::new(
                        specl::ExprKind::Binary {
                            op: specl::BinOp::In,
                            left: Box::new(x_k),
                            right: Box::new(t),
                        },
                        span,
                    )
                }
            }
        } else {
            let t = self.translate_expr(range, in_action)?;
            specl::Expr::new(
                specl::ExprKind::Binary {
                    op: specl::BinOp::In,
                    left: Box::new(x_k),
                    right: Box::new(t),
                },
                span,
            )
        };

        let forall = specl::Expr::new(
            specl::ExprKind::Quantifier {
                kind: specl::QuantifierKind::Forall,
                bindings: vec![specl::Binding {
                    var: k_var.clone(),
                    domain: specl::Expr::new(specl::ExprKind::Keys(Box::new(x.clone())), span),
                    span,
                }],
                body: Box::new(specl::Expr::new(
                    specl::ExprKind::Paren(Box::new(body)),
                    span,
                )),
            },
            span,
        );

        Ok(specl::Expr::new(
            specl::ExprKind::Binary {
                op: specl::BinOp::And,
                left: Box::new(keys_eq),
                right: Box::new(forall),
            },
            span,
        ))
    }

    /// Translate `x \in Seq(S)` (membership in a sequence set).
    ///
    /// Extracted from translate_expr_impl to reduce its stack frame size.
    /// `x \in Seq(S)` expands to: `forall i in 1..len(x): x[i] in S`
    #[inline(never)]
    fn translate_in_seq(
        &self,
        left: &TlaExpr,
        elem_type: &TlaExpr,
        in_action: bool,
        span: Span,
    ) -> Result<specl::Expr, TranslateError> {
        let x = self.translate_expr(left, in_action)?;
        let s = self.translate_expr(elem_type, in_action)?;

        let i_var = specl::Ident::new("__i", span);
        let len_x = specl::Expr::new(specl::ExprKind::Len(Box::new(x.clone())), span);
        let domain = specl::Expr::new(
            specl::ExprKind::Range {
                lo: Box::new(specl::Expr::new(specl::ExprKind::Int(1), span)),
                hi: Box::new(len_x),
            },
            span,
        );

        let forall = specl::Expr::new(
            specl::ExprKind::Quantifier {
                kind: specl::QuantifierKind::Forall,
                bindings: vec![specl::Binding {
                    var: i_var.clone(),
                    domain,
                    span,
                }],
                body: Box::new(specl::Expr::new(
                    specl::ExprKind::Paren(Box::new(specl::Expr::new(
                        specl::ExprKind::Binary {
                            op: specl::BinOp::In,
                            left: Box::new(specl::Expr::new(
                                specl::ExprKind::Index {
                                    base: Box::new(x),
                                    index: Box::new(specl::Expr::new(
                                        specl::ExprKind::Ident("__i".to_string()),
                                        span,
                                    )),
                                },
                                span,
                            )),
                            right: Box::new(s),
                        },
                        span,
                    ))),
                    span,
                )),
            },
            span,
        );

        Ok(forall)
    }

    /// Translate a TLA+ LET...IN expression.
    ///
    /// Extracted from translate_expr_impl to reduce its stack frame size.
    #[inline(never)]
    fn translate_let_in(
        &self,
        defs: &[TlaLetDef],
        body: &TlaExpr,
        in_action: bool,
        span: Span,
    ) -> Result<specl::Expr, TranslateError> {
        let mut local_ops: std::collections::HashMap<String, (Vec<String>, &TlaExpr)> =
            std::collections::HashMap::new();
        let mut simple_defs: Vec<&TlaLetDef> = Vec::new();
        let mut recursive_fns: Vec<&TlaLetDef> = Vec::new();

        for def in defs {
            if def.recursive_binding.is_some() {
                recursive_fns.push(def);
            } else if def.params.is_empty() {
                simple_defs.push(def);
            } else {
                let param_names: Vec<String> = def.params.iter().map(|p| p.name.clone()).collect();
                local_ops.insert(def.name.name.clone(), (param_names, &def.body));
            }
        }

        let inlined_body = self.inline_local_ops(body, &local_ops)?;
        let body_expr = self.translate_expr(&inlined_body, in_action)?;
        let mut result = specl::Expr::new(specl::ExprKind::Paren(Box::new(body_expr)), span);

        for def in simple_defs.iter().rev() {
            let inlined_def_body = self.inline_local_ops(&def.body, &local_ops)?;
            let def_expr = self.translate_expr(&inlined_def_body, in_action)?;
            let wrapped_value = specl::Expr::new(
                specl::ExprKind::Paren(Box::new(def_expr)),
                translate_span(def.span),
            );
            result = specl::Expr::new(
                specl::ExprKind::Let {
                    var: specl::Ident::new(
                        escape_ident(&def.name.name),
                        translate_span(def.name.span),
                    ),
                    value: Box::new(wrapped_value),
                    body: Box::new(result),
                },
                translate_span(def.span),
            );
        }

        for def in recursive_fns.iter().rev() {
            if let Some(binding) = &def.recursive_binding {
                let domain_expr = self.translate_expr(&binding.domain, in_action)?;
                let inlined_fn_body = self.inline_local_ops(&def.body, &local_ops)?;
                let fn_body_expr = self.translate_expr(&inlined_fn_body, in_action)?;
                let fn_lit = specl::Expr::new(
                    specl::ExprKind::FnLit {
                        var: specl::Ident::new(
                            escape_ident(&binding.var.name),
                            translate_span(binding.var.span),
                        ),
                        domain: Box::new(domain_expr),
                        body: Box::new(fn_body_expr),
                    },
                    translate_span(def.span),
                );
                let wrapped_fn_lit = specl::Expr::new(
                    specl::ExprKind::Paren(Box::new(fn_lit)),
                    translate_span(def.span),
                );
                result = specl::Expr::new(
                    specl::ExprKind::Let {
                        var: specl::Ident::new(
                            escape_ident(&def.name.name),
                            translate_span(def.name.span),
                        ),
                        value: Box::new(wrapped_fn_lit),
                        body: Box::new(result),
                    },
                    translate_span(def.span),
                );
            }
        }

        Ok(result)
    }

    /// Translate a TLA+ `[f EXCEPT ![...] = ...]` expression.
    ///
    /// Extracted from translate_expr_impl to reduce its stack frame size.
    #[inline(never)]
    fn translate_except_arm(
        &self,
        base: &TlaExpr,
        updates: &[TlaExceptUpdate],
        in_action: bool,
        span: Span,
    ) -> Result<specl::Expr, TranslateError> {
        let mut result = self.translate_expr(base, in_action)?;
        let base_for_at = result.clone();

        for update in updates {
            if update.path.len() == 1 {
                let key = self.translate_expr(&update.path[0], in_action)?;
                let at_replacement = specl::Expr::new(
                    specl::ExprKind::Index {
                        base: Box::new(base_for_at.clone()),
                        index: Box::new(key.clone()),
                    },
                    span,
                );
                let value =
                    self.translate_except_value(&update.value, in_action, &at_replacement)?;
                result = specl::Expr::new(
                    specl::ExprKind::RecordUpdate {
                        base: Box::new(result),
                        updates: vec![specl::RecordFieldUpdate::Dynamic { key, value }],
                    },
                    span,
                );
            } else {
                let keys: Vec<_> = update
                    .path
                    .iter()
                    .map(|k| self.translate_expr(k, in_action))
                    .collect::<Result<_, _>>()?;

                let mut at_replacement = base_for_at.clone();
                for key in &keys {
                    at_replacement = specl::Expr::new(
                        specl::ExprKind::Index {
                            base: Box::new(at_replacement),
                            index: Box::new(key.clone()),
                        },
                        span,
                    );
                }

                let value =
                    self.translate_except_value(&update.value, in_action, &at_replacement)?;

                let mut prefix = base_for_at.clone();
                for key in keys.iter().take(keys.len() - 1) {
                    prefix = specl::Expr::new(
                        specl::ExprKind::Index {
                            base: Box::new(prefix),
                            index: Box::new(key.clone()),
                        },
                        span,
                    );
                }
                let mut nested = specl::Expr::new(
                    specl::ExprKind::RecordUpdate {
                        base: Box::new(prefix),
                        updates: vec![specl::RecordFieldUpdate::Dynamic {
                            key: keys.last().unwrap().clone(),
                            value,
                        }],
                    },
                    span,
                );

                for i in (0..keys.len() - 1).rev() {
                    let mut outer_prefix = base_for_at.clone();
                    for key in keys.iter().take(i) {
                        outer_prefix = specl::Expr::new(
                            specl::ExprKind::Index {
                                base: Box::new(outer_prefix),
                                index: Box::new(key.clone()),
                            },
                            span,
                        );
                    }
                    nested = specl::Expr::new(
                        specl::ExprKind::RecordUpdate {
                            base: Box::new(outer_prefix),
                            updates: vec![specl::RecordFieldUpdate::Dynamic {
                                key: keys[i].clone(),
                                value: nested,
                            }],
                        },
                        span,
                    );
                }

                result = nested;
            }
        }
        Ok(result)
    }

    fn translate_enabled_expr(
        &self,
        inner: &TlaExpr,
        in_action: bool,
    ) -> Result<specl::Expr, TranslateError> {
        let span = translate_span(inner.span);
        match &inner.kind {
            TlaExprKind::Ident(name) => Ok(specl::Expr::new(
                specl::ExprKind::Enabled(specl::Ident::new(escape_ident(name), span)),
                span,
            )),
            TlaExprKind::OpApp { name, args } => {
                // Check if this is an action helper with parameters.
                if let Some((params, body)) = self.action_helpers.get(name).cloned() {
                    let inlined = self.substitute_params(&body, &params, args)?;
                    let guard = self.extract_guard(&inlined)?;
                    return self.translate_expr(&guard, in_action);
                }
                Ok(specl::Expr::new(
                    specl::ExprKind::Enabled(specl::Ident::new(escape_ident(name), span)),
                    span,
                ))
            }
            TlaExprKind::Paren(expr) => self.translate_enabled_expr(expr, in_action),
            TlaExprKind::Binary {
                op: TlaBinOp::Or,
                left,
                right,
            } => {
                let left_enabled = self.translate_enabled_expr(left, in_action)?;
                let right_enabled = self.translate_enabled_expr(right, in_action)?;
                Ok(specl::Expr::new(
                    specl::ExprKind::Binary {
                        op: specl::BinOp::Or,
                        left: Box::new(left_enabled),
                        right: Box::new(right_enabled),
                    },
                    span,
                ))
            }
            TlaExprKind::Binary {
                op: TlaBinOp::And,
                left,
                right,
            } => {
                let left_enabled = self.translate_enabled_expr(left, in_action)?;
                let right_enabled = self.translate_enabled_expr(right, in_action)?;
                Ok(specl::Expr::new(
                    specl::ExprKind::Binary {
                        op: specl::BinOp::And,
                        left: Box::new(left_enabled),
                        right: Box::new(right_enabled),
                    },
                    span,
                ))
            }
            _ => Err(TranslateError::Unsupported {
                message: "complex ENABLED expression".to_string(),
            }),
        }
    }

    fn translate_binding(&self, binding: &TlaBinding) -> Result<specl::Binding, TranslateError> {
        let domain_expr = self.translate_expr(&binding.domain, false)?;
        Ok(specl::Binding {
            var: specl::Ident::new(
                escape_ident(&binding.var.name),
                translate_span(binding.var.span),
            ),
            domain: domain_expr,
            span: translate_span(binding.span),
        })
    }
}

fn translate_span(_span: crate::token::Span) -> Span {
    // Use dummy spans since Specl spans require line/column info we don't have
    Span::dummy()
}

/// Specl reserved keywords that must be escaped when used as identifiers
const SPECL_RESERVED: &[&str] = &[
    "len",
    "head",
    "tail",
    "keys",
    "values",
    "if",
    "then",
    "else",
    "and",
    "or",
    "not",
    "in",
    "notin",
    "true",
    "false",
    "forall",
    "exists",
    "choose",
    "fix",
    "let",
    "fn",
    "module",
    "const",
    "var",
    "init",
    "action",
    "next",
    "invariant",
    "func",
    "require",
    "import",
    "type",
    "set",
    "seq",
    "map",
    "bool",
    "int",
    "nat",
    "string",
    "any",
    "all", // specl quantifiers
];

/// Escape an identifier if it conflicts with a specl reserved keyword
fn escape_ident(name: &str) -> String {
    if SPECL_RESERVED.contains(&name.to_lowercase().as_str()) {
        format!("{}_", name)
    } else {
        name.to_string()
    }
}

fn translate_binop(op: TlaBinOp) -> specl::BinOp {
    match op {
        TlaBinOp::And => specl::BinOp::And,
        TlaBinOp::Or => specl::BinOp::Or,
        TlaBinOp::Implies => specl::BinOp::Implies,
        TlaBinOp::Iff => specl::BinOp::Iff,
        TlaBinOp::Eq => specl::BinOp::Eq,
        TlaBinOp::Ne => specl::BinOp::Ne,
        TlaBinOp::Lt => specl::BinOp::Lt,
        TlaBinOp::Le => specl::BinOp::Le,
        TlaBinOp::Gt => specl::BinOp::Gt,
        TlaBinOp::Ge => specl::BinOp::Ge,
        TlaBinOp::Add => specl::BinOp::Add,
        TlaBinOp::Sub => specl::BinOp::Sub,
        TlaBinOp::Mul => specl::BinOp::Mul,
        TlaBinOp::Div => specl::BinOp::Div,
        TlaBinOp::Mod => specl::BinOp::Mod,
        TlaBinOp::Exp => specl::BinOp::Mul, // Approximate
        TlaBinOp::In => specl::BinOp::In,
        TlaBinOp::NotIn => specl::BinOp::NotIn,
        TlaBinOp::Cup => specl::BinOp::Union,
        TlaBinOp::Cap => specl::BinOp::Intersect,
        TlaBinOp::SetDiff => specl::BinOp::Diff,
        TlaBinOp::SubsetEq => specl::BinOp::SubsetOf,
        TlaBinOp::Times => specl::BinOp::Mul, // Approximate: cartesian product
        TlaBinOp::Concat => specl::BinOp::Concat,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_translate_simple_module() {
        let input = r#"---- MODULE Counter ----
VARIABLE count

Init == count = 0

Increment == count' = count + 1

Next == Increment
====
"#;
        let result = translate(input).unwrap();
        assert!(result.contains("module Counter"));
        assert!(result.contains("var count: Int"));
        assert!(result.contains("init {"));
        // Note: The translator does not currently emit action declarations for TLA+ operators
    }

    #[test]
    fn test_translate_with_constants() {
        let input = r#"---- MODULE Test ----
CONSTANT Max
VARIABLE x

Init == x = 0

Increment ==
    /\ x < Max
    /\ x' = x + 1

Next == Increment
====
"#;
        let result = translate(input).unwrap();
        assert!(result.contains("const Max:"));
        assert!(result.contains("var x: Int"));
        // Note: The translator does not currently emit action declarations for TLA+ operators
    }

    #[test]
    fn test_translate_invariant() {
        let input = r#"---- MODULE Test ----
VARIABLE x

Init == x = 0

TypeInvariant == x >= 0

Next == x' = x + 1
====
"#;
        let result = translate(input).unwrap();
        assert!(result.contains("invariant TypeInvariant"));
    }

    #[test]
    fn test_translate_recursive_operator_no_overflow() {
        let input = r#"---- MODULE Rec ----
EXTENDS Sequences
RECURSIVE SeqSum(_)
SeqSum(s) == IF Len(s) = 0 THEN 0 ELSE Head(s) + SeqSum(Tail(s))
ASSUME SeqSum(<<1,2,3>>) = 6
====
"#;
        let result = translate(input).unwrap();
        assert!(result.contains("func SeqSum("));
    }

    #[test]
    fn test_translate_recursive_operator_under_bigunion_no_overflow() {
        let input = r#"---- MODULE Rec2 ----
EXTENDS Sequences
CONSTANT N
RECURSIVE Partitions(_ , _)
Partitions(seq, wt) ==
  IF Len(seq) = N
    THEN {seq}
    ELSE UNION { Partitions(seq, wt - 1) : x \in 1..1 }
ASSUME TRUE
====
"#;
        let result = translate(input).unwrap();
        assert!(result.contains("func Partitions("));
    }
}

//! AST to IR compiler.

use crate::ir::{
    BinOp as IrBinOp, CompiledAction, CompiledExpr, CompiledInvariant, CompiledSpec,
    ConstDecl as IrConstDecl, KeySource, SymmetryGroup, VarDecl as IrVarDecl,
};
use specl_syntax::{
    ActionDecl, ConstValue, Decl, Expr, ExprKind, Module, QuantifierKind, RecordFieldUpdate,
};
use specl_types::{check_module, Type, TypeEnv};
use std::collections::HashMap;
use thiserror::Error;

/// Compilation error.
#[derive(Debug, Error)]
pub enum CompileError {
    #[error("type error: {0}")]
    TypeError(#[from] specl_types::TypeError),

    #[error("undefined variable: {0}")]
    UndefinedVariable(String),

    #[error("undefined action: {0}")]
    UndefinedAction(String),

    #[error("unsupported feature: {0}")]
    Unsupported(String),

    #[error("variable '{var}' assigned multiple times in action '{action}'")]
    DuplicateAssignment { var: String, action: String },
}

pub type CompileResult<T> = Result<T, CompileError>;

/// Compile a module to IR.
pub fn compile(module: &Module) -> CompileResult<CompiledSpec> {
    let env = check_module(module)?;
    let mut compiler = Compiler::new(env);
    compiler.compile_module(module)
}

/// A user-defined function (for inlining).
#[derive(Clone)]
struct FuncDef {
    params: Vec<String>,
    body: Expr,
}

/// The IR compiler.
struct Compiler {
    /// Type environment from type checking.
    env: TypeEnv,
    /// State variable name to index mapping.
    var_indices: HashMap<String, usize>,
    /// Constant name to index mapping.
    const_indices: HashMap<String, usize>,
    /// Action name to index mapping.
    action_indices: HashMap<String, usize>,
    /// User-defined function definitions (for inlining).
    func_defs: HashMap<String, FuncDef>,
    /// Current local variable stack (for let bindings, quantifiers).
    locals: Vec<String>,
    /// Current action parameters (during action compilation).
    params: Vec<String>,
}

impl Compiler {
    fn new(env: TypeEnv) -> Self {
        Self {
            env,
            var_indices: HashMap::new(),
            const_indices: HashMap::new(),
            action_indices: HashMap::new(),
            func_defs: HashMap::new(),
            locals: Vec::new(),
            params: Vec::new(),
        }
    }

    fn compile_module(&mut self, module: &Module) -> CompileResult<CompiledSpec> {
        let mut vars = Vec::new();
        let mut consts = Vec::new();
        let mut actions = Vec::new();
        let mut invariants = Vec::new();
        let mut auxiliary_invariants = Vec::new();
        let mut init = CompiledExpr::Bool(true);

        // First pass: collect declarations and build indices
        for decl in &module.decls {
            match decl {
                Decl::Var(d) => {
                    let index = vars.len();
                    self.var_indices.insert(d.name.name.clone(), index);
                    let ty = self.lookup_var_type(&d.name.name);
                    vars.push(IrVarDecl {
                        name: d.name.name.clone(),
                        index,
                        ty,
                    });
                }
                Decl::Const(d) => {
                    let index = consts.len();
                    self.const_indices.insert(d.name.name.clone(), index);
                    let ty = self.lookup_const_type(&d.name.name);
                    let default_value = match &d.value {
                        ConstValue::Scalar(n) => Some(*n),
                        ConstValue::Type(_) => d.default_value,
                    };
                    consts.push(IrConstDecl {
                        name: d.name.name.clone(),
                        index,
                        ty,
                        default_value,
                    });
                }
                Decl::Func(d) => {
                    let params = d.params.iter().map(|p| p.name.name.clone()).collect();
                    self.func_defs.insert(
                        d.name.name.clone(),
                        FuncDef {
                            params,
                            body: d.body.clone(),
                        },
                    );
                }
                Decl::Action(d) => {
                    let index = actions.len();
                    self.action_indices.insert(d.name.name.clone(), index);
                    // Placeholder - will compile later
                    actions.push(CompiledAction {
                        name: d.name.name.clone(),
                        params: Vec::new(),
                        param_type_exprs: Vec::new(),
                        guard: CompiledExpr::Bool(true),
                        effect: CompiledExpr::Bool(true),
                        changes: Vec::new(),
                        reads: Vec::new(),
                        write_key_params: Vec::new(),
                        read_key_params: Vec::new(),
                        guard_cost: 1,
                    });
                }
                _ => {}
            }
        }

        // Second pass: compile bodies
        for decl in &module.decls {
            match decl {
                Decl::Init(d) => {
                    init = self.compile_expr(&d.body)?;
                }
                Decl::Action(d) => {
                    let action = self.compile_action(d)?;
                    let index = *self.action_indices.get(&d.name.name).unwrap();
                    actions[index] = action;
                }
                Decl::Invariant(d) => {
                    let body = self.compile_expr(&d.body)?;
                    let compiled = CompiledInvariant {
                        name: d.name.name.clone(),
                        body,
                    };
                    if d.is_auxiliary {
                        auxiliary_invariants.push(compiled);
                    } else {
                        invariants.push(compiled);
                    }
                }
                _ => {}
            }
        }

        // Resolve view variables
        let mut view_variables = None;
        for decl in &module.decls {
            if let Decl::View(d) = decl {
                let mut indices = Vec::new();
                for var in &d.variables {
                    let idx = self
                        .var_indices
                        .get(&var.name)
                        .ok_or_else(|| CompileError::UndefinedVariable(var.name.clone()))?;
                    indices.push(*idx);
                }
                view_variables = Some(indices);
            }
        }

        // Compute independence matrix for POR
        // Actions A and B are independent if:
        // writes(A) ∩ (reads(B) ∪ writes(B)) = ∅ AND writes(B) ∩ (reads(A) ∪ writes(A)) = ∅
        let n = actions.len();
        let mut independent = vec![vec![false; n]; n];
        for i in 0..n {
            for j in 0..n {
                if i == j {
                    // An action is not independent with itself
                    independent[i][j] = false;
                } else {
                    let writes_a = &actions[i].changes;
                    let reads_a = &actions[i].reads;
                    let writes_b = &actions[j].changes;
                    let reads_b = &actions[j].reads;

                    // Check writes(A) ∩ (reads(B) ∪ writes(B)) = ∅
                    let a_interferes_b = writes_a
                        .iter()
                        .any(|w| reads_b.contains(w) || writes_b.contains(w));

                    // Check writes(B) ∩ (reads(A) ∪ writes(A)) = ∅
                    let b_interferes_a = writes_b
                        .iter()
                        .any(|w| reads_a.contains(w) || writes_a.contains(w));

                    independent[i][j] = !a_interferes_b && !b_interferes_a;
                }
            }
        }

        // Detect symmetry groups from variable types
        let symmetry_groups = self.detect_symmetry_groups(&vars);

        // Compute refinable pairs for instance-level POR.
        // A pair (i,j) is refinable if they are template-dependent but all shared
        // variables are accessed via keyed Dict ops on both sides.
        let refinable_pairs = {
            let mut rp = vec![vec![false; n]; n];
            for i in 0..n {
                // Include diagonal (i == j): different instances of the same
                // action template can be independent if they access disjoint keys.
                for j in i..n {
                    if !independent[i][j] {
                        let refinable = Self::check_refinable(&actions[i], &actions[j]);
                        rp[i][j] = refinable;
                        rp[j][i] = refinable;
                    }
                }
            }
            rp
        };

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
            view_variables,
        })
    }

    fn compile_action(&mut self, decl: &ActionDecl) -> CompileResult<CompiledAction> {
        // Set up parameters
        self.params = decl.params.iter().map(|p| p.name.name.clone()).collect();

        let param_types: Vec<(String, Type)> = decl
            .params
            .iter()
            .map(|p| {
                let ty = self.env.resolve_type(
                    &self
                        .env
                        .lookup_action(&decl.name.name)
                        .map(|sig| {
                            sig.params
                                .iter()
                                .find(|(n, _)| n == &p.name.name)
                                .map(|(_, t)| t.clone())
                                .unwrap_or(specl_types::Type::Error)
                        })
                        .unwrap_or(specl_types::Type::Error),
                );
                (p.name.name.clone(), ty)
            })
            .collect();

        // Compile guard (conjunction of requires)
        let guard = if decl.body.requires.is_empty() {
            CompiledExpr::Bool(true)
        } else {
            let mut guard = self.compile_expr(&decl.body.requires[0])?;
            for req in decl.body.requires.iter().skip(1) {
                let compiled = self.compile_expr(req)?;
                guard = CompiledExpr::Binary {
                    op: IrBinOp::And,
                    left: Box::new(guard),
                    right: Box::new(compiled),
                };
            }
            guard
        };

        // Compile effect
        let effect = if let Some(eff) = &decl.body.effect {
            self.compile_expr(eff)?
        } else {
            CompiledExpr::Bool(true)
        };

        // Collect changed variables from the effect and check for duplicates
        let mut raw_changes = Vec::new();
        self.collect_changes_impl(&effect, &mut raw_changes);
        {
            let mut seen = std::collections::HashSet::new();
            for &idx in &raw_changes {
                if !seen.insert(idx) {
                    let var_name = self
                        .var_indices
                        .iter()
                        .find(|(_, &i)| i == idx)
                        .map(|(n, _)| n.clone())
                        .unwrap_or_else(|| format!("var_{}", idx));
                    return Err(CompileError::DuplicateAssignment {
                        var: var_name,
                        action: decl.name.name.clone(),
                    });
                }
            }
        }
        raw_changes.sort();
        raw_changes.dedup();
        let changes = raw_changes;

        // Collect read variables from guard and effect (for POR)
        let mut reads = self.collect_reads(&guard);
        reads.extend(self.collect_reads(&effect));
        reads.sort();
        reads.dedup();

        // Collect key access info for instance-level POR (before adding implicit frame)
        let write_key_params = Self::collect_write_key_params(&effect, &changes);
        let read_key_params = Self::collect_read_key_params(&guard, &effect, &reads);

        // Add implicit frame (unchanged constraints) for vars not in changes
        let effect = self.add_implicit_frame(effect, &changes);

        // Store original type expressions for deferred range resolution
        let param_type_exprs: Vec<_> = decl.params.iter().map(|p| p.ty.clone()).collect();

        self.params.clear();

        let guard_cost = expr_cost(&guard);
        Ok(CompiledAction {
            name: decl.name.name.clone(),
            params: param_types,
            param_type_exprs,
            guard,
            effect,
            changes,
            reads,
            write_key_params,
            read_key_params,
            guard_cost,
        })
    }

    fn compile_expr(&mut self, expr: &Expr) -> CompileResult<CompiledExpr> {
        let compiled = match &expr.kind {
            ExprKind::Bool(b) => CompiledExpr::Bool(*b),
            ExprKind::Int(n) => CompiledExpr::Int(*n),
            ExprKind::String(s) => CompiledExpr::String(s.clone()),

            ExprKind::Ident(name) => self.compile_ident(name)?,
            ExprKind::Primed(name) => {
                if let Some(&idx) = self.var_indices.get(name) {
                    CompiledExpr::PrimedVar(idx)
                } else {
                    return Err(CompileError::UndefinedVariable(name.clone()));
                }
            }

            ExprKind::Binary { op, left, right } => CompiledExpr::Binary {
                op: (*op).into(),
                left: Box::new(self.compile_expr(left)?),
                right: Box::new(self.compile_expr(right)?),
            },

            ExprKind::Unary { op, operand } => CompiledExpr::Unary {
                op: (*op).into(),
                operand: Box::new(self.compile_expr(operand)?),
            },

            ExprKind::Index { base, index } => CompiledExpr::Index {
                base: Box::new(self.compile_expr(base)?),
                index: Box::new(self.compile_expr(index)?),
            },

            ExprKind::Slice { base, lo, hi } => CompiledExpr::Slice {
                base: Box::new(self.compile_expr(base)?),
                lo: Box::new(self.compile_expr(lo)?),
                hi: Box::new(self.compile_expr(hi)?),
            },

            ExprKind::Field { base, field } => CompiledExpr::Field {
                base: Box::new(self.compile_expr(base)?),
                field: field.name.clone(),
            },

            ExprKind::Call { func, args } => {
                // Check if it's an action call
                if let ExprKind::Ident(name) = &func.kind {
                    if let Some(&action_index) = self.action_indices.get(name) {
                        let compiled_args: Vec<_> = args
                            .iter()
                            .map(|a| self.compile_expr(a))
                            .collect::<CompileResult<_>>()?;
                        return Ok(CompiledExpr::ActionCall {
                            action_index,
                            args: compiled_args,
                        });
                    }

                    // Check if it's a user-defined function call - inline it
                    if let Some(func_def) = self.func_defs.get(name).cloned() {
                        if args.len() != func_def.params.len() {
                            return Err(CompileError::Unsupported(format!(
                                "function {} expects {} arguments, got {}",
                                name,
                                func_def.params.len(),
                                args.len()
                            )));
                        }
                        // Inline: wrap body in nested let bindings for each arg
                        // func(a, b) { body } called with (x, y) becomes:
                        // let a = x in let b = y in body
                        let compiled_args: Vec<_> = args
                            .iter()
                            .map(|a| self.compile_expr(a))
                            .collect::<CompileResult<_>>()?;
                        // Push all params onto locals stack
                        for param in &func_def.params {
                            self.locals.push(param.clone());
                        }
                        let body = self.compile_expr(&func_def.body)?;
                        // Pop all params
                        for _ in &func_def.params {
                            self.locals.pop();
                        }
                        // Build nested lets from inside out.
                        // compiled_args[i] executes after i Let bindings have been
                        // pushed, so shift its Local indices up by i.
                        let mut result = body;
                        for (i, _param) in func_def.params.iter().enumerate().rev() {
                            result = CompiledExpr::Let {
                                value: Box::new(compiled_args[i].shift_locals(i)),
                                body: Box::new(result),
                            };
                        }
                        return Ok(result);
                    }
                }

                CompiledExpr::Call {
                    func: Box::new(self.compile_expr(func)?),
                    args: args
                        .iter()
                        .map(|a| self.compile_expr(a))
                        .collect::<CompileResult<_>>()?,
                }
            }

            ExprKind::SetLit(elements) => CompiledExpr::SetLit(
                elements
                    .iter()
                    .map(|e| self.compile_expr(e))
                    .collect::<CompileResult<_>>()?,
            ),

            ExprKind::SeqLit(elements) => CompiledExpr::SeqLit(
                elements
                    .iter()
                    .map(|e| self.compile_expr(e))
                    .collect::<CompileResult<_>>()?,
            ),

            ExprKind::TupleLit(elements) => CompiledExpr::TupleLit(
                elements
                    .iter()
                    .map(|e| self.compile_expr(e))
                    .collect::<CompileResult<_>>()?,
            ),

            ExprKind::DictLit(entries) => {
                let compiled_entries: Vec<_> = entries
                    .iter()
                    .map(|(key, value)| Ok((self.compile_expr(key)?, self.compile_expr(value)?)))
                    .collect::<CompileResult<_>>()?;
                CompiledExpr::DictLit(compiled_entries)
            }

            ExprKind::FnLit { var, domain, body } => {
                let compiled_domain = self.compile_expr(domain)?;
                self.locals.push(var.name.clone());
                let compiled_body = self.compile_expr(body)?;
                self.locals.pop();
                CompiledExpr::FnLit {
                    domain: Box::new(compiled_domain),
                    body: Box::new(compiled_body),
                }
            }

            ExprKind::SetComprehension {
                element,
                var,
                domain,
                filter,
            } => {
                let compiled_domain = self.compile_expr(domain)?;
                self.locals.push(var.name.clone());
                let compiled_element = self.compile_expr(element)?;
                let compiled_filter = filter
                    .as_ref()
                    .map(|f| self.compile_expr(f))
                    .transpose()?
                    .map(Box::new);
                self.locals.pop();
                CompiledExpr::SetComprehension {
                    element: Box::new(compiled_element),
                    domain: Box::new(compiled_domain),
                    filter: compiled_filter,
                }
            }

            ExprKind::RecordUpdate { base, updates } => {
                let compiled_base = self.compile_expr(base)?;
                let mut field_updates = Vec::new();
                let mut dynamic_updates = Vec::new();

                for update in updates {
                    match update {
                        RecordFieldUpdate::Field { name, value } => {
                            field_updates.push((name.name.clone(), self.compile_expr(value)?));
                        }
                        RecordFieldUpdate::Dynamic { key, value } => {
                            dynamic_updates
                                .push((self.compile_expr(key)?, self.compile_expr(value)?));
                        }
                    }
                }

                // If we have dynamic updates, this is a function update
                if !dynamic_updates.is_empty() {
                    // Chain all dynamic updates: f with {[k1]:v1, [k2]:v2} -> FnUpdate(FnUpdate(f, k1, v1), k2, v2)
                    let mut result = compiled_base;
                    for (key, value) in dynamic_updates {
                        result = CompiledExpr::FnUpdate {
                            base: Box::new(result),
                            key: Box::new(key),
                            value: Box::new(value),
                        };
                    }
                    return Ok(result);
                }

                CompiledExpr::RecordUpdate {
                    base: Box::new(compiled_base),
                    updates: field_updates,
                }
            }

            ExprKind::Quantifier {
                kind,
                bindings,
                body,
            } => {
                // Handle multiple bindings by nesting them
                // `any i in A, j in B: body` becomes `any i in A: (any j in B: body)`
                if bindings.is_empty() {
                    return Err(CompileError::Unsupported(
                        "empty quantifier bindings".to_string(),
                    ));
                }

                // Push ALL locals first so body can reference all binding variables
                for binding in bindings {
                    self.locals.push(binding.var.name.clone());
                }

                // Compile body with all bindings in scope
                let mut result = self.compile_expr(body)?;

                // Pop all locals
                for _ in bindings {
                    self.locals.pop();
                }

                // Build nested quantifier structure from inside out
                for binding in bindings.iter().rev() {
                    let compiled_domain = self.compile_expr(&binding.domain)?;
                    result = match kind {
                        QuantifierKind::Forall => CompiledExpr::Forall {
                            domain: Box::new(compiled_domain),
                            body: Box::new(result),
                        },
                        QuantifierKind::Exists => CompiledExpr::Exists {
                            domain: Box::new(compiled_domain),
                            body: Box::new(result),
                        },
                    };
                }

                result
            }

            ExprKind::Choose {
                var,
                domain,
                predicate,
            } => {
                let compiled_domain = self.compile_expr(domain)?;
                self.locals.push(var.name.clone());
                let compiled_pred = self.compile_expr(predicate)?;
                self.locals.pop();
                CompiledExpr::Choose {
                    domain: Box::new(compiled_domain),
                    predicate: Box::new(compiled_pred),
                }
            }

            ExprKind::Fix { var, predicate } => {
                self.locals.push(var.name.clone());
                let compiled_pred = self.compile_expr(predicate)?;
                self.locals.pop();
                CompiledExpr::Fix {
                    predicate: Box::new(compiled_pred),
                }
            }

            ExprKind::Let { var, value, body } => {
                let compiled_value = self.compile_expr(value)?;
                self.locals.push(var.name.clone());
                let compiled_body = self.compile_expr(body)?;
                self.locals.pop();
                CompiledExpr::Let {
                    value: Box::new(compiled_value),
                    body: Box::new(compiled_body),
                }
            }

            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => CompiledExpr::If {
                cond: Box::new(self.compile_expr(cond)?),
                then_branch: Box::new(self.compile_expr(then_branch)?),
                else_branch: Box::new(self.compile_expr(else_branch)?),
            },

            ExprKind::Require(inner) => {
                // Require is only used during action body parsing, should already be handled
                self.compile_expr(inner)?
            }

            ExprKind::Changes(var) => {
                if let Some(&idx) = self.var_indices.get(&var.name) {
                    CompiledExpr::Changes(idx)
                } else {
                    return Err(CompileError::UndefinedVariable(var.name.clone()));
                }
            }

            ExprKind::Enabled(action) => {
                if let Some(&idx) = self.action_indices.get(&action.name) {
                    CompiledExpr::Enabled(idx)
                } else {
                    return Err(CompileError::UndefinedAction(action.name.clone()));
                }
            }

            ExprKind::SeqHead(seq) => CompiledExpr::SeqHead(Box::new(self.compile_expr(seq)?)),

            ExprKind::SeqTail(seq) => CompiledExpr::SeqTail(Box::new(self.compile_expr(seq)?)),

            ExprKind::Len(expr) => CompiledExpr::Len(Box::new(self.compile_expr(expr)?)),

            ExprKind::Keys(expr) => CompiledExpr::Keys(Box::new(self.compile_expr(expr)?)),

            ExprKind::Values(expr) => CompiledExpr::Values(Box::new(self.compile_expr(expr)?)),

            ExprKind::BigUnion(expr) => CompiledExpr::BigUnion(Box::new(self.compile_expr(expr)?)),

            ExprKind::Powerset(expr) => CompiledExpr::Powerset(Box::new(self.compile_expr(expr)?)),

            ExprKind::Always(_) | ExprKind::Eventually(_) | ExprKind::LeadsTo { .. } => {
                // Temporal operators are handled at the property level, not here
                return Err(CompileError::Unsupported(
                    "temporal operators in expression context".to_string(),
                ));
            }

            ExprKind::Range { lo, hi } => CompiledExpr::Range {
                lo: Box::new(self.compile_expr(lo)?),
                hi: Box::new(self.compile_expr(hi)?),
            },

            ExprKind::Paren(inner) => self.compile_expr(inner)?,
        };

        Ok(compiled)
    }

    fn compile_ident(&self, name: &str) -> CompileResult<CompiledExpr> {
        // Check locals first (innermost to outermost)
        for (i, local) in self.locals.iter().rev().enumerate() {
            if local == name {
                return Ok(CompiledExpr::Local(i));
            }
        }

        // Check parameters
        for (i, param) in self.params.iter().enumerate() {
            if param == name {
                return Ok(CompiledExpr::Param(i));
            }
        }

        // Check constants
        if let Some(&idx) = self.const_indices.get(name) {
            return Ok(CompiledExpr::Const(idx));
        }

        // Check state variables
        if let Some(&idx) = self.var_indices.get(name) {
            return Ok(CompiledExpr::Var(idx));
        }

        Err(CompileError::UndefinedVariable(name.to_string()))
    }

    fn lookup_var_type(&self, name: &str) -> Type {
        self.env
            .lookup_var(name)
            .map(|ty| self.env.resolve_type(ty))
            .unwrap_or(specl_types::Type::Error)
    }

    fn lookup_const_type(&self, name: &str) -> Type {
        self.env
            .lookup_const(name)
            .map(|ty| self.env.resolve_type(ty))
            .unwrap_or(specl_types::Type::Error)
    }

    fn collect_changes_impl(&self, expr: &CompiledExpr, changes: &mut Vec<usize>) {
        match expr {
            CompiledExpr::PrimedVar(idx) => changes.push(*idx),
            CompiledExpr::Changes(idx) => changes.push(*idx),
            CompiledExpr::Binary { left, right, .. } => {
                self.collect_changes_impl(left, changes);
                self.collect_changes_impl(right, changes);
            }
            CompiledExpr::Unary { operand, .. } => {
                self.collect_changes_impl(operand, changes);
            }
            CompiledExpr::SetLit(elems)
            | CompiledExpr::SeqLit(elems)
            | CompiledExpr::TupleLit(elems) => {
                for e in elems {
                    self.collect_changes_impl(e, changes);
                }
            }
            CompiledExpr::DictLit(entries) => {
                for (k, v) in entries {
                    self.collect_changes_impl(k, changes);
                    self.collect_changes_impl(v, changes);
                }
            }
            CompiledExpr::Index { base, index } => {
                self.collect_changes_impl(base, changes);
                self.collect_changes_impl(index, changes);
            }
            CompiledExpr::Slice { base, lo, hi } => {
                self.collect_changes_impl(base, changes);
                self.collect_changes_impl(lo, changes);
                self.collect_changes_impl(hi, changes);
            }
            CompiledExpr::Field { base, .. } => {
                self.collect_changes_impl(base, changes);
            }
            CompiledExpr::Call { func, args } => {
                self.collect_changes_impl(func, changes);
                for a in args {
                    self.collect_changes_impl(a, changes);
                }
            }
            CompiledExpr::ActionCall { args, .. } => {
                for a in args {
                    self.collect_changes_impl(a, changes);
                }
            }
            CompiledExpr::FnLit { domain, body }
            | CompiledExpr::Forall { domain, body }
            | CompiledExpr::Exists { domain, body }
            | CompiledExpr::Choose {
                domain,
                predicate: body,
            } => {
                self.collect_changes_impl(domain, changes);
                self.collect_changes_impl(body, changes);
            }
            CompiledExpr::SetComprehension {
                element,
                domain,
                filter,
            } => {
                self.collect_changes_impl(element, changes);
                self.collect_changes_impl(domain, changes);
                if let Some(f) = filter {
                    self.collect_changes_impl(f, changes);
                }
            }
            CompiledExpr::RecordUpdate { base, updates } => {
                self.collect_changes_impl(base, changes);
                for (_, v) in updates {
                    self.collect_changes_impl(v, changes);
                }
            }
            CompiledExpr::FnUpdate { base, key, value } => {
                self.collect_changes_impl(base, changes);
                self.collect_changes_impl(key, changes);
                self.collect_changes_impl(value, changes);
            }
            CompiledExpr::Let { value, body } => {
                self.collect_changes_impl(value, changes);
                self.collect_changes_impl(body, changes);
            }
            CompiledExpr::If {
                cond,
                then_branch,
                else_branch,
            } => {
                self.collect_changes_impl(cond, changes);
                self.collect_changes_impl(then_branch, changes);
                self.collect_changes_impl(else_branch, changes);
            }
            CompiledExpr::Range { lo, hi } => {
                self.collect_changes_impl(lo, changes);
                self.collect_changes_impl(hi, changes);
            }
            CompiledExpr::SeqHead(seq)
            | CompiledExpr::SeqTail(seq)
            | CompiledExpr::Len(seq)
            | CompiledExpr::Keys(seq)
            | CompiledExpr::Values(seq) => {
                self.collect_changes_impl(seq, changes);
            }
            _ => {}
        }
    }

    /// Collect all variables read by an expression (Var references, not PrimedVar).
    fn collect_reads(&self, expr: &CompiledExpr) -> Vec<usize> {
        let mut reads = Vec::new();
        self.collect_reads_impl(expr, &mut reads);
        reads.sort();
        reads.dedup();
        reads
    }

    fn collect_reads_impl(&self, expr: &CompiledExpr, reads: &mut Vec<usize>) {
        match expr {
            CompiledExpr::Var(idx) => reads.push(*idx),
            CompiledExpr::Binary { left, right, .. } => {
                self.collect_reads_impl(left, reads);
                self.collect_reads_impl(right, reads);
            }
            CompiledExpr::Unary { operand, .. } => {
                self.collect_reads_impl(operand, reads);
            }
            CompiledExpr::SetLit(elems)
            | CompiledExpr::SeqLit(elems)
            | CompiledExpr::TupleLit(elems) => {
                for e in elems {
                    self.collect_reads_impl(e, reads);
                }
            }
            CompiledExpr::DictLit(entries) => {
                for (k, v) in entries {
                    self.collect_reads_impl(k, reads);
                    self.collect_reads_impl(v, reads);
                }
            }
            CompiledExpr::Index { base, index } => {
                self.collect_reads_impl(base, reads);
                self.collect_reads_impl(index, reads);
            }
            CompiledExpr::Slice { base, lo, hi } => {
                self.collect_reads_impl(base, reads);
                self.collect_reads_impl(lo, reads);
                self.collect_reads_impl(hi, reads);
            }
            CompiledExpr::Field { base, .. } => {
                self.collect_reads_impl(base, reads);
            }
            CompiledExpr::Call { func, args } => {
                self.collect_reads_impl(func, reads);
                for arg in args {
                    self.collect_reads_impl(arg, reads);
                }
            }
            CompiledExpr::ActionCall { args, .. } => {
                for arg in args {
                    self.collect_reads_impl(arg, reads);
                }
            }
            CompiledExpr::Forall { domain, body }
            | CompiledExpr::Exists { domain, body }
            | CompiledExpr::FnLit { domain, body } => {
                self.collect_reads_impl(domain, reads);
                self.collect_reads_impl(body, reads);
            }
            CompiledExpr::Choose { domain, predicate } => {
                self.collect_reads_impl(domain, reads);
                self.collect_reads_impl(predicate, reads);
            }
            CompiledExpr::SetComprehension {
                element,
                domain,
                filter,
            } => {
                self.collect_reads_impl(element, reads);
                self.collect_reads_impl(domain, reads);
                if let Some(f) = filter {
                    self.collect_reads_impl(f, reads);
                }
            }
            CompiledExpr::RecordUpdate { base, updates } => {
                self.collect_reads_impl(base, reads);
                for (_, v) in updates {
                    self.collect_reads_impl(v, reads);
                }
            }
            CompiledExpr::FnUpdate { base, key, value } => {
                self.collect_reads_impl(base, reads);
                self.collect_reads_impl(key, reads);
                self.collect_reads_impl(value, reads);
            }
            CompiledExpr::Let { value, body } => {
                self.collect_reads_impl(value, reads);
                self.collect_reads_impl(body, reads);
            }
            CompiledExpr::If {
                cond,
                then_branch,
                else_branch,
            } => {
                self.collect_reads_impl(cond, reads);
                self.collect_reads_impl(then_branch, reads);
                self.collect_reads_impl(else_branch, reads);
            }
            CompiledExpr::Range { lo, hi } => {
                self.collect_reads_impl(lo, reads);
                self.collect_reads_impl(hi, reads);
            }
            CompiledExpr::SeqHead(seq)
            | CompiledExpr::SeqTail(seq)
            | CompiledExpr::Len(seq)
            | CompiledExpr::Keys(seq)
            | CompiledExpr::Values(seq) => {
                self.collect_reads_impl(seq, reads);
            }
            _ => {}
        }
    }

    /// Analyze effect to extract write key params for instance-level POR.
    /// For each variable in `changes`, determine if writes are keyed (via FnUpdate chain).
    /// Returns (var_idx, Some(keys)) for keyed writes, (var_idx, None) for unkeyed.
    fn collect_write_key_params(
        effect: &CompiledExpr,
        changes: &[usize],
    ) -> Vec<(usize, Option<Vec<KeySource>>)> {
        use std::collections::HashMap;
        let mut result: HashMap<usize, Option<Vec<KeySource>>> = HashMap::new();

        // Decompose effect into conjuncts and find PrimedVar(v) == rhs assignments
        Self::extract_assignments(effect, &mut |var_idx, rhs| {
            if !changes.contains(&var_idx) {
                return;
            }
            // Check if rhs is a FnUpdate chain rooted at Var(var_idx)
            let keys = Self::extract_fn_update_keys(rhs, var_idx);
            match result.get(&var_idx) {
                None => {
                    result.insert(var_idx, keys);
                }
                Some(None) => {} // Already unkeyed, can't improve
                Some(Some(_)) if keys.is_none() => {
                    result.insert(var_idx, None); // Downgrade to unkeyed
                }
                _ => {} // Both keyed, keep first
            }
        });

        // Any variable in changes not found in effect is unkeyed
        for &var_idx in changes {
            result.entry(var_idx).or_insert(None);
        }

        let mut pairs: Vec<_> = result.into_iter().collect();
        pairs.sort_by_key(|(v, _)| *v);
        pairs
    }

    /// Walk effect And-tree to find PrimedVar(v) == rhs assignments.
    fn extract_assignments(expr: &CompiledExpr, callback: &mut impl FnMut(usize, &CompiledExpr)) {
        match expr {
            CompiledExpr::Binary {
                op: IrBinOp::And,
                left,
                right,
            } => {
                Self::extract_assignments(left, callback);
                Self::extract_assignments(right, callback);
            }
            CompiledExpr::Binary {
                op: IrBinOp::Eq,
                left,
                right,
            } => {
                if let CompiledExpr::PrimedVar(idx) = left.as_ref() {
                    callback(*idx, right);
                } else if let CompiledExpr::PrimedVar(idx) = right.as_ref() {
                    callback(*idx, left);
                }
            }
            _ => {}
        }
    }

    /// Extract key sources from a dict update expression.
    /// Handles both FnUpdate chains and Union with DictLit (dict merge `|` syntax).
    /// Returns Some(keys) if the expression updates target_var at known keys, None otherwise.
    fn extract_fn_update_keys(expr: &CompiledExpr, target_var: usize) -> Option<Vec<KeySource>> {
        match expr {
            // FnUpdate chain: dict[k1 -> v1][k2 -> v2]...
            CompiledExpr::FnUpdate { base, key, .. } => {
                let mut keys = Self::extract_fn_update_keys(base, target_var)?;
                match key.as_ref() {
                    CompiledExpr::Param(p) => keys.push(KeySource::Param(*p)),
                    CompiledExpr::Int(k) => keys.push(KeySource::Literal(*k)),
                    _ => return None,
                }
                Some(keys)
            }
            // Dict merge: var | { k1: v1, k2: v2 }
            // Compiles to Binary { op: Union, left: Var(target), right: DictLit(pairs) }
            CompiledExpr::Binary {
                op: IrBinOp::Union,
                left,
                right,
            } => {
                // Left must be Var(target_var)
                if !matches!(left.as_ref(), CompiledExpr::Var(idx) if *idx == target_var) {
                    return None;
                }
                // Right must be DictLit with statically resolvable keys
                if let CompiledExpr::DictLit(pairs) = right.as_ref() {
                    let mut keys = Vec::new();
                    for (key_expr, _) in pairs {
                        match key_expr {
                            CompiledExpr::Param(p) => keys.push(KeySource::Param(*p)),
                            CompiledExpr::Int(k) => keys.push(KeySource::Literal(*k)),
                            _ => return None,
                        }
                    }
                    Some(keys)
                } else {
                    None
                }
            }
            CompiledExpr::Var(idx) if *idx == target_var => Some(Vec::new()),
            _ => None,
        }
    }

    /// Analyze guard and effect to extract read key params for instance-level POR.
    /// For each variable in `reads`, determine if all reads are keyed (via Index).
    fn collect_read_key_params(
        guard: &CompiledExpr,
        effect: &CompiledExpr,
        reads: &[usize],
    ) -> Vec<(usize, Option<Vec<KeySource>>)> {
        use std::collections::HashMap;
        // Track: var_idx -> (keys_seen, has_unkeyed_access)
        let mut info: HashMap<usize, (Vec<KeySource>, bool)> = HashMap::new();

        for &var_idx in reads {
            info.insert(var_idx, (Vec::new(), false));
        }

        Self::collect_read_keys_impl(guard, &mut info);
        Self::collect_read_keys_impl(effect, &mut info);

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

    /// Recursively collect read key info from an expression.
    /// `parent_is_index` tracks whether the current Var is inside an Index base.
    fn collect_read_keys_impl(
        expr: &CompiledExpr,
        info: &mut std::collections::HashMap<usize, (Vec<KeySource>, bool)>,
    ) {
        match expr {
            // Key pattern: var[key] — keyed read
            CompiledExpr::Index { base, index } => {
                if let CompiledExpr::Var(var_idx) = base.as_ref() {
                    if let Some((keys, _)) = info.get_mut(var_idx) {
                        match index.as_ref() {
                            CompiledExpr::Param(p) => keys.push(KeySource::Param(*p)),
                            CompiledExpr::Int(k) => keys.push(KeySource::Literal(*k)),
                            _ => {
                                // Computed index — mark as unkeyed
                                info.get_mut(var_idx).unwrap().1 = true;
                            }
                        }
                    }
                } else {
                    // base is not a simple Var — recurse into base
                    Self::collect_read_keys_impl(base, info);
                }
                // Always recurse into index expr (it may contain Var refs)
                Self::collect_read_keys_impl(index, info);
            }
            // Bare Var without Index — unkeyed read
            CompiledExpr::Var(var_idx) => {
                if let Some((_, has_unkeyed)) = info.get_mut(var_idx) {
                    *has_unkeyed = true;
                }
            }
            // Dict merge pattern: var | { k: v, ... }
            // The Var on the left is the base being updated, not a whole-variable read.
            // Only recurse into the DictLit values (reads) and keys.
            CompiledExpr::Binary {
                op: IrBinOp::Union,
                left,
                right,
            } if matches!(left.as_ref(), CompiledExpr::Var(_))
                && matches!(right.as_ref(), CompiledExpr::DictLit(_)) =>
            {
                // Skip left (Var) — it's the update base, not a whole-variable read.
                // Recurse into the DictLit entries (values may contain keyed reads).
                if let CompiledExpr::DictLit(entries) = right.as_ref() {
                    for (k, v) in entries {
                        Self::collect_read_keys_impl(k, info);
                        Self::collect_read_keys_impl(v, info);
                    }
                }
            }
            // Recurse into all subexpressions
            CompiledExpr::Binary { left, right, .. } => {
                Self::collect_read_keys_impl(left, info);
                Self::collect_read_keys_impl(right, info);
            }
            CompiledExpr::Unary { operand, .. } => {
                Self::collect_read_keys_impl(operand, info);
            }
            CompiledExpr::SetLit(elems)
            | CompiledExpr::SeqLit(elems)
            | CompiledExpr::TupleLit(elems) => {
                for e in elems {
                    Self::collect_read_keys_impl(e, info);
                }
            }
            CompiledExpr::DictLit(entries) => {
                for (k, v) in entries {
                    Self::collect_read_keys_impl(k, info);
                    Self::collect_read_keys_impl(v, info);
                }
            }
            CompiledExpr::Slice { base, lo, hi } => {
                Self::collect_read_keys_impl(base, info);
                Self::collect_read_keys_impl(lo, info);
                Self::collect_read_keys_impl(hi, info);
            }
            CompiledExpr::Field { base, .. } => {
                Self::collect_read_keys_impl(base, info);
            }
            CompiledExpr::Call { func, args } => {
                Self::collect_read_keys_impl(func, info);
                for a in args {
                    Self::collect_read_keys_impl(a, info);
                }
            }
            CompiledExpr::ActionCall { args, .. } => {
                for a in args {
                    Self::collect_read_keys_impl(a, info);
                }
            }
            CompiledExpr::Forall { domain, body }
            | CompiledExpr::Exists { domain, body }
            | CompiledExpr::FnLit { domain, body } => {
                Self::collect_read_keys_impl(domain, info);
                Self::collect_read_keys_impl(body, info);
            }
            CompiledExpr::Choose { domain, predicate } => {
                Self::collect_read_keys_impl(domain, info);
                Self::collect_read_keys_impl(predicate, info);
            }
            CompiledExpr::SetComprehension {
                element,
                domain,
                filter,
            } => {
                Self::collect_read_keys_impl(element, info);
                Self::collect_read_keys_impl(domain, info);
                if let Some(f) = filter {
                    Self::collect_read_keys_impl(f, info);
                }
            }
            CompiledExpr::RecordUpdate { base, updates } => {
                Self::collect_read_keys_impl(base, info);
                for (_, v) in updates {
                    Self::collect_read_keys_impl(v, info);
                }
            }
            // FnUpdate chain: var[k1 -> v1][k2 -> v2]...
            // The innermost base Var is the update target, not a whole-variable read.
            CompiledExpr::FnUpdate { base, key, value } => {
                // Only skip the base Var for the innermost base of the chain.
                // If base is another FnUpdate, recurse normally (it handles its own base).
                // If base is Var, skip it (same logic as Union+DictLit).
                if !matches!(base.as_ref(), CompiledExpr::Var(_)) {
                    Self::collect_read_keys_impl(base, info);
                }
                Self::collect_read_keys_impl(key, info);
                Self::collect_read_keys_impl(value, info);
            }
            CompiledExpr::Let { value, body } => {
                Self::collect_read_keys_impl(value, info);
                Self::collect_read_keys_impl(body, info);
            }
            CompiledExpr::If {
                cond,
                then_branch,
                else_branch,
            } => {
                Self::collect_read_keys_impl(cond, info);
                Self::collect_read_keys_impl(then_branch, info);
                Self::collect_read_keys_impl(else_branch, info);
            }
            CompiledExpr::Range { lo, hi } => {
                Self::collect_read_keys_impl(lo, info);
                Self::collect_read_keys_impl(hi, info);
            }
            CompiledExpr::Len(inner)
            | CompiledExpr::Keys(inner)
            | CompiledExpr::Values(inner)
            | CompiledExpr::SeqHead(inner)
            | CompiledExpr::SeqTail(inner)
            | CompiledExpr::BigUnion(inner)
            | CompiledExpr::Powerset(inner) => {
                // These access the variable as a whole — mark unkeyed if it's a Var
                if let CompiledExpr::Var(var_idx) = inner.as_ref() {
                    if let Some((_, has_unkeyed)) = info.get_mut(var_idx) {
                        *has_unkeyed = true;
                    }
                } else {
                    Self::collect_read_keys_impl(inner, info);
                }
            }
            _ => {}
        }
    }

    /// Add implicit frame constraints for variables not mentioned in changes.
    fn add_implicit_frame(&self, effect: CompiledExpr, changes: &[usize]) -> CompiledExpr {
        let mut result = effect;

        for &var_idx in self.var_indices.values() {
            if !changes.contains(&var_idx) {
                // Add: var' == var
                let unchanged = CompiledExpr::Unchanged(var_idx);
                result = CompiledExpr::Binary {
                    op: IrBinOp::And,
                    left: Box::new(result),
                    right: Box::new(unchanged),
                };
            }
        }

        result
    }

    /// Detect symmetry groups from variable types.
    /// A symmetry group contains variables with Fn[0..N, T] type where they share
    /// the same domain size N.
    fn detect_symmetry_groups(&self, vars: &[IrVarDecl]) -> Vec<SymmetryGroup> {
        use std::collections::HashMap;

        // Map domain_size -> list of variable indices with Fn[0..domain_size, T] type
        let mut groups: HashMap<usize, Vec<usize>> = HashMap::new();

        for var in vars {
            if let Type::Fn(key_ty, _) = &var.ty {
                // Check if key type is a range 0..N
                if let Type::Range(0, hi) = key_ty.as_ref() {
                    let domain_size = (*hi + 1) as usize;
                    groups.entry(domain_size).or_default().push(var.index);
                }
            }
        }

        // Only create symmetry groups for domains with at least one variable
        groups
            .into_iter()
            .filter(|(_, vars)| !vars.is_empty())
            .map(|(domain_size, variables)| SymmetryGroup {
                domain_size,
                variables,
            })
            .collect()
    }
    /// Check if two template-dependent actions could be instance-independent.
    /// True iff every shared variable (in the write/read intersection) has keyed
    /// access on both sides.
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

        // For each variable that A writes and B reads or writes
        for &var_idx in &a.changes {
            if b.reads.contains(&var_idx) || b.changes.contains(&var_idx) {
                // A must have keyed write access
                match find_key_info(&a.write_key_params, var_idx) {
                    Some(Some(_)) => {} // Keyed — ok
                    _ => return false,  // Unkeyed or missing — not refinable
                }
                // B must have keyed access for both reads and writes
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
        // Symmetric: B writes, A reads
        for &var_idx in &b.changes {
            if a.reads.contains(&var_idx) && !a.changes.contains(&var_idx) {
                // Already checked A.changes above; only check A.reads here
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
}

/// Estimate the evaluation cost of a compiled expression for guard reordering.
/// Lower cost = cheaper to evaluate = should be checked first (short-circuit).
fn expr_cost(expr: &CompiledExpr) -> u32 {
    match expr {
        // Leaves: O(1)
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

        // Simple operations
        CompiledExpr::Binary { left, right, .. } => 1 + expr_cost(left) + expr_cost(right),
        CompiledExpr::Unary { operand, .. } => 1 + expr_cost(operand),
        CompiledExpr::Index { base, index } => 2 + expr_cost(base) + expr_cost(index),
        CompiledExpr::Let { value, body } => 1 + expr_cost(value) + expr_cost(body),
        CompiledExpr::If {
            cond,
            then_branch,
            else_branch,
        } => 1 + expr_cost(cond) + expr_cost(then_branch).max(expr_cost(else_branch)),

        // Collection literals
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

        // Quantifiers and comprehensions: expensive (iterate domain)
        CompiledExpr::Forall { domain, body }
        | CompiledExpr::Exists { domain, body }
        | CompiledExpr::FnLit { domain, body } => 10 + expr_cost(domain) * expr_cost(body),
        CompiledExpr::Choose { domain, predicate }
        | CompiledExpr::SetComprehension {
            domain,
            filter: Some(predicate),
            ..
        } => 10 + expr_cost(domain) * expr_cost(predicate),
        CompiledExpr::SetComprehension {
            domain,
            element,
            filter: None,
        } => 10 + expr_cost(domain) * expr_cost(element),
        CompiledExpr::Fix { predicate } => 10 + expr_cost(predicate),

        // Access operations
        CompiledExpr::Slice { base, lo, hi } => 3 + expr_cost(base) + expr_cost(lo) + expr_cost(hi),
        CompiledExpr::Field { base, .. } => 1 + expr_cost(base),
        CompiledExpr::SeqHead(inner) | CompiledExpr::SeqTail(inner) => 2 + expr_cost(inner),
        CompiledExpr::Len(inner) | CompiledExpr::Keys(inner) | CompiledExpr::Values(inner) => {
            2 + expr_cost(inner)
        }
        CompiledExpr::BigUnion(inner) | CompiledExpr::Powerset(inner) => 10 + expr_cost(inner),

        // Updates
        CompiledExpr::FnUpdate { base, key, value } => {
            2 + expr_cost(base) + expr_cost(key) + expr_cost(value)
        }
        CompiledExpr::RecordUpdate { base, updates } => {
            2 + expr_cost(base) + updates.iter().map(|(_, v)| expr_cost(v)).sum::<u32>()
        }

        // Calls
        CompiledExpr::Call { args, .. } => args.iter().map(expr_cost).sum::<u32>() + 5,
        CompiledExpr::ActionCall { args, .. } => args.iter().map(expr_cost).sum::<u32>() + 10,

        // Range
        CompiledExpr::Range { lo, hi } => 2 + expr_cost(lo) + expr_cost(hi),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use specl_syntax::parse;

    #[test]
    fn test_compile_simple() {
        let source = r#"
module Counter
const MAX: Nat
var count: Nat
init { count == 0 }
action Inc() {
    require count < MAX
    count = count + 1
}
invariant Bounded { count <= MAX }
"#;
        let module = parse(source).unwrap();
        let spec = compile(&module).unwrap();

        assert_eq!(spec.vars.len(), 1);
        assert_eq!(spec.vars[0].name, "count");
        assert_eq!(spec.consts.len(), 1);
        assert_eq!(spec.consts[0].name, "MAX");
        assert_eq!(spec.actions.len(), 1);
        assert_eq!(spec.actions[0].name, "Inc");
        assert_eq!(spec.invariants.len(), 1);
    }

    #[test]
    fn test_implicit_frame() {
        let source = r#"
module Test
var x: Nat
var y: Nat
action SetX() {
    x = 1
}
"#;
        let module = parse(source).unwrap();
        let spec = compile(&module).unwrap();

        // Action should have y as unchanged
        let action = &spec.actions[0];
        assert_eq!(action.changes.len(), 1); // Only x changes

        // Effect should include implicit frame for y
        // (We can verify this by checking the structure)
        match &action.effect {
            CompiledExpr::Binary {
                op: IrBinOp::And, ..
            } => {
                // Good - there's an And, meaning frame was added
            }
            _ => panic!("expected implicit frame"),
        }
    }

    #[test]
    fn test_changes_detection() {
        let source = r#"
module Test
var alice: 0..20
var bob: 0..20
init { alice == 10 and bob == 10 }
action BrokenDeposit() {
    bob = bob + 5
}
"#;
        let module = parse(source).unwrap();
        let spec = compile(&module).unwrap();

        println!("Actions:");
        for action in &spec.actions {
            println!("  {}: changes={:?}", action.name, action.changes);
        }

        assert_eq!(spec.actions.len(), 1);
        assert_eq!(spec.actions[0].changes, vec![1]); // bob is at index 1
    }

    #[test]
    fn test_write_key_params_transfer() {
        let source = r#"
module Transfer
const N: Int
var balance: Dict[0..N, Int]
init { balance == {i: 10 for i in 0..N} }
action Transfer(from: 0..N, to: 0..N) {
    require from != to
    require balance[from] >= 1
    balance = balance | { from: balance[from] - 1, to: balance[to] + 1 }
}
"#;
        let module = parse(source).unwrap();
        let spec = compile(&module).unwrap();

        let action = &spec.actions[0];
        assert_eq!(action.name, "Transfer");
        // Write key params: balance written at keys Param(0) and Param(1)
        assert_eq!(action.write_key_params.len(), 1);
        assert_eq!(action.write_key_params[0].0, 0);
        let write_keys = action.write_key_params[0].1.as_ref().unwrap();
        assert!(write_keys.contains(&KeySource::Param(0)));
        assert!(write_keys.contains(&KeySource::Param(1)));

        // Read key params: balance read at Param(0) and Param(1)
        assert_eq!(action.read_key_params.len(), 1);
        assert_eq!(action.read_key_params[0].0, 0);
        let read_keys = action.read_key_params[0].1.as_ref().unwrap();
        assert!(read_keys.contains(&KeySource::Param(0)));
        assert!(read_keys.contains(&KeySource::Param(1)));

        // Self-pair should be refinable (keyed access on both sides)
        assert!(spec.refinable_pairs[0][0]);
    }
}

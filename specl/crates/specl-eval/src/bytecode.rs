//! Bytecode VM for fast expression evaluation.
//!
//! Compiles CompiledExpr trees to flat bytecode and executes them in a tight
//! loop, eliminating recursive dispatch overhead of the tree-walk interpreter.

use crate::eval::{eval, eval_bool, eval_int, expect_int, type_mismatch};
use crate::value::Value;
use crate::{EvalContext, EvalError, EvalResult};
use specl_ir::{BinOp, CompiledExpr, UnaryOp};
use std::sync::Arc;

/// Bytecode operation.
#[derive(Debug, Clone)]
pub enum Op {
    // === Literals ===
    Int(i64),
    Bool(bool),

    // === Context access ===
    Var(u16),
    PrimedVar(u16),
    Const(u16),
    Param(u16),
    Local(u16),

    // === Arithmetic (pop 2, push 1) ===
    Add,
    Sub,
    Mul,
    Div,
    Mod,

    // === Unary ===
    Neg,
    Not,

    // === Comparison ===
    /// General equality (pop 2 Values, push bool).
    Eq,
    Ne,
    /// Integer comparison (pop 2, extract ints, push bool).
    IntEq,
    IntNe,
    IntLt,
    IntLe,
    IntGt,
    IntGe,

    // === Control flow ===
    /// Jump to target if top of stack is false. Does NOT pop.
    JumpIfFalse(u32),
    /// Jump to target if top of stack is true. Does NOT pop.
    JumpIfTrue(u32),
    /// Unconditional jump.
    Jump(u32),
    /// Pop and discard top of stack.
    Pop,

    // === Collection ops ===
    /// Pop key, pop dict → push dict[key].
    DictGet,
    /// Pop value, pop key, pop dict → push dict | {key: value}.
    DictUpdate,
    /// Pop collection → push len as Int.
    Len,
    /// Pop set, pop elem → push (elem in set).
    Contains,
    /// Pop set, pop elem → push (elem not in set).
    NotContains,
    /// Nested 2-level dict update. Stack: [value, k2, k1, dict] (dict on top).
    /// Performs dict | {k1: (dict[k1] | {k2: value})} in a single pass.
    NestedDictUpdate2,
    /// Nested 3-level dict update. Stack: [value, k3, k2, k1, dict] (dict on top).
    /// Performs dict | {k1: (dict[k1] | {k2: (dict[k1][k2] | {k3: value})})} in a single pass.
    NestedDictUpdate3,

    // === Local variable management ===
    /// Pop value stack → push onto local stack.
    PushLocal,
    /// Pop from local stack (discard).
    PopLocal,

    // === Range quantifier: Forall ===
    /// Pop hi, pop lo. If lo > hi: push true, jump to end_pc.
    /// Else: push Int(lo) onto locals, continue.
    ForallRangeInit(u32),
    /// Pop body result (bool). If false: pop local, push false, jump to end_pc.
    /// Else: increment local. If > hi: pop local, push true, jump to end_pc.
    /// Else: jump to body_pc.
    ForallRangeStep {
        body_pc: u32,
        end_pc: u32,
    },

    // === Range quantifier: Exists ===
    ExistsRangeInit(u32),
    ExistsRangeStep {
        body_pc: u32,
        end_pc: u32,
    },

    // === Count filtered (len of set comprehension over range) ===
    CountRangeInit(u32),
    CountRangeStep {
        body_pc: u32,
        end_pc: u32,
    },

    // === FnLit over range ===
    /// Pop hi, pop lo. If lo > hi: push empty Fn, jump to end_pc.
    /// Else: push Int(lo) onto locals, continue.
    FnLitRangeInit(u32),
    /// Pop body result (value). Append (local, value) to fn being built.
    /// Increment local. If > hi: pop local, push completed Fn, jump to end_pc.
    /// Else: jump to body_pc.
    FnLitRangeStep {
        body_pc: u32,
        end_pc: u32,
    },

    // === Fallback to tree-walk ===
    /// Evaluate fallback expression via tree-walk, push result.
    Fallback(u16),
    /// Evaluate fallback expression via tree-walk as bool, push Bool result.
    FallbackBool(u16),
    /// Evaluate fallback expression via tree-walk as int, push Int result.
    FallbackInt(u16),

    /// End of bytecode.
    Halt,
}

/// Loop state for range-based quantifiers.
struct LoopState {
    hi: i64,
    /// Accumulator for CountRange.
    counter: i64,
    /// Accumulator for FnLitRange.
    fn_buf: Vec<(Value, Value)>,
}

/// Compiled bytecode with fallback expression table.
pub struct Bytecode {
    pub ops: Vec<Op>,
    pub fallbacks: Vec<CompiledExpr>,
}

// ============================================================================
// Compiler
// ============================================================================

/// Compiler state.
struct Compiler {
    ops: Vec<Op>,
    fallbacks: Vec<CompiledExpr>,
}

impl Compiler {
    fn new() -> Self {
        Self {
            ops: Vec::new(),
            fallbacks: Vec::new(),
        }
    }

    fn emit(&mut self, op: Op) -> usize {
        let pc = self.ops.len();
        self.ops.push(op);
        pc
    }

    fn current_pc(&self) -> usize {
        self.ops.len()
    }

    /// Patch a jump target at the given instruction.
    fn patch_jump(&mut self, instr_pc: usize, target: u32) {
        match &mut self.ops[instr_pc] {
            Op::JumpIfFalse(t)
            | Op::JumpIfTrue(t)
            | Op::Jump(t)
            | Op::ForallRangeInit(t)
            | Op::ExistsRangeInit(t)
            | Op::CountRangeInit(t)
            | Op::FnLitRangeInit(t) => *t = target,
            Op::ForallRangeStep { end_pc, .. }
            | Op::ExistsRangeStep { end_pc, .. }
            | Op::CountRangeStep { end_pc, .. }
            | Op::FnLitRangeStep { end_pc, .. } => *end_pc = target,
            _ => {}
        }
    }

    fn add_fallback(&mut self, expr: &CompiledExpr) -> u16 {
        let idx = self.fallbacks.len();
        self.fallbacks.push(expr.clone());
        idx as u16
    }

    /// Compile an expression (result pushed as Value).
    fn compile(&mut self, expr: &CompiledExpr) {
        match expr {
            CompiledExpr::Bool(b) => {
                self.emit(Op::Bool(*b));
            }
            CompiledExpr::Int(n) => {
                self.emit(Op::Int(*n));
            }
            CompiledExpr::Var(idx) => {
                self.emit(Op::Var(*idx as u16));
            }
            CompiledExpr::PrimedVar(idx) => {
                self.emit(Op::PrimedVar(*idx as u16));
            }
            CompiledExpr::Const(idx) => {
                self.emit(Op::Const(*idx as u16));
            }
            CompiledExpr::Param(idx) => {
                self.emit(Op::Param(*idx as u16));
            }
            CompiledExpr::Local(idx) => {
                self.emit(Op::Local(*idx as u16));
            }

            CompiledExpr::Binary { op, left, right } => {
                self.compile_binary(*op, left, right);
            }

            CompiledExpr::Unary {
                op: UnaryOp::Not,
                operand,
            } => {
                self.compile(operand);
                self.emit(Op::Not);
            }
            CompiledExpr::Unary {
                op: UnaryOp::Neg,
                operand,
            } => {
                self.compile(operand);
                self.emit(Op::Neg);
            }

            CompiledExpr::Index { base, index } => {
                self.compile(base);
                self.compile(index);
                self.emit(Op::DictGet);
            }

            CompiledExpr::FnUpdate { base, key, value } => {
                if !self.try_compile_nested_update(base, key, value) {
                    self.compile(base);
                    self.compile(key);
                    self.compile(value);
                    self.emit(Op::DictUpdate);
                }
            }

            CompiledExpr::Len(inner) => {
                self.compile_len(inner);
            }

            CompiledExpr::If {
                cond,
                then_branch,
                else_branch,
            } => {
                self.compile(cond);
                let jump_else = self.emit(Op::JumpIfFalse(0));
                self.emit(Op::Pop);
                self.compile(then_branch);
                let jump_end = self.emit(Op::Jump(0));
                let else_pc = self.current_pc();
                self.patch_jump(jump_else, else_pc as u32);
                self.emit(Op::Pop);
                self.compile(else_branch);
                let end_pc = self.current_pc();
                self.patch_jump(jump_end, end_pc as u32);
            }

            CompiledExpr::Let { value, body } => {
                self.compile(value);
                self.emit(Op::PushLocal);
                self.compile(body);
                self.emit(Op::PopLocal);
            }

            CompiledExpr::Forall { domain, body } => {
                self.compile_forall(domain, body);
            }

            CompiledExpr::Exists { domain, body } => {
                self.compile_exists(domain, body);
            }

            CompiledExpr::FnLit { domain, body } => {
                self.compile_fn_lit(domain, body);
            }

            // Fallback for everything else
            _ => {
                let idx = self.add_fallback(expr);
                self.emit(Op::Fallback(idx));
            }
        }
    }

    fn compile_binary(&mut self, op: BinOp, left: &CompiledExpr, right: &CompiledExpr) {
        match op {
            // Short-circuit AND
            BinOp::And => {
                self.compile(left);
                let jump = self.emit(Op::JumpIfFalse(0));
                self.emit(Op::Pop);
                self.compile(right);
                let end = self.current_pc();
                self.patch_jump(jump, end as u32);
            }
            // Short-circuit OR
            BinOp::Or => {
                self.compile(left);
                let jump = self.emit(Op::JumpIfTrue(0));
                self.emit(Op::Pop);
                self.compile(right);
                let end = self.current_pc();
                self.patch_jump(jump, end as u32);
            }
            // Implies: !left || right
            BinOp::Implies => {
                self.compile(left);
                let jump_false = self.emit(Op::JumpIfFalse(0));
                self.emit(Op::Pop);
                self.compile(right);
                let jump_end = self.emit(Op::Jump(0));
                let true_pc = self.current_pc();
                self.patch_jump(jump_false, true_pc as u32);
                self.emit(Op::Pop);
                self.emit(Op::Bool(true));
                let end_pc = self.current_pc();
                self.patch_jump(jump_end, end_pc as u32);
            }
            // Equality with int fast path
            BinOp::Eq => {
                self.compile(left);
                self.compile(right);
                if is_int_expr(left) || is_int_expr(right) {
                    self.emit(Op::IntEq);
                } else {
                    self.emit(Op::Eq);
                }
            }
            BinOp::Ne => {
                self.compile(left);
                self.compile(right);
                if is_int_expr(left) || is_int_expr(right) {
                    self.emit(Op::IntNe);
                } else {
                    self.emit(Op::Ne);
                }
            }
            // Integer comparisons
            BinOp::Lt => {
                self.compile(left);
                self.compile(right);
                self.emit(Op::IntLt);
            }
            BinOp::Le => {
                self.compile(left);
                self.compile(right);
                self.emit(Op::IntLe);
            }
            BinOp::Gt => {
                self.compile(left);
                self.compile(right);
                self.emit(Op::IntGt);
            }
            BinOp::Ge => {
                self.compile(left);
                self.compile(right);
                self.emit(Op::IntGe);
            }
            // Arithmetic
            BinOp::Add => {
                self.compile(left);
                self.compile(right);
                self.emit(Op::Add);
            }
            BinOp::Sub => {
                self.compile(left);
                self.compile(right);
                self.emit(Op::Sub);
            }
            BinOp::Mul => {
                self.compile(left);
                self.compile(right);
                self.emit(Op::Mul);
            }
            BinOp::Div => {
                self.compile(left);
                self.compile(right);
                self.emit(Op::Div);
            }
            BinOp::Mod => {
                self.compile(left);
                self.compile(right);
                self.emit(Op::Mod);
            }
            // Iff: a == b for booleans
            BinOp::Iff => {
                self.compile(left);
                self.compile(right);
                self.emit(Op::Eq);
            }
            // Set membership
            BinOp::In => {
                self.compile(left);
                self.compile(right);
                self.emit(Op::Contains);
            }
            BinOp::NotIn => {
                self.compile(left);
                self.compile(right);
                self.emit(Op::NotContains);
            }
            // Dict merge: base | {k: v} → DictUpdate (with nested detection)
            BinOp::Union => {
                if let CompiledExpr::DictLit(entries) = right {
                    if entries.len() == 1 {
                        let (key, value) = &entries[0];
                        if !self.try_compile_nested_update(left, key, value) {
                            self.compile(left);
                            self.compile(key);
                            self.compile(value);
                            self.emit(Op::DictUpdate);
                        }
                    } else {
                        // Multi-key dict merge: base | {k1: v1, k2: v2, ...}
                        // Compile as chained DictUpdates
                        self.compile(left);
                        for (key, value) in entries {
                            self.compile(key);
                            self.compile(value);
                            self.emit(Op::DictUpdate);
                        }
                    }
                } else {
                    // General set union → fallback
                    let expr = CompiledExpr::Binary {
                        op,
                        left: Box::new(left.clone()),
                        right: Box::new(right.clone()),
                    };
                    let idx = self.add_fallback(&expr);
                    self.emit(Op::Fallback(idx));
                }
            }
            // Set/sequence operations → fallback
            BinOp::Intersect | BinOp::Diff | BinOp::SubsetOf | BinOp::Concat => {
                let expr = CompiledExpr::Binary {
                    op,
                    left: Box::new(left.clone()),
                    right: Box::new(right.clone()),
                };
                let idx = self.add_fallback(&expr);
                self.emit(Op::Fallback(idx));
            }
        }
    }

    fn compile_len(&mut self, inner: &CompiledExpr) {
        // Fast path: len({x in lo..hi if pred}) → count without materializing
        if let CompiledExpr::SetComprehension {
            element,
            domain,
            filter,
        } = inner
        {
            if matches!(element.as_ref(), CompiledExpr::Local(0)) {
                if let Some(filter) = filter {
                    if let CompiledExpr::Range { lo, hi } = domain.as_ref() {
                        self.compile(lo);
                        self.compile(hi);
                        let init = self.emit(Op::CountRangeInit(0));
                        let body_pc = self.current_pc();
                        self.compile(filter);
                        let step = self.emit(Op::CountRangeStep {
                            body_pc: body_pc as u32,
                            end_pc: 0,
                        });
                        let end_pc = self.current_pc();
                        self.patch_jump(init, end_pc as u32);
                        self.patch_jump(step, end_pc as u32);
                        return;
                    }
                }
            }
        }
        // General case
        self.compile(inner);
        self.emit(Op::Len);
    }

    fn compile_forall(&mut self, domain: &CompiledExpr, body: &CompiledExpr) {
        if let CompiledExpr::Range { lo, hi } = domain {
            self.compile(lo);
            self.compile(hi);
            let init = self.emit(Op::ForallRangeInit(0));
            let body_pc = self.current_pc();
            self.compile(body);
            let step = self.emit(Op::ForallRangeStep {
                body_pc: body_pc as u32,
                end_pc: 0,
            });
            let end_pc = self.current_pc();
            self.patch_jump(init, end_pc as u32);
            self.patch_jump(step, end_pc as u32);
        } else {
            // Fallback for non-range domains
            let expr = CompiledExpr::Forall {
                domain: Box::new(domain.clone()),
                body: Box::new(body.clone()),
            };
            let idx = self.add_fallback(&expr);
            self.emit(Op::Fallback(idx));
        }
    }

    fn compile_exists(&mut self, domain: &CompiledExpr, body: &CompiledExpr) {
        if let CompiledExpr::Range { lo, hi } = domain {
            self.compile(lo);
            self.compile(hi);
            let init = self.emit(Op::ExistsRangeInit(0));
            let body_pc = self.current_pc();
            self.compile(body);
            let step = self.emit(Op::ExistsRangeStep {
                body_pc: body_pc as u32,
                end_pc: 0,
            });
            let end_pc = self.current_pc();
            self.patch_jump(init, end_pc as u32);
            self.patch_jump(step, end_pc as u32);
        } else {
            // Fallback for non-range domains (powerset, set, etc.)
            let expr = CompiledExpr::Exists {
                domain: Box::new(domain.clone()),
                body: Box::new(body.clone()),
            };
            let idx = self.add_fallback(&expr);
            self.emit(Op::Fallback(idx));
        }
    }

    fn compile_fn_lit(&mut self, domain: &CompiledExpr, body: &CompiledExpr) {
        if let CompiledExpr::Range { lo, hi } = domain {
            self.compile(lo);
            self.compile(hi);
            let init = self.emit(Op::FnLitRangeInit(0));
            let body_pc = self.current_pc();
            self.compile(body);
            let step = self.emit(Op::FnLitRangeStep {
                body_pc: body_pc as u32,
                end_pc: 0,
            });
            let end_pc = self.current_pc();
            self.patch_jump(init, end_pc as u32);
            self.patch_jump(step, end_pc as u32);
        } else {
            let expr = CompiledExpr::FnLit {
                domain: Box::new(domain.clone()),
                body: Box::new(body.clone()),
            };
            let idx = self.add_fallback(&expr);
            self.emit(Op::Fallback(idx));
        }
    }

    /// Try to compile a nested dict update pattern into a specialized opcode.
    /// Returns true if the pattern was detected and compiled.
    ///
    /// Detects patterns like:
    ///   2-level: `base | {k1: (base[k1] | {k2: value})}`
    ///   3-level: `base | {k1: (base[k1] | {k2: (base[k1][k2] | {k3: value})})}`
    /// Works with both FnUpdate and Union+DictLit representations.
    fn try_compile_nested_update(
        &mut self,
        base: &CompiledExpr,
        key: &CompiledExpr,
        value: &CompiledExpr,
    ) -> bool {
        // Check for 2-level: value is a dict update of base[key]
        if let Some((inner_base, inner_key, inner_value)) = extract_dict_update(value) {
            if let CompiledExpr::Index {
                base: idx_base,
                index: idx_key,
            } = inner_base
            {
                if expr_structural_eq(base, idx_base) && expr_structural_eq(key, idx_key) {
                    // Check for 3-level: inner_value is a dict update of base[key][inner_key]
                    if let Some((inner2_base, inner2_key, inner2_value)) =
                        extract_dict_update(inner_value)
                    {
                        if let CompiledExpr::Index {
                            base: idx2_base,
                            index: idx2_key,
                        } = inner2_base
                        {
                            if let CompiledExpr::Index {
                                base: idx2_inner_base,
                                index: idx2_inner_key,
                            } = idx2_base.as_ref()
                            {
                                if expr_structural_eq(base, idx2_inner_base)
                                    && expr_structural_eq(key, idx2_inner_key)
                                    && expr_structural_eq(inner_key, idx2_key)
                                {
                                    // 3-level match! Compile: value3, k3, k2, k1, base
                                    self.compile(inner2_value);
                                    self.compile(inner2_key);
                                    self.compile(inner_key);
                                    self.compile(key);
                                    self.compile(base);
                                    self.emit(Op::NestedDictUpdate3);
                                    return true;
                                }
                            }
                        }
                    }

                    // 2-level match. Compile: value2, k2, k1, base
                    self.compile(inner_value);
                    self.compile(inner_key);
                    self.compile(key);
                    self.compile(base);
                    self.emit(Op::NestedDictUpdate2);
                    return true;
                }
            }
        }
        false
    }

    fn finish(mut self) -> Bytecode {
        self.emit(Op::Halt);
        Bytecode {
            ops: self.ops,
            fallbacks: self.fallbacks,
        }
    }
}

/// Extract a dict-update triple (base, key, value) from an expression.
/// Recognizes both:
///   - `FnUpdate { base, key, value }`
///   - `Binary { op: Union, left: base, right: DictLit([(key, value)]) }`
fn extract_dict_update(
    expr: &CompiledExpr,
) -> Option<(&CompiledExpr, &CompiledExpr, &CompiledExpr)> {
    match expr {
        CompiledExpr::FnUpdate { base, key, value } => Some((base, key, value)),
        CompiledExpr::Binary {
            op: BinOp::Union,
            left: base,
            right,
        } => {
            if let CompiledExpr::DictLit(entries) = right.as_ref() {
                if entries.len() == 1 {
                    return Some((base, &entries[0].0, &entries[0].1));
                }
            }
            None
        }
        _ => None,
    }
}

/// Structural equality for simple (leaf-node) CompiledExpr used in nested update detection.
fn expr_structural_eq(a: &CompiledExpr, b: &CompiledExpr) -> bool {
    match (a, b) {
        (CompiledExpr::Var(i), CompiledExpr::Var(j)) => i == j,
        (CompiledExpr::PrimedVar(i), CompiledExpr::PrimedVar(j)) => i == j,
        (CompiledExpr::Param(i), CompiledExpr::Param(j)) => i == j,
        (CompiledExpr::Const(i), CompiledExpr::Const(j)) => i == j,
        (CompiledExpr::Local(i), CompiledExpr::Local(j)) => i == j,
        (CompiledExpr::Int(i), CompiledExpr::Int(j)) => i == j,
        (CompiledExpr::Bool(i), CompiledExpr::Bool(j)) => i == j,
        _ => false,
    }
}

/// Check if an expression is statically known to produce an Int.
fn is_int_expr(expr: &CompiledExpr) -> bool {
    matches!(
        expr,
        CompiledExpr::Int(_)
            | CompiledExpr::Len(_)
            | CompiledExpr::Binary {
                op: BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod,
                ..
            }
    )
}

/// Compile a CompiledExpr to bytecode.
pub fn compile_expr(expr: &CompiledExpr) -> Bytecode {
    let mut compiler = Compiler::new();
    compiler.compile(expr);
    compiler.finish()
}

// ============================================================================
// VM Execution
// ============================================================================

/// Execute bytecode and return the result as a bool.
pub fn vm_eval_bool(
    bytecode: &Bytecode,
    vars: &[Value],
    next_vars: &[Value],
    consts: &[Value],
    params: &[Value],
) -> EvalResult<bool> {
    let result = vm_eval(bytecode, vars, next_vars, consts, params)?;
    match result {
        Value::Bool(b) => Ok(b),
        _ => Err(EvalError::TypeMismatch {
            expected: "Bool".to_string(),
            actual: result.type_name().to_string(),
        }),
    }
}

/// Execute bytecode and return the result as a Value.
pub fn vm_eval(
    bytecode: &Bytecode,
    vars: &[Value],
    next_vars: &[Value],
    consts: &[Value],
    params: &[Value],
) -> EvalResult<Value> {
    let ops = &bytecode.ops;
    let mut stack: Vec<Value> = Vec::with_capacity(16);
    let mut locals: Vec<Value> = Vec::new();
    let mut loops: Vec<LoopState> = Vec::new();
    let mut pc: usize = 0;

    loop {
        // Safety: compiler always emits Halt, so pc is always valid
        let op = unsafe { ops.get_unchecked(pc) };
        match op {
            Op::Int(n) => stack.push(Value::Int(*n)),
            Op::Bool(b) => stack.push(Value::Bool(*b)),

            Op::Var(idx) => stack.push(vars[*idx as usize].clone()),
            Op::PrimedVar(idx) => stack.push(next_vars[*idx as usize].clone()),
            Op::Const(idx) => stack.push(consts[*idx as usize].clone()),
            Op::Param(idx) => stack.push(params[*idx as usize].clone()),
            Op::Local(idx) => {
                let stack_idx = locals.len() - 1 - *idx as usize;
                stack.push(locals[stack_idx].clone());
            }

            // Arithmetic
            Op::Add => {
                let b = pop_int(&mut stack)?;
                let a = pop_int(&mut stack)?;
                stack.push(Value::Int(a + b));
            }
            Op::Sub => {
                let b = pop_int(&mut stack)?;
                let a = pop_int(&mut stack)?;
                stack.push(Value::Int(a - b));
            }
            Op::Mul => {
                let b = pop_int(&mut stack)?;
                let a = pop_int(&mut stack)?;
                stack.push(Value::Int(a * b));
            }
            Op::Div => {
                let b = pop_int(&mut stack)?;
                let a = pop_int(&mut stack)?;
                if b == 0 {
                    return Err(EvalError::DivisionByZero);
                }
                stack.push(Value::Int(a / b));
            }
            Op::Mod => {
                let b = pop_int(&mut stack)?;
                let a = pop_int(&mut stack)?;
                if b == 0 {
                    return Err(EvalError::DivisionByZero);
                }
                stack.push(Value::Int(a % b));
            }
            Op::Neg => {
                let a = pop_int(&mut stack)?;
                stack.push(Value::Int(-a));
            }

            // Boolean
            Op::Not => {
                let a = pop_bool(&mut stack)?;
                stack.push(Value::Bool(!a));
            }

            // General comparison
            Op::Eq => {
                let b = stack.pop().unwrap();
                let a = stack.pop().unwrap();
                stack.push(Value::Bool(a == b));
            }
            Op::Ne => {
                let b = stack.pop().unwrap();
                let a = stack.pop().unwrap();
                stack.push(Value::Bool(a != b));
            }

            // Integer comparison
            Op::IntEq => {
                let b = pop_int(&mut stack)?;
                let a = pop_int(&mut stack)?;
                stack.push(Value::Bool(a == b));
            }
            Op::IntNe => {
                let b = pop_int(&mut stack)?;
                let a = pop_int(&mut stack)?;
                stack.push(Value::Bool(a != b));
            }
            Op::IntLt => {
                let b = pop_int(&mut stack)?;
                let a = pop_int(&mut stack)?;
                stack.push(Value::Bool(a < b));
            }
            Op::IntLe => {
                let b = pop_int(&mut stack)?;
                let a = pop_int(&mut stack)?;
                stack.push(Value::Bool(a <= b));
            }
            Op::IntGt => {
                let b = pop_int(&mut stack)?;
                let a = pop_int(&mut stack)?;
                stack.push(Value::Bool(a > b));
            }
            Op::IntGe => {
                let b = pop_int(&mut stack)?;
                let a = pop_int(&mut stack)?;
                stack.push(Value::Bool(a >= b));
            }

            // Control flow
            Op::JumpIfFalse(target) => {
                if !peek_bool(&stack)? {
                    pc = *target as usize;
                    continue;
                }
            }
            Op::JumpIfTrue(target) => {
                if peek_bool(&stack)? {
                    pc = *target as usize;
                    continue;
                }
            }
            Op::Jump(target) => {
                pc = *target as usize;
                continue;
            }
            Op::Pop => {
                stack.pop();
            }

            // Dict/collection ops
            Op::DictGet => {
                let key = stack.pop().unwrap();
                let base = stack.pop().unwrap();
                match &base {
                    Value::IntMap(arr) => {
                        let k = expect_int(&key)? as usize;
                        stack.push(Value::Int(arr[k]));
                    }
                    Value::Fn(map) => {
                        let val = Value::fn_get(map, &key)
                            .cloned()
                            .ok_or_else(|| EvalError::KeyNotFound(key.to_string()))?;
                        stack.push(val);
                    }
                    Value::Seq(seq) => {
                        let idx = expect_int(&key)?;
                        if idx < 0 || idx as usize >= seq.len() {
                            return Err(EvalError::IndexOutOfBounds {
                                index: idx,
                                length: seq.len(),
                            });
                        }
                        stack.push(seq[idx as usize].clone());
                    }
                    _ => {
                        return Err(EvalError::TypeMismatch {
                            expected: "Fn or Seq".to_string(),
                            actual: base.type_name().to_string(),
                        })
                    }
                }
            }
            Op::DictUpdate => {
                let value = stack.pop().unwrap();
                let key = stack.pop().unwrap();
                let base = stack.pop().unwrap();
                match base {
                    Value::IntMap(mut arr) => {
                        let k = expect_int(&key)? as usize;
                        if let Value::Int(v) = value {
                            Arc::make_mut(&mut arr)[k] = v;
                            stack.push(Value::IntMap(arr));
                        } else {
                            let mut fn_vec: Vec<(Value, Value)> = arr
                                .iter()
                                .enumerate()
                                .map(|(i, v)| (Value::Int(i as i64), Value::Int(*v)))
                                .collect();
                            Value::fn_insert(&mut fn_vec, key, value);
                            stack.push(Value::Fn(Arc::new(fn_vec)));
                        }
                    }
                    Value::Fn(mut map) => {
                        Value::fn_insert(Arc::make_mut(&mut map), key, value);
                        stack.push(Value::Fn(map));
                    }
                    _ => {
                        return Err(EvalError::TypeMismatch {
                            expected: "Fn".to_string(),
                            actual: base.type_name().to_string(),
                        })
                    }
                }
            }
            Op::NestedDictUpdate2 => {
                let dict = stack.pop().unwrap();
                let k1 = stack.pop().unwrap();
                let k2 = stack.pop().unwrap();
                let value = stack.pop().unwrap();
                match dict {
                    Value::Fn(mut outer_arc) => {
                        let outer = Arc::make_mut(&mut outer_arc);
                        let pos = outer
                            .binary_search_by(|(k, _)| k.cmp(&k1))
                            .map_err(|_| EvalError::KeyNotFound(k1.to_string()))?;
                        match &mut outer[pos].1 {
                            Value::IntMap(inner_arc) => {
                                let k2_int = expect_int(&k2)? as usize;
                                let v_int = expect_int(&value)?;
                                Arc::make_mut(inner_arc)[k2_int] = v_int;
                            }
                            Value::Fn(inner_arc) => {
                                Value::fn_insert(Arc::make_mut(inner_arc), k2, value);
                            }
                            _ => {
                                return Err(EvalError::TypeMismatch {
                                    expected: "Fn".to_string(),
                                    actual: outer[pos].1.type_name().to_string(),
                                })
                            }
                        }
                        stack.push(Value::Fn(outer_arc));
                    }
                    _ => {
                        return Err(EvalError::TypeMismatch {
                            expected: "Fn".to_string(),
                            actual: dict.type_name().to_string(),
                        })
                    }
                }
            }
            Op::NestedDictUpdate3 => {
                let dict = stack.pop().unwrap();
                let k1 = stack.pop().unwrap();
                let k2 = stack.pop().unwrap();
                let k3 = stack.pop().unwrap();
                let value = stack.pop().unwrap();
                match dict {
                    Value::Fn(mut outer_arc) => {
                        let outer = Arc::make_mut(&mut outer_arc);
                        let pos1 = outer
                            .binary_search_by(|(k, _)| k.cmp(&k1))
                            .map_err(|_| EvalError::KeyNotFound(k1.to_string()))?;
                        match &mut outer[pos1].1 {
                            Value::Fn(mid_arc) => {
                                let mid = Arc::make_mut(mid_arc);
                                let pos2 = mid
                                    .binary_search_by(|(k, _)| k.cmp(&k2))
                                    .map_err(|_| EvalError::KeyNotFound(k2.to_string()))?;
                                match &mut mid[pos2].1 {
                                    Value::IntMap(inner_arc) => {
                                        let k3_int = expect_int(&k3)? as usize;
                                        let v_int = expect_int(&value)?;
                                        Arc::make_mut(inner_arc)[k3_int] = v_int;
                                    }
                                    Value::Fn(inner_arc) => {
                                        Value::fn_insert(Arc::make_mut(inner_arc), k3, value);
                                    }
                                    _ => {
                                        return Err(EvalError::TypeMismatch {
                                            expected: "Fn".to_string(),
                                            actual: mid[pos2].1.type_name().to_string(),
                                        })
                                    }
                                }
                            }
                            _ => {
                                return Err(EvalError::TypeMismatch {
                                    expected: "Fn".to_string(),
                                    actual: outer[pos1].1.type_name().to_string(),
                                })
                            }
                        }
                        stack.push(Value::Fn(outer_arc));
                    }
                    _ => {
                        return Err(EvalError::TypeMismatch {
                            expected: "Fn".to_string(),
                            actual: dict.type_name().to_string(),
                        })
                    }
                }
            }
            Op::Len => {
                let val = stack.pop().unwrap();
                let len = match &val {
                    Value::Set(s) => s.len() as i64,
                    Value::Seq(s) => s.len() as i64,
                    Value::Fn(f) => f.len() as i64,
                    Value::IntMap(arr) => arr.len() as i64,
                    _ => {
                        return Err(EvalError::TypeMismatch {
                            expected: "Set, Seq, or Fn".to_string(),
                            actual: val.type_name().to_string(),
                        })
                    }
                };
                stack.push(Value::Int(len));
            }
            Op::Contains => {
                let right_val = stack.pop().unwrap();
                let elem = stack.pop().unwrap();
                let result = match &right_val {
                    Value::Set(s) => Value::set_contains(s, &elem),
                    Value::Fn(f) => Value::fn_get(f, &elem).is_some(),
                    _ => return Err(type_mismatch("Set or Dict", &right_val)),
                };
                stack.push(Value::Bool(result));
            }
            Op::NotContains => {
                let right_val = stack.pop().unwrap();
                let elem = stack.pop().unwrap();
                let result = match &right_val {
                    Value::Set(s) => !Value::set_contains(s, &elem),
                    Value::Fn(f) => Value::fn_get(f, &elem).is_none(),
                    _ => return Err(type_mismatch("Set or Dict", &right_val)),
                };
                stack.push(Value::Bool(result));
            }

            // Local variable management
            Op::PushLocal => {
                let val = stack.pop().unwrap();
                locals.push(val);
            }
            Op::PopLocal => {
                locals.pop();
            }

            // === Range quantifiers ===
            Op::ForallRangeInit(end_pc) => {
                let hi = pop_int(&mut stack)?;
                let lo = pop_int(&mut stack)?;
                if lo > hi {
                    stack.push(Value::Bool(true));
                    pc = *end_pc as usize;
                    continue;
                }
                loops.push(LoopState {
                    hi,
                    counter: 0,
                    fn_buf: Vec::new(),
                });
                locals.push(Value::Int(lo));
            }
            Op::ForallRangeStep { body_pc, end_pc } => {
                let body_result = pop_bool(&mut stack)?;
                if !body_result {
                    locals.pop();
                    loops.pop();
                    stack.push(Value::Bool(false));
                    pc = *end_pc as usize;
                    continue;
                }
                let current = get_local_int(&locals)?;
                let hi = loops.last().unwrap().hi;
                if current >= hi {
                    locals.pop();
                    loops.pop();
                    stack.push(Value::Bool(true));
                    pc = *end_pc as usize;
                    continue;
                }
                *locals.last_mut().unwrap() = Value::Int(current + 1);
                pc = *body_pc as usize;
                continue;
            }

            Op::ExistsRangeInit(end_pc) => {
                let hi = pop_int(&mut stack)?;
                let lo = pop_int(&mut stack)?;
                if lo > hi {
                    stack.push(Value::Bool(false));
                    pc = *end_pc as usize;
                    continue;
                }
                loops.push(LoopState {
                    hi,
                    counter: 0,
                    fn_buf: Vec::new(),
                });
                locals.push(Value::Int(lo));
            }
            Op::ExistsRangeStep { body_pc, end_pc } => {
                let body_result = pop_bool(&mut stack)?;
                if body_result {
                    locals.pop();
                    loops.pop();
                    stack.push(Value::Bool(true));
                    pc = *end_pc as usize;
                    continue;
                }
                let current = get_local_int(&locals)?;
                let hi = loops.last().unwrap().hi;
                if current >= hi {
                    locals.pop();
                    loops.pop();
                    stack.push(Value::Bool(false));
                    pc = *end_pc as usize;
                    continue;
                }
                *locals.last_mut().unwrap() = Value::Int(current + 1);
                pc = *body_pc as usize;
                continue;
            }

            // === Count filtered ===
            Op::CountRangeInit(end_pc) => {
                let hi = pop_int(&mut stack)?;
                let lo = pop_int(&mut stack)?;
                if lo > hi {
                    stack.push(Value::Int(0));
                    pc = *end_pc as usize;
                    continue;
                }
                loops.push(LoopState {
                    hi,
                    counter: 0,
                    fn_buf: Vec::new(),
                });
                locals.push(Value::Int(lo));
            }
            Op::CountRangeStep { body_pc, end_pc } => {
                let pred = pop_bool(&mut stack)?;
                let loop_state = loops.last_mut().unwrap();
                if pred {
                    loop_state.counter += 1;
                }
                let current = get_local_int(&locals)?;
                if current >= loop_state.hi {
                    let count = loop_state.counter;
                    locals.pop();
                    loops.pop();
                    stack.push(Value::Int(count));
                    pc = *end_pc as usize;
                    continue;
                }
                *locals.last_mut().unwrap() = Value::Int(current + 1);
                pc = *body_pc as usize;
                continue;
            }

            // === FnLit range ===
            Op::FnLitRangeInit(end_pc) => {
                let hi = pop_int(&mut stack)?;
                let lo = pop_int(&mut stack)?;
                if lo > hi {
                    stack.push(Value::Fn(Arc::new(Vec::new())));
                    pc = *end_pc as usize;
                    continue;
                }
                let cap = (hi - lo + 1).max(0) as usize;
                loops.push(LoopState {
                    hi,
                    counter: 0,
                    fn_buf: Vec::with_capacity(cap),
                });
                locals.push(Value::Int(lo));
            }
            Op::FnLitRangeStep { body_pc, end_pc } => {
                let body_val = stack.pop().unwrap();
                let current = get_local_int(&locals)?;
                let loop_state = loops.last_mut().unwrap();
                loop_state.fn_buf.push((Value::Int(current), body_val));
                if current >= loop_state.hi {
                    let fn_buf = std::mem::take(&mut loop_state.fn_buf);
                    locals.pop();
                    loops.pop();
                    // Produce IntMap if keys start at 0 and all values are Int
                    let lo_zero = fn_buf.first().is_none_or(|(k, _)| k == &Value::Int(0));
                    if lo_zero && fn_buf.iter().all(|(_, v)| matches!(v, Value::Int(_))) {
                        let arr: Vec<i64> = fn_buf
                            .iter()
                            .map(|(_, v)| {
                                if let Value::Int(n) = v {
                                    *n
                                } else {
                                    unreachable!()
                                }
                            })
                            .collect();
                        stack.push(Value::IntMap(Arc::new(arr)));
                    } else {
                        stack.push(Value::Fn(Arc::new(fn_buf)));
                    }
                    pc = *end_pc as usize;
                    continue;
                }
                *locals.last_mut().unwrap() = Value::Int(current + 1);
                pc = *body_pc as usize;
                continue;
            }

            // === Fallback to tree-walk ===
            Op::Fallback(idx) => {
                let expr = &bytecode.fallbacks[*idx as usize];
                let mut ctx = EvalContext::new(vars, next_vars, consts, params);
                ctx.locals = locals.clone();
                let result = eval(expr, &mut ctx)?;
                stack.push(result);
            }
            Op::FallbackBool(idx) => {
                let expr = &bytecode.fallbacks[*idx as usize];
                let mut ctx = EvalContext::new(vars, next_vars, consts, params);
                ctx.locals = locals.clone();
                let result = eval_bool(expr, &mut ctx)?;
                stack.push(Value::Bool(result));
            }
            Op::FallbackInt(idx) => {
                let expr = &bytecode.fallbacks[*idx as usize];
                let mut ctx = EvalContext::new(vars, next_vars, consts, params);
                ctx.locals = locals.clone();
                let result = eval_int(expr, &mut ctx)?;
                stack.push(Value::Int(result));
            }

            Op::Halt => {
                return stack.pop().ok_or(EvalError::Internal(
                    "bytecode VM: empty stack at halt".to_string(),
                ));
            }
        }
        pc += 1;
    }
}

// ============================================================================
// Helper functions
// ============================================================================

#[inline(always)]
fn pop_int(stack: &mut Vec<Value>) -> EvalResult<i64> {
    match stack.pop().unwrap() {
        Value::Int(n) => Ok(n),
        other => Err(EvalError::TypeMismatch {
            expected: "Int".to_string(),
            actual: other.type_name().to_string(),
        }),
    }
}

#[inline(always)]
fn pop_bool(stack: &mut Vec<Value>) -> EvalResult<bool> {
    match stack.pop().unwrap() {
        Value::Bool(b) => Ok(b),
        other => Err(EvalError::TypeMismatch {
            expected: "Bool".to_string(),
            actual: other.type_name().to_string(),
        }),
    }
}

#[inline(always)]
fn peek_bool(stack: &[Value]) -> EvalResult<bool> {
    match stack.last().unwrap() {
        Value::Bool(b) => Ok(*b),
        other => Err(EvalError::TypeMismatch {
            expected: "Bool".to_string(),
            actual: other.type_name().to_string(),
        }),
    }
}

#[inline(always)]
fn get_local_int(locals: &[Value]) -> EvalResult<i64> {
    match locals.last().unwrap() {
        Value::Int(n) => Ok(*n),
        other => Err(EvalError::TypeMismatch {
            expected: "Int".to_string(),
            actual: other.type_name().to_string(),
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_int_arithmetic() {
        // 2 + 3
        let expr = CompiledExpr::Binary {
            op: BinOp::Add,
            left: Box::new(CompiledExpr::Int(2)),
            right: Box::new(CompiledExpr::Int(3)),
        };
        let bc = compile_expr(&expr);
        let result = vm_eval(&bc, &[], &[], &[], &[]).unwrap();
        assert_eq!(result, Value::Int(5));
    }

    #[test]
    fn test_short_circuit_and() {
        // false and (1/0 == 0) -- should not divide by zero
        let expr = CompiledExpr::Binary {
            op: BinOp::And,
            left: Box::new(CompiledExpr::Bool(false)),
            right: Box::new(CompiledExpr::Binary {
                op: BinOp::Eq,
                left: Box::new(CompiledExpr::Binary {
                    op: BinOp::Div,
                    left: Box::new(CompiledExpr::Int(1)),
                    right: Box::new(CompiledExpr::Int(0)),
                }),
                right: Box::new(CompiledExpr::Int(0)),
            }),
        };
        let bc = compile_expr(&expr);
        let result = vm_eval_bool(&bc, &[], &[], &[], &[]).unwrap();
        assert!(!result);
    }

    #[test]
    fn test_dict_get() {
        // var[0][1] where var = {0: {0: 10, 1: 20}, 1: {0: 30, 1: 40}}
        let expr = CompiledExpr::Index {
            base: Box::new(CompiledExpr::Index {
                base: Box::new(CompiledExpr::Var(0)),
                index: Box::new(CompiledExpr::Int(0)),
            }),
            index: Box::new(CompiledExpr::Int(1)),
        };
        let inner0 = Value::Fn(Arc::new(vec![
            (Value::Int(0), Value::Int(10)),
            (Value::Int(1), Value::Int(20)),
        ]));
        let inner1 = Value::Fn(Arc::new(vec![
            (Value::Int(0), Value::Int(30)),
            (Value::Int(1), Value::Int(40)),
        ]));
        let dict = Value::Fn(Arc::new(vec![
            (Value::Int(0), inner0),
            (Value::Int(1), inner1),
        ]));
        let bc = compile_expr(&expr);
        let result = vm_eval(&bc, &[dict], &[], &[], &[]).unwrap();
        assert_eq!(result, Value::Int(20));
    }

    #[test]
    fn test_forall_range() {
        // forall i in 0..2: i >= 0
        let expr = CompiledExpr::Forall {
            domain: Box::new(CompiledExpr::Range {
                lo: Box::new(CompiledExpr::Int(0)),
                hi: Box::new(CompiledExpr::Int(2)),
            }),
            body: Box::new(CompiledExpr::Binary {
                op: BinOp::Ge,
                left: Box::new(CompiledExpr::Local(0)),
                right: Box::new(CompiledExpr::Int(0)),
            }),
        };
        let bc = compile_expr(&expr);
        let result = vm_eval_bool(&bc, &[], &[], &[], &[]).unwrap();
        assert!(result);
    }

    #[test]
    fn test_exists_range() {
        // exists i in 0..5: i == 3
        let expr = CompiledExpr::Exists {
            domain: Box::new(CompiledExpr::Range {
                lo: Box::new(CompiledExpr::Int(0)),
                hi: Box::new(CompiledExpr::Int(5)),
            }),
            body: Box::new(CompiledExpr::Binary {
                op: BinOp::Eq,
                left: Box::new(CompiledExpr::Local(0)),
                right: Box::new(CompiledExpr::Int(3)),
            }),
        };
        let bc = compile_expr(&expr);
        let result = vm_eval_bool(&bc, &[], &[], &[], &[]).unwrap();
        assert!(result);
    }

    #[test]
    fn test_count_filtered() {
        // len({x in 0..4 if x > 1}) == 3
        let expr = CompiledExpr::Binary {
            op: BinOp::Eq,
            left: Box::new(CompiledExpr::Len(Box::new(
                CompiledExpr::SetComprehension {
                    element: Box::new(CompiledExpr::Local(0)),
                    domain: Box::new(CompiledExpr::Range {
                        lo: Box::new(CompiledExpr::Int(0)),
                        hi: Box::new(CompiledExpr::Int(4)),
                    }),
                    filter: Some(Box::new(CompiledExpr::Binary {
                        op: BinOp::Gt,
                        left: Box::new(CompiledExpr::Local(0)),
                        right: Box::new(CompiledExpr::Int(1)),
                    })),
                },
            ))),
            right: Box::new(CompiledExpr::Int(3)),
        };
        let bc = compile_expr(&expr);
        let result = vm_eval_bool(&bc, &[], &[], &[], &[]).unwrap();
        assert!(result);
    }

    #[test]
    fn test_implies() {
        // false implies anything == true
        let expr = CompiledExpr::Binary {
            op: BinOp::Implies,
            left: Box::new(CompiledExpr::Bool(false)),
            right: Box::new(CompiledExpr::Bool(false)),
        };
        let bc = compile_expr(&expr);
        assert!(vm_eval_bool(&bc, &[], &[], &[], &[]).unwrap());

        // true implies false == false
        let expr2 = CompiledExpr::Binary {
            op: BinOp::Implies,
            left: Box::new(CompiledExpr::Bool(true)),
            right: Box::new(CompiledExpr::Bool(false)),
        };
        let bc2 = compile_expr(&expr2);
        assert!(!vm_eval_bool(&bc2, &[], &[], &[], &[]).unwrap());
    }

    #[test]
    fn test_nested_dict_update_2() {
        // var0 | {param0: (var0[param0] | {param1: 99})}
        // where var0 = {0: {0: 10, 1: 20}, 1: {0: 30, 1: 40}}, param0 = 0, param1 = 1
        let expr = CompiledExpr::FnUpdate {
            base: Box::new(CompiledExpr::Var(0)),
            key: Box::new(CompiledExpr::Param(0)),
            value: Box::new(CompiledExpr::FnUpdate {
                base: Box::new(CompiledExpr::Index {
                    base: Box::new(CompiledExpr::Var(0)),
                    index: Box::new(CompiledExpr::Param(0)),
                }),
                key: Box::new(CompiledExpr::Param(1)),
                value: Box::new(CompiledExpr::Int(99)),
            }),
        };
        let inner0 = Value::Fn(Arc::new(vec![
            (Value::Int(0), Value::Int(10)),
            (Value::Int(1), Value::Int(20)),
        ]));
        let inner1 = Value::Fn(Arc::new(vec![
            (Value::Int(0), Value::Int(30)),
            (Value::Int(1), Value::Int(40)),
        ]));
        let dict = Value::Fn(Arc::new(vec![
            (Value::Int(0), inner0),
            (Value::Int(1), inner1),
        ]));
        let bc = compile_expr(&expr);
        // Should use NestedDictUpdate2 opcode
        assert!(
            bc.ops.iter().any(|op| matches!(op, Op::NestedDictUpdate2)),
            "expected NestedDictUpdate2 opcode"
        );
        let result = vm_eval(&bc, &[dict], &[], &[], &[Value::Int(0), Value::Int(1)]).unwrap();
        // dict[0][1] should be 99 now
        let outer = result.as_fn().unwrap();
        let inner = Value::fn_get(outer, &Value::Int(0))
            .unwrap()
            .as_fn()
            .unwrap();
        assert_eq!(Value::fn_get(inner, &Value::Int(1)), Some(&Value::Int(99)));
        // dict[0][0] should be unchanged
        assert_eq!(Value::fn_get(inner, &Value::Int(0)), Some(&Value::Int(10)));
        // dict[1] should be unchanged
        let inner1 = Value::fn_get(outer, &Value::Int(1))
            .unwrap()
            .as_fn()
            .unwrap();
        assert_eq!(Value::fn_get(inner1, &Value::Int(0)), Some(&Value::Int(30)));
    }

    #[test]
    fn test_nested_dict_update_3() {
        // var0 | {p0: (var0[p0] | {p1: (var0[p0][p1] | {p2: true})})}
        // where var0 = {0: {0: {0: false, 1: false}}}, p0=0, p1=0, p2=1
        let expr = CompiledExpr::FnUpdate {
            base: Box::new(CompiledExpr::Var(0)),
            key: Box::new(CompiledExpr::Param(0)),
            value: Box::new(CompiledExpr::FnUpdate {
                base: Box::new(CompiledExpr::Index {
                    base: Box::new(CompiledExpr::Var(0)),
                    index: Box::new(CompiledExpr::Param(0)),
                }),
                key: Box::new(CompiledExpr::Param(1)),
                value: Box::new(CompiledExpr::FnUpdate {
                    base: Box::new(CompiledExpr::Index {
                        base: Box::new(CompiledExpr::Index {
                            base: Box::new(CompiledExpr::Var(0)),
                            index: Box::new(CompiledExpr::Param(0)),
                        }),
                        index: Box::new(CompiledExpr::Param(1)),
                    }),
                    key: Box::new(CompiledExpr::Param(2)),
                    value: Box::new(CompiledExpr::Bool(true)),
                }),
            }),
        };
        let innermost = Value::Fn(Arc::new(vec![
            (Value::Int(0), Value::Bool(false)),
            (Value::Int(1), Value::Bool(false)),
        ]));
        let middle = Value::Fn(Arc::new(vec![(Value::Int(0), innermost)]));
        let dict = Value::Fn(Arc::new(vec![(Value::Int(0), middle)]));
        let bc = compile_expr(&expr);
        assert!(
            bc.ops.iter().any(|op| matches!(op, Op::NestedDictUpdate3)),
            "expected NestedDictUpdate3 opcode"
        );
        let result = vm_eval(
            &bc,
            &[dict],
            &[],
            &[],
            &[Value::Int(0), Value::Int(0), Value::Int(1)],
        )
        .unwrap();
        // dict[0][0][1] should be true
        let outer = result.as_fn().unwrap();
        let mid = Value::fn_get(outer, &Value::Int(0))
            .unwrap()
            .as_fn()
            .unwrap();
        let inner = Value::fn_get(mid, &Value::Int(0)).unwrap().as_fn().unwrap();
        assert_eq!(
            Value::fn_get(inner, &Value::Int(1)),
            Some(&Value::Bool(true))
        );
        // dict[0][0][0] should still be false
        assert_eq!(
            Value::fn_get(inner, &Value::Int(0)),
            Some(&Value::Bool(false))
        );
    }
}

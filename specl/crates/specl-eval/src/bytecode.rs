//! Bytecode VM for fast expression evaluation.
//!
//! Compiles CompiledExpr trees to flat bytecode and executes them in a tight
//! loop, eliminating recursive dispatch overhead of the tree-walk interpreter.

use crate::eval::{
    eval, eval_bool, eval_int, expect_int, sorted_vec_diff, sorted_vec_union, type_mismatch,
};
use crate::value::{IntMap2Data, Value, VK};
use crate::{EvalContext, EvalError, EvalResult};
use specl_ir::{BinOp, CompiledExpr, UnaryOp};
use std::sync::Arc;

/// Bytecode operation.
#[derive(Debug, Clone)]
pub enum Op {
    // === Literals ===
    Int(i64),
    Bool(bool),
    /// Push a pre-created constant Value (e.g., string literals).
    PushValue(Value),

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
    /// Batch dict update: pop N (value, key) pairs then pop dict, apply all in one clone.
    /// Stack: [dict, k1, v1, k2, v2, ..., kN, vN] (dict deepest).
    DictUpdateN(u16),
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

    // === Set comprehension over range ===
    /// Pop hi, pop lo. If lo > hi: push empty set, jump to end_pc.
    /// Else: push Int(lo) onto locals, init set buffer, continue to body.
    SetCompRangeInit(u32),
    /// Pop element value, add to set buffer. Increment local.
    /// If > hi: pop local, push completed Set, jump to end_pc.
    /// Else: jump to body_pc.
    SetCompRangeStep {
        body_pc: u32,
        end_pc: u32,
    },
    /// Advance loop without collecting (filter was false). Increment local.
    /// If > hi: pop local, push completed Set, jump to end_pc.
    /// Else: jump to body_pc.
    SetCompRangeAdvance {
        body_pc: u32,
        end_pc: u32,
    },

    // === Quantifiers/comprehensions over set domain ===
    /// Pop set value. If empty: push true, jump to end_pc.
    /// Else: store set, push first element to locals, continue.
    ForallSetInit(u32),
    /// Pop body result (bool). If false: cleanup, push false, jump to end_pc.
    /// Else: advance index. If done: cleanup, push true, jump to end_pc.
    /// Else: update local to next element, jump to body_pc.
    ForallSetStep {
        body_pc: u32,
        end_pc: u32,
    },
    /// Pop set value. If empty: push false, jump to end_pc.
    /// Else: store set, push first element to locals, continue.
    ExistsSetInit(u32),
    /// Pop body result (bool). If true: cleanup, push true, jump to end_pc.
    /// Else: advance index. If done: cleanup, push false, jump to end_pc.
    /// Else: update local to next element, jump to body_pc.
    ExistsSetStep {
        body_pc: u32,
        end_pc: u32,
    },
    /// Pop set value. If empty: push empty set, jump to end_pc.
    /// Else: store set, push first element to locals, init set buffer, continue.
    SetCompSetInit(u32),
    /// Pop element, add to buffer. Advance index. If done: push completed set, jump to end_pc.
    /// Else: update local to next element, jump to body_pc.
    SetCompSetStep {
        body_pc: u32,
        end_pc: u32,
    },
    /// Advance set-comp without collecting (filter was false).
    SetCompSetAdvance {
        body_pc: u32,
        end_pc: u32,
    },

    // === Quantifiers over powerset domain ===
    /// Pop base set. Iterate 2^n bitmasks. Push first subset ({}) to locals.
    ForallPowersetInit(u32),
    /// Pop body result (bool). If false: cleanup, push false, jump to end_pc.
    /// Advance mask. If done: cleanup, push true, jump to end_pc.
    /// Create next subset, jump to body_pc.
    ForallPowersetStep {
        body_pc: u32,
        end_pc: u32,
    },
    /// Pop base set. Iterate 2^n bitmasks. Push first subset ({}) to locals.
    ExistsPowersetInit(u32),
    /// Pop body result (bool). If true: cleanup, push true, jump to end_pc.
    /// Advance mask. If done: cleanup, push false, jump to end_pc.
    /// Create next subset, jump to body_pc.
    ExistsPowersetStep {
        body_pc: u32,
        end_pc: u32,
    },

    // === Set/Seq construction ===
    /// Pop N values → push Set (sorted, deduped).
    SetLit(u16),
    /// Pop N values → push Seq.
    SeqLit(u16),
    /// Pop two sets → push set union.
    SetUnion,
    /// Pop two sets → push set difference.
    SetDiff,
    /// Pop two seqs → push concatenated seq.
    SeqConcat,
    /// Pop hi, pop lo, pop seq → push seq[lo..hi].
    SeqSlice,
    /// Pop seq → push first element.
    SeqHead,
    /// Pop seq → push tail (all but first).
    SeqTail,
    /// Pop hi, pop lo → push Set of lo..=hi integers.
    MakeRange,

    // === Superinstructions (fused sequences) ===
    /// Fused Var(i) + DictGet: var is the key, base dict is on stack.
    VarDictGet(u16),
    /// Fused Var(i) + Int(k) + IntEq: compare var to constant.
    VarIntEq(u16, i64),
    /// Fused Var(i) + Param(j) + DictGet: dict[param] from var.
    VarParamDictGet(u16, u16),
    /// Fused VarParamDictGet(a, b) + Param(c) + DictGet: two-level dict lookup vars[a][params[b]][params[c]].
    VarParam2DictGet(u16, u16, u16),
    /// Fused VarParamDictGet(a, b) + Int(k) + IntEq: dict lookup + int compare vars[a][params[b]] == k.
    VarParamDictGetIntEq(u16, u16, i64),
    /// Fused VarParamDictGet(a, b) + Len: len(vars[a][params[b]]) without cloning the collection.
    VarParamDictGetLen(u16, u16),
    /// Fused Param(p) + Int(k) + DictGet: params[p][k] — direct seq/dict index on parameter.
    /// Common in message-parameterized actions: msg[0], msg[2], msg[3], etc.
    ParamIntDictGet(u16, i64),
    /// Fused Var(v) + Param(p) + Int(k) + DictGet + DictGet: vars[v][params[p][k]].
    /// Common in protocol specs: currentTerm[msg[2]], state[msg[2]], logTerm[msg[2]], etc.
    VarParamIntDictGet2(u16, u16, i64),
    /// Fused VarParamDictGet(a, b) + Bool(v) + Eq: dict lookup + bool compare.
    /// vars[a][params[b]] == v without cloning. Common in guards: has_req[p] == true.
    VarParamDictGetBoolEq(u16, u16, bool),
    /// Fused VarParam2DictGet(a, b, c) + Bool(v) + Eq: two-level dict lookup + bool compare.
    /// vars[a][params[b]][params[c]] == v without cloning. Common: reply[p][q] == false.
    VarParam2DictGetBoolEq(u16, u16, u16, bool),

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

/// Loop state for range-based quantifiers and set iteration.
struct LoopState {
    hi: i64,
    /// Accumulator for CountRange / index for set iteration.
    counter: i64,
    /// Accumulator for FnLitRange.
    fn_buf: Vec<(Value, Value)>,
    /// Accumulator for SetCompRange / SetCompSet.
    set_buf: Vec<Value>,
    /// Domain value for set/seq iteration (Forall/Exists/SetComp over sets).
    domain_val: Option<Value>,
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
            | Op::FnLitRangeInit(t)
            | Op::SetCompRangeInit(t)
            | Op::ForallSetInit(t)
            | Op::ExistsSetInit(t)
            | Op::SetCompSetInit(t)
            | Op::ForallPowersetInit(t)
            | Op::ExistsPowersetInit(t) => *t = target,
            Op::ForallRangeStep { end_pc, .. }
            | Op::ExistsRangeStep { end_pc, .. }
            | Op::CountRangeStep { end_pc, .. }
            | Op::FnLitRangeStep { end_pc, .. }
            | Op::SetCompRangeStep { end_pc, .. }
            | Op::SetCompRangeAdvance { end_pc, .. }
            | Op::ForallSetStep { end_pc, .. }
            | Op::ExistsSetStep { end_pc, .. }
            | Op::SetCompSetStep { end_pc, .. }
            | Op::SetCompSetAdvance { end_pc, .. }
            | Op::ForallPowersetStep { end_pc, .. }
            | Op::ExistsPowersetStep { end_pc, .. } => *end_pc = target,
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
            CompiledExpr::String(s) => {
                self.emit(Op::PushValue(Value::string(s.clone())));
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

            CompiledExpr::SetLit(elems) => {
                for e in elems {
                    self.compile(e);
                }
                self.emit(Op::SetLit(elems.len() as u16));
            }

            CompiledExpr::SeqLit(elems) => {
                for e in elems {
                    self.compile(e);
                }
                self.emit(Op::SeqLit(elems.len() as u16));
            }

            CompiledExpr::Slice { base, lo, hi } => {
                self.compile(base);
                self.compile(lo);
                self.compile(hi);
                self.emit(Op::SeqSlice);
            }

            CompiledExpr::SeqHead(seq) => {
                self.compile(seq);
                self.emit(Op::SeqHead);
            }
            CompiledExpr::SeqTail(seq) => {
                self.compile(seq);
                self.emit(Op::SeqTail);
            }
            CompiledExpr::Range { lo, hi } => {
                self.compile(lo);
                self.compile(hi);
                self.emit(Op::MakeRange);
            }

            CompiledExpr::SetComprehension {
                element,
                domain,
                filter,
            } => {
                self.compile_set_comp(element, domain, filter.as_deref());
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
                        // Batch update: clone dict once, apply all updates
                        self.compile(left);
                        for (key, value) in entries.iter() {
                            self.compile(key);
                            self.compile(value);
                        }
                        self.emit(Op::DictUpdateN(entries.len() as u16));
                    }
                } else {
                    // General set union
                    self.compile(left);
                    self.compile(right);
                    self.emit(Op::SetUnion);
                }
            }
            // Set difference
            BinOp::Diff => {
                self.compile(left);
                self.compile(right);
                self.emit(Op::SetDiff);
            }
            // Sequence concatenation
            BinOp::Concat => {
                self.compile(left);
                self.compile(right);
                self.emit(Op::SeqConcat);
            }
            // Remaining set operations → fallback
            BinOp::Intersect | BinOp::SubsetOf => {
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
        } else if let CompiledExpr::Powerset(inner) = domain {
            // Powerset domain — iterate bitmasks
            self.compile(inner);
            let init = self.emit(Op::ForallPowersetInit(0));
            let body_pc = self.current_pc();
            self.compile(body);
            let step = self.emit(Op::ForallPowersetStep {
                body_pc: body_pc as u32,
                end_pc: 0,
            });
            let end_pc = self.current_pc();
            self.patch_jump(init, end_pc as u32);
            self.patch_jump(step, end_pc as u32);
        } else {
            // Set-valued domain (Var, Keys, etc.) — iterate elements
            self.compile(domain);
            let init = self.emit(Op::ForallSetInit(0));
            let body_pc = self.current_pc();
            self.compile(body);
            let step = self.emit(Op::ForallSetStep {
                body_pc: body_pc as u32,
                end_pc: 0,
            });
            let end_pc = self.current_pc();
            self.patch_jump(init, end_pc as u32);
            self.patch_jump(step, end_pc as u32);
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
        } else if let CompiledExpr::Powerset(inner) = domain {
            // Powerset domain — iterate bitmasks
            self.compile(inner);
            let init = self.emit(Op::ExistsPowersetInit(0));
            let body_pc = self.current_pc();
            self.compile(body);
            let step = self.emit(Op::ExistsPowersetStep {
                body_pc: body_pc as u32,
                end_pc: 0,
            });
            let end_pc = self.current_pc();
            self.patch_jump(init, end_pc as u32);
            self.patch_jump(step, end_pc as u32);
        } else {
            // Set-valued domain — iterate elements
            self.compile(domain);
            let init = self.emit(Op::ExistsSetInit(0));
            let body_pc = self.current_pc();
            self.compile(body);
            let step = self.emit(Op::ExistsSetStep {
                body_pc: body_pc as u32,
                end_pc: 0,
            });
            let end_pc = self.current_pc();
            self.patch_jump(init, end_pc as u32);
            self.patch_jump(step, end_pc as u32);
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

    fn compile_set_comp(
        &mut self,
        element: &CompiledExpr,
        domain: &CompiledExpr,
        filter: Option<&CompiledExpr>,
    ) {
        if let CompiledExpr::Range { lo, hi } = domain {
            self.compile(lo);
            self.compile(hi);
            let init = self.emit(Op::SetCompRangeInit(0));
            let body_pc = self.current_pc();

            if let Some(filter) = filter {
                // With filter: evaluate filter, skip element if false
                self.compile(filter);
                let jump_skip = self.emit(Op::JumpIfFalse(0));
                self.emit(Op::Pop); // pop the true
                self.compile(element);
                let step = self.emit(Op::SetCompRangeStep {
                    body_pc: body_pc as u32,
                    end_pc: 0,
                });
                let skip_pc = self.current_pc();
                self.patch_jump(jump_skip, skip_pc as u32);
                self.emit(Op::Pop); // pop the false
                let advance = self.emit(Op::SetCompRangeAdvance {
                    body_pc: body_pc as u32,
                    end_pc: 0,
                });
                let end_pc = self.current_pc();
                self.patch_jump(init, end_pc as u32);
                self.patch_jump(step, end_pc as u32);
                self.patch_jump(advance, end_pc as u32);
            } else {
                // No filter: just evaluate element for each value
                self.compile(element);
                let step = self.emit(Op::SetCompRangeStep {
                    body_pc: body_pc as u32,
                    end_pc: 0,
                });
                let end_pc = self.current_pc();
                self.patch_jump(init, end_pc as u32);
                self.patch_jump(step, end_pc as u32);
            }
        } else if !matches!(domain, CompiledExpr::Powerset(_)) {
            // Set-valued domain — iterate elements
            self.compile(domain);
            let init = self.emit(Op::SetCompSetInit(0));
            let body_pc = self.current_pc();

            if let Some(filter) = filter {
                self.compile(filter);
                let jump_skip = self.emit(Op::JumpIfFalse(0));
                self.emit(Op::Pop);
                self.compile(element);
                let step = self.emit(Op::SetCompSetStep {
                    body_pc: body_pc as u32,
                    end_pc: 0,
                });
                let skip_pc = self.current_pc();
                self.patch_jump(jump_skip, skip_pc as u32);
                self.emit(Op::Pop);
                let advance = self.emit(Op::SetCompSetAdvance {
                    body_pc: body_pc as u32,
                    end_pc: 0,
                });
                let end_pc = self.current_pc();
                self.patch_jump(init, end_pc as u32);
                self.patch_jump(step, end_pc as u32);
                self.patch_jump(advance, end_pc as u32);
            } else {
                self.compile(element);
                let step = self.emit(Op::SetCompSetStep {
                    body_pc: body_pc as u32,
                    end_pc: 0,
                });
                let end_pc = self.current_pc();
                self.patch_jump(init, end_pc as u32);
                self.patch_jump(step, end_pc as u32);
            }
        } else {
            // Powerset domain: fallback to tree-walk
            let expr = CompiledExpr::SetComprehension {
                element: Box::new(element.clone()),
                domain: Box::new(domain.clone()),
                filter: filter.map(|f| Box::new(f.clone())),
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
        if let Some((
            CompiledExpr::Index {
                base: idx_base,
                index: idx_key,
            },
            inner_key,
            inner_value,
        )) = extract_dict_update(value)
        {
            if expr_structural_eq(base, idx_base) && expr_structural_eq(key, idx_key) {
                // Check for 3-level: inner_value is a dict update of base[key][inner_key]
                if let Some((
                    CompiledExpr::Index {
                        base: idx2_base,
                        index: idx2_key,
                    },
                    inner2_key,
                    inner2_value,
                )) = extract_dict_update(inner_value)
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

                // 2-level match. Compile: value2, k2, k1, base
                self.compile(inner_value);
                self.compile(inner_key);
                self.compile(key);
                self.compile(base);
                self.emit(Op::NestedDictUpdate2);
                return true;
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

/// Compile a CompiledExpr to bytecode with peephole optimization.
pub fn compile_expr(expr: &CompiledExpr) -> Bytecode {
    let mut compiler = Compiler::new();
    compiler.compile(expr);
    let mut bc = compiler.finish();
    peephole_optimize(&mut bc.ops);
    bc
}

/// Peephole optimization: fuse common instruction sequences into superinstructions.
/// Only fuses sequences that don't contain jump targets (safe for straight-line code).
fn peephole_optimize(ops: &mut Vec<Op>) {
    // Collect all jump targets so we don't fuse across them
    let mut jump_targets = vec![false; ops.len() + 1];
    for op in ops.iter() {
        match op {
            Op::JumpIfFalse(t) | Op::JumpIfTrue(t) | Op::Jump(t) => {
                let target = *t as usize;
                if target < jump_targets.len() {
                    jump_targets[target] = true;
                }
            }
            Op::ForallRangeInit(t)
            | Op::ExistsRangeInit(t)
            | Op::CountRangeInit(t)
            | Op::FnLitRangeInit(t)
            | Op::SetCompRangeInit(t)
            | Op::ForallSetInit(t)
            | Op::ExistsSetInit(t)
            | Op::SetCompSetInit(t)
            | Op::ForallPowersetInit(t)
            | Op::ExistsPowersetInit(t) => {
                let target = *t as usize;
                if target < jump_targets.len() {
                    jump_targets[target] = true;
                }
            }
            Op::ForallRangeStep { body_pc, end_pc }
            | Op::ExistsRangeStep { body_pc, end_pc }
            | Op::CountRangeStep { body_pc, end_pc }
            | Op::FnLitRangeStep { body_pc, end_pc }
            | Op::SetCompRangeStep { body_pc, end_pc }
            | Op::SetCompRangeAdvance { body_pc, end_pc }
            | Op::ForallSetStep { body_pc, end_pc }
            | Op::ExistsSetStep { body_pc, end_pc }
            | Op::SetCompSetStep { body_pc, end_pc }
            | Op::SetCompSetAdvance { body_pc, end_pc }
            | Op::ForallPowersetStep { body_pc, end_pc }
            | Op::ExistsPowersetStep { body_pc, end_pc } => {
                let b = *body_pc as usize;
                let e = *end_pc as usize;
                if b < jump_targets.len() {
                    jump_targets[b] = true;
                }
                if e < jump_targets.len() {
                    jump_targets[e] = true;
                }
            }
            _ => {}
        }
    }

    let mut i = 0;
    while i + 1 < ops.len() {
        // Don't fuse if the second instruction is a jump target
        if jump_targets.get(i + 1).copied().unwrap_or(false) {
            i += 1;
            continue;
        }

        // Pattern: Var(i), DictGet → VarDictGet(i)
        if let (Op::Var(var_idx), Op::DictGet) = (&ops[i], &ops[i + 1]) {
            let var_idx = *var_idx;
            ops[i] = Op::VarDictGet(var_idx);
            ops.remove(i + 1);
            // Patch jump targets after removal
            patch_jumps_after_remove(ops, i + 1, &mut jump_targets);
            continue;
        }

        // Pattern: Var(i), Param(j), DictGet → VarParamDictGet(i, j) (3 → 1)
        if i + 2 < ops.len() && !jump_targets.get(i + 2).copied().unwrap_or(false) {
            if let (Op::Var(var_idx), Op::Param(param_idx), Op::DictGet) =
                (&ops[i], &ops[i + 1], &ops[i + 2])
            {
                let var_idx = *var_idx;
                let param_idx = *param_idx;
                ops[i] = Op::VarParamDictGet(var_idx, param_idx);
                ops.remove(i + 2);
                patch_jumps_after_remove(ops, i + 2, &mut jump_targets);
                ops.remove(i + 1);
                patch_jumps_after_remove(ops, i + 1, &mut jump_targets);
                continue;
            }
        }

        // Pattern: Var(i), Int(k), IntEq → VarIntEq(i, k) (3 → 1)
        if i + 2 < ops.len() && !jump_targets.get(i + 2).copied().unwrap_or(false) {
            if let (Op::Var(var_idx), Op::Int(k), Op::IntEq) = (&ops[i], &ops[i + 1], &ops[i + 2]) {
                let var_idx = *var_idx;
                let k = *k;
                ops[i] = Op::VarIntEq(var_idx, k);
                ops.remove(i + 2);
                patch_jumps_after_remove(ops, i + 2, &mut jump_targets);
                ops.remove(i + 1);
                patch_jumps_after_remove(ops, i + 1, &mut jump_targets);
                continue;
            }
        }

        // Pattern: VarParamDictGet(a, b), Param(c), DictGet → VarParam2DictGet(a, b, c)
        // Two-level dict lookup: vars[a][params[b]][params[c]] without intermediate Arc clone.
        if i + 2 < ops.len() && !jump_targets.get(i + 2).copied().unwrap_or(false) {
            if let (Op::VarParamDictGet(var_idx, param1_idx), Op::Param(param2_idx), Op::DictGet) =
                (&ops[i], &ops[i + 1], &ops[i + 2])
            {
                let var_idx = *var_idx;
                let param1_idx = *param1_idx;
                let param2_idx = *param2_idx;
                ops[i] = Op::VarParam2DictGet(var_idx, param1_idx, param2_idx);
                ops.remove(i + 2);
                patch_jumps_after_remove(ops, i + 2, &mut jump_targets);
                ops.remove(i + 1);
                patch_jumps_after_remove(ops, i + 1, &mut jump_targets);
                continue;
            }
        }

        // Pattern: VarParamDictGet(a, b), Int(k), IntEq → VarParamDictGetIntEq(a, b, k)
        // Dict lookup + comparison: vars[a][params[b]] == k without cloning the dict.
        if i + 2 < ops.len() && !jump_targets.get(i + 2).copied().unwrap_or(false) {
            if let (Op::VarParamDictGet(var_idx, param_idx), Op::Int(k), Op::IntEq) =
                (&ops[i], &ops[i + 1], &ops[i + 2])
            {
                let var_idx = *var_idx;
                let param_idx = *param_idx;
                let k = *k;
                ops[i] = Op::VarParamDictGetIntEq(var_idx, param_idx, k);
                ops.remove(i + 2);
                patch_jumps_after_remove(ops, i + 2, &mut jump_targets);
                ops.remove(i + 1);
                patch_jumps_after_remove(ops, i + 1, &mut jump_targets);
                continue;
            }
        }

        // Pattern: VarParamDictGet(a, b), Bool(v), Eq → VarParamDictGetBoolEq(a, b, v)
        // Dict lookup + bool compare: vars[a][params[b]] == v without cloning.
        if i + 2 < ops.len() && !jump_targets.get(i + 2).copied().unwrap_or(false) {
            if let (Op::VarParamDictGet(var_idx, param_idx), Op::Bool(v), Op::Eq) =
                (&ops[i], &ops[i + 1], &ops[i + 2])
            {
                let var_idx = *var_idx;
                let param_idx = *param_idx;
                let v = *v;
                ops[i] = Op::VarParamDictGetBoolEq(var_idx, param_idx, v);
                ops.remove(i + 2);
                patch_jumps_after_remove(ops, i + 2, &mut jump_targets);
                ops.remove(i + 1);
                patch_jumps_after_remove(ops, i + 1, &mut jump_targets);
                continue;
            }
        }

        // Pattern: VarParam2DictGet(a, b, c), Bool(v), Eq → VarParam2DictGetBoolEq(a, b, c, v)
        // Two-level dict lookup + bool compare: vars[a][params[b]][params[c]] == v without cloning.
        if i + 2 < ops.len() && !jump_targets.get(i + 2).copied().unwrap_or(false) {
            if let (Op::VarParam2DictGet(var_idx, param1_idx, param2_idx), Op::Bool(v), Op::Eq) =
                (&ops[i], &ops[i + 1], &ops[i + 2])
            {
                let var_idx = *var_idx;
                let param1_idx = *param1_idx;
                let param2_idx = *param2_idx;
                let v = *v;
                ops[i] = Op::VarParam2DictGetBoolEq(var_idx, param1_idx, param2_idx, v);
                ops.remove(i + 2);
                patch_jumps_after_remove(ops, i + 2, &mut jump_targets);
                ops.remove(i + 1);
                patch_jumps_after_remove(ops, i + 1, &mut jump_targets);
                continue;
            }
        }

        // Pattern: VarParamDictGet(a, b), Len → VarParamDictGetLen(a, b)
        // len(vars[a][params[b]]) without cloning the intermediate collection.
        if let (Op::VarParamDictGet(var_idx, param_idx), Op::Len) = (&ops[i], &ops[i + 1]) {
            let var_idx = *var_idx;
            let param_idx = *param_idx;
            ops[i] = Op::VarParamDictGetLen(var_idx, param_idx);
            ops.remove(i + 1);
            patch_jumps_after_remove(ops, i + 1, &mut jump_targets);
            continue;
        }

        // Pattern: Param(p), Int(k), DictGet → ParamIntDictGet(p, k) (3 → 1)
        // Direct seq/dict index on parameter: params[p][k]
        // Very common in message-parameterized actions: msg[0], msg[2], msg[3], etc.
        if i + 2 < ops.len() && !jump_targets.get(i + 2).copied().unwrap_or(false) {
            if let (Op::Param(param_idx), Op::Int(k), Op::DictGet) =
                (&ops[i], &ops[i + 1], &ops[i + 2])
            {
                let param_idx = *param_idx;
                let k = *k;
                ops[i] = Op::ParamIntDictGet(param_idx, k);
                ops.remove(i + 2);
                patch_jumps_after_remove(ops, i + 2, &mut jump_targets);
                ops.remove(i + 1);
                patch_jumps_after_remove(ops, i + 1, &mut jump_targets);
                continue;
            }
        }

        // Pattern: Var(v), ParamIntDictGet(p, k), DictGet → VarParamIntDictGet2(v, p, k) (3 → 1)
        // Two-level lookup: vars[v][params[p][k]] — e.g. currentTerm[msg[2]], state[msg[2]]
        if i + 2 < ops.len() && !jump_targets.get(i + 2).copied().unwrap_or(false) {
            if let (Op::Var(var_idx), Op::ParamIntDictGet(param_idx, k), Op::DictGet) =
                (&ops[i], &ops[i + 1], &ops[i + 2])
            {
                let var_idx = *var_idx;
                let param_idx = *param_idx;
                let k = *k;
                ops[i] = Op::VarParamIntDictGet2(var_idx, param_idx, k);
                ops.remove(i + 2);
                patch_jumps_after_remove(ops, i + 2, &mut jump_targets);
                ops.remove(i + 1);
                patch_jumps_after_remove(ops, i + 1, &mut jump_targets);
                continue;
            }
        }

        i += 1;
    }
}

/// After removing an instruction at position `removed_pos`, patch all jump targets
/// that pointed at or after that position.
fn patch_jumps_after_remove(ops: &mut [Op], removed_pos: usize, jump_targets: &mut Vec<bool>) {
    // Shift jump_targets array
    if removed_pos < jump_targets.len() {
        jump_targets.remove(removed_pos);
    }
    // Patch jump targets in ops
    for op in ops.iter_mut() {
        match op {
            Op::JumpIfFalse(t) | Op::JumpIfTrue(t) | Op::Jump(t) => {
                if (*t as usize) > removed_pos {
                    *t -= 1;
                }
            }
            Op::ForallRangeInit(t)
            | Op::ExistsRangeInit(t)
            | Op::CountRangeInit(t)
            | Op::FnLitRangeInit(t)
            | Op::SetCompRangeInit(t)
            | Op::ForallSetInit(t)
            | Op::ExistsSetInit(t)
            | Op::SetCompSetInit(t)
            | Op::ForallPowersetInit(t)
            | Op::ExistsPowersetInit(t) => {
                if (*t as usize) > removed_pos {
                    *t -= 1;
                }
            }
            Op::ForallRangeStep { body_pc, end_pc }
            | Op::ExistsRangeStep { body_pc, end_pc }
            | Op::CountRangeStep { body_pc, end_pc }
            | Op::FnLitRangeStep { body_pc, end_pc }
            | Op::SetCompRangeStep { body_pc, end_pc }
            | Op::SetCompRangeAdvance { body_pc, end_pc }
            | Op::ForallSetStep { body_pc, end_pc }
            | Op::ExistsSetStep { body_pc, end_pc }
            | Op::SetCompSetStep { body_pc, end_pc }
            | Op::SetCompSetAdvance { body_pc, end_pc }
            | Op::ForallPowersetStep { body_pc, end_pc }
            | Op::ExistsPowersetStep { body_pc, end_pc } => {
                if (*body_pc as usize) > removed_pos {
                    *body_pc -= 1;
                }
                if (*end_pc as usize) > removed_pos {
                    *end_pc -= 1;
                }
            }
            _ => {}
        }
    }
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
    result.as_bool().ok_or_else(|| EvalError::TypeMismatch {
        expected: "Bool".to_string(),
        actual: result.type_name().to_string(),
    })
}

/// Reusable VM evaluation buffers.
///
/// Pre-allocate once per thread, reuse across all `vm_eval_reuse` calls.
/// Eliminates per-evaluation Vec allocations in the hot path.
pub struct VmBufs {
    stack: Vec<Value>,
    locals: Vec<Value>,
    loops: Vec<LoopState>,
}

impl VmBufs {
    pub fn new() -> Self {
        Self {
            stack: Vec::with_capacity(16),
            locals: Vec::new(),
            loops: Vec::new(),
        }
    }
}

impl Default for VmBufs {
    fn default() -> Self {
        Self::new()
    }
}

/// Execute bytecode using reusable buffers. Returns the result as a Value.
/// Buffers are cleared before use and left in a clean state on return.
pub fn vm_eval_reuse(
    bytecode: &Bytecode,
    vars: &[Value],
    next_vars: &[Value],
    consts: &[Value],
    params: &[Value],
    bufs: &mut VmBufs,
) -> EvalResult<Value> {
    bufs.stack.clear();
    bufs.locals.clear();
    bufs.loops.clear();
    vm_eval_inner(
        &bytecode.ops,
        &bytecode.fallbacks,
        vars,
        next_vars,
        consts,
        params,
        &mut bufs.stack,
        &mut bufs.locals,
        &mut bufs.loops,
    )
}

/// Execute bytecode using reusable buffers. Returns the result as a bool.
pub fn vm_eval_bool_reuse(
    bytecode: &Bytecode,
    vars: &[Value],
    next_vars: &[Value],
    consts: &[Value],
    params: &[Value],
    bufs: &mut VmBufs,
) -> EvalResult<bool> {
    let result = vm_eval_reuse(bytecode, vars, next_vars, consts, params, bufs)?;
    result.as_bool().ok_or_else(|| EvalError::TypeMismatch {
        expected: "Bool".to_string(),
        actual: result.type_name().to_string(),
    })
}

/// Execute bytecode and return the result as a Value.
pub fn vm_eval(
    bytecode: &Bytecode,
    vars: &[Value],
    next_vars: &[Value],
    consts: &[Value],
    params: &[Value],
) -> EvalResult<Value> {
    let mut stack: Vec<Value> = Vec::with_capacity(16);
    let mut locals: Vec<Value> = Vec::new();
    let mut loops: Vec<LoopState> = Vec::new();
    vm_eval_inner(
        &bytecode.ops,
        &bytecode.fallbacks,
        vars,
        next_vars,
        consts,
        params,
        &mut stack,
        &mut locals,
        &mut loops,
    )
}

/// Core VM execution loop. Shared by `vm_eval` and `vm_eval_reuse`.
fn vm_eval_inner(
    ops: &[Op],
    fallbacks: &[CompiledExpr],
    vars: &[Value],
    next_vars: &[Value],
    consts: &[Value],
    params: &[Value],
    stack: &mut Vec<Value>,
    locals: &mut Vec<Value>,
    loops: &mut Vec<LoopState>,
) -> EvalResult<Value> {
    let mut pc: usize = 0;

    loop {
        // Safety: compiler always emits Halt, so pc is always valid
        let op = unsafe { ops.get_unchecked(pc) };
        match op {
            Op::Int(n) => stack.push(Value::int(*n)),
            Op::Bool(b) => stack.push(Value::bool(*b)),
            Op::PushValue(v) => stack.push(v.clone()),

            Op::Var(idx) => stack.push(vars[*idx as usize].clone()),
            Op::PrimedVar(idx) => stack.push(next_vars[*idx as usize].clone()),
            Op::Const(idx) => stack.push(consts[*idx as usize].clone()),
            Op::Param(idx) => {
                let i = *idx as usize;
                if i >= params.len() {
                    return Err(EvalError::Internal(format!("param {} not found", i)));
                }
                stack.push(params[i].clone());
            }
            Op::Local(idx) => {
                let stack_idx = locals.len() - 1 - *idx as usize;
                stack.push(locals[stack_idx].clone());
            }

            // Arithmetic
            Op::Add => {
                let b = pop_int(stack)?;
                let a = pop_int(stack)?;
                stack.push(Value::int(a + b));
            }
            Op::Sub => {
                let b = pop_int(stack)?;
                let a = pop_int(stack)?;
                stack.push(Value::int(a - b));
            }
            Op::Mul => {
                let b = pop_int(stack)?;
                let a = pop_int(stack)?;
                stack.push(Value::int(a * b));
            }
            Op::Div => {
                let b = pop_int(stack)?;
                let a = pop_int(stack)?;
                if b == 0 {
                    return Err(EvalError::DivisionByZero);
                }
                stack.push(Value::int(a / b));
            }
            Op::Mod => {
                let b = pop_int(stack)?;
                let a = pop_int(stack)?;
                if b == 0 {
                    return Err(EvalError::DivisionByZero);
                }
                stack.push(Value::int(a % b));
            }
            Op::Neg => {
                let a = pop_int(stack)?;
                stack.push(Value::int(-a));
            }

            // Boolean
            Op::Not => {
                let a = pop_bool(stack)?;
                stack.push(Value::bool(!a));
            }

            // General comparison
            Op::Eq => {
                let b = stack.pop().unwrap();
                let a = stack.pop().unwrap();
                stack.push(Value::bool(a == b));
            }
            Op::Ne => {
                let b = stack.pop().unwrap();
                let a = stack.pop().unwrap();
                stack.push(Value::bool(a != b));
            }

            // Integer comparison
            Op::IntEq => {
                let b = pop_int(stack)?;
                let a = pop_int(stack)?;
                stack.push(Value::bool(a == b));
            }
            Op::IntNe => {
                let b = pop_int(stack)?;
                let a = pop_int(stack)?;
                stack.push(Value::bool(a != b));
            }
            Op::IntLt => {
                let b = pop_int(stack)?;
                let a = pop_int(stack)?;
                stack.push(Value::bool(a < b));
            }
            Op::IntLe => {
                let b = pop_int(stack)?;
                let a = pop_int(stack)?;
                stack.push(Value::bool(a <= b));
            }
            Op::IntGt => {
                let b = pop_int(stack)?;
                let a = pop_int(stack)?;
                stack.push(Value::bool(a > b));
            }
            Op::IntGe => {
                let b = pop_int(stack)?;
                let a = pop_int(stack)?;
                stack.push(Value::bool(a >= b));
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

            // === Superinstructions ===
            Op::VarDictGet(var_idx) => {
                // Fused: Var(i) + DictGet — Var(i) is the KEY (last pushed),
                // base dict is already on stack below.
                let key = &vars[*var_idx as usize];
                let base = stack.pop().unwrap();
                match base.kind() {
                    VK::IntMap2(inner_size, data) => {
                        let k = expect_int(key)? as usize;
                        let start = k * inner_size as usize;
                        let row = data[start..start + inner_size as usize].to_vec();
                        stack.push(Value::intmap(Arc::new(row)));
                    }
                    VK::IntMap(arr) => {
                        let k = expect_int(key)? as usize;
                        stack.push(arr[k].clone());
                    }
                    VK::Fn(map) => {
                        let val = Value::fn_get(map, key)
                            .cloned()
                            .ok_or_else(|| EvalError::KeyNotFound(key.to_string()))?;
                        stack.push(val);
                    }
                    VK::Seq(seq) => {
                        let idx = expect_int(key)?;
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
            Op::VarIntEq(var_idx, k) => {
                // Fused: Var(i) + Int(k) + IntEq — compare var to constant
                match vars[*var_idx as usize].as_int() {
                    Some(v) => stack.push(Value::bool(v == *k)),
                    None => {
                        return Err(EvalError::TypeMismatch {
                            expected: "Int".to_string(),
                            actual: vars[*var_idx as usize].type_name().to_string(),
                        });
                    }
                }
            }
            Op::VarParamDictGet(var_idx, param_idx) => {
                // Fused: Var(i) + Param(j) + DictGet — dict[param] from var
                let key = &params[*param_idx as usize];
                let base = &vars[*var_idx as usize];
                match base.kind() {
                    VK::IntMap2(inner_size, data) => {
                        let k = expect_int(key)? as usize;
                        let start = k * inner_size as usize;
                        let row = data[start..start + inner_size as usize].to_vec();
                        stack.push(Value::intmap(Arc::new(row)));
                    }
                    VK::IntMap(arr) => {
                        let k = expect_int(key)? as usize;
                        stack.push(arr[k].clone());
                    }
                    VK::Fn(map) => {
                        let val = Value::fn_get(map, key)
                            .cloned()
                            .ok_or_else(|| EvalError::KeyNotFound(key.to_string()))?;
                        stack.push(val);
                    }
                    _ => {
                        return Err(EvalError::TypeMismatch {
                            expected: "Fn or Seq".to_string(),
                            actual: base.type_name().to_string(),
                        })
                    }
                }
            }
            Op::VarParam2DictGet(var_idx, param1_idx, param2_idx) => {
                // Fused: VarParamDictGet(a,b) + Param(c) + DictGet
                // Two-level lookup: vars[a][params[b]][params[c]] without intermediate clone.
                let key1 = &params[*param1_idx as usize];
                let key2 = &params[*param2_idx as usize];
                let outer = &vars[*var_idx as usize];
                match outer.kind() {
                    VK::IntMap2(inner_size, data) => {
                        let k1 = expect_int(key1)? as usize;
                        let k2 = expect_int(key2)? as usize;
                        stack.push(data[k1 * inner_size as usize + k2].clone());
                    }
                    _ => {
                        let inner_ref = match outer.kind() {
                            VK::IntMap(arr) => {
                                let k = expect_int(key1)? as usize;
                                &arr[k]
                            }
                            VK::Fn(map) => {
                                Value::fn_get(map, key1)
                                    .ok_or_else(|| EvalError::KeyNotFound(key1.to_string()))?
                            }
                            _ => {
                                return Err(EvalError::TypeMismatch {
                                    expected: "Fn or IntMap".to_string(),
                                    actual: outer.type_name().to_string(),
                                })
                            }
                        };
                        match inner_ref.kind() {
                            VK::IntMap(arr) => {
                                let k = expect_int(key2)? as usize;
                                stack.push(arr[k].clone());
                            }
                            VK::Fn(inner_map) => {
                                let val = Value::fn_get(inner_map, key2)
                                    .cloned()
                                    .ok_or_else(|| EvalError::KeyNotFound(key2.to_string()))?;
                                stack.push(val);
                            }
                            _ => {
                                return Err(EvalError::TypeMismatch {
                                    expected: "Fn or IntMap".to_string(),
                                    actual: inner_ref.type_name().to_string(),
                                })
                            }
                        }
                    }
                }
            }
            Op::VarParamDictGetIntEq(var_idx, param_idx, k) => {
                // Fused: VarParamDictGet(a,b) + Int(k) + IntEq
                // Dict lookup + compare: vars[a][params[b]] == k without cloning the dict.
                let key = &params[*param_idx as usize];
                let base = &vars[*var_idx as usize];
                match base.kind() {
                    VK::IntMap(arr) => {
                        let idx = expect_int(key)? as usize;
                        stack.push(Value::bool(arr[idx] == Value::int(*k)));
                    }
                    VK::Fn(map) => {
                        let val = Value::fn_get(map, key)
                            .ok_or_else(|| EvalError::KeyNotFound(key.to_string()))?;
                        stack.push(Value::bool(val.as_int() == Some(*k)));
                    }
                    _ => {
                        return Err(EvalError::TypeMismatch {
                            expected: "Fn or IntMap".to_string(),
                            actual: base.type_name().to_string(),
                        })
                    }
                }
            }
            Op::VarParamDictGetBoolEq(var_idx, param_idx, bool_val) => {
                // Fused: VarParamDictGet(a,b) + Bool(v) + Eq
                // Dict lookup + bool compare: vars[a][params[b]] == v without cloning.
                let key = &params[*param_idx as usize];
                let base = &vars[*var_idx as usize];
                let expected = Value::bool(*bool_val);
                match base.kind() {
                    VK::IntMap(arr) => {
                        let idx = expect_int(key)? as usize;
                        stack.push(Value::bool(arr[idx] == expected));
                    }
                    VK::Fn(map) => {
                        let val = Value::fn_get(map, key)
                            .ok_or_else(|| EvalError::KeyNotFound(key.to_string()))?;
                        stack.push(Value::bool(*val == expected));
                    }
                    _ => {
                        return Err(EvalError::TypeMismatch {
                            expected: "Fn or IntMap".to_string(),
                            actual: base.type_name().to_string(),
                        })
                    }
                }
            }
            Op::VarParam2DictGetBoolEq(var_idx, param1_idx, param2_idx, bool_val) => {
                // Fused: VarParam2DictGet(a,b,c) + Bool(v) + Eq
                // Two-level lookup + bool compare: vars[a][params[b]][params[c]] == v without cloning.
                let key1 = &params[*param1_idx as usize];
                let key2 = &params[*param2_idx as usize];
                let outer = &vars[*var_idx as usize];
                let expected = Value::bool(*bool_val);
                match outer.kind() {
                    VK::IntMap2(inner_size, data) => {
                        let k1 = expect_int(key1)? as usize;
                        let k2 = expect_int(key2)? as usize;
                        stack.push(Value::bool(data[k1 * inner_size as usize + k2] == expected));
                    }
                    _ => {
                        let inner_ref = match outer.kind() {
                            VK::IntMap(arr) => {
                                let k = expect_int(key1)? as usize;
                                &arr[k]
                            }
                            VK::Fn(map) => {
                                Value::fn_get(map, key1)
                                    .ok_or_else(|| EvalError::KeyNotFound(key1.to_string()))?
                            }
                            _ => {
                                return Err(EvalError::TypeMismatch {
                                    expected: "Fn or IntMap".to_string(),
                                    actual: outer.type_name().to_string(),
                                })
                            }
                        };
                        match inner_ref.kind() {
                            VK::IntMap(arr) => {
                                let k = expect_int(key2)? as usize;
                                stack.push(Value::bool(arr[k] == expected));
                            }
                            VK::Fn(inner_map) => {
                                let val = Value::fn_get(inner_map, key2)
                                    .ok_or_else(|| EvalError::KeyNotFound(key2.to_string()))?;
                                stack.push(Value::bool(*val == expected));
                            }
                            _ => {
                                return Err(EvalError::TypeMismatch {
                                    expected: "Fn or IntMap".to_string(),
                                    actual: inner_ref.type_name().to_string(),
                                })
                            }
                        }
                    }
                }
            }
            Op::VarParamDictGetLen(var_idx, param_idx) => {
                // Fused: VarParamDictGet(a,b) + Len
                // len(vars[a][params[b]]) without cloning the intermediate collection.
                let key = &params[*param_idx as usize];
                let base = &vars[*var_idx as usize];
                let val = match base.kind() {
                    VK::IntMap(arr) => {
                        let k = expect_int(key)? as usize;
                        &arr[k]
                    }
                    VK::Fn(map) => {
                        Value::fn_get(map, key)
                            .ok_or_else(|| EvalError::KeyNotFound(key.to_string()))?
                    }
                    _ => {
                        return Err(EvalError::TypeMismatch {
                            expected: "Fn or IntMap".to_string(),
                            actual: base.type_name().to_string(),
                        })
                    }
                };
                let len = match val.kind() {
                    VK::Set(s) => s.len() as i64,
                    VK::Seq(s) => s.len() as i64,
                    VK::Fn(f) => f.len() as i64,
                    VK::IntMap(arr) => arr.len() as i64,
                    _ => {
                        return Err(EvalError::TypeMismatch {
                            expected: "Set, Seq, or Fn".to_string(),
                            actual: val.type_name().to_string(),
                        })
                    }
                };
                stack.push(Value::int(len));
            }

            Op::ParamIntDictGet(param_idx, k) => {
                // Fused: Param(p) + Int(k) + DictGet → params[p][k]
                // Direct access into a Seq/Dict parameter at a constant index.
                let param = &params[*param_idx as usize];
                match param.kind() {
                    VK::IntMap(arr) => {
                        stack.push(arr[*k as usize].clone());
                    }
                    VK::Seq(s) => {
                        stack.push(s[*k as usize].clone());
                    }
                    VK::Fn(map) => {
                        let key = Value::int(*k);
                        let val = Value::fn_get(map, &key)
                            .cloned()
                            .ok_or_else(|| EvalError::KeyNotFound(key.to_string()))?;
                        stack.push(val);
                    }
                    _ => {
                        return Err(EvalError::TypeMismatch {
                            expected: "Seq, Fn, or IntMap".to_string(),
                            actual: param.type_name().to_string(),
                        })
                    }
                }
            }
            Op::VarParamIntDictGet2(var_idx, param_idx, k) => {
                // Fused: Var(v) + Param(p) + Int(k) + DictGet + DictGet → vars[v][params[p][k]]
                // Two-level lookup: first index into the parameter seq/dict, then use result
                // as key into a state variable. E.g. currentTerm[msg[2]], state[msg[2]].
                let param = &params[*param_idx as usize];
                let inner_key = match param.kind() {
                    VK::IntMap(arr) => arr[*k as usize].clone(),
                    VK::Seq(s) => s[*k as usize].clone(),
                    VK::Fn(map) => {
                        let key = Value::int(*k);
                        Value::fn_get(map, &key)
                            .cloned()
                            .ok_or_else(|| EvalError::KeyNotFound(key.to_string()))?
                    }
                    _ => {
                        return Err(EvalError::TypeMismatch {
                            expected: "Seq, Fn, or IntMap".to_string(),
                            actual: param.type_name().to_string(),
                        })
                    }
                };
                let base = &vars[*var_idx as usize];
                match base.kind() {
                    VK::IntMap(arr) => {
                        let idx = expect_int(&inner_key)? as usize;
                        stack.push(arr[idx].clone());
                    }
                    VK::Fn(map) => {
                        let val = Value::fn_get(map, &inner_key)
                            .cloned()
                            .ok_or_else(|| EvalError::KeyNotFound(inner_key.to_string()))?;
                        stack.push(val);
                    }
                    _ => {
                        return Err(EvalError::TypeMismatch {
                            expected: "Fn or IntMap".to_string(),
                            actual: base.type_name().to_string(),
                        })
                    }
                }
            }

            // Dict/collection ops
            Op::DictGet => {
                let key = stack.pop().unwrap();
                let base = stack.pop().unwrap();
                match base.kind() {
                    VK::IntMap2(inner_size, data) => {
                        let k = expect_int(&key)? as usize;
                        let start = k * inner_size as usize;
                        let row = data[start..start + inner_size as usize].to_vec();
                        stack.push(Value::intmap(Arc::new(row)));
                    }
                    VK::IntMap(arr) => {
                        let k = expect_int(&key)? as usize;
                        stack.push(arr[k].clone());
                    }
                    VK::Fn(map) => {
                        let val = Value::fn_get(map, &key)
                            .cloned()
                            .ok_or_else(|| EvalError::KeyNotFound(key.to_string()))?;
                        stack.push(val);
                    }
                    VK::Seq(seq) => {
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
                if base.is_intmap2() {
                    let k = expect_int(&key)? as usize;
                    let mut arc = base.into_intmap2_arc();
                    let d = Arc::make_mut(&mut arc);
                    let start = k * d.inner_size as usize;
                    match value.kind() {
                        VK::IntMap(row) => {
                            d.data[start..start + d.inner_size as usize]
                                .clone_from_slice(row);
                        }
                        _ => {
                            return Err(EvalError::TypeMismatch {
                                expected: "IntMap".to_string(),
                                actual: value.type_name().to_string(),
                            });
                        }
                    }
                    stack.push(Value::from_intmap2_arc(arc));
                } else if base.is_intmap() {
                    let mut arr = base.into_intmap_arc();
                    let k = expect_int(&key)? as usize;
                    Arc::make_mut(&mut arr)[k] = value;
                    stack.push(Value::from_intmap_arc(arr));
                } else if base.is_fn() {
                    let mut map = base.into_fn_arc();
                    Value::fn_insert(Arc::make_mut(&mut map), key, value);
                    stack.push(Value::from_fn_arc(map));
                } else {
                    return Err(EvalError::TypeMismatch {
                        expected: "Fn".to_string(),
                        actual: base.type_name().to_string(),
                    });
                }
            }
            Op::DictUpdateN(n) => {
                // Stack: [dict, k1, v1, k2, v2, ..., kN, vN] (dict deepest)
                // Pop N (value, key) pairs in reverse order
                let n = *n as usize;
                let mut pairs = Vec::with_capacity(n);
                for _ in 0..n {
                    let value = stack.pop().unwrap();
                    let key = stack.pop().unwrap();
                    pairs.push((key, value));
                }
                pairs.reverse();
                let base = stack.pop().unwrap();
                if base.is_intmap2() {
                    let mut arc = base.into_intmap2_arc();
                    let d = Arc::make_mut(&mut arc);
                    for (key, value) in pairs {
                        let k = expect_int(&key)? as usize;
                        let start = k * d.inner_size as usize;
                        match value.kind() {
                            VK::IntMap(row) => {
                                d.data[start..start + d.inner_size as usize]
                                    .clone_from_slice(row);
                            }
                            _ => {
                                return Err(EvalError::TypeMismatch {
                                    expected: "IntMap".to_string(),
                                    actual: value.type_name().to_string(),
                                });
                            }
                        }
                    }
                    stack.push(Value::from_intmap2_arc(arc));
                } else if base.is_intmap() {
                    let mut arr = base.into_intmap_arc();
                    let data = Arc::make_mut(&mut arr);
                    for (key, value) in pairs {
                        let k = expect_int(&key)? as usize;
                        data[k] = value;
                    }
                    stack.push(Value::from_intmap_arc(arr));
                } else if base.is_fn() {
                    let mut map = base.into_fn_arc();
                    let data = Arc::make_mut(&mut map);
                    for (key, value) in pairs {
                        Value::fn_insert(data, key, value);
                    }
                    stack.push(Value::from_fn_arc(map));
                } else {
                    return Err(EvalError::TypeMismatch {
                        expected: "Fn".to_string(),
                        actual: base.type_name().to_string(),
                    });
                }
            }
            Op::NestedDictUpdate2 => {
                let dict = stack.pop().unwrap();
                let k1 = stack.pop().unwrap();
                let k2 = stack.pop().unwrap();
                let value = stack.pop().unwrap();
                if dict.is_intmap2() {
                    let k1_int = expect_int(&k1)? as usize;
                    let k2_int = expect_int(&k2)? as usize;
                    let mut arc = dict.into_intmap2_arc();
                    let d = Arc::make_mut(&mut arc);
                    d.data[k1_int * d.inner_size as usize + k2_int] = value;
                    stack.push(Value::from_intmap2_arc(arc));
                } else if dict.is_intmap() {
                    let mut outer_arc = dict.into_intmap_arc();
                    let k1_int = expect_int(&k1)? as usize;
                    let outer = Arc::make_mut(&mut outer_arc);
                    let inner_val = std::mem::replace(&mut outer[k1_int], Value::none());
                    if inner_val.is_intmap() {
                        let k2_int = expect_int(&k2)? as usize;
                        let mut inner_arc = inner_val.into_intmap_arc();
                        Arc::make_mut(&mut inner_arc)[k2_int] = value;
                        outer[k1_int] = Value::from_intmap_arc(inner_arc);
                    } else if inner_val.is_fn() {
                        let mut inner_arc = inner_val.into_fn_arc();
                        Value::fn_insert(Arc::make_mut(&mut inner_arc), k2, value);
                        outer[k1_int] = Value::from_fn_arc(inner_arc);
                    } else {
                        return Err(EvalError::TypeMismatch {
                            expected: "Fn or IntMap".to_string(),
                            actual: inner_val.type_name().to_string(),
                        });
                    }
                    stack.push(Value::from_intmap_arc(outer_arc));
                } else if dict.is_fn() {
                    let mut outer_arc = dict.into_fn_arc();
                    let outer = Arc::make_mut(&mut outer_arc);
                    let pos = outer
                        .binary_search_by(|(k, _)| k.cmp(&k1))
                        .map_err(|_| EvalError::KeyNotFound(k1.to_string()))?;
                    if outer[pos].1.is_intmap() {
                        let k2_int = expect_int(&k2)? as usize;
                        let inner_val = std::mem::replace(&mut outer[pos].1, Value::none());
                        let mut inner_arc = inner_val.into_intmap_arc();
                        Arc::make_mut(&mut inner_arc)[k2_int] = value;
                        outer[pos].1 = Value::from_intmap_arc(inner_arc);
                    } else if outer[pos].1.is_fn() {
                        let inner_val = std::mem::replace(&mut outer[pos].1, Value::none());
                        let mut inner_arc = inner_val.into_fn_arc();
                        Value::fn_insert(Arc::make_mut(&mut inner_arc), k2, value);
                        outer[pos].1 = Value::from_fn_arc(inner_arc);
                    } else {
                        return Err(EvalError::TypeMismatch {
                            expected: "Fn or IntMap".to_string(),
                            actual: outer[pos].1.type_name().to_string(),
                        });
                    }
                    stack.push(Value::from_fn_arc(outer_arc));
                } else {
                    return Err(EvalError::TypeMismatch {
                        expected: "Fn or IntMap".to_string(),
                        actual: dict.type_name().to_string(),
                    });
                }
            }
            Op::NestedDictUpdate3 => {
                let dict = stack.pop().unwrap();
                let k1 = stack.pop().unwrap();
                let k2 = stack.pop().unwrap();
                let k3 = stack.pop().unwrap();
                let value = stack.pop().unwrap();

                // Helper: update the innermost (3rd level) dict
                let update_inner =
                    |inner_val: Value, k3: Value, value: Value| -> Result<Value, EvalError> {
                        if inner_val.is_intmap() {
                            let k3_int = expect_int(&k3)? as usize;
                            let mut inner_arc = inner_val.into_intmap_arc();
                            Arc::make_mut(&mut inner_arc)[k3_int] = value;
                            Ok(Value::from_intmap_arc(inner_arc))
                        } else if inner_val.is_fn() {
                            let mut inner_arc = inner_val.into_fn_arc();
                            Value::fn_insert(Arc::make_mut(&mut inner_arc), k3, value);
                            Ok(Value::from_fn_arc(inner_arc))
                        } else {
                            Err(EvalError::TypeMismatch {
                                expected: "Fn or IntMap".to_string(),
                                actual: inner_val.type_name().to_string(),
                            })
                        }
                    };

                // Helper: update the middle (2nd level) dict
                let update_mid =
                    |mid_val: Value,
                     k2: Value,
                     k3: Value,
                     value: Value|
                     -> Result<Value, EvalError> {
                        if mid_val.is_intmap() {
                            let k2_int = expect_int(&k2)? as usize;
                            let mut mid_arc = mid_val.into_intmap_arc();
                            let mid = Arc::make_mut(&mut mid_arc);
                            let inner_val = std::mem::replace(&mut mid[k2_int], Value::none());
                            mid[k2_int] = update_inner(inner_val, k3, value)?;
                            Ok(Value::from_intmap_arc(mid_arc))
                        } else if mid_val.is_fn() {
                            let mut mid_arc = mid_val.into_fn_arc();
                            let mid = Arc::make_mut(&mut mid_arc);
                            let pos2 = mid
                                .binary_search_by(|(k, _)| k.cmp(&k2))
                                .map_err(|_| EvalError::KeyNotFound(k2.to_string()))?;
                            let inner_val = std::mem::replace(&mut mid[pos2].1, Value::none());
                            mid[pos2].1 = update_inner(inner_val, k3, value)?;
                            Ok(Value::from_fn_arc(mid_arc))
                        } else {
                            Err(EvalError::TypeMismatch {
                                expected: "Fn or IntMap".to_string(),
                                actual: mid_val.type_name().to_string(),
                            })
                        }
                    };

                if dict.is_intmap() {
                    let k1_int = expect_int(&k1)? as usize;
                    let mut outer_arc = dict.into_intmap_arc();
                    let outer = Arc::make_mut(&mut outer_arc);
                    let mid_val = std::mem::replace(&mut outer[k1_int], Value::none());
                    outer[k1_int] = update_mid(mid_val, k2, k3, value)?;
                    stack.push(Value::from_intmap_arc(outer_arc));
                } else if dict.is_fn() {
                    let mut outer_arc = dict.into_fn_arc();
                    let outer = Arc::make_mut(&mut outer_arc);
                    let pos1 = outer
                        .binary_search_by(|(k, _)| k.cmp(&k1))
                        .map_err(|_| EvalError::KeyNotFound(k1.to_string()))?;
                    let mid_val = std::mem::replace(&mut outer[pos1].1, Value::none());
                    outer[pos1].1 = update_mid(mid_val, k2, k3, value)?;
                    stack.push(Value::from_fn_arc(outer_arc));
                } else {
                    return Err(EvalError::TypeMismatch {
                        expected: "Fn or IntMap".to_string(),
                        actual: dict.type_name().to_string(),
                    });
                }
            }
            Op::Len => {
                let val = stack.pop().unwrap();
                let len = match val.kind() {
                    VK::Set(s) => s.len() as i64,
                    VK::Seq(s) => s.len() as i64,
                    VK::Fn(f) => f.len() as i64,
                    VK::IntMap(arr) => arr.len() as i64,
                    VK::IntMap2(inner_size, data) => {
                        if inner_size > 0 { (data.len() / inner_size as usize) as i64 } else { 0 }
                    }
                    _ => {
                        return Err(EvalError::TypeMismatch {
                            expected: "Set, Seq, or Fn".to_string(),
                            actual: val.type_name().to_string(),
                        })
                    }
                };
                stack.push(Value::int(len));
            }
            Op::Contains => {
                let right_val = stack.pop().unwrap();
                let elem = stack.pop().unwrap();
                let result = match right_val.kind() {
                    VK::Set(s) => Value::set_contains(s, &elem),
                    VK::Fn(f) => Value::fn_get(f, &elem).is_some(),
                    VK::IntMap(arr) => {
                        let k = expect_int(&elem)? as usize;
                        k < arr.len()
                    }
                    VK::IntMap2(inner_size, data) => {
                        let k = expect_int(&elem)? as usize;
                        let outer_size = if inner_size > 0 { data.len() / inner_size as usize } else { 0 };
                        k < outer_size
                    }
                    _ => return Err(type_mismatch("Set or Dict", &right_val)),
                };
                stack.push(Value::bool(result));
            }
            Op::NotContains => {
                let right_val = stack.pop().unwrap();
                let elem = stack.pop().unwrap();
                let result = match right_val.kind() {
                    VK::Set(s) => !Value::set_contains(s, &elem),
                    VK::Fn(f) => Value::fn_get(f, &elem).is_none(),
                    VK::IntMap(arr) => {
                        let k = expect_int(&elem)? as usize;
                        k >= arr.len()
                    }
                    VK::IntMap2(inner_size, data) => {
                        let k = expect_int(&elem)? as usize;
                        let outer_size = if inner_size > 0 { data.len() / inner_size as usize } else { 0 };
                        k >= outer_size
                    }
                    _ => return Err(type_mismatch("Set or Dict", &right_val)),
                };
                stack.push(Value::bool(result));
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
                let hi = pop_int(stack)?;
                let lo = pop_int(stack)?;
                if lo > hi {
                    stack.push(Value::bool(true));
                    pc = *end_pc as usize;
                    continue;
                }
                loops.push(LoopState {
                    hi,
                    counter: 0,
                    fn_buf: Vec::new(),
                    set_buf: Vec::new(),
                    domain_val: None,
                });
                locals.push(Value::int(lo));
            }
            Op::ForallRangeStep { body_pc, end_pc } => {
                let body_result = pop_bool(stack)?;
                if !body_result {
                    locals.pop();
                    loops.pop();
                    stack.push(Value::bool(false));
                    pc = *end_pc as usize;
                    continue;
                }
                let current = get_local_int(&locals)?;
                let hi = loops.last().unwrap().hi;
                if current >= hi {
                    locals.pop();
                    loops.pop();
                    stack.push(Value::bool(true));
                    pc = *end_pc as usize;
                    continue;
                }
                *locals.last_mut().unwrap() = Value::int(current + 1);
                pc = *body_pc as usize;
                continue;
            }

            Op::ExistsRangeInit(end_pc) => {
                let hi = pop_int(stack)?;
                let lo = pop_int(stack)?;
                if lo > hi {
                    stack.push(Value::bool(false));
                    pc = *end_pc as usize;
                    continue;
                }
                loops.push(LoopState {
                    hi,
                    counter: 0,
                    fn_buf: Vec::new(),
                    set_buf: Vec::new(),
                    domain_val: None,
                });
                locals.push(Value::int(lo));
            }
            Op::ExistsRangeStep { body_pc, end_pc } => {
                let body_result = pop_bool(stack)?;
                if body_result {
                    locals.pop();
                    loops.pop();
                    stack.push(Value::bool(true));
                    pc = *end_pc as usize;
                    continue;
                }
                let current = get_local_int(&locals)?;
                let hi = loops.last().unwrap().hi;
                if current >= hi {
                    locals.pop();
                    loops.pop();
                    stack.push(Value::bool(false));
                    pc = *end_pc as usize;
                    continue;
                }
                *locals.last_mut().unwrap() = Value::int(current + 1);
                pc = *body_pc as usize;
                continue;
            }

            // === Count filtered ===
            Op::CountRangeInit(end_pc) => {
                let hi = pop_int(stack)?;
                let lo = pop_int(stack)?;
                if lo > hi {
                    stack.push(Value::int(0));
                    pc = *end_pc as usize;
                    continue;
                }
                loops.push(LoopState {
                    hi,
                    counter: 0,
                    fn_buf: Vec::new(),
                    set_buf: Vec::new(),
                    domain_val: None,
                });
                locals.push(Value::int(lo));
            }
            Op::CountRangeStep { body_pc, end_pc } => {
                let pred = pop_bool(stack)?;
                let loop_state = loops.last_mut().unwrap();
                if pred {
                    loop_state.counter += 1;
                }
                let current = get_local_int(&locals)?;
                if current >= loop_state.hi {
                    let count = loop_state.counter;
                    locals.pop();
                    loops.pop();
                    stack.push(Value::int(count));
                    pc = *end_pc as usize;
                    continue;
                }
                *locals.last_mut().unwrap() = Value::int(current + 1);
                pc = *body_pc as usize;
                continue;
            }

            // === SetComprehension over range ===
            Op::SetCompRangeInit(end_pc) => {
                let hi = pop_int(stack)?;
                let lo = pop_int(stack)?;
                if lo > hi {
                    stack.push(Value::empty_set());
                    pc = *end_pc as usize;
                    continue;
                }
                let cap = (hi - lo + 1).max(0) as usize;
                loops.push(LoopState {
                    hi,
                    counter: 0,
                    fn_buf: Vec::new(),
                    set_buf: Vec::with_capacity(cap),
                    domain_val: None,
                });
                locals.push(Value::int(lo));
            }
            Op::SetCompRangeStep { body_pc, end_pc } => {
                let element = stack.pop().unwrap();
                let loop_state = loops.last_mut().unwrap();
                loop_state.set_buf.push(element);
                let current = get_local_int(&locals)?;
                if current >= loop_state.hi {
                    let mut set_buf = std::mem::take(&mut loop_state.set_buf);
                    locals.pop();
                    loops.pop();
                    set_buf.sort();
                    set_buf.dedup();
                    stack.push(Value::set(Arc::new(set_buf)));
                    pc = *end_pc as usize;
                    continue;
                }
                *locals.last_mut().unwrap() = Value::int(current + 1);
                pc = *body_pc as usize;
                continue;
            }
            Op::SetCompRangeAdvance { body_pc, end_pc } => {
                let current = get_local_int(&locals)?;
                let loop_state = loops.last().unwrap();
                if current >= loop_state.hi {
                    let mut set_buf = std::mem::take(&mut loops.last_mut().unwrap().set_buf);
                    locals.pop();
                    loops.pop();
                    set_buf.sort();
                    set_buf.dedup();
                    stack.push(Value::set(Arc::new(set_buf)));
                    pc = *end_pc as usize;
                    continue;
                }
                *locals.last_mut().unwrap() = Value::int(current + 1);
                pc = *body_pc as usize;
                continue;
            }

            // === Forall over set ===
            Op::ForallSetInit(end_pc) => {
                let domain = stack.pop().unwrap();
                let domain = normalize_domain(domain)?;
                let set = domain.as_set().unwrap();
                if set.is_empty() {
                    stack.push(Value::bool(true));
                    pc = *end_pc as usize;
                    continue;
                }
                locals.push(set[0].clone());
                loops.push(LoopState {
                    hi: 0,
                    counter: 0,
                    fn_buf: Vec::new(),
                    set_buf: Vec::new(),
                    domain_val: Some(domain),
                });
            }
            Op::ForallSetStep { body_pc, end_pc } => {
                let body_result = pop_bool(stack)?;
                if !body_result {
                    locals.pop();
                    loops.pop();
                    stack.push(Value::bool(false));
                    pc = *end_pc as usize;
                    continue;
                }
                let loop_state = loops.last_mut().unwrap();
                loop_state.counter += 1;
                let set = loop_state.domain_val.as_ref().unwrap().as_set().unwrap();
                if loop_state.counter as usize >= set.len() {
                    locals.pop();
                    loops.pop();
                    stack.push(Value::bool(true));
                    pc = *end_pc as usize;
                    continue;
                }
                *locals.last_mut().unwrap() = set[loop_state.counter as usize].clone();
                pc = *body_pc as usize;
                continue;
            }

            // === Exists over set ===
            Op::ExistsSetInit(end_pc) => {
                let domain = stack.pop().unwrap();
                let domain = normalize_domain(domain)?;
                let set = domain.as_set().unwrap();
                if set.is_empty() {
                    stack.push(Value::bool(false));
                    pc = *end_pc as usize;
                    continue;
                }
                locals.push(set[0].clone());
                loops.push(LoopState {
                    hi: 0,
                    counter: 0,
                    fn_buf: Vec::new(),
                    set_buf: Vec::new(),
                    domain_val: Some(domain),
                });
            }
            Op::ExistsSetStep { body_pc, end_pc } => {
                let body_result = pop_bool(stack)?;
                if body_result {
                    locals.pop();
                    loops.pop();
                    stack.push(Value::bool(true));
                    pc = *end_pc as usize;
                    continue;
                }
                let loop_state = loops.last_mut().unwrap();
                loop_state.counter += 1;
                let set = loop_state.domain_val.as_ref().unwrap().as_set().unwrap();
                if loop_state.counter as usize >= set.len() {
                    locals.pop();
                    loops.pop();
                    stack.push(Value::bool(false));
                    pc = *end_pc as usize;
                    continue;
                }
                *locals.last_mut().unwrap() = set[loop_state.counter as usize].clone();
                pc = *body_pc as usize;
                continue;
            }

            // === SetComprehension over set ===
            Op::SetCompSetInit(end_pc) => {
                let domain = stack.pop().unwrap();
                let domain = normalize_domain(domain)?;
                let set = domain.as_set().unwrap();
                if set.is_empty() {
                    stack.push(Value::empty_set());
                    pc = *end_pc as usize;
                    continue;
                }
                locals.push(set[0].clone());
                let cap = set.len();
                loops.push(LoopState {
                    hi: 0,
                    counter: 0,
                    fn_buf: Vec::new(),
                    set_buf: Vec::with_capacity(cap),
                    domain_val: Some(domain),
                });
            }
            Op::SetCompSetStep { body_pc, end_pc } => {
                let element = stack.pop().unwrap();
                let loop_state = loops.last_mut().unwrap();
                loop_state.set_buf.push(element);
                loop_state.counter += 1;
                let set = loop_state.domain_val.as_ref().unwrap().as_set().unwrap();
                if loop_state.counter as usize >= set.len() {
                    let mut set_buf = std::mem::take(&mut loop_state.set_buf);
                    locals.pop();
                    loops.pop();
                    set_buf.sort();
                    set_buf.dedup();
                    stack.push(Value::set(Arc::new(set_buf)));
                    pc = *end_pc as usize;
                    continue;
                }
                *locals.last_mut().unwrap() = set[loop_state.counter as usize].clone();
                pc = *body_pc as usize;
                continue;
            }
            Op::SetCompSetAdvance { body_pc, end_pc } => {
                let loop_state = loops.last_mut().unwrap();
                loop_state.counter += 1;
                let set = loop_state.domain_val.as_ref().unwrap().as_set().unwrap();
                if loop_state.counter as usize >= set.len() {
                    let mut set_buf = std::mem::take(&mut loop_state.set_buf);
                    locals.pop();
                    loops.pop();
                    set_buf.sort();
                    set_buf.dedup();
                    stack.push(Value::set(Arc::new(set_buf)));
                    pc = *end_pc as usize;
                    continue;
                }
                *locals.last_mut().unwrap() = set[loop_state.counter as usize].clone();
                pc = *body_pc as usize;
                continue;
            }

            // === Forall over powerset (bitmask iteration) ===
            Op::ForallPowersetInit(end_pc) => {
                let base = stack.pop().unwrap();
                let base = normalize_domain(base)?;
                let set = base.as_set().unwrap();
                let n = set.len();
                // Powerset always has at least 1 element (empty set at mask=0)
                let subset = Value::empty_set();
                locals.push(subset);
                loops.push(LoopState {
                    hi: (1i64 << n) - 1, // max mask (inclusive)
                    counter: 0,          // current mask
                    fn_buf: Vec::new(),
                    set_buf: Vec::with_capacity(n),
                    domain_val: Some(base),
                });
                let _ = end_pc; // used for patching only
            }
            Op::ForallPowersetStep { body_pc, end_pc } => {
                let body_result = pop_bool(stack)?;
                if !body_result {
                    locals.pop();
                    loops.pop();
                    stack.push(Value::bool(false));
                    pc = *end_pc as usize;
                    continue;
                }
                let loop_state = loops.last_mut().unwrap();
                if loop_state.counter >= loop_state.hi {
                    locals.pop();
                    loops.pop();
                    stack.push(Value::bool(true));
                    pc = *end_pc as usize;
                    continue;
                }
                loop_state.counter += 1;
                let mask = loop_state.counter;
                let set = loop_state.domain_val.as_ref().unwrap().as_set().unwrap();
                loop_state.set_buf.clear();
                for (i, elem) in set.iter().enumerate() {
                    if mask & (1 << i) != 0 {
                        loop_state.set_buf.push(elem.clone());
                    }
                }
                *locals.last_mut().unwrap() = Value::set(Arc::new(loop_state.set_buf.clone()));
                pc = *body_pc as usize;
                continue;
            }

            // === Exists over powerset (bitmask iteration) ===
            Op::ExistsPowersetInit(end_pc) => {
                let base = stack.pop().unwrap();
                let base = normalize_domain(base)?;
                let set = base.as_set().unwrap();
                let n = set.len();
                let subset = Value::empty_set();
                locals.push(subset);
                loops.push(LoopState {
                    hi: (1i64 << n) - 1,
                    counter: 0,
                    fn_buf: Vec::new(),
                    set_buf: Vec::with_capacity(n),
                    domain_val: Some(base),
                });
                let _ = end_pc;
            }
            Op::ExistsPowersetStep { body_pc, end_pc } => {
                let body_result = pop_bool(stack)?;
                if body_result {
                    locals.pop();
                    loops.pop();
                    stack.push(Value::bool(true));
                    pc = *end_pc as usize;
                    continue;
                }
                let loop_state = loops.last_mut().unwrap();
                if loop_state.counter >= loop_state.hi {
                    locals.pop();
                    loops.pop();
                    stack.push(Value::bool(false));
                    pc = *end_pc as usize;
                    continue;
                }
                loop_state.counter += 1;
                let mask = loop_state.counter;
                let set = loop_state.domain_val.as_ref().unwrap().as_set().unwrap();
                loop_state.set_buf.clear();
                for (i, elem) in set.iter().enumerate() {
                    if mask & (1 << i) != 0 {
                        loop_state.set_buf.push(elem.clone());
                    }
                }
                *locals.last_mut().unwrap() = Value::set(Arc::new(loop_state.set_buf.clone()));
                pc = *body_pc as usize;
                continue;
            }

            // === FnLit range ===
            Op::FnLitRangeInit(end_pc) => {
                let hi = pop_int(stack)?;
                let lo = pop_int(stack)?;
                if lo > hi {
                    stack.push(Value::func(Arc::new(Vec::new())));
                    pc = *end_pc as usize;
                    continue;
                }
                let cap = (hi - lo + 1).max(0) as usize;
                loops.push(LoopState {
                    hi,
                    counter: 0,
                    fn_buf: Vec::with_capacity(cap),
                    set_buf: Vec::new(),
                    domain_val: None,
                });
                locals.push(Value::int(lo));
            }
            Op::FnLitRangeStep { body_pc, end_pc } => {
                let body_val = stack.pop().unwrap();
                let current = get_local_int(&locals)?;
                let loop_state = loops.last_mut().unwrap();
                loop_state.fn_buf.push((Value::int(current), body_val));
                if current >= loop_state.hi {
                    let fn_buf = std::mem::take(&mut loop_state.fn_buf);
                    locals.pop();
                    loops.pop();
                    // Produce IntMap if keys start at 0
                    let lo_zero = fn_buf.first().is_none_or(|(k, _)| k == &Value::int(0));
                    if lo_zero {
                        let arr: Vec<Value> =
                            fn_buf.into_iter().map(|(_, v)| v).collect();
                        // Promote to IntMap2 if all values are same-size IntMaps
                        let inner_size = match arr.first().map(|v| v.kind()) {
                            Some(VK::IntMap(a)) => Some(a.len()),
                            _ => None,
                        };
                        if let Some(is) = inner_size {
                            if is > 0 && arr.iter().all(|v| matches!(v.kind(), VK::IntMap(a) if a.len() == is)) {
                                let mut flat = Vec::with_capacity(arr.len() * is);
                                for v in arr {
                                    let row_arc = v.into_intmap_arc();
                                    match Arc::try_unwrap(row_arc) {
                                        Ok(row) => flat.extend(row),
                                        Err(arc) => flat.extend_from_slice(&arc),
                                    }
                                }
                                stack.push(Value::intmap2(IntMap2Data {
                                    inner_size: is as u32,
                                    data: flat,
                                }));
                                pc = *end_pc as usize;
                                continue;
                            }
                        }
                        stack.push(Value::intmap(Arc::new(arr)));
                    } else {
                        stack.push(Value::func(Arc::new(fn_buf)));
                    }
                    pc = *end_pc as usize;
                    continue;
                }
                *locals.last_mut().unwrap() = Value::int(current + 1);
                pc = *body_pc as usize;
                continue;
            }

            // === Set/Seq construction ===
            Op::SetLit(n) => {
                let n = *n as usize;
                let start = stack.len() - n;
                let mut elems: Vec<Value> = stack.drain(start..).collect();
                elems.sort();
                elems.dedup();
                stack.push(Value::set(Arc::new(elems)));
            }
            Op::SeqLit(n) => {
                let n = *n as usize;
                let start = stack.len() - n;
                let elems: Vec<Value> = stack.drain(start..).collect();
                stack.push(Value::seq(elems));
            }
            Op::SetUnion => {
                let right_val = stack.pop().unwrap();
                let left_val = stack.pop().unwrap();
                if left_val.is_set_v() && right_val.is_set_v() {
                    let a = left_val.into_set_arc();
                    let b = right_val.into_set_arc();
                    if b.len() <= 4 {
                        let mut result = a;
                        let inner = Arc::make_mut(&mut result);
                        for v in b.iter() {
                            Value::set_insert(inner, v.clone());
                        }
                        stack.push(Value::from_set_arc(result));
                    } else if a.len() <= 4 {
                        let mut result = b;
                        let inner = Arc::make_mut(&mut result);
                        for v in a.iter() {
                            Value::set_insert(inner, v.clone());
                        }
                        stack.push(Value::from_set_arc(result));
                    } else {
                        stack.push(Value::set(Arc::new(sorted_vec_union(&a, &b))));
                    }
                } else {
                    return Err(type_mismatch("Set", &left_val));
                }
            }
            Op::SetDiff => {
                let right_val = stack.pop().unwrap();
                let left_val = stack.pop().unwrap();
                match (left_val.kind(), right_val.kind()) {
                    (VK::Set(a), VK::Set(b)) => {
                        stack.push(Value::set(Arc::new(sorted_vec_diff(a, b))));
                    }
                    _ => return Err(type_mismatch("Set", &left_val)),
                }
            }
            Op::SeqConcat => {
                let right_val = stack.pop().unwrap();
                let left_val = stack.pop().unwrap();
                let mut a = left_val.into_seq_arc();
                let b = right_val.into_seq_arc();
                Arc::make_mut(&mut a).extend(b.iter().cloned());
                stack.push(Value::from_seq_arc(a));
            }
            Op::SeqSlice => {
                let hi = pop_int(stack)?;
                let lo = pop_int(stack)?;
                let base_val = stack.pop().unwrap();
                match base_val.kind() {
                    VK::Seq(seq) => {
                        let start = lo.max(0) as usize;
                        let end = if hi < 0 {
                            0
                        } else {
                            (hi as usize).min(seq.len())
                        };
                        if start >= end {
                            stack.push(Value::seq(Vec::new()));
                        } else {
                            stack.push(Value::seq(seq[start..end].to_vec()));
                        }
                    }
                    _ => return Err(type_mismatch("Seq", &base_val)),
                }
            }

            Op::SeqHead => {
                let seq_val = stack.pop().unwrap();
                match seq_val.kind() {
                    VK::Seq(s) if !s.is_empty() => stack.push(s[0].clone()),
                    VK::Seq(_) => {
                        return Err(EvalError::IndexOutOfBounds {
                            index: 0,
                            length: 0,
                        })
                    }
                    _ => return Err(type_mismatch("Seq", &seq_val)),
                }
            }
            Op::SeqTail => {
                let seq_val = stack.pop().unwrap();
                match seq_val.kind() {
                    VK::Seq(s) if !s.is_empty() => stack.push(Value::seq(s[1..].to_vec())),
                    VK::Seq(_) => stack.push(Value::seq(vec![])),
                    _ => return Err(type_mismatch("Seq", &seq_val)),
                }
            }

            Op::MakeRange => {
                let hi = pop_int(stack)?;
                let lo = pop_int(stack)?;
                stack.push(Value::range(lo, hi));
            }

            // === Fallback to tree-walk ===
            Op::Fallback(idx) => {
                let expr = &fallbacks[*idx as usize];
                #[cfg(feature = "trace-fallbacks")]
                {
                    let domain_kind = match expr {
                        CompiledExpr::SetComprehension { domain, .. }
                        | CompiledExpr::Exists { domain, .. }
                        | CompiledExpr::Forall { domain, .. } => {
                            format!("dom={:?}", std::mem::discriminant(domain.as_ref()))
                        }
                        _ => String::new(),
                    };
                    eprintln!(
                        "[FALLBACK] idx={} disc={:?} {}",
                        idx,
                        std::mem::discriminant(expr),
                        domain_kind
                    );
                }
                let mut ctx = EvalContext::new(vars, next_vars, consts, params);
                ctx.locals = locals.clone();
                let result = eval(expr, &mut ctx)?;
                stack.push(result);
            }
            Op::FallbackBool(idx) => {
                let expr = &fallbacks[*idx as usize];
                #[cfg(feature = "trace-fallbacks")]
                eprintln!(
                    "[FALLBACK-BOOL] idx={} disc={:?}",
                    idx,
                    std::mem::discriminant(expr)
                );
                let mut ctx = EvalContext::new(vars, next_vars, consts, params);
                ctx.locals = locals.clone();
                let result = eval_bool(expr, &mut ctx)?;
                stack.push(Value::bool(result));
            }
            Op::FallbackInt(idx) => {
                let expr = &fallbacks[*idx as usize];
                #[cfg(feature = "trace-fallbacks")]
                eprintln!(
                    "[FALLBACK-INT] idx={} disc={:?}",
                    idx,
                    std::mem::discriminant(expr)
                );
                let mut ctx = EvalContext::new(vars, next_vars, consts, params);
                ctx.locals = locals.clone();
                let result = eval_int(expr, &mut ctx)?;
                stack.push(Value::int(result));
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
    let v = stack.pop().unwrap();
    v.as_int().ok_or_else(|| EvalError::TypeMismatch {
        expected: "Int".to_string(),
        actual: v.type_name().to_string(),
    })
}

#[inline(always)]
fn pop_bool(stack: &mut Vec<Value>) -> EvalResult<bool> {
    let v = stack.pop().unwrap();
    v.as_bool().ok_or_else(|| EvalError::TypeMismatch {
        expected: "Bool".to_string(),
        actual: v.type_name().to_string(),
    })
}

#[inline(always)]
fn peek_bool(stack: &[Value]) -> EvalResult<bool> {
    let v = stack.last().unwrap();
    v.as_bool().ok_or_else(|| EvalError::TypeMismatch {
        expected: "Bool".to_string(),
        actual: v.type_name().to_string(),
    })
}

#[inline(always)]
fn get_local_int(locals: &[Value]) -> EvalResult<i64> {
    let v = locals.last().unwrap();
    v.as_int().ok_or_else(|| EvalError::TypeMismatch {
        expected: "Int".to_string(),
        actual: v.type_name().to_string(),
    })
}

/// Normalize a domain value to a Set for iteration.
/// Handles Set (passthrough), Fn/Dict (extract keys), and IntMap (0..len indices).
#[inline]
fn normalize_domain(domain: Value) -> EvalResult<Value> {
    match domain.kind() {
        VK::Set(_) => Ok(domain),
        VK::Fn(m) => {
            let keys: Vec<Value> = m.iter().map(|(k, _)| k.clone()).collect();
            Ok(Value::set(Arc::new(keys)))
        }
        VK::IntMap(arr) => {
            let keys: Vec<Value> = (0..arr.len() as i64).map(Value::int).collect();
            Ok(Value::set(Arc::new(keys)))
        }
        VK::IntMap2(inner_size, data) => {
            let outer_size = if inner_size > 0 { data.len() / inner_size as usize } else { 0 };
            let keys: Vec<Value> = (0..outer_size as i64).map(Value::int).collect();
            Ok(Value::set(Arc::new(keys)))
        }
        _ => Err(type_mismatch("Set or Dict", &domain)),
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
        assert_eq!(result, Value::int(5));
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
        let inner0 = Value::func(Arc::new(vec![
            (Value::int(0), Value::int(10)),
            (Value::int(1), Value::int(20)),
        ]));
        let inner1 = Value::func(Arc::new(vec![
            (Value::int(0), Value::int(30)),
            (Value::int(1), Value::int(40)),
        ]));
        let dict = Value::func(Arc::new(vec![
            (Value::int(0), inner0),
            (Value::int(1), inner1),
        ]));
        let bc = compile_expr(&expr);
        let result = vm_eval(&bc, &[dict], &[], &[], &[]).unwrap();
        assert_eq!(result, Value::int(20));
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
        let inner0 = Value::func(Arc::new(vec![
            (Value::int(0), Value::int(10)),
            (Value::int(1), Value::int(20)),
        ]));
        let inner1 = Value::func(Arc::new(vec![
            (Value::int(0), Value::int(30)),
            (Value::int(1), Value::int(40)),
        ]));
        let dict = Value::func(Arc::new(vec![
            (Value::int(0), inner0),
            (Value::int(1), inner1),
        ]));
        let bc = compile_expr(&expr);
        // Should use NestedDictUpdate2 opcode
        assert!(
            bc.ops.iter().any(|op| matches!(op, Op::NestedDictUpdate2)),
            "expected NestedDictUpdate2 opcode"
        );
        let result = vm_eval(&bc, &[dict], &[], &[], &[Value::int(0), Value::int(1)]).unwrap();
        // dict[0][1] should be 99 now
        let outer = result.as_fn().unwrap();
        let inner = Value::fn_get(outer, &Value::int(0))
            .unwrap()
            .as_fn()
            .unwrap();
        assert_eq!(Value::fn_get(inner, &Value::int(1)), Some(&Value::int(99)));
        // dict[0][0] should be unchanged
        assert_eq!(Value::fn_get(inner, &Value::int(0)), Some(&Value::int(10)));
        // dict[1] should be unchanged
        let inner1 = Value::fn_get(outer, &Value::int(1))
            .unwrap()
            .as_fn()
            .unwrap();
        assert_eq!(Value::fn_get(inner1, &Value::int(0)), Some(&Value::int(30)));
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
        let innermost = Value::func(Arc::new(vec![
            (Value::int(0), Value::bool(false)),
            (Value::int(1), Value::bool(false)),
        ]));
        let middle = Value::func(Arc::new(vec![(Value::int(0), innermost)]));
        let dict = Value::func(Arc::new(vec![(Value::int(0), middle)]));
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
            &[Value::int(0), Value::int(0), Value::int(1)],
        )
        .unwrap();
        // dict[0][0][1] should be true
        let outer = result.as_fn().unwrap();
        let mid = Value::fn_get(outer, &Value::int(0))
            .unwrap()
            .as_fn()
            .unwrap();
        let inner = Value::fn_get(mid, &Value::int(0)).unwrap().as_fn().unwrap();
        assert_eq!(
            Value::fn_get(inner, &Value::int(1)),
            Some(&Value::bool(true))
        );
        // dict[0][0][0] should still be false
        assert_eq!(
            Value::fn_get(inner, &Value::int(0)),
            Some(&Value::bool(false))
        );
    }
}

//! Intermediate representation for compiled Specl specifications.

use specl_syntax::TypeExpr;
use specl_types::Type;

/// A compiled Specl specification.
#[derive(Debug, Clone)]
pub struct CompiledSpec {
    /// State variable declarations.
    pub vars: Vec<VarDecl>,
    /// Constant declarations.
    pub consts: Vec<ConstDecl>,
    /// Initial state predicate.
    pub init: CompiledExpr,
    /// Actions.
    pub actions: Vec<CompiledAction>,
    /// Invariants (checked as proof goals).
    pub invariants: Vec<CompiledInvariant>,
    /// Auxiliary invariants (assumed as hypotheses, not checked).
    pub auxiliary_invariants: Vec<CompiledInvariant>,
    /// Independence matrix for POR: independent[i][j] = true if actions i and j are independent.
    pub independent: Vec<Vec<bool>>,
    /// Refinable pairs for instance-level POR: refinable_pairs[i][j] = true iff templates i,j
    /// are template-dependent but all shared variables are accessed via keyed Dict ops on both
    /// sides, so instance-level key disjointness could make them independent.
    pub refinable_pairs: Vec<Vec<bool>>,
    /// Symmetry groups for symmetry reduction.
    pub symmetry_groups: Vec<SymmetryGroup>,
    /// View variable indices for state abstraction. When set, only these
    /// variables are included in fingerprint/dedup. None means all variables.
    pub view_variables: Option<Vec<usize>>,
}

/// Source of a Dict key access in an action, for instance-level POR.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum KeySource {
    /// Key comes from action parameter at this index.
    Param(usize),
    /// Key is a literal integer value.
    Literal(i64),
}

/// A symmetry group for symmetry reduction.
/// Variables in the same group can be permuted together.
#[derive(Debug, Clone)]
pub struct SymmetryGroup {
    /// The size of the symmetric domain (e.g., 3 for 0..2).
    pub domain_size: usize,
    /// Variable indices that use this symmetric domain as their key type.
    /// These variables are of type Fn[0..N, T] where N defines the domain.
    pub variables: Vec<usize>,
}

/// A variable declaration.
#[derive(Debug, Clone)]
pub struct VarDecl {
    /// Variable name.
    pub name: String,
    /// Variable index (for efficient lookup).
    pub index: usize,
    /// Variable type.
    pub ty: Type,
}

/// A constant declaration.
#[derive(Debug, Clone)]
pub struct ConstDecl {
    /// Constant name.
    pub name: String,
    /// Constant index.
    pub index: usize,
    /// Constant type.
    pub ty: Type,
    /// Default value for scalar constants (None if type-constrained).
    pub default_value: Option<i64>,
}

/// A compiled action.
#[derive(Debug, Clone)]
pub struct CompiledAction {
    /// Action name.
    pub name: String,
    /// Parameter names and types.
    pub params: Vec<(String, Type)>,
    /// Original type expressions for parameters (for deferred range resolution).
    pub param_type_exprs: Vec<TypeExpr>,
    /// Guard condition (conjunction of requires).
    pub guard: CompiledExpr,
    /// Effect relation.
    pub effect: CompiledExpr,
    /// Variables that may change (for frame).
    pub changes: Vec<usize>,
    /// Variables that are read (for POR).
    pub reads: Vec<usize>,
    /// Per-variable write key info for instance-level POR.
    /// (var_idx, None) = unkeyed write (full variable), always conflicts.
    /// (var_idx, Some(keys)) = writes only at these Dict keys.
    pub write_key_params: Vec<(usize, Option<Vec<KeySource>>)>,
    /// Per-variable read key info for instance-level POR.
    /// (var_idx, None) = unkeyed read, always conflicts.
    /// (var_idx, Some(keys)) = reads only at these Dict keys.
    pub read_key_params: Vec<(usize, Option<Vec<KeySource>>)>,
    /// Estimated evaluation cost of the guard expression (for action ordering).
    pub guard_cost: u32,
}

/// A compiled invariant.
#[derive(Debug, Clone)]
pub struct CompiledInvariant {
    /// Invariant name.
    pub name: String,
    /// Invariant predicate.
    pub body: CompiledExpr,
}

/// A compiled expression.
#[derive(Debug, Clone)]
pub enum CompiledExpr {
    // === Literals ===
    /// Boolean literal.
    Bool(bool),
    /// Integer literal.
    Int(i64),
    /// String literal.
    String(String),

    // === Variables ===
    /// State variable (current state).
    Var(usize),
    /// State variable (next state).
    PrimedVar(usize),
    /// Constant.
    Const(usize),
    /// Local variable (de Bruijn index).
    Local(usize),
    /// Parameter (index within action).
    Param(usize),

    // === Operations ===
    /// Binary operation.
    Binary {
        op: BinOp,
        left: Box<CompiledExpr>,
        right: Box<CompiledExpr>,
    },
    /// Unary operation.
    Unary {
        op: UnaryOp,
        operand: Box<CompiledExpr>,
    },

    // === Data structures ===
    /// Set literal.
    SetLit(Vec<CompiledExpr>),
    /// Sequence literal.
    SeqLit(Vec<CompiledExpr>),
    /// Tuple literal.
    TupleLit(Vec<CompiledExpr>),
    /// Dict literal { key: value, ... }.
    DictLit(Vec<(CompiledExpr, CompiledExpr)>),
    /// Function/map literal: fn(var in domain) => body.
    FnLit {
        domain: Box<CompiledExpr>,
        body: Box<CompiledExpr>,
    },

    // === Access ===
    /// Index into sequence or function.
    Index {
        base: Box<CompiledExpr>,
        index: Box<CompiledExpr>,
    },
    /// Slice of sequence.
    Slice {
        base: Box<CompiledExpr>,
        lo: Box<CompiledExpr>,
        hi: Box<CompiledExpr>,
    },
    /// Head of sequence (first element).
    SeqHead(Box<CompiledExpr>),
    /// Tail of sequence (all but first element).
    SeqTail(Box<CompiledExpr>),
    /// Length of sequence, set, or function.
    Len(Box<CompiledExpr>),
    /// Keys of function (domain as set).
    Keys(Box<CompiledExpr>),
    /// Values of function (range as set).
    Values(Box<CompiledExpr>),
    /// Distributed union (union of all sets in the given set).
    BigUnion(Box<CompiledExpr>),
    /// Powerset (set of all subsets).
    Powerset(Box<CompiledExpr>),
    /// Field access.
    Field {
        base: Box<CompiledExpr>,
        field: String,
    },
    /// Function/action call.
    Call {
        func: Box<CompiledExpr>,
        args: Vec<CompiledExpr>,
    },
    /// Action invocation (returns boolean).
    ActionCall {
        action_index: usize,
        args: Vec<CompiledExpr>,
    },

    // === Updates ===
    /// Record update.
    RecordUpdate {
        base: Box<CompiledExpr>,
        updates: Vec<(String, CompiledExpr)>,
    },
    /// Function update.
    FnUpdate {
        base: Box<CompiledExpr>,
        key: Box<CompiledExpr>,
        value: Box<CompiledExpr>,
    },

    // === Comprehensions ===
    /// Set comprehension.
    SetComprehension {
        element: Box<CompiledExpr>,
        domain: Box<CompiledExpr>,
        filter: Option<Box<CompiledExpr>>,
    },

    // === Quantifiers ===
    /// Universal quantifier.
    Forall {
        domain: Box<CompiledExpr>,
        body: Box<CompiledExpr>,
    },
    /// Existential quantifier.
    Exists {
        domain: Box<CompiledExpr>,
        body: Box<CompiledExpr>,
    },
    /// Fix (deterministic selection): `fix x in S: P` or `fix x: P`.
    Fix {
        domain: Option<Box<CompiledExpr>>,
        predicate: Box<CompiledExpr>,
    },

    // === Control ===
    /// Let binding.
    Let {
        value: Box<CompiledExpr>,
        body: Box<CompiledExpr>,
    },
    /// Conditional.
    If {
        cond: Box<CompiledExpr>,
        then_branch: Box<CompiledExpr>,
        else_branch: Box<CompiledExpr>,
    },

    // === Frame ===
    /// Changes operator (explicit nondeterminism).
    Changes(usize),
    /// Unchanged constraint (var' == var).
    Unchanged(usize),

    // === Enabled ===
    /// Enabled predicate for an action.
    Enabled(usize),

    // === Range ===
    /// Range expression (creates a set).
    Range {
        lo: Box<CompiledExpr>,
        hi: Box<CompiledExpr>,
    },
}

impl CompiledExpr {
    /// Shift all free Local indices up by `amount`.
    /// Used when an expression compiled in one scope is placed inside
    /// nested Let bindings that add locals before it executes.
    /// `depth` tracks how many binders we're inside (don't shift bound locals).
    pub fn shift_locals(&self, amount: usize) -> CompiledExpr {
        self.shift_locals_inner(amount, 0)
    }

    fn shift_locals_inner(&self, amount: usize, depth: usize) -> CompiledExpr {
        match self {
            CompiledExpr::Local(idx) => {
                if *idx >= depth {
                    CompiledExpr::Local(*idx + amount)
                } else {
                    self.clone()
                }
            }
            CompiledExpr::Binary { op, left, right } => CompiledExpr::Binary {
                op: *op,
                left: Box::new(left.shift_locals_inner(amount, depth)),
                right: Box::new(right.shift_locals_inner(amount, depth)),
            },
            CompiledExpr::Unary { op, operand } => CompiledExpr::Unary {
                op: *op,
                operand: Box::new(operand.shift_locals_inner(amount, depth)),
            },
            CompiledExpr::Index { base, index } => CompiledExpr::Index {
                base: Box::new(base.shift_locals_inner(amount, depth)),
                index: Box::new(index.shift_locals_inner(amount, depth)),
            },
            CompiledExpr::Slice { base, lo, hi } => CompiledExpr::Slice {
                base: Box::new(base.shift_locals_inner(amount, depth)),
                lo: Box::new(lo.shift_locals_inner(amount, depth)),
                hi: Box::new(hi.shift_locals_inner(amount, depth)),
            },
            CompiledExpr::Len(inner) => {
                CompiledExpr::Len(Box::new(inner.shift_locals_inner(amount, depth)))
            }
            CompiledExpr::If {
                cond,
                then_branch,
                else_branch,
            } => CompiledExpr::If {
                cond: Box::new(cond.shift_locals_inner(amount, depth)),
                then_branch: Box::new(then_branch.shift_locals_inner(amount, depth)),
                else_branch: Box::new(else_branch.shift_locals_inner(amount, depth)),
            },
            // Binders: increase depth by 1
            CompiledExpr::Let { value, body } => CompiledExpr::Let {
                value: Box::new(value.shift_locals_inner(amount, depth)),
                body: Box::new(body.shift_locals_inner(amount, depth + 1)),
            },
            CompiledExpr::Forall { domain, body } => CompiledExpr::Forall {
                domain: Box::new(domain.shift_locals_inner(amount, depth)),
                body: Box::new(body.shift_locals_inner(amount, depth + 1)),
            },
            CompiledExpr::Exists { domain, body } => CompiledExpr::Exists {
                domain: Box::new(domain.shift_locals_inner(amount, depth)),
                body: Box::new(body.shift_locals_inner(amount, depth + 1)),
            },
            CompiledExpr::FnLit { domain, body } => CompiledExpr::FnLit {
                domain: Box::new(domain.shift_locals_inner(amount, depth)),
                body: Box::new(body.shift_locals_inner(amount, depth + 1)),
            },
            CompiledExpr::SetComprehension {
                element,
                domain,
                filter,
            } => CompiledExpr::SetComprehension {
                element: Box::new(element.shift_locals_inner(amount, depth + 1)),
                domain: Box::new(domain.shift_locals_inner(amount, depth)),
                filter: filter
                    .as_ref()
                    .map(|f| Box::new(f.shift_locals_inner(amount, depth + 1))),
            },
            CompiledExpr::Fix { domain, predicate } => CompiledExpr::Fix {
                domain: domain
                    .as_ref()
                    .map(|d| Box::new(d.shift_locals_inner(amount, depth))),
                predicate: Box::new(predicate.shift_locals_inner(amount, depth + 1)),
            },
            CompiledExpr::Call { func, args } => CompiledExpr::Call {
                func: Box::new(func.shift_locals_inner(amount, depth)),
                args: args
                    .iter()
                    .map(|a| a.shift_locals_inner(amount, depth))
                    .collect(),
            },
            CompiledExpr::FnUpdate { base, key, value } => CompiledExpr::FnUpdate {
                base: Box::new(base.shift_locals_inner(amount, depth)),
                key: Box::new(key.shift_locals_inner(amount, depth)),
                value: Box::new(value.shift_locals_inner(amount, depth)),
            },
            CompiledExpr::SeqLit(elems) => CompiledExpr::SeqLit(
                elems
                    .iter()
                    .map(|e| e.shift_locals_inner(amount, depth))
                    .collect(),
            ),
            CompiledExpr::SetLit(elems) => CompiledExpr::SetLit(
                elems
                    .iter()
                    .map(|e| e.shift_locals_inner(amount, depth))
                    .collect(),
            ),
            CompiledExpr::TupleLit(elems) => CompiledExpr::TupleLit(
                elems
                    .iter()
                    .map(|e| e.shift_locals_inner(amount, depth))
                    .collect(),
            ),
            CompiledExpr::DictLit(pairs) => CompiledExpr::DictLit(
                pairs
                    .iter()
                    .map(|(k, v)| {
                        (
                            k.shift_locals_inner(amount, depth),
                            v.shift_locals_inner(amount, depth),
                        )
                    })
                    .collect(),
            ),
            CompiledExpr::RecordUpdate { base, updates } => CompiledExpr::RecordUpdate {
                base: Box::new(base.shift_locals_inner(amount, depth)),
                updates: updates
                    .iter()
                    .map(|(k, v)| (k.clone(), v.shift_locals_inner(amount, depth)))
                    .collect(),
            },
            CompiledExpr::Range { lo, hi } => CompiledExpr::Range {
                lo: Box::new(lo.shift_locals_inner(amount, depth)),
                hi: Box::new(hi.shift_locals_inner(amount, depth)),
            },
            CompiledExpr::SeqHead(inner) => {
                CompiledExpr::SeqHead(Box::new(inner.shift_locals_inner(amount, depth)))
            }
            CompiledExpr::SeqTail(inner) => {
                CompiledExpr::SeqTail(Box::new(inner.shift_locals_inner(amount, depth)))
            }
            CompiledExpr::Keys(inner) => {
                CompiledExpr::Keys(Box::new(inner.shift_locals_inner(amount, depth)))
            }
            CompiledExpr::Values(inner) => {
                CompiledExpr::Values(Box::new(inner.shift_locals_inner(amount, depth)))
            }
            CompiledExpr::BigUnion(inner) => {
                CompiledExpr::BigUnion(Box::new(inner.shift_locals_inner(amount, depth)))
            }
            CompiledExpr::Powerset(inner) => {
                CompiledExpr::Powerset(Box::new(inner.shift_locals_inner(amount, depth)))
            }
            CompiledExpr::Field { base, field } => CompiledExpr::Field {
                base: Box::new(base.shift_locals_inner(amount, depth)),
                field: field.clone(),
            },
            // Leaves: no locals to shift
            CompiledExpr::Bool(_)
            | CompiledExpr::Int(_)
            | CompiledExpr::String(_)
            | CompiledExpr::Var(_)
            | CompiledExpr::PrimedVar(_)
            | CompiledExpr::Const(_)
            | CompiledExpr::Param(_)
            | CompiledExpr::Changes(_)
            | CompiledExpr::Unchanged(_)
            | CompiledExpr::Enabled(_)
            | CompiledExpr::ActionCall { .. } => self.clone(),
        }
    }
}

/// Binary operator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    // Logical
    And,
    Or,
    Implies,
    Iff,
    // Comparison
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    // Arithmetic
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    // Set
    In,
    NotIn,
    Union,
    Intersect,
    Diff,
    SubsetOf,
    // Sequence
    Concat,
}

impl From<specl_syntax::BinOp> for BinOp {
    fn from(op: specl_syntax::BinOp) -> Self {
        match op {
            specl_syntax::BinOp::And => BinOp::And,
            specl_syntax::BinOp::Or => BinOp::Or,
            specl_syntax::BinOp::Implies => BinOp::Implies,
            specl_syntax::BinOp::Iff => BinOp::Iff,
            specl_syntax::BinOp::Eq => BinOp::Eq,
            specl_syntax::BinOp::Ne => BinOp::Ne,
            specl_syntax::BinOp::Lt => BinOp::Lt,
            specl_syntax::BinOp::Le => BinOp::Le,
            specl_syntax::BinOp::Gt => BinOp::Gt,
            specl_syntax::BinOp::Ge => BinOp::Ge,
            specl_syntax::BinOp::Add => BinOp::Add,
            specl_syntax::BinOp::Sub => BinOp::Sub,
            specl_syntax::BinOp::Mul => BinOp::Mul,
            specl_syntax::BinOp::Div => BinOp::Div,
            specl_syntax::BinOp::Mod => BinOp::Mod,
            specl_syntax::BinOp::In => BinOp::In,
            specl_syntax::BinOp::NotIn => BinOp::NotIn,
            specl_syntax::BinOp::Union => BinOp::Union,
            specl_syntax::BinOp::Intersect => BinOp::Intersect,
            specl_syntax::BinOp::Diff => BinOp::Diff,
            specl_syntax::BinOp::SubsetOf => BinOp::SubsetOf,
            specl_syntax::BinOp::Concat => BinOp::Concat,
        }
    }
}

/// Unary operator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Not,
    Neg,
}

impl From<specl_syntax::UnaryOp> for UnaryOp {
    fn from(op: specl_syntax::UnaryOp) -> Self {
        match op {
            specl_syntax::UnaryOp::Not => UnaryOp::Not,
            specl_syntax::UnaryOp::Neg => UnaryOp::Neg,
        }
    }
}

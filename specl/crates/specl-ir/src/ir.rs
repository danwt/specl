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
    /// Invariants.
    pub invariants: Vec<CompiledInvariant>,
    /// Independence matrix for POR: independent[i][j] = true if actions i and j are independent.
    pub independent: Vec<Vec<bool>>,
    /// Symmetry groups for symmetry reduction.
    pub symmetry_groups: Vec<SymmetryGroup>,
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
    /// Choose (deterministic selection).
    Choose {
        domain: Box<CompiledExpr>,
        predicate: Box<CompiledExpr>,
    },
    /// Fix (deterministic selection without domain).
    Fix { predicate: Box<CompiledExpr> },

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

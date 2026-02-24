//! Transition system types — generic, zero specl dependencies.

use serde::{Deserialize, Serialize};

/// A generic transition system specification.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct TransitionSystem {
    /// Specification name.
    pub name: String,
    /// State variable declarations.
    pub variables: Vec<TsVariable>,
    /// Constant declarations.
    pub constants: Vec<TsConstant>,
    /// Initial state: explicit assignment for every variable.
    pub init: Vec<TsAssignment>,
    /// Actions (guarded transitions).
    pub actions: Vec<TsAction>,
    /// Invariants (checked as proof goals).
    pub invariants: Vec<TsInvariant>,
    /// Auxiliary invariants (assumed as hypotheses, not checked).
    #[serde(default)]
    pub auxiliary_invariants: Vec<TsInvariant>,
    /// View variable indices for state abstraction (None = all variables).
    #[serde(default)]
    pub view_variables: Option<Vec<usize>>,
}

/// A state variable declaration.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct TsVariable {
    pub name: String,
    pub ty: TsType,
}

/// A constant declaration.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct TsConstant {
    pub name: String,
    pub ty: TsType,
    #[serde(default)]
    pub default_value: Option<i64>,
}

/// An action (guarded transition).
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct TsAction {
    pub name: String,
    /// Parameters with typed finite domains.
    #[serde(default)]
    pub params: Vec<TsParam>,
    /// Guard: boolean expression over current state.
    pub guard: TsExpr,
    /// Assignments: only listed variables change; all others are implicitly unchanged.
    pub assignments: Vec<TsAssignment>,
}

/// An assignment: `variables[var_idx] := value`.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct TsAssignment {
    pub var_idx: usize,
    pub value: TsExpr,
}

/// An action parameter.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct TsParam {
    pub name: String,
    pub ty: TsType,
}

/// An invariant.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct TsInvariant {
    pub name: String,
    pub body: TsExpr,
}

/// Types — maps 1:1 to `specl_types::Type`.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
#[serde(tag = "kind")]
pub enum TsType {
    Bool,
    Nat,
    Int,
    String,
    Range {
        lo: i64,
        hi: i64,
    },
    Set {
        element: Box<TsType>,
    },
    Seq {
        element: Box<TsType>,
    },
    Map {
        key: Box<TsType>,
        value: Box<TsType>,
    },
    Option {
        inner: Box<TsType>,
    },
}

/// Expressions — subset of `CompiledExpr` without PrimedVar/Unchanged/Changes/Enabled.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(tag = "kind")]
pub enum TsExpr {
    // Literals
    Bool {
        value: bool,
    },
    Int {
        value: i64,
    },
    Str {
        value: String,
    },

    // Variable references (by index)
    Var {
        index: usize,
    },
    Const {
        index: usize,
    },
    Local {
        index: usize,
    },
    Param {
        index: usize,
    },

    // Operators
    Binary {
        op: TsBinOp,
        left: Box<TsExpr>,
        right: Box<TsExpr>,
    },
    Unary {
        op: TsUnaryOp,
        operand: Box<TsExpr>,
    },

    // Collections
    SetLit {
        elements: Vec<TsExpr>,
    },
    SeqLit {
        elements: Vec<TsExpr>,
    },
    DictLit {
        entries: Vec<(TsExpr, TsExpr)>,
    },
    FnLit {
        domain: Box<TsExpr>,
        body: Box<TsExpr>,
    },
    MapUpdate {
        base: Box<TsExpr>,
        key: Box<TsExpr>,
        value: Box<TsExpr>,
    },

    // Access
    Index {
        base: Box<TsExpr>,
        index: Box<TsExpr>,
    },
    Slice {
        base: Box<TsExpr>,
        lo: Box<TsExpr>,
        hi: Box<TsExpr>,
    },
    Field {
        base: Box<TsExpr>,
        field: String,
    },
    Len {
        expr: Box<TsExpr>,
    },
    Keys {
        expr: Box<TsExpr>,
    },
    Values {
        expr: Box<TsExpr>,
    },
    SeqHead {
        expr: Box<TsExpr>,
    },
    SeqTail {
        expr: Box<TsExpr>,
    },

    // Comprehensions
    SetComprehension {
        element: Box<TsExpr>,
        domain: Box<TsExpr>,
        filter: Option<Box<TsExpr>>,
    },

    // Quantifiers
    Forall {
        domain: Box<TsExpr>,
        body: Box<TsExpr>,
    },
    Exists {
        domain: Box<TsExpr>,
        body: Box<TsExpr>,
    },

    // Control
    Let {
        value: Box<TsExpr>,
        body: Box<TsExpr>,
    },
    If {
        cond: Box<TsExpr>,
        then_branch: Box<TsExpr>,
        else_branch: Box<TsExpr>,
    },

    // Range
    Range {
        lo: Box<TsExpr>,
        hi: Box<TsExpr>,
    },
}

/// Binary operators — same as `specl_ir::BinOp`.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
pub enum TsBinOp {
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

/// Unary operators.
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
pub enum TsUnaryOp {
    Not,
    Neg,
}

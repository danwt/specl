//! Abstract Syntax Tree for the Specl specification language.

use crate::token::Span;

/// A Specl module (top-level compilation unit).
#[derive(Debug, Clone)]
pub struct Module {
    /// Module name.
    pub name: Ident,
    /// Module declarations.
    pub decls: Vec<Decl>,
    /// Span covering the entire module.
    pub span: Span,
}

/// An identifier with its source span.
#[derive(Debug, Clone)]
pub struct Ident {
    /// The identifier name.
    pub name: String,
    /// Source span.
    pub span: Span,
}

impl Ident {
    pub fn new(name: impl Into<String>, span: Span) -> Self {
        Self {
            name: name.into(),
            span,
        }
    }
}

/// A top-level declaration.
#[derive(Debug, Clone)]
pub enum Decl {
    /// `use ModuleName`
    Use(UseDecl),
    /// `const NAME: Type`
    Const(ConstDecl),
    /// `var NAME: Type`
    Var(VarDecl),
    /// `type NAME = Type`
    Type(TypeDecl),
    /// `func NAME(params) { expr }`
    Func(FuncDecl),
    /// `init { ... }`
    Init(InitDecl),
    /// `action NAME(...) { ... }`
    Action(ActionDecl),
    /// `invariant NAME { ... }`
    Invariant(InvariantDecl),
    /// `property NAME { ... }`
    Property(PropertyDecl),
    /// `fairness { ... }`
    Fairness(FairnessDecl),
}

impl Decl {
    pub fn span(&self) -> Span {
        match self {
            Decl::Use(d) => d.span,
            Decl::Const(d) => d.span,
            Decl::Var(d) => d.span,
            Decl::Type(d) => d.span,
            Decl::Func(d) => d.span,
            Decl::Init(d) => d.span,
            Decl::Action(d) => d.span,
            Decl::Invariant(d) => d.span,
            Decl::Property(d) => d.span,
            Decl::Fairness(d) => d.span,
        }
    }
}

/// `use ModuleName`
#[derive(Debug, Clone)]
pub struct UseDecl {
    pub module: Ident,
    pub span: Span,
}

/// The value of a constant declaration.
#[derive(Debug, Clone)]
pub enum ConstValue {
    /// Type constraint: `const X: 0..10` - value provided at runtime via --constant
    Type(TypeExpr),
    /// Scalar value: `const X: 3` - fixed value
    Scalar(i64),
}

/// `const NAME: Type` or `const NAME: value`
#[derive(Debug, Clone)]
pub struct ConstDecl {
    pub name: Ident,
    pub value: ConstValue,
    pub span: Span,
}

/// `var NAME: Type`
#[derive(Debug, Clone)]
pub struct VarDecl {
    pub name: Ident,
    pub ty: TypeExpr,
    pub span: Span,
}

/// `type NAME = Type`
#[derive(Debug, Clone)]
pub struct TypeDecl {
    pub name: Ident,
    pub ty: TypeExpr,
    pub span: Span,
}

/// `func NAME(params) { body }`
/// User-defined helper function for reuse (like TLA+ operator definitions).
/// Functions are pure and are inlined at call sites during compilation.
#[derive(Debug, Clone)]
pub struct FuncDecl {
    pub name: Ident,
    pub params: Vec<FuncParam>,
    pub body: Expr,
    pub span: Span,
}

/// A function parameter (untyped - types are inferred).
#[derive(Debug, Clone)]
pub struct FuncParam {
    pub name: Ident,
    pub span: Span,
}

/// `init { expr }`
#[derive(Debug, Clone)]
pub struct InitDecl {
    pub body: Expr,
    pub span: Span,
}

/// `action NAME(params) { body }`
#[derive(Debug, Clone)]
pub struct ActionDecl {
    pub name: Ident,
    pub params: Vec<Param>,
    pub body: ActionBody,
    pub span: Span,
}

/// Action body with requires and effects.
#[derive(Debug, Clone)]
pub struct ActionBody {
    /// Guard conditions (`require expr`).
    pub requires: Vec<Expr>,
    /// Effect expression (state transition relation).
    pub effect: Option<Expr>,
    pub span: Span,
}

/// A parameter declaration.
#[derive(Debug, Clone)]
pub struct Param {
    pub name: Ident,
    pub ty: TypeExpr,
    pub span: Span,
}

/// `invariant NAME { expr }`
#[derive(Debug, Clone)]
pub struct InvariantDecl {
    pub name: Ident,
    pub body: Expr,
    pub span: Span,
}

/// `property NAME { expr }`
#[derive(Debug, Clone)]
pub struct PropertyDecl {
    pub name: Ident,
    pub body: Expr,
    pub span: Span,
}

/// `fairness { constraints }`
#[derive(Debug, Clone)]
pub struct FairnessDecl {
    pub constraints: Vec<FairnessConstraint>,
    pub span: Span,
}

/// A fairness constraint.
#[derive(Debug, Clone)]
pub struct FairnessConstraint {
    pub kind: FairnessKind,
    pub action: Ident,
    pub span: Span,
}

/// Kind of fairness constraint.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FairnessKind {
    Weak,
    Strong,
}

/// A type expression.
#[derive(Debug, Clone)]
pub enum TypeExpr {
    /// Named type (e.g., `Nat`, `AccountId`).
    Named(Ident),
    /// Set type `Set[T]`.
    Set(Box<TypeExpr>, Span),
    /// Sequence type `Seq[T]`.
    Seq(Box<TypeExpr>, Span),
    /// Dict type `dict[K, V]`.
    Dict(Box<TypeExpr>, Box<TypeExpr>, Span),
    /// Option type `Option[T]`.
    Option(Box<TypeExpr>, Span),
    /// Range type `lo..hi`.
    Range(Box<Expr>, Box<Expr>, Span),
    /// Tuple type `(T1, T2, ...)`.
    Tuple(Vec<TypeExpr>, Span),
}

impl TypeExpr {
    pub fn span(&self) -> Span {
        match self {
            TypeExpr::Named(id) => id.span,
            TypeExpr::Set(_, span) => *span,
            TypeExpr::Seq(_, span) => *span,
            TypeExpr::Dict(_, _, span) => *span,
            TypeExpr::Option(_, span) => *span,
            TypeExpr::Range(_, _, span) => *span,
            TypeExpr::Tuple(_, span) => *span,
        }
    }
}

/// An expression.
#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

impl Expr {
    pub fn new(kind: ExprKind, span: Span) -> Self {
        Self { kind, span }
    }
}

/// The kind of expression.
#[derive(Debug, Clone)]
pub enum ExprKind {
    /// Boolean literal.
    Bool(bool),
    /// Integer literal.
    Int(i64),
    /// String literal.
    String(String),
    /// Identifier.
    Ident(String),
    /// Primed identifier (next-state variable).
    Primed(String),

    /// Binary operation.
    Binary {
        op: BinOp,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    /// Unary operation.
    Unary { op: UnaryOp, operand: Box<Expr> },

    /// Function/set/sequence indexing `e[i]`.
    Index { base: Box<Expr>, index: Box<Expr> },
    /// Sequence slicing `e[lo..hi]`.
    Slice {
        base: Box<Expr>,
        lo: Box<Expr>,
        hi: Box<Expr>,
    },
    /// Field access `e.field`.
    Field { base: Box<Expr>, field: Ident },
    /// Function call `f(args)`.
    Call { func: Box<Expr>, args: Vec<Expr> },

    /// Set literal `{ a, b, c }` or empty `{}`.
    SetLit(Vec<Expr>),
    /// Sequence literal `[a, b, c]` or empty `[]`.
    SeqLit(Vec<Expr>),
    /// Tuple literal `(a, b, c)`.
    TupleLit(Vec<Expr>),
    /// Dict literal `{ key: value, ... }` where keys are expressions.
    DictLit(Vec<(Expr, Expr)>),
    /// Function literal `fn(x in S) => e`.
    FnLit {
        var: Ident,
        domain: Box<Expr>,
        body: Box<Expr>,
    },

    /// Set comprehension `{ e for x in S }` or `{ x in S if P }` or `{ e for x in S if P }`.
    SetComprehension {
        element: Box<Expr>,
        var: Ident,
        domain: Box<Expr>,
        filter: Option<Box<Expr>>,
    },

    /// Record update `e with { field: value, ... }`.
    RecordUpdate {
        base: Box<Expr>,
        updates: Vec<RecordFieldUpdate>,
    },

    /// Quantifier `forall x in S: P` or `exists x in S: P`.
    Quantifier {
        kind: QuantifierKind,
        bindings: Vec<Binding>,
        body: Box<Expr>,
    },
    /// Choose `choose x in S: P`.
    Choose {
        var: Ident,
        domain: Box<Expr>,
        predicate: Box<Expr>,
    },
    /// Fix `fix x: P` - picks an arbitrary value satisfying P (used for CHOOSE without domain).
    Fix { var: Ident, predicate: Box<Expr> },

    /// Let binding `let x = e1 in e2`.
    Let {
        var: Ident,
        value: Box<Expr>,
        body: Box<Expr>,
    },
    /// Conditional `if c then t else f`.
    If {
        cond: Box<Expr>,
        then_branch: Box<Expr>,
        else_branch: Box<Expr>,
    },

    /// Require statement (in action body).
    Require(Box<Expr>),
    /// Changes operator (explicit nondeterminism).
    Changes(Ident),
    /// Enabled predicate `enabled(Action)`.
    Enabled(Ident),

    /// Sequence head `head(seq)` - get first element.
    SeqHead(Box<Expr>),
    /// Sequence tail `tail(seq)` - get all but first element.
    SeqTail(Box<Expr>),
    /// Length `len(x)` - get length of sequence, set, or function.
    Len(Box<Expr>),
    /// Function keys `keys(f)` - get domain of function as set.
    Keys(Box<Expr>),
    /// Function values `values(f)` - get range of function as set.
    Values(Box<Expr>),
    /// Distributed union `union_all(S)` - union of all sets in S.
    BigUnion(Box<Expr>),
    /// Powerset `powerset(S)` - set of all subsets of S.
    Powerset(Box<Expr>),

    /// Temporal: `always P`.
    Always(Box<Expr>),
    /// Temporal: `eventually P`.
    Eventually(Box<Expr>),
    /// Temporal: `P leads_to Q`.
    LeadsTo { left: Box<Expr>, right: Box<Expr> },

    /// Range expression `lo..hi` (as value, not type).
    Range { lo: Box<Expr>, hi: Box<Expr> },

    /// Parenthesized expression (for preserving source).
    Paren(Box<Expr>),
}

/// A record field update.
#[derive(Debug, Clone)]
pub enum RecordFieldUpdate {
    /// Simple field update `field: value`.
    Field { name: Ident, value: Expr },
    /// Dynamic key update `[key]: value`.
    Dynamic { key: Expr, value: Expr },
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

impl BinOp {
    /// Get the precedence of this operator (higher = binds tighter).
    pub fn precedence(self) -> u8 {
        match self {
            BinOp::Iff => 1,
            BinOp::Implies => 2,
            BinOp::Or => 3,
            BinOp::And => 4,
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => 5,
            BinOp::In | BinOp::NotIn | BinOp::SubsetOf => 5,
            BinOp::Union | BinOp::Diff | BinOp::Concat => 6,
            BinOp::Add | BinOp::Sub => 6,
            BinOp::Intersect => 7,
            BinOp::Mul | BinOp::Div | BinOp::Mod => 7,
        }
    }

    /// Check if this operator is right-associative.
    pub fn is_right_assoc(self) -> bool {
        matches!(self, BinOp::Implies | BinOp::Iff)
    }
}

/// Unary operator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Not,
    Neg,
}

/// Quantifier kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuantifierKind {
    Forall,
    Exists,
}

/// A variable binding `x in S`.
#[derive(Debug, Clone)]
pub struct Binding {
    pub var: Ident,
    pub domain: Expr,
    pub span: Span,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_binop_precedence() {
        // Multiplication binds tighter than addition
        assert!(BinOp::Mul.precedence() > BinOp::Add.precedence());
        // Addition binds tighter than comparison
        assert!(BinOp::Add.precedence() > BinOp::Eq.precedence());
        // Comparison binds tighter than and
        assert!(BinOp::Eq.precedence() > BinOp::And.precedence());
        // And binds tighter than or
        assert!(BinOp::And.precedence() > BinOp::Or.precedence());
        // Or binds tighter than implies
        assert!(BinOp::Or.precedence() > BinOp::Implies.precedence());
    }
}

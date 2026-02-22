//! TLA+ Abstract Syntax Tree.

use crate::token::Span;

/// A TLA+ module.
#[derive(Debug, Clone)]
pub struct TlaModule {
    /// Module name.
    pub name: String,
    /// Extended modules.
    pub extends: Vec<String>,
    /// Module declarations.
    pub declarations: Vec<TlaDecl>,
    /// Source span.
    pub span: Span,
}

/// An identifier with its source span.
#[derive(Debug, Clone)]
pub struct TlaIdent {
    pub name: String,
    pub span: Span,
}

impl TlaIdent {
    pub fn new(name: impl Into<String>, span: Span) -> Self {
        Self {
            name: name.into(),
            span,
        }
    }
}

/// A TLA+ declaration.
#[derive(Debug, Clone)]
pub enum TlaDecl {
    /// CONSTANT declarations.
    Constant { names: Vec<TlaIdent>, span: Span },
    /// VARIABLE declarations.
    Variable { names: Vec<TlaIdent>, span: Span },
    /// Operator definition: Name(params) == body
    Operator {
        name: TlaIdent,
        params: Vec<TlaIdent>,
        body: TlaExpr,
        span: Span,
    },
    /// INSTANCE substitution.
    Instance {
        name: Option<TlaIdent>,
        module: TlaIdent,
        substitutions: Vec<(TlaIdent, TlaExpr)>,
        span: Span,
    },
    /// ASSUME assertion.
    Assume { expr: TlaExpr, span: Span },
    /// THEOREM declaration.
    Theorem {
        name: Option<TlaIdent>,
        expr: TlaExpr,
        span: Span,
    },
}

impl TlaDecl {
    pub fn span(&self) -> Span {
        match self {
            TlaDecl::Constant { span, .. } => *span,
            TlaDecl::Variable { span, .. } => *span,
            TlaDecl::Operator { span, .. } => *span,
            TlaDecl::Instance { span, .. } => *span,
            TlaDecl::Assume { span, .. } => *span,
            TlaDecl::Theorem { span, .. } => *span,
        }
    }
}

/// A TLA+ expression.
#[derive(Debug, Clone)]
pub struct TlaExpr {
    pub kind: TlaExprKind,
    pub span: Span,
}

impl TlaExpr {
    pub fn new(kind: TlaExprKind, span: Span) -> Self {
        Self { kind, span }
    }
}

/// The kind of a TLA+ expression.
#[derive(Debug, Clone)]
pub enum TlaExprKind {
    // === Literals ===
    /// Boolean literal.
    Bool(bool),
    /// Integer literal.
    Int(i64),
    /// String literal.
    String(String),

    // === Variables ===
    /// Identifier.
    Ident(String),
    /// Primed expression: e'.
    Primed(Box<TlaExpr>),

    // === Operators ===
    /// Binary operation.
    Binary {
        op: TlaBinOp,
        left: Box<TlaExpr>,
        right: Box<TlaExpr>,
    },
    /// Unary operation.
    Unary {
        op: TlaUnaryOp,
        operand: Box<TlaExpr>,
    },
    /// Instance operator access: Instance!Operator(args).
    InstanceOp {
        instance: Box<TlaExpr>,
        name: TlaIdent,
        args: Vec<TlaExpr>,
    },

    // === Quantifiers ===
    /// Universal quantifier: \A vars: body.
    Forall {
        bindings: Vec<TlaBinding>,
        body: Box<TlaExpr>,
    },
    /// Existential quantifier: \E vars: body.
    Exists {
        bindings: Vec<TlaBinding>,
        body: Box<TlaExpr>,
    },
    /// CHOOSE: CHOOSE x \in S: P or CHOOSE x: P (domain is optional).
    Choose {
        var: TlaIdent,
        domain: Option<Box<TlaExpr>>,
        predicate: Box<TlaExpr>,
    },

    // === Functions ===
    /// Function definition: [x \in S |-> e].
    FunctionDef {
        var: TlaIdent,
        domain: Box<TlaExpr>,
        body: Box<TlaExpr>,
    },
    /// Function set: [S -> T] (set of all functions from S to T).
    FunctionSet {
        domain: Box<TlaExpr>,
        range: Box<TlaExpr>,
    },
    /// Function application: f[x] or f[x, y].
    FunctionApp {
        func: Box<TlaExpr>,
        args: Vec<TlaExpr>,
    },
    /// Operator application: Op(args).
    OpApp { name: String, args: Vec<TlaExpr> },
    /// EXCEPT: [f EXCEPT ![k] = v, ...].
    Except {
        base: Box<TlaExpr>,
        updates: Vec<TlaExceptUpdate>,
    },
    /// @ (old value reference in EXCEPT).
    ExceptAt,
    /// Function combination: f @@ g (merge two functions, g takes precedence).
    FunctionCombine {
        left: Box<TlaExpr>,
        right: Box<TlaExpr>,
    },
    /// Singleton function: k :> v (creates function mapping k to v).
    SingletonFunction {
        key: Box<TlaExpr>,
        value: Box<TlaExpr>,
    },

    // === Sets ===
    /// Set enumeration: {a, b, c}.
    SetEnum { elements: Vec<TlaExpr> },
    /// Set comprehension: {e: x \in S} (map form).
    SetMap {
        element: Box<TlaExpr>,
        var: TlaIdent,
        domain: Box<TlaExpr>,
    },
    /// Set filter: {x \in S: P(x)}.
    SetFilter {
        var: TlaIdent,
        domain: Box<TlaExpr>,
        predicate: Box<TlaExpr>,
    },

    // === Sequences/Tuples ===
    /// Tuple/sequence: <<a, b, c>>.
    Tuple { elements: Vec<TlaExpr> },

    // === Records ===
    /// Record constructor: [a |-> e1, b |-> e2].
    Record { fields: Vec<(TlaIdent, TlaExpr)> },
    /// Record set: [a: S, b: T] (set of records).
    RecordSet { fields: Vec<(TlaIdent, TlaExpr)> },
    /// Record/function field access: r.field.
    FieldAccess { base: Box<TlaExpr>, field: TlaIdent },

    // === Control ===
    /// IF-THEN-ELSE.
    IfThenElse {
        cond: Box<TlaExpr>,
        then_branch: Box<TlaExpr>,
        else_branch: Box<TlaExpr>,
    },
    /// CASE expression.
    Case {
        arms: Vec<(TlaExpr, TlaExpr)>,
        other: Option<Box<TlaExpr>>,
    },
    /// LET-IN.
    LetIn {
        defs: Vec<TlaLetDef>,
        body: Box<TlaExpr>,
    },

    // === Temporal ===
    /// Always: []P.
    Always(Box<TlaExpr>),
    /// Eventually: <>P.
    Eventually(Box<TlaExpr>),
    /// Leads-to: P ~> Q.
    LeadsTo {
        left: Box<TlaExpr>,
        right: Box<TlaExpr>,
    },
    /// Box action: [A]_v.
    BoxAction {
        action: Box<TlaExpr>,
        vars: Box<TlaExpr>,
    },
    /// Angle action: <A>_v.
    AngleAction {
        action: Box<TlaExpr>,
        vars: Box<TlaExpr>,
    },
    /// Weak fairness: WF_v(A).
    WeakFairness {
        vars: Box<TlaExpr>,
        action: Box<TlaExpr>,
    },
    /// Strong fairness: SF_v(A).
    StrongFairness {
        vars: Box<TlaExpr>,
        action: Box<TlaExpr>,
    },

    // === Action operators ===
    /// ENABLED: ENABLED A.
    Enabled(Box<TlaExpr>),
    /// UNCHANGED: UNCHANGED <<vars>> or UNCHANGED var.
    Unchanged(Vec<TlaIdent>),

    // === Special ===
    /// DOMAIN f.
    Domain(Box<TlaExpr>),
    /// SUBSET S (power set).
    PowerSet(Box<TlaExpr>),
    /// UNION S (distributed union).
    BigUnion(Box<TlaExpr>),
    /// Range: lo..hi.
    Range { lo: Box<TlaExpr>, hi: Box<TlaExpr> },
    /// Parenthesized expression.
    Paren(Box<TlaExpr>),
}

/// A binding in a quantifier.
#[derive(Debug, Clone)]
pub struct TlaBinding {
    pub var: TlaIdent,
    pub domain: TlaExpr,
    pub span: Span,
}

/// An update in an EXCEPT expression.
#[derive(Debug, Clone)]
pub struct TlaExceptUpdate {
    /// The path of keys: ![k1][k2]...
    pub path: Vec<TlaExpr>,
    /// The new value.
    pub value: TlaExpr,
    pub span: Span,
}

/// A definition in a LET-IN expression.
#[derive(Debug, Clone)]
pub struct TlaLetDef {
    pub name: TlaIdent,
    /// Parameters for operator-style definitions: Name(a, b) == ...
    pub params: Vec<TlaIdent>,
    /// For recursive function definitions: Name[var \in Domain] == ...
    /// Contains the bound variable and its domain.
    pub recursive_binding: Option<TlaBinding>,
    pub body: TlaExpr,
    pub span: Span,
}

/// TLA+ binary operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TlaBinOp {
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
    Exp, // ^

    // Set
    In,
    NotIn,
    Cup,     // \cup (union)
    Cap,     // \cap (intersection)
    SetDiff, // \ (set difference)
    SubsetEq,
    Times, // \times (cartesian product)

    // Sequence
    Concat, // \o
}

impl TlaBinOp {
    /// Get the precedence of this operator (higher = binds tighter).
    pub fn precedence(self) -> u8 {
        match self {
            TlaBinOp::Iff => 1,
            TlaBinOp::Implies => 2,
            TlaBinOp::Or => 3,
            TlaBinOp::And => 4,
            TlaBinOp::Eq
            | TlaBinOp::Ne
            | TlaBinOp::Lt
            | TlaBinOp::Le
            | TlaBinOp::Gt
            | TlaBinOp::Ge
            | TlaBinOp::In
            | TlaBinOp::NotIn
            | TlaBinOp::SubsetEq => 5,
            TlaBinOp::Cup | TlaBinOp::Cap | TlaBinOp::SetDiff | TlaBinOp::Times => 6,
            TlaBinOp::Add | TlaBinOp::Sub | TlaBinOp::Concat => 7,
            TlaBinOp::Mul | TlaBinOp::Div | TlaBinOp::Mod => 8,
            TlaBinOp::Exp => 9,
        }
    }

    /// Check if this operator is right-associative.
    pub fn is_right_assoc(self) -> bool {
        matches!(self, TlaBinOp::Implies | TlaBinOp::Exp)
    }
}

/// TLA+ unary operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TlaUnaryOp {
    Not,
    Neg,
}

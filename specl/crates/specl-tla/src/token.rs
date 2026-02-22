//! TLA+ tokens and spans.

use std::fmt;

/// A span in the source code.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    pub fn merge(self, other: Span) -> Span {
        Span {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }
}

/// A token with its kind and span.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

impl Token {
    pub fn new(kind: TokenKind, span: Span) -> Self {
        Self { kind, span }
    }
}

/// The kind of a TLA+ token.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenKind {
    // === Module structure ===
    /// ---- (module delimiter start)
    ModuleStart,
    /// ==== (module delimiter end)
    ModuleEnd,

    // === Keywords ===
    Module,
    Extends,
    Constant,
    Constants,
    Variable,
    Variables,
    Assume,
    Axiom,
    Theorem,
    Lemma,
    Proposition,
    Corollary,
    Local,
    Instance,
    With,
    Let,
    In,
    If,
    Then,
    Else,
    Case,
    Other,
    Choose,
    Enabled,
    Unchanged,
    Except,
    Subset,    // SUBSET (power set)
    Union,     // UNION (distributed union)
    Domain,    // DOMAIN
    Boolean,   // BOOLEAN
    Recursive, // RECURSIVE

    // === Logical operators ===
    /// /\ (and)
    And,
    /// \/ (or)
    Or,
    /// ~ (not)
    Not,
    /// => (implies)
    Implies,
    /// <=> (iff)
    Iff,
    /// TRUE
    True,
    /// FALSE
    False,

    // === Quantifiers ===
    /// \A (forall)
    Forall,
    /// \E (exists)
    Exists,

    // === Temporal operators ===
    /// [] (always/box)
    Always,
    /// <> (eventually/diamond)
    Eventually,
    /// ~> (leads-to)
    LeadsTo,
    /// -+-> (leads-to variant)
    LeadsToArrow,
    /// WF_ (weak fairness)
    WeakFairness,
    /// SF_ (strong fairness)
    StrongFairness,

    // === Set operators ===
    /// \in (member)
    SetIn,
    /// \notin (not member)
    SetNotIn,
    /// \cup (union)
    Cup,
    /// \cap (intersection)
    Cap,
    /// \ (set difference)
    SetMinus,
    /// \subseteq (subset)
    SubsetEq,
    /// \times (cartesian product)
    Times,

    // === Comparison ===
    /// =
    Eq,
    /// # or /=
    Neq,
    /// <
    Lt,
    /// <=
    Le,
    /// >
    Gt,
    /// >=
    Ge,
    /// -> (function set)
    Arrow,
    /// <- (substitution in INSTANCE)
    LeftArrow,

    // === Arithmetic ===
    /// +
    Plus,
    /// -
    Minus,
    /// *
    Star,
    /// /
    Slash,
    /// \div (integer division)
    Div,
    /// %
    Percent,
    /// ^ (power)
    Caret,
    /// ..
    DotDot,

    // === Sequence operators ===
    /// \o (concatenation)
    Concat,

    // === Punctuation ===
    /// (
    LParen,
    /// )
    RParen,
    /// [
    LBracket,
    /// ]
    RBracket,
    /// {
    LBrace,
    /// }
    RBrace,
    /// <<
    LAngle,
    /// >>
    RAngle,
    /// ,
    Comma,
    /// :
    Colon,
    /// ::
    ColonColon,
    /// ;
    Semi,
    /// .
    Dot,
    /// !
    Bang,
    /// @
    At,
    /// @@
    AtAt,
    /// :>
    ColonGt,
    /// _
    Underscore,

    // === Definition and assignment ===
    /// ==
    DefEq,
    /// |->
    MapsTo,
    /// '
    Prime,

    // === Literals ===
    /// Integer literal
    Int(i64),
    /// String literal
    String(String),
    /// Identifier
    Ident(String),

    // === Special ===
    /// End of file
    Eof,
    /// Error token
    Error(String),
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TokenKind::ModuleStart => write!(f, "----"),
            TokenKind::ModuleEnd => write!(f, "===="),
            TokenKind::Module => write!(f, "MODULE"),
            TokenKind::Extends => write!(f, "EXTENDS"),
            TokenKind::Constant => write!(f, "CONSTANT"),
            TokenKind::Constants => write!(f, "CONSTANTS"),
            TokenKind::Variable => write!(f, "VARIABLE"),
            TokenKind::Variables => write!(f, "VARIABLES"),
            TokenKind::Assume => write!(f, "ASSUME"),
            TokenKind::Axiom => write!(f, "AXIOM"),
            TokenKind::Theorem => write!(f, "THEOREM"),
            TokenKind::Lemma => write!(f, "LEMMA"),
            TokenKind::Proposition => write!(f, "PROPOSITION"),
            TokenKind::Corollary => write!(f, "COROLLARY"),
            TokenKind::Local => write!(f, "LOCAL"),
            TokenKind::Instance => write!(f, "INSTANCE"),
            TokenKind::With => write!(f, "WITH"),
            TokenKind::Let => write!(f, "LET"),
            TokenKind::In => write!(f, "IN"),
            TokenKind::If => write!(f, "IF"),
            TokenKind::Then => write!(f, "THEN"),
            TokenKind::Else => write!(f, "ELSE"),
            TokenKind::Case => write!(f, "CASE"),
            TokenKind::Other => write!(f, "OTHER"),
            TokenKind::Choose => write!(f, "CHOOSE"),
            TokenKind::Enabled => write!(f, "ENABLED"),
            TokenKind::Unchanged => write!(f, "UNCHANGED"),
            TokenKind::Except => write!(f, "EXCEPT"),
            TokenKind::Subset => write!(f, "SUBSET"),
            TokenKind::Union => write!(f, "UNION"),
            TokenKind::Domain => write!(f, "DOMAIN"),
            TokenKind::Boolean => write!(f, "BOOLEAN"),
            TokenKind::Recursive => write!(f, "RECURSIVE"),
            TokenKind::And => write!(f, "/\\"),
            TokenKind::Or => write!(f, "\\/"),
            TokenKind::Not => write!(f, "~"),
            TokenKind::Implies => write!(f, "=>"),
            TokenKind::Iff => write!(f, "<=>"),
            TokenKind::True => write!(f, "TRUE"),
            TokenKind::False => write!(f, "FALSE"),
            TokenKind::Forall => write!(f, "\\A"),
            TokenKind::Exists => write!(f, "\\E"),
            TokenKind::Always => write!(f, "[]"),
            TokenKind::Eventually => write!(f, "<>"),
            TokenKind::LeadsTo => write!(f, "~>"),
            TokenKind::LeadsToArrow => write!(f, "-+->"),
            TokenKind::WeakFairness => write!(f, "WF_"),
            TokenKind::StrongFairness => write!(f, "SF_"),
            TokenKind::SetIn => write!(f, "\\in"),
            TokenKind::SetNotIn => write!(f, "\\notin"),
            TokenKind::Cup => write!(f, "\\cup"),
            TokenKind::Cap => write!(f, "\\cap"),
            TokenKind::SetMinus => write!(f, "\\"),
            TokenKind::SubsetEq => write!(f, "\\subseteq"),
            TokenKind::Times => write!(f, "\\times"),
            TokenKind::Eq => write!(f, "="),
            TokenKind::Neq => write!(f, "#"),
            TokenKind::Lt => write!(f, "<"),
            TokenKind::Le => write!(f, "<="),
            TokenKind::Gt => write!(f, ">"),
            TokenKind::Ge => write!(f, ">="),
            TokenKind::Arrow => write!(f, "->"),
            TokenKind::LeftArrow => write!(f, "<-"),
            TokenKind::Plus => write!(f, "+"),
            TokenKind::Minus => write!(f, "-"),
            TokenKind::Star => write!(f, "*"),
            TokenKind::Slash => write!(f, "/"),
            TokenKind::Div => write!(f, "\\div"),
            TokenKind::Percent => write!(f, "%"),
            TokenKind::Caret => write!(f, "^"),
            TokenKind::DotDot => write!(f, ".."),
            TokenKind::Concat => write!(f, "\\o"),
            TokenKind::LParen => write!(f, "("),
            TokenKind::RParen => write!(f, ")"),
            TokenKind::LBracket => write!(f, "["),
            TokenKind::RBracket => write!(f, "]"),
            TokenKind::LBrace => write!(f, "{{"),
            TokenKind::RBrace => write!(f, "}}"),
            TokenKind::LAngle => write!(f, "<<"),
            TokenKind::RAngle => write!(f, ">>"),
            TokenKind::Comma => write!(f, ","),
            TokenKind::Colon => write!(f, ":"),
            TokenKind::ColonColon => write!(f, "::"),
            TokenKind::Semi => write!(f, ";"),
            TokenKind::Dot => write!(f, "."),
            TokenKind::Bang => write!(f, "!"),
            TokenKind::At => write!(f, "@"),
            TokenKind::AtAt => write!(f, "@@"),
            TokenKind::ColonGt => write!(f, ":>"),
            TokenKind::Underscore => write!(f, "_"),
            TokenKind::DefEq => write!(f, "=="),
            TokenKind::MapsTo => write!(f, "|->"),
            TokenKind::Prime => write!(f, "'"),
            TokenKind::Int(n) => write!(f, "{}", n),
            TokenKind::String(s) => write!(f, "\"{}\"", s),
            TokenKind::Ident(s) => write!(f, "{}", s),
            TokenKind::Eof => write!(f, "EOF"),
            TokenKind::Error(msg) => write!(f, "ERROR: {}", msg),
        }
    }
}

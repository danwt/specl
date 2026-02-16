//! Token types and source span tracking for the Specl lexer.

use std::fmt;

/// A span in the source code, tracking byte offsets and line/column.
#[derive(Clone, Copy, PartialEq, Eq, Default)]
pub struct Span {
    /// Start byte offset (inclusive).
    pub start: usize,
    /// End byte offset (exclusive).
    pub end: usize,
    /// Line number (1-indexed).
    pub line: u32,
    /// Column number (1-indexed, in characters not bytes).
    pub column: u32,
}

impl Span {
    /// Create a new span.
    pub fn new(start: usize, end: usize, line: u32, column: u32) -> Self {
        Self {
            start,
            end,
            line,
            column,
        }
    }

    /// Create a dummy span for generated code.
    pub fn dummy() -> Self {
        Self::default()
    }

    /// Merge two spans into one that covers both.
    pub fn merge(self, other: Self) -> Self {
        Self {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
            line: self.line.min(other.line),
            column: if self.line <= other.line {
                self.column
            } else {
                other.column
            },
        }
    }

    /// Length in bytes.
    pub fn len(&self) -> usize {
        self.end - self.start
    }

    /// Check if span is empty.
    pub fn is_empty(&self) -> bool {
        self.start == self.end
    }
}

impl fmt::Debug for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.column)
    }
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.column)
    }
}

/// The kind of token.
#[derive(Clone, Debug, PartialEq)]
pub enum TokenKind {
    // === Keywords ===
    /// `module`
    Module,
    /// `use`
    Use,
    /// `const`
    Const,
    /// `var`
    Var,
    /// `type`
    Type,
    /// `init`
    Init,
    /// `action`
    Action,
    /// `invariant`
    Invariant,
    /// `property`
    Property,
    /// `fairness`
    Fairness,
    /// `func` - user-defined helper function
    Func,
    /// `view` - state abstraction for dedup
    View,

    // === Logical keywords ===
    /// `and`
    And,
    /// `or`
    Or,
    /// `not`
    Not,
    /// `implies`
    Implies,
    /// `iff`
    Iff,

    // === Quantifiers ===
    /// `all` (universal quantifier, Python-like)
    All,
    /// `any` (existential quantifier, Python-like)
    Any,
    /// `choose` (deterministic selection)
    Choose,

    // === Control flow ===
    /// `in`
    In,
    /// `for`
    For,
    /// `if`
    If,
    /// `then`
    Then,
    /// `else`
    Else,
    /// `let`
    Let,
    /// `with`
    With,
    /// `require`
    Require,

    // === Frame keywords ===
    /// `changes`
    Changes,

    // === Temporal keywords ===
    /// `always`
    Always,
    /// `eventually`
    Eventually,
    /// `leads_to`
    LeadsTo,
    /// `enabled`
    Enabled,

    // === Fairness keywords ===
    /// `weak_fair`
    WeakFair,
    /// `strong_fair`
    StrongFair,

    // === Boolean literals ===
    /// `true`
    True,
    /// `false`
    False,

    // === Built-in types ===
    /// `Nat`
    Nat,
    /// `Int`
    Int,
    /// `Bool`
    Bool,
    /// `String`
    String_,
    /// `Set`
    Set,
    /// `Seq`
    Seq,
    /// `dict` - Python-like dictionary type (lowercase only)
    Dict,
    /// `Option`
    Option_,
    /// `Some`
    Some_,
    /// `None`
    None_,

    // === Punctuation ===
    /// `(`
    LParen,
    /// `)`
    RParen,
    /// `{`
    LBrace,
    /// `}`
    RBrace,
    /// `[`
    LBracket,
    /// `]`
    RBracket,
    /// `,`
    Comma,
    /// `:`
    Colon,
    /// `;`
    Semicolon,
    /// `.`
    Dot,
    /// `..`
    DotDot,
    /// `->`
    Arrow,
    /// `=>`
    FatArrow,
    /// `'` (prime for next-state variables)
    Prime,
    /// `|`
    Pipe,

    // === Comparison operators ===
    /// `==`
    Eq,
    /// `!=`
    Ne,
    /// `<`
    Lt,
    /// `<=`
    Le,
    /// `>`
    Gt,
    /// `>=`
    Ge,

    // === Arithmetic operators ===
    /// `+`
    Plus,
    /// `-`
    Minus,
    /// `*`
    Star,
    /// `/`
    Slash,
    /// `%`
    Percent,

    // === Set operators ===
    /// `union`
    Union,
    /// `intersect`
    Intersect,
    /// `diff`
    Diff,
    /// `subset_of`
    SubsetOf,

    // === Sequence operators ===
    /// `++`
    PlusPlus,
    /// `head` - get first element of sequence
    Head,
    /// `tail` - get all but first element of sequence
    Tail,
    /// `len` - get length of sequence/set/function
    Len,

    // === Function/Map operators ===
    /// `keys` - get domain of function as set
    Keys,
    /// `values` - get range of function as set
    Values,
    /// `powerset` - get set of all subsets
    Powerset,
    /// `union_all` - distributed union (union of all sets in set)
    UnionAll,

    // === Other operators ===
    /// `&`
    Ampersand,
    /// `=`
    Assign,

    // === Literals ===
    /// Integer literal
    Integer(i64),
    /// String literal (without quotes)
    StringLit(std::string::String),
    /// Identifier
    Ident(std::string::String),

    // === Comments ===
    /// Single-line comment `// ...`
    Comment(std::string::String),
    /// Documentation comment `/// ...`
    DocComment(std::string::String),

    // === Special ===
    /// End of file
    Eof,
    /// Lexer error
    Error(std::string::String),
}

impl TokenKind {
    /// Check if this token is a keyword.
    pub fn is_keyword(&self) -> bool {
        matches!(
            self,
            TokenKind::Module
                | TokenKind::Use
                | TokenKind::Const
                | TokenKind::Var
                | TokenKind::Type
                | TokenKind::Init
                | TokenKind::Action
                | TokenKind::Invariant
                | TokenKind::Property
                | TokenKind::Fairness
                | TokenKind::Func
                | TokenKind::View
                | TokenKind::And
                | TokenKind::Or
                | TokenKind::Not
                | TokenKind::Implies
                | TokenKind::Iff
                | TokenKind::All
                | TokenKind::Any
                | TokenKind::Choose
                | TokenKind::In
                | TokenKind::For
                | TokenKind::If
                | TokenKind::Then
                | TokenKind::Else
                | TokenKind::Let
                | TokenKind::With
                | TokenKind::Require
                | TokenKind::Changes
                | TokenKind::Always
                | TokenKind::Eventually
                | TokenKind::LeadsTo
                | TokenKind::Enabled
                | TokenKind::WeakFair
                | TokenKind::StrongFair
                | TokenKind::True
                | TokenKind::False
                | TokenKind::Nat
                | TokenKind::Int
                | TokenKind::Bool
                | TokenKind::String_
                | TokenKind::Set
                | TokenKind::Seq
                | TokenKind::Dict
                | TokenKind::Option_
                | TokenKind::Some_
                | TokenKind::None_
                | TokenKind::Union
                | TokenKind::Intersect
                | TokenKind::Diff
                | TokenKind::SubsetOf
                | TokenKind::Head
                | TokenKind::Tail
                | TokenKind::Len
                | TokenKind::Keys
                | TokenKind::Values
                | TokenKind::Powerset
                | TokenKind::UnionAll
        )
    }

    /// Get the keyword for a given identifier, if any.
    pub fn keyword(ident: &str) -> Option<TokenKind> {
        Some(match ident {
            "module" => TokenKind::Module,
            "use" => TokenKind::Use,
            "const" => TokenKind::Const,
            "var" => TokenKind::Var,
            "type" => TokenKind::Type,
            "init" => TokenKind::Init,
            "action" => TokenKind::Action,
            "invariant" => TokenKind::Invariant,
            "property" => TokenKind::Property,
            "fairness" => TokenKind::Fairness,
            "func" => TokenKind::Func,
            "view" => TokenKind::View,
            "and" => TokenKind::And,
            "or" => TokenKind::Or,
            "not" => TokenKind::Not,
            "implies" => TokenKind::Implies,
            "iff" => TokenKind::Iff,
            "all" => TokenKind::All,
            "any" => TokenKind::Any,
            "fix" => TokenKind::Choose,
            "in" => TokenKind::In,
            "for" => TokenKind::For,
            "if" => TokenKind::If,
            "then" => TokenKind::Then,
            "else" => TokenKind::Else,
            "let" => TokenKind::Let,
            "with" => TokenKind::With,
            "require" => TokenKind::Require,
            "changes" => TokenKind::Changes,
            "always" => TokenKind::Always,
            "eventually" => TokenKind::Eventually,
            "leads_to" => TokenKind::LeadsTo,
            "enabled" => TokenKind::Enabled,
            "weak_fair" => TokenKind::WeakFair,
            "strong_fair" => TokenKind::StrongFair,
            "true" => TokenKind::True,
            "false" => TokenKind::False,
            "Nat" => TokenKind::Nat,
            "Int" => TokenKind::Int,
            "Bool" => TokenKind::Bool,
            "String" => TokenKind::String_,
            "Set" => TokenKind::Set,
            "Seq" => TokenKind::Seq,
            "Dict" => TokenKind::Dict,
            "Option" => TokenKind::Option_,
            "Some" => TokenKind::Some_,
            "None" => TokenKind::None_,
            "union" => TokenKind::Union,
            "intersect" => TokenKind::Intersect,
            "diff" => TokenKind::Diff,
            "subset_of" => TokenKind::SubsetOf,
            "head" => TokenKind::Head,
            "tail" => TokenKind::Tail,
            "len" => TokenKind::Len,
            "keys" => TokenKind::Keys,
            "values" => TokenKind::Values,
            "powerset" => TokenKind::Powerset,
            "union_all" => TokenKind::UnionAll,
            _ => return None,
        })
    }

    /// Check if this is a trivia token (comment, whitespace).
    pub fn is_trivia(&self) -> bool {
        matches!(self, TokenKind::Comment(_) | TokenKind::DocComment(_))
    }
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TokenKind::Module => write!(f, "module"),
            TokenKind::Use => write!(f, "use"),
            TokenKind::Const => write!(f, "const"),
            TokenKind::Var => write!(f, "var"),
            TokenKind::Type => write!(f, "type"),
            TokenKind::Init => write!(f, "init"),
            TokenKind::Action => write!(f, "action"),
            TokenKind::Invariant => write!(f, "invariant"),
            TokenKind::Property => write!(f, "property"),
            TokenKind::Fairness => write!(f, "fairness"),
            TokenKind::Func => write!(f, "func"),
            TokenKind::View => write!(f, "view"),
            TokenKind::And => write!(f, "and"),
            TokenKind::Or => write!(f, "or"),
            TokenKind::Not => write!(f, "not"),
            TokenKind::Implies => write!(f, "implies"),
            TokenKind::Iff => write!(f, "iff"),
            TokenKind::All => write!(f, "all"),
            TokenKind::Any => write!(f, "any"),
            TokenKind::Choose => write!(f, "choose"),
            TokenKind::In => write!(f, "in"),
            TokenKind::For => write!(f, "for"),
            TokenKind::If => write!(f, "if"),
            TokenKind::Then => write!(f, "then"),
            TokenKind::Else => write!(f, "else"),
            TokenKind::Let => write!(f, "let"),
            TokenKind::With => write!(f, "with"),
            TokenKind::Require => write!(f, "require"),
            TokenKind::Changes => write!(f, "changes"),
            TokenKind::Always => write!(f, "always"),
            TokenKind::Eventually => write!(f, "eventually"),
            TokenKind::LeadsTo => write!(f, "leads_to"),
            TokenKind::Enabled => write!(f, "enabled"),
            TokenKind::WeakFair => write!(f, "weak_fair"),
            TokenKind::StrongFair => write!(f, "strong_fair"),
            TokenKind::True => write!(f, "true"),
            TokenKind::False => write!(f, "false"),
            TokenKind::Nat => write!(f, "Nat"),
            TokenKind::Int => write!(f, "Int"),
            TokenKind::Bool => write!(f, "Bool"),
            TokenKind::String_ => write!(f, "String"),
            TokenKind::Set => write!(f, "Set"),
            TokenKind::Seq => write!(f, "Seq"),
            TokenKind::Dict => write!(f, "Dict"),
            TokenKind::Option_ => write!(f, "Option"),
            TokenKind::Some_ => write!(f, "Some"),
            TokenKind::None_ => write!(f, "None"),
            TokenKind::LParen => write!(f, "("),
            TokenKind::RParen => write!(f, ")"),
            TokenKind::LBrace => write!(f, "{{"),
            TokenKind::RBrace => write!(f, "}}"),
            TokenKind::LBracket => write!(f, "["),
            TokenKind::RBracket => write!(f, "]"),
            TokenKind::Comma => write!(f, ","),
            TokenKind::Colon => write!(f, ":"),
            TokenKind::Semicolon => write!(f, ";"),
            TokenKind::Dot => write!(f, "."),
            TokenKind::DotDot => write!(f, ".."),
            TokenKind::Arrow => write!(f, "->"),
            TokenKind::FatArrow => write!(f, "=>"),
            TokenKind::Prime => write!(f, "'"),
            TokenKind::Pipe => write!(f, "|"),
            TokenKind::Eq => write!(f, "=="),
            TokenKind::Ne => write!(f, "!="),
            TokenKind::Lt => write!(f, "<"),
            TokenKind::Le => write!(f, "<="),
            TokenKind::Gt => write!(f, ">"),
            TokenKind::Ge => write!(f, ">="),
            TokenKind::Plus => write!(f, "+"),
            TokenKind::Minus => write!(f, "-"),
            TokenKind::Star => write!(f, "*"),
            TokenKind::Slash => write!(f, "/"),
            TokenKind::Percent => write!(f, "%"),
            TokenKind::Union => write!(f, "union"),
            TokenKind::Intersect => write!(f, "intersect"),
            TokenKind::Diff => write!(f, "diff"),
            TokenKind::SubsetOf => write!(f, "subset_of"),
            TokenKind::PlusPlus => write!(f, "++"),
            TokenKind::Head => write!(f, "head"),
            TokenKind::Tail => write!(f, "tail"),
            TokenKind::Len => write!(f, "len"),
            TokenKind::Keys => write!(f, "keys"),
            TokenKind::Values => write!(f, "values"),
            TokenKind::Powerset => write!(f, "powerset"),
            TokenKind::UnionAll => write!(f, "union_all"),
            TokenKind::Ampersand => write!(f, "&"),
            TokenKind::Assign => write!(f, "="),
            TokenKind::Integer(n) => write!(f, "{}", n),
            TokenKind::StringLit(s) => write!(f, "\"{}\"", s),
            TokenKind::Ident(s) => write!(f, "{}", s),
            TokenKind::Comment(s) => write!(f, "// {}", s),
            TokenKind::DocComment(s) => write!(f, "/// {}", s),
            TokenKind::Eof => write!(f, "EOF"),
            TokenKind::Error(msg) => write!(f, "ERROR: {}", msg),
        }
    }
}

/// A token with its span in the source code.
#[derive(Clone, Debug, PartialEq)]
pub struct Token {
    /// The kind of token.
    pub kind: TokenKind,
    /// The span in the source code.
    pub span: Span,
}

impl Token {
    /// Create a new token.
    pub fn new(kind: TokenKind, span: Span) -> Self {
        Self { kind, span }
    }

    /// Check if this is the end of file.
    pub fn is_eof(&self) -> bool {
        matches!(self.kind, TokenKind::Eof)
    }

    /// Check if this is an error token.
    pub fn is_error(&self) -> bool {
        matches!(self.kind, TokenKind::Error(_))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_span_merge() {
        let s1 = Span::new(0, 5, 1, 1);
        let s2 = Span::new(10, 15, 1, 11);
        let merged = s1.merge(s2);
        assert_eq!(merged.start, 0);
        assert_eq!(merged.end, 15);
    }

    #[test]
    fn test_keyword_lookup() {
        assert_eq!(TokenKind::keyword("module"), Some(TokenKind::Module));
        assert_eq!(TokenKind::keyword("and"), Some(TokenKind::And));
        assert_eq!(TokenKind::keyword("Nat"), Some(TokenKind::Nat));
        assert_eq!(TokenKind::keyword("foo"), None);
    }

    #[test]
    fn test_is_keyword() {
        assert!(TokenKind::Module.is_keyword());
        assert!(TokenKind::And.is_keyword());
        assert!(!TokenKind::LParen.is_keyword());
        assert!(!TokenKind::Integer(42).is_keyword());
    }
}

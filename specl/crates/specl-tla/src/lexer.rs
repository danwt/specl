//! TLA+ lexer.

use crate::token::{Span, Token, TokenKind};

/// TLA+ lexer.
pub struct Lexer<'a> {
    _source: &'a str,
    chars: std::iter::Peekable<std::str::CharIndices<'a>>,
    position: usize,
}

impl<'a> Lexer<'a> {
    /// Create a new lexer for the given source.
    pub fn new(source: &'a str) -> Self {
        Self {
            _source: source,
            chars: source.char_indices().peekable(),
            position: 0,
        }
    }

    /// Tokenize the entire source.
    pub fn tokenize(mut self) -> Vec<Token> {
        let mut tokens = Vec::new();
        loop {
            let token = self.next_token();
            let is_eof = token.kind == TokenKind::Eof;
            tokens.push(token);
            if is_eof {
                break;
            }
        }
        tokens
    }

    /// Get the next token.
    pub fn next_token(&mut self) -> Token {
        self.skip_whitespace_and_comments();

        let start = self.position;

        let Some((_, c)) = self.advance() else {
            return Token::new(TokenKind::Eof, Span::new(start, start));
        };

        let kind = match c {
            // Module delimiters
            '-' => self.lex_minus_or_module_start(start),
            '=' => self.lex_equals(start),

            // Operators that start with /
            '/' => self.lex_slash(),

            // Backslash operators
            '\\' => self.lex_backslash(),

            // Angle brackets and temporal
            '<' => self.lex_less_than(),
            '>' => self.lex_greater_than(),

            // Square brackets
            '[' => self.lex_lbracket(),
            ']' => TokenKind::RBracket,

            // Curly braces
            '{' => TokenKind::LBrace,
            '}' => TokenKind::RBrace,

            // Parentheses
            '(' => self.lex_lparen(),
            ')' => TokenKind::RParen,

            // Other operators
            '~' => self.lex_tilde(),
            '|' => self.lex_pipe(),
            '+' => TokenKind::Plus,
            '*' => TokenKind::Star,
            '%' => TokenKind::Percent,
            '^' => TokenKind::Caret,
            '#' => TokenKind::Neq,
            '\'' => TokenKind::Prime,
            ',' => TokenKind::Comma,
            ':' => {
                if self.peek() == Some('>') {
                    self.advance();
                    TokenKind::ColonGt
                } else if self.peek() == Some(':') {
                    self.advance();
                    TokenKind::ColonColon
                } else {
                    TokenKind::Colon
                }
            }
            ';' => TokenKind::Semi,
            '.' => self.lex_dot(),
            '!' => TokenKind::Bang,
            '@' => {
                if self.peek() == Some('@') {
                    self.advance();
                    TokenKind::AtAt
                } else {
                    TokenKind::At
                }
            }
            '_' => {
                // Check if this is the start of an identifier (e.g., _SendNoRestriction)
                if let Some(next) = self.peek() {
                    if next.is_alphanumeric() {
                        self.lex_ident('_')
                    } else {
                        TokenKind::Underscore
                    }
                } else {
                    TokenKind::Underscore
                }
            }

            // String literals
            '"' => self.lex_string(),

            // Numbers
            c if c.is_ascii_digit() => self.lex_number(c),

            // Identifiers and keywords
            c if c.is_alphabetic() || c == '_' => self.lex_ident(c),

            _ => TokenKind::Error(format!("unexpected character: {}", c)),
        };

        let end = self.position;
        Token::new(kind, Span::new(start, end))
    }

    fn advance(&mut self) -> Option<(usize, char)> {
        let result = self.chars.next();
        if let Some((pos, c)) = result {
            self.position = pos + c.len_utf8();
        }
        result
    }

    fn peek(&mut self) -> Option<char> {
        self.chars.peek().map(|(_, c)| *c)
    }

    fn skip_whitespace_and_comments(&mut self) {
        loop {
            match self.peek() {
                Some(' ' | '\t' | '\n' | '\r') => {
                    self.advance();
                }
                Some('\\') => {
                    // Check for \* line comment
                    let saved_pos = self.position;
                    let saved_chars = self.chars.clone();
                    self.advance(); // consume \
                    if self.peek() == Some('*') {
                        self.advance(); // consume *
                                        // Skip to end of line
                        while let Some(c) = self.peek() {
                            if c == '\n' {
                                break;
                            }
                            self.advance();
                        }
                    } else {
                        // Not a comment, restore position
                        self.position = saved_pos;
                        self.chars = saved_chars;
                        break;
                    }
                }
                Some('(') => {
                    // Check for (* block comment *)
                    let saved_pos = self.position;
                    let saved_chars = self.chars.clone();
                    self.advance(); // consume (
                    if self.peek() == Some('*') {
                        self.advance(); // consume *
                                        // Skip until *)
                        loop {
                            match self.advance() {
                                Some((_, '*')) => {
                                    if self.peek() == Some(')') {
                                        self.advance();
                                        break;
                                    }
                                }
                                Some(_) => continue,
                                None => break, // Unclosed comment
                            }
                        }
                    } else {
                        // Not a comment, restore position
                        self.position = saved_pos;
                        self.chars = saved_chars;
                        break;
                    }
                }
                _ => break,
            }
        }
    }

    fn lex_minus_or_module_start(&mut self, _start: usize) -> TokenKind {
        // Check for -> (function set arrow)
        if self.peek() == Some('>') {
            self.advance();
            return TokenKind::Arrow;
        }

        // Check for -+-> (leads-to arrow)
        if self.peek() == Some('+') {
            self.advance(); // +
            if self.peek() == Some('-') {
                self.advance(); // -
                if self.peek() == Some('>') {
                    self.advance(); // >
                    return TokenKind::LeadsToArrow;
                }
            }
            return TokenKind::Error("unexpected sequence after -+".into());
        }

        // Count consecutive dashes
        let mut dash_count = 1;
        while self.peek() == Some('-') {
            self.advance();
            dash_count += 1;
        }

        if dash_count >= 4 {
            TokenKind::ModuleStart
        } else {
            TokenKind::Minus
        }
    }

    fn lex_equals(&mut self, _start: usize) -> TokenKind {
        match self.peek() {
            Some('=') => {
                self.advance();
                // Check for ==== (module end)
                let mut eq_count = 2;
                while self.peek() == Some('=') {
                    self.advance();
                    eq_count += 1;
                }
                if eq_count >= 4 {
                    TokenKind::ModuleEnd
                } else {
                    TokenKind::DefEq
                }
            }
            Some('<') => {
                // Accept legacy ASCII variant "=<" as "<=".
                self.advance();
                TokenKind::Le
            }
            Some('>') => {
                self.advance();
                TokenKind::Implies
            }
            _ => TokenKind::Eq,
        }
    }

    fn lex_slash(&mut self) -> TokenKind {
        match self.peek() {
            Some('\\') => {
                self.advance();
                TokenKind::And
            }
            Some('=') => {
                self.advance();
                TokenKind::Neq
            }
            _ => TokenKind::Slash,
        }
    }

    fn lex_backslash(&mut self) -> TokenKind {
        // Check for backslash operators

        // Collect identifier after backslash
        let mut ident = String::new();
        while let Some(c) = self.peek() {
            if c.is_alphabetic() {
                ident.push(c);
                self.advance();
            } else {
                break;
            }
        }

        match ident.as_str() {
            "A" | "forall" => TokenKind::Forall,
            "E" | "exists" => TokenKind::Exists,
            "in" => TokenKind::SetIn,
            "notin" => TokenKind::SetNotIn,
            "cup" | "union" => TokenKind::Cup,
            "div" => TokenKind::Div,
            "cap" | "intersect" => TokenKind::Cap,
            "subseteq" => TokenKind::SubsetEq,
            "subset" => TokenKind::SubsetEq, // Some specs use \subset for \subseteq
            "leq" => TokenKind::Le,
            "geq" => TokenKind::Ge,
            "neg" | "lnot" => TokenKind::Not,
            "land" => TokenKind::And,
            "lor" => TokenKind::Or,
            "times" => TokenKind::Times,
            "X" => TokenKind::Times, // \X is also cartesian product
            "o" => TokenKind::Concat,
            // Comparison operators (treated as regular comparisons)
            "prec" => TokenKind::Lt, // lexicographic less-than
            "succ" => TokenKind::Gt, // lexicographic greater-than
            "preceq" => TokenKind::Le,
            "succeq" => TokenKind::Ge,
            // Set/sequence operators
            "oplus" => TokenKind::Cup, // sometimes used for disjoint union
            "ominus" => TokenKind::SetMinus,
            "circ" => TokenKind::Concat, // function composition
            "/" => {
                // \/ (or)
                TokenKind::Or
            }
            "" => {
                // Just a backslash - check for \/
                if self.peek() == Some('/') {
                    self.advance();
                    TokenKind::Or
                } else {
                    TokenKind::SetMinus
                }
            }
            _ => TokenKind::Error(format!("unknown backslash operator: \\{}", ident)),
        }
    }

    fn lex_less_than(&mut self) -> TokenKind {
        match self.peek() {
            Some('<') => {
                self.advance();
                TokenKind::LAngle
            }
            Some('-') => {
                self.advance();
                TokenKind::LeftArrow // <- for INSTANCE substitutions
            }
            Some('=') => {
                self.advance();
                if self.peek() == Some('>') {
                    self.advance();
                    TokenKind::Iff
                } else {
                    TokenKind::Le
                }
            }
            Some('>') => {
                self.advance();
                TokenKind::Eventually
            }
            _ => TokenKind::Lt,
        }
    }

    fn lex_greater_than(&mut self) -> TokenKind {
        match self.peek() {
            Some('>') => {
                self.advance();
                TokenKind::RAngle
            }
            Some('=') => {
                self.advance();
                TokenKind::Ge
            }
            _ => TokenKind::Gt,
        }
    }

    fn lex_lbracket(&mut self) -> TokenKind {
        // Check for [] (always/box operator)
        if self.peek() == Some(']') {
            self.advance();
            TokenKind::Always
        } else {
            TokenKind::LBracket
        }
    }

    fn lex_lparen(&mut self) -> TokenKind {
        // We already checked for (* comments in skip_whitespace_and_comments
        TokenKind::LParen
    }

    fn lex_tilde(&mut self) -> TokenKind {
        if self.peek() == Some('>') {
            self.advance();
            TokenKind::LeadsTo
        } else {
            TokenKind::Not
        }
    }

    fn lex_pipe(&mut self) -> TokenKind {
        if self.peek() == Some('-') {
            self.advance();
            if self.peek() == Some('>') {
                self.advance();
                TokenKind::MapsTo
            } else {
                TokenKind::Error("expected -> after |-".into())
            }
        } else {
            TokenKind::Error("unexpected |".into())
        }
    }

    fn lex_dot(&mut self) -> TokenKind {
        if self.peek() == Some('.') {
            self.advance();
            TokenKind::DotDot
        } else {
            TokenKind::Dot
        }
    }

    fn lex_string(&mut self) -> TokenKind {
        let mut s = String::new();
        loop {
            match self.advance() {
                Some((_, '"')) => break,
                Some((_, '\\')) => match self.advance() {
                    Some((_, 'n')) => s.push('\n'),
                    Some((_, 't')) => s.push('\t'),
                    Some((_, 'r')) => s.push('\r'),
                    Some((_, '\\')) => s.push('\\'),
                    Some((_, '"')) => s.push('"'),
                    Some((_, c)) => return TokenKind::Error(format!("unknown escape: \\{}", c)),
                    None => return TokenKind::Error("unterminated string".into()),
                },
                Some((_, c)) => s.push(c),
                None => return TokenKind::Error("unterminated string".into()),
            }
        }
        TokenKind::String(s)
    }

    fn lex_number(&mut self, first: char) -> TokenKind {
        let mut s = String::new();
        s.push(first);

        while let Some(c) = self.peek() {
            if c.is_ascii_digit() {
                s.push(c);
                self.advance();
            } else {
                break;
            }
        }

        match s.parse::<i64>() {
            Ok(n) => TokenKind::Int(n),
            Err(_) => TokenKind::Error(format!("invalid number: {}", s)),
        }
    }

    fn lex_ident(&mut self, first: char) -> TokenKind {
        let mut s = String::new();
        s.push(first);

        while let Some(c) = self.peek() {
            if c.is_alphanumeric() || c == '_' {
                s.push(c);
                self.advance();
            } else {
                break;
            }
        }

        // Check for keywords
        match s.as_str() {
            "MODULE" => TokenKind::Module,
            "EXTENDS" => TokenKind::Extends,
            "CONSTANT" => TokenKind::Constant,
            "CONSTANTS" => TokenKind::Constants,
            "VARIABLE" => TokenKind::Variable,
            "VARIABLES" => TokenKind::Variables,
            "ASSUME" => TokenKind::Assume,
            "AXIOM" => TokenKind::Axiom,
            "THEOREM" => TokenKind::Theorem,
            "LEMMA" => TokenKind::Lemma,
            "PROPOSITION" => TokenKind::Proposition,
            "COROLLARY" => TokenKind::Corollary,
            "LOCAL" => TokenKind::Local,
            "INSTANCE" => TokenKind::Instance,
            "WITH" => TokenKind::With,
            "LET" => TokenKind::Let,
            "IN" => TokenKind::In,
            "IF" => TokenKind::If,
            "THEN" => TokenKind::Then,
            "ELSE" => TokenKind::Else,
            "CASE" => TokenKind::Case,
            "OTHER" => TokenKind::Other,
            "CHOOSE" => TokenKind::Choose,
            "ENABLED" => TokenKind::Enabled,
            "UNCHANGED" => TokenKind::Unchanged,
            "EXCEPT" => TokenKind::Except,
            "SUBSET" => TokenKind::Subset,
            "UNION" => TokenKind::Union,
            "DOMAIN" => TokenKind::Domain,
            "BOOLEAN" => TokenKind::Boolean,
            "RECURSIVE" => TokenKind::Recursive,
            "TRUE" => TokenKind::True,
            "FALSE" => TokenKind::False,
            "WF_" => TokenKind::WeakFairness,
            "SF_" => TokenKind::StrongFairness,
            _ => TokenKind::Ident(s),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lex(input: &str) -> Vec<TokenKind> {
        Lexer::new(input)
            .tokenize()
            .into_iter()
            .map(|t| t.kind)
            .filter(|k| *k != TokenKind::Eof)
            .collect()
    }

    #[test]
    fn test_module_delimiters() {
        assert_eq!(
            lex("---- MODULE"),
            vec![TokenKind::ModuleStart, TokenKind::Module]
        );
        assert_eq!(lex("===="), vec![TokenKind::ModuleEnd]);
        assert_eq!(lex("--------"), vec![TokenKind::ModuleStart]);
    }

    #[test]
    fn test_logical_operators() {
        assert_eq!(lex("/\\"), vec![TokenKind::And]);
        assert_eq!(lex("\\/"), vec![TokenKind::Or]);
        assert_eq!(lex("~"), vec![TokenKind::Not]);
        assert_eq!(lex("=>"), vec![TokenKind::Implies]);
        assert_eq!(lex("<=>"), vec![TokenKind::Iff]);
    }

    #[test]
    fn test_quantifiers() {
        assert_eq!(lex("\\A"), vec![TokenKind::Forall]);
        assert_eq!(lex("\\E"), vec![TokenKind::Exists]);
    }

    #[test]
    fn test_set_operators() {
        assert_eq!(lex("\\in"), vec![TokenKind::SetIn]);
        assert_eq!(lex("\\notin"), vec![TokenKind::SetNotIn]);
        assert_eq!(lex("\\cup"), vec![TokenKind::Cup]);
        assert_eq!(lex("\\cap"), vec![TokenKind::Cap]);
        assert_eq!(lex("\\subseteq"), vec![TokenKind::SubsetEq]);
        assert_eq!(lex("\\times"), vec![TokenKind::Times]);
    }

    #[test]
    fn test_temporal_operators() {
        assert_eq!(lex("[]"), vec![TokenKind::Always]);
        assert_eq!(lex("<>"), vec![TokenKind::Eventually]);
        assert_eq!(lex("~>"), vec![TokenKind::LeadsTo]);
    }

    #[test]
    fn test_comparison() {
        assert_eq!(
            lex("= # < <= =< > >="),
            vec![
                TokenKind::Eq,
                TokenKind::Neq,
                TokenKind::Lt,
                TokenKind::Le,
                TokenKind::Le,
                TokenKind::Gt,
                TokenKind::Ge,
            ]
        );
    }

    #[test]
    fn test_punctuation() {
        assert_eq!(
            lex("( ) [ ] { } << >>"),
            vec![
                TokenKind::LParen,
                TokenKind::RParen,
                TokenKind::LBracket,
                TokenKind::RBracket,
                TokenKind::LBrace,
                TokenKind::RBrace,
                TokenKind::LAngle,
                TokenKind::RAngle,
            ]
        );
    }

    #[test]
    fn test_definition() {
        assert_eq!(lex("== |->"), vec![TokenKind::DefEq, TokenKind::MapsTo]);
    }

    #[test]
    fn test_literals() {
        assert_eq!(lex("42"), vec![TokenKind::Int(42)]);
        assert_eq!(lex("\"hello\""), vec![TokenKind::String("hello".into())]);
    }

    #[test]
    fn test_identifiers_and_keywords() {
        assert_eq!(lex("foo"), vec![TokenKind::Ident("foo".into())]);
        assert_eq!(lex("Init"), vec![TokenKind::Ident("Init".into())]);
        assert_eq!(lex("VARIABLE"), vec![TokenKind::Variable]);
        assert_eq!(lex("TRUE FALSE"), vec![TokenKind::True, TokenKind::False]);
    }

    #[test]
    fn test_prime() {
        assert_eq!(
            lex("x'"),
            vec![TokenKind::Ident("x".into()), TokenKind::Prime]
        );
    }

    #[test]
    fn test_line_comment() {
        assert_eq!(
            lex("x \\* comment\ny"),
            vec![TokenKind::Ident("x".into()), TokenKind::Ident("y".into()),]
        );
    }

    #[test]
    fn test_block_comment() {
        assert_eq!(
            lex("x (* comment *) y"),
            vec![TokenKind::Ident("x".into()), TokenKind::Ident("y".into()),]
        );
    }

    #[test]
    fn test_complex_expression() {
        let tokens = lex("\\A x \\in S: x' = x + 1");
        assert_eq!(
            tokens,
            vec![
                TokenKind::Forall,
                TokenKind::Ident("x".into()),
                TokenKind::SetIn,
                TokenKind::Ident("S".into()),
                TokenKind::Colon,
                TokenKind::Ident("x".into()),
                TokenKind::Prime,
                TokenKind::Eq,
                TokenKind::Ident("x".into()),
                TokenKind::Plus,
                TokenKind::Int(1),
            ]
        );
    }
}

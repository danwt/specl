//! Lexer for the Specl specification language.
//!
//! Converts source text into a stream of tokens.

use crate::token::{Span, Token, TokenKind};
use std::str::Chars;

/// Lexer for Specl source code.
pub struct Lexer<'a> {
    /// Source text being lexed.
    source: &'a str,
    /// Character iterator.
    chars: Chars<'a>,
    /// Current byte position.
    pos: usize,
    /// Current line number (1-indexed).
    line: u32,
    /// Current column number (1-indexed).
    column: u32,
    /// Start position of current token.
    token_start: usize,
    /// Start line of current token.
    token_start_line: u32,
    /// Start column of current token.
    token_start_column: u32,
}

impl<'a> Lexer<'a> {
    /// Create a new lexer for the given source text.
    pub fn new(source: &'a str) -> Self {
        Self {
            source,
            chars: source.chars(),
            pos: 0,
            line: 1,
            column: 1,
            token_start: 0,
            token_start_line: 1,
            token_start_column: 1,
        }
    }

    /// Tokenize the entire source, returning all tokens including EOF.
    pub fn tokenize(mut self) -> Vec<Token> {
        let mut tokens = Vec::new();
        loop {
            let token = self.next_token();
            let is_eof = token.is_eof();
            tokens.push(token);
            if is_eof {
                break;
            }
        }
        tokens
    }

    /// Get the next token.
    pub fn next_token(&mut self) -> Token {
        self.skip_whitespace();
        self.mark_token_start();

        let Some(c) = self.peek() else {
            return self.make_token(TokenKind::Eof);
        };

        // Single-line comment
        if c == '/' && self.peek_next() == Some('/') {
            return self.lex_comment();
        }

        // Multi-line comment
        if c == '/' && self.peek_next() == Some('*') {
            return self.lex_multiline_comment();
        }

        // String literal
        if c == '"' {
            return self.lex_string();
        }

        // Number literal
        if c.is_ascii_digit() {
            return self.lex_number();
        }

        // Identifier or keyword
        if c.is_alphabetic() || c == '_' {
            return self.lex_identifier();
        }

        // Operators and punctuation
        self.lex_operator_or_punctuation()
    }

    /// Skip whitespace characters.
    fn skip_whitespace(&mut self) {
        while let Some(c) = self.peek() {
            if c.is_whitespace() {
                self.advance();
            } else {
                break;
            }
        }
    }

    /// Mark the start of a new token.
    fn mark_token_start(&mut self) {
        self.token_start = self.pos;
        self.token_start_line = self.line;
        self.token_start_column = self.column;
    }

    /// Peek at the current character without consuming it.
    fn peek(&self) -> Option<char> {
        self.chars.clone().next()
    }

    /// Peek at the next character (after current) without consuming.
    fn peek_next(&self) -> Option<char> {
        let mut chars = self.chars.clone();
        chars.next();
        chars.next()
    }

    /// Advance to the next character, returning the current one.
    fn advance(&mut self) -> Option<char> {
        let c = self.chars.next()?;
        self.pos += c.len_utf8();
        if c == '\n' {
            self.line += 1;
            self.column = 1;
        } else {
            self.column += 1;
        }
        Some(c)
    }

    /// Create a token with the current span.
    fn make_token(&self, kind: TokenKind) -> Token {
        Token::new(
            kind,
            Span::new(
                self.token_start,
                self.pos,
                self.token_start_line,
                self.token_start_column,
            ),
        )
    }

    /// Get the text of the current token.
    fn token_text(&self) -> &'a str {
        &self.source[self.token_start..self.pos]
    }

    /// Lex a single-line comment.
    fn lex_comment(&mut self) -> Token {
        // Skip //
        self.advance();
        self.advance();

        // Check for doc comment ///
        let is_doc = self.peek() == Some('/');
        if is_doc {
            self.advance();
        }

        // Skip optional leading space
        if self.peek() == Some(' ') {
            self.advance();
        }

        let content_start = self.pos;

        // Read until end of line
        while let Some(c) = self.peek() {
            if c == '\n' {
                break;
            }
            self.advance();
        }

        let content = self.source[content_start..self.pos].to_string();

        if is_doc {
            self.make_token(TokenKind::DocComment(content))
        } else {
            self.make_token(TokenKind::Comment(content))
        }
    }

    /// Lex a multi-line comment.
    fn lex_multiline_comment(&mut self) -> Token {
        // Skip /*
        self.advance();
        self.advance();

        let content_start = self.pos;
        let mut depth = 1;

        while depth > 0 {
            match self.peek() {
                None => {
                    return self.make_token(TokenKind::Error(
                        "unterminated multi-line comment".to_string(),
                    ));
                }
                Some('*') if self.peek_next() == Some('/') => {
                    self.advance();
                    self.advance();
                    depth -= 1;
                }
                Some('/') if self.peek_next() == Some('*') => {
                    self.advance();
                    self.advance();
                    depth += 1;
                }
                Some(_) => {
                    self.advance();
                }
            }
        }

        let content = self.source[content_start..self.pos - 2].to_string();
        self.make_token(TokenKind::Comment(content))
    }

    /// Lex a string literal.
    fn lex_string(&mut self) -> Token {
        // Skip opening quote
        self.advance();

        let mut content = String::new();
        loop {
            match self.peek() {
                None | Some('\n') => {
                    return self
                        .make_token(TokenKind::Error("unterminated string literal".to_string()));
                }
                Some('"') => {
                    self.advance();
                    break;
                }
                Some('\\') => {
                    self.advance();
                    match self.peek() {
                        Some('n') => {
                            content.push('\n');
                            self.advance();
                        }
                        Some('t') => {
                            content.push('\t');
                            self.advance();
                        }
                        Some('r') => {
                            content.push('\r');
                            self.advance();
                        }
                        Some('\\') => {
                            content.push('\\');
                            self.advance();
                        }
                        Some('"') => {
                            content.push('"');
                            self.advance();
                        }
                        Some(c) => {
                            return self.make_token(TokenKind::Error(format!(
                                "invalid escape sequence: \\{}",
                                c
                            )));
                        }
                        None => {
                            return self.make_token(TokenKind::Error(
                                "unterminated string literal".to_string(),
                            ));
                        }
                    }
                }
                Some(c) => {
                    content.push(c);
                    self.advance();
                }
            }
        }

        self.make_token(TokenKind::StringLit(content))
    }

    /// Lex a number literal.
    fn lex_number(&mut self) -> Token {
        while let Some(c) = self.peek() {
            if c.is_ascii_digit() {
                self.advance();
            } else {
                break;
            }
        }

        let text = self.token_text();
        match text.parse::<i64>() {
            Ok(n) => self.make_token(TokenKind::Integer(n)),
            Err(_) => self.make_token(TokenKind::Error(format!("invalid integer: {}", text))),
        }
    }

    /// Lex an identifier or keyword.
    fn lex_identifier(&mut self) -> Token {
        while let Some(c) = self.peek() {
            if c.is_alphanumeric() || c == '_' {
                self.advance();
            } else {
                break;
            }
        }

        let text = self.token_text();

        // Check if it's a keyword
        if let Some(keyword) = TokenKind::keyword(text) {
            self.make_token(keyword)
        } else {
            self.make_token(TokenKind::Ident(text.to_string()))
        }
    }

    /// Lex an operator or punctuation.
    fn lex_operator_or_punctuation(&mut self) -> Token {
        let c = self.advance().unwrap();

        match c {
            '(' => self.make_token(TokenKind::LParen),
            ')' => self.make_token(TokenKind::RParen),
            '{' => self.make_token(TokenKind::LBrace),
            '}' => self.make_token(TokenKind::RBrace),
            '[' => self.make_token(TokenKind::LBracket),
            ']' => self.make_token(TokenKind::RBracket),
            ',' => self.make_token(TokenKind::Comma),
            ':' => self.make_token(TokenKind::Colon),
            ';' => self.make_token(TokenKind::Semicolon),
            '\'' => self.make_token(TokenKind::Prime),
            '|' => self.make_token(TokenKind::Pipe),
            '&' => self.make_token(TokenKind::Ampersand),
            '%' => self.make_token(TokenKind::Percent),
            '*' => self.make_token(TokenKind::Star),
            '.' => {
                if self.peek() == Some('.') {
                    self.advance();
                    self.make_token(TokenKind::DotDot)
                } else {
                    self.make_token(TokenKind::Dot)
                }
            }
            '+' => {
                if self.peek() == Some('+') {
                    self.advance();
                    self.make_token(TokenKind::PlusPlus)
                } else {
                    self.make_token(TokenKind::Plus)
                }
            }
            '-' => {
                if self.peek() == Some('>') {
                    self.advance();
                    self.make_token(TokenKind::Arrow)
                } else {
                    self.make_token(TokenKind::Minus)
                }
            }
            '/' => self.make_token(TokenKind::Slash),
            '=' => {
                if self.peek() == Some('=') {
                    self.advance();
                    self.make_token(TokenKind::Eq)
                } else if self.peek() == Some('>') {
                    self.advance();
                    self.make_token(TokenKind::FatArrow)
                } else {
                    self.make_token(TokenKind::Assign)
                }
            }
            '!' => {
                if self.peek() == Some('=') {
                    self.advance();
                    self.make_token(TokenKind::Ne)
                } else {
                    self.make_token(TokenKind::Error(format!("unexpected character: {}", c)))
                }
            }
            '<' => {
                if self.peek() == Some('=') {
                    self.advance();
                    self.make_token(TokenKind::Le)
                } else {
                    self.make_token(TokenKind::Lt)
                }
            }
            '>' => {
                if self.peek() == Some('=') {
                    self.advance();
                    self.make_token(TokenKind::Ge)
                } else {
                    self.make_token(TokenKind::Gt)
                }
            }
            _ => self.make_token(TokenKind::Error(format!("unexpected character: {}", c))),
        }
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        let token = self.next_token();
        if token.is_eof() {
            None
        } else {
            Some(token)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lex(source: &str) -> Vec<TokenKind> {
        Lexer::new(source)
            .tokenize()
            .into_iter()
            .map(|t| t.kind)
            .collect()
    }

    #[test]
    fn test_empty() {
        assert_eq!(lex(""), vec![TokenKind::Eof]);
    }

    #[test]
    fn test_whitespace() {
        assert_eq!(lex("   \n\t  "), vec![TokenKind::Eof]);
    }

    #[test]
    fn test_keywords() {
        assert_eq!(
            lex("module action init"),
            vec![
                TokenKind::Module,
                TokenKind::Action,
                TokenKind::Init,
                TokenKind::Eof
            ]
        );
    }

    #[test]
    fn test_identifiers() {
        assert_eq!(
            lex("foo bar_baz _private"),
            vec![
                TokenKind::Ident("foo".to_string()),
                TokenKind::Ident("bar_baz".to_string()),
                TokenKind::Ident("_private".to_string()),
                TokenKind::Eof
            ]
        );
    }

    #[test]
    fn test_numbers() {
        assert_eq!(
            lex("0 42 123456"),
            vec![
                TokenKind::Integer(0),
                TokenKind::Integer(42),
                TokenKind::Integer(123456),
                TokenKind::Eof
            ]
        );
    }

    #[test]
    fn test_strings() {
        assert_eq!(
            lex(r#""hello" "world""#),
            vec![
                TokenKind::StringLit("hello".to_string()),
                TokenKind::StringLit("world".to_string()),
                TokenKind::Eof
            ]
        );
    }

    #[test]
    fn test_string_escapes() {
        assert_eq!(
            lex(r#""line1\nline2" "tab\there" "quote\"end""#),
            vec![
                TokenKind::StringLit("line1\nline2".to_string()),
                TokenKind::StringLit("tab\there".to_string()),
                TokenKind::StringLit("quote\"end".to_string()),
                TokenKind::Eof
            ]
        );
    }

    #[test]
    fn test_operators() {
        assert_eq!(
            lex("== != < <= > >= + - * / %"),
            vec![
                TokenKind::Eq,
                TokenKind::Ne,
                TokenKind::Lt,
                TokenKind::Le,
                TokenKind::Gt,
                TokenKind::Ge,
                TokenKind::Plus,
                TokenKind::Minus,
                TokenKind::Star,
                TokenKind::Slash,
                TokenKind::Percent,
                TokenKind::Eof
            ]
        );
    }

    #[test]
    fn test_punctuation() {
        assert_eq!(
            lex("( ) { } [ ] , : ; . .. -> => ' |"),
            vec![
                TokenKind::LParen,
                TokenKind::RParen,
                TokenKind::LBrace,
                TokenKind::RBrace,
                TokenKind::LBracket,
                TokenKind::RBracket,
                TokenKind::Comma,
                TokenKind::Colon,
                TokenKind::Semicolon,
                TokenKind::Dot,
                TokenKind::DotDot,
                TokenKind::Arrow,
                TokenKind::FatArrow,
                TokenKind::Prime,
                TokenKind::Pipe,
                TokenKind::Eof
            ]
        );
    }

    #[test]
    fn test_comments() {
        let tokens = lex("foo // comment\nbar");
        assert_eq!(
            tokens,
            vec![
                TokenKind::Ident("foo".to_string()),
                TokenKind::Comment("comment".to_string()),
                TokenKind::Ident("bar".to_string()),
                TokenKind::Eof
            ]
        );
    }

    #[test]
    fn test_doc_comments() {
        let tokens = lex("/// This is documentation\nfoo");
        assert_eq!(
            tokens,
            vec![
                TokenKind::DocComment("This is documentation".to_string()),
                TokenKind::Ident("foo".to_string()),
                TokenKind::Eof
            ]
        );
    }

    #[test]
    fn test_multiline_comment() {
        let tokens = lex("foo /* comment */ bar");
        assert_eq!(
            tokens,
            vec![
                TokenKind::Ident("foo".to_string()),
                TokenKind::Comment(" comment ".to_string()),
                TokenKind::Ident("bar".to_string()),
                TokenKind::Eof
            ]
        );
    }

    #[test]
    fn test_nested_multiline_comment() {
        let tokens = lex("/* outer /* inner */ outer */ foo");
        assert_eq!(
            tokens,
            vec![
                TokenKind::Comment(" outer /* inner */ outer ".to_string()),
                TokenKind::Ident("foo".to_string()),
                TokenKind::Eof
            ]
        );
    }

    #[test]
    fn test_logical_keywords() {
        assert_eq!(
            lex("and or not implies iff"),
            vec![
                TokenKind::And,
                TokenKind::Or,
                TokenKind::Not,
                TokenKind::Implies,
                TokenKind::Iff,
                TokenKind::Eof
            ]
        );
    }

    #[test]
    fn test_quantifiers() {
        assert_eq!(
            lex("all any fix in"),
            vec![
                TokenKind::All,
                TokenKind::Any,
                TokenKind::Fix,
                TokenKind::In,
                TokenKind::Eof
            ]
        );
    }

    #[test]
    fn test_temporal() {
        assert_eq!(
            lex("always eventually leads_to enabled"),
            vec![
                TokenKind::Always,
                TokenKind::Eventually,
                TokenKind::LeadsTo,
                TokenKind::Enabled,
                TokenKind::Eof
            ]
        );
    }

    #[test]
    fn test_types() {
        assert_eq!(
            lex("Nat Int Bool String Set Seq Dict Option"),
            vec![
                TokenKind::Nat,
                TokenKind::Int,
                TokenKind::Bool,
                TokenKind::String_,
                TokenKind::Set,
                TokenKind::Seq,
                TokenKind::Dict,
                TokenKind::Option_,
                TokenKind::Eof
            ]
        );
    }

    #[test]
    fn test_sample_spec() {
        let source = r#"
module Counter

var count: Nat

init {
    count == 0
}

action Increment() {
    count' == count + 1
}
"#;
        let tokens: Vec<_> = Lexer::new(source)
            .tokenize()
            .into_iter()
            .filter(|t| !t.kind.is_trivia())
            .map(|t| t.kind)
            .collect();

        assert_eq!(
            tokens,
            vec![
                TokenKind::Module,
                TokenKind::Ident("Counter".to_string()),
                TokenKind::Var,
                TokenKind::Ident("count".to_string()),
                TokenKind::Colon,
                TokenKind::Nat,
                TokenKind::Init,
                TokenKind::LBrace,
                TokenKind::Ident("count".to_string()),
                TokenKind::Eq,
                TokenKind::Integer(0),
                TokenKind::RBrace,
                TokenKind::Action,
                TokenKind::Ident("Increment".to_string()),
                TokenKind::LParen,
                TokenKind::RParen,
                TokenKind::LBrace,
                TokenKind::Ident("count".to_string()),
                TokenKind::Prime,
                TokenKind::Eq,
                TokenKind::Ident("count".to_string()),
                TokenKind::Plus,
                TokenKind::Integer(1),
                TokenKind::RBrace,
                TokenKind::Eof
            ]
        );
    }

    #[test]
    fn test_span_tracking() {
        let tokens = Lexer::new("foo bar").tokenize();
        assert_eq!(tokens[0].span.line, 1);
        assert_eq!(tokens[0].span.column, 1);
        assert_eq!(tokens[1].span.line, 1);
        assert_eq!(tokens[1].span.column, 5);
    }

    #[test]
    fn test_span_multiline() {
        let tokens = Lexer::new("foo\nbar").tokenize();
        assert_eq!(tokens[0].span.line, 1);
        assert_eq!(tokens[1].span.line, 2);
        assert_eq!(tokens[1].span.column, 1);
    }

    #[test]
    fn test_error_recovery() {
        let tokens = lex("foo @ bar");
        assert!(matches!(tokens[1], TokenKind::Error(_)));
        assert_eq!(tokens[2], TokenKind::Ident("bar".to_string()));
    }
}

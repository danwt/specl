//! Recursive descent parser for the Specl specification language.

use crate::ast::*;
use crate::lexer::Lexer;
use crate::token::{Span, Token, TokenKind};
use thiserror::Error;

/// Parser error.
#[derive(Debug, Error)]
pub enum ParseError {
    #[error("unexpected token at {span}: expected {expected}, found {found}")]
    UnexpectedToken {
        expected: String,
        found: String,
        span: Span,
    },
    #[error("unexpected end of file at {span}")]
    UnexpectedEof { span: Span },
    #[error("invalid syntax at {span}: {message}")]
    InvalidSyntax { message: String, span: Span },
}

impl ParseError {
    /// Get the source span where this error occurred.
    pub fn span(&self) -> Span {
        match self {
            ParseError::UnexpectedToken { span, .. } => *span,
            ParseError::UnexpectedEof { span } => *span,
            ParseError::InvalidSyntax { span, .. } => *span,
        }
    }
}

pub type ParseResult<T> = Result<T, ParseError>;

/// Parser for Specl source code.
pub struct Parser {
    tokens: Vec<Token>,
    pos: usize,
    /// Nesting depth inside brackets. When > 0, `..` is reserved for slice syntax.
    in_bracket: usize,
}

impl Parser {
    /// Create a new parser from source text.
    pub fn new(source: &str) -> Self {
        let tokens: Vec<_> = Lexer::new(source)
            .tokenize()
            .into_iter()
            .filter(|t| !t.kind.is_trivia())
            .collect();
        Self {
            tokens,
            pos: 0,
            in_bracket: 0,
        }
    }

    /// Parse a complete module.
    pub fn parse_module(&mut self) -> ParseResult<Module> {
        let start = self.current_span();

        self.expect(TokenKind::Module)?;
        let name = self.parse_ident()?;

        let mut decls = Vec::new();
        while !self.is_at_end() {
            decls.push(self.parse_decl()?);
        }

        let span = start.merge(self.prev_span());
        Ok(Module { name, decls, span })
    }

    /// Parse a declaration.
    fn parse_decl(&mut self) -> ParseResult<Decl> {
        match self.peek_kind() {
            TokenKind::Use => self.parse_use_decl().map(Decl::Use),
            TokenKind::Const => self.parse_const_decl().map(Decl::Const),
            TokenKind::Var => self.parse_var_decl().map(Decl::Var),
            TokenKind::Type => self.parse_type_decl().map(Decl::Type),
            TokenKind::Func => self.parse_func_decl().map(Decl::Func),
            TokenKind::Init => self.parse_init_decl().map(Decl::Init),
            TokenKind::Action => self.parse_action_decl().map(Decl::Action),
            TokenKind::Invariant => self.parse_invariant_decl().map(Decl::Invariant),
            TokenKind::Property => self.parse_property_decl().map(Decl::Property),
            TokenKind::Fairness => self.parse_fairness_decl().map(Decl::Fairness),
            TokenKind::View => self.parse_view_decl().map(Decl::View),
            _ => Err(ParseError::UnexpectedToken {
                expected: "declaration".to_string(),
                found: self.peek_kind().to_string(),
                span: self.current_span(),
            }),
        }
    }

    fn parse_use_decl(&mut self) -> ParseResult<UseDecl> {
        let start = self.current_span();
        self.expect(TokenKind::Use)?;
        let module = self.parse_ident()?;
        let span = start.merge(self.prev_span());
        Ok(UseDecl { module, span })
    }

    fn parse_const_decl(&mut self) -> ParseResult<ConstDecl> {
        let start = self.current_span();
        self.expect(TokenKind::Const)?;
        let name = self.parse_ident()?;
        self.expect(TokenKind::Colon)?;

        // Check if this is a scalar constant (integer not followed by ..)
        let value = if let TokenKind::Integer(n) = self.peek_kind() {
            if self.peek_ahead_kind(1) != TokenKind::DotDot {
                // Scalar constant: const X: 3
                self.advance();
                ConstValue::Scalar(n)
            } else {
                // Range type: const X: 0..10
                ConstValue::Type(self.parse_type_expr()?)
            }
        } else {
            // Type expression: const X: Bool, const X: Set[Int], etc.
            ConstValue::Type(self.parse_type_expr()?)
        };

        // Optional default value: const N: Int = 5
        let default_value =
            if matches!(value, ConstValue::Type(_)) && self.peek_kind() == TokenKind::Assign {
                self.advance();
                if let TokenKind::Integer(n) = self.peek_kind() {
                    self.advance();
                    Some(n)
                } else {
                    return Err(ParseError::UnexpectedToken {
                        expected: "integer literal".to_string(),
                        found: format!("{:?}", self.peek_kind()),
                        span: self.current_span(),
                    });
                }
            } else {
                None
            };

        let span = start.merge(self.prev_span());
        Ok(ConstDecl {
            name,
            value,
            default_value,
            span,
        })
    }

    fn parse_var_decl(&mut self) -> ParseResult<VarDecl> {
        let start = self.current_span();
        self.expect(TokenKind::Var)?;
        let name = self.parse_ident()?;
        self.expect(TokenKind::Colon)?;
        let ty = self.parse_type_expr()?;
        let span = start.merge(self.prev_span());
        Ok(VarDecl { name, ty, span })
    }

    fn parse_type_decl(&mut self) -> ParseResult<TypeDecl> {
        let start = self.current_span();
        self.expect(TokenKind::Type)?;
        let name = self.parse_ident()?;
        self.expect(TokenKind::Assign)?;
        let ty = self.parse_type_expr()?;
        let span = start.merge(self.prev_span());
        Ok(TypeDecl { name, ty, span })
    }

    /// Parse `func Name(param1, param2) { expr }`
    fn parse_func_decl(&mut self) -> ParseResult<FuncDecl> {
        let start = self.current_span();
        self.expect(TokenKind::Func)?;
        let name = self.parse_ident()?;
        self.expect(TokenKind::LParen)?;
        let params = self.parse_func_params()?;
        self.expect(TokenKind::RParen)?;
        self.expect(TokenKind::LBrace)?;
        let body = self.parse_expr()?;
        self.expect(TokenKind::RBrace)?;
        let span = start.merge(self.prev_span());
        Ok(FuncDecl {
            name,
            params,
            body,
            span,
        })
    }

    /// Parse function parameters (just names, no types).
    fn parse_func_params(&mut self) -> ParseResult<Vec<FuncParam>> {
        let mut params = Vec::new();
        if self.peek_kind() == TokenKind::RParen {
            return Ok(params);
        }
        loop {
            let start = self.current_span();
            let name = self.parse_ident()?;
            let span = start.merge(self.prev_span());
            params.push(FuncParam { name, span });
            if self.peek_kind() == TokenKind::Comma {
                self.advance();
            } else {
                break;
            }
        }
        Ok(params)
    }

    fn parse_init_decl(&mut self) -> ParseResult<InitDecl> {
        let start = self.current_span();
        self.expect(TokenKind::Init)?;
        self.expect(TokenKind::LBrace)?;

        // Parse semicolon-separated statements (also accepts old 'and' syntax
        // since parse_expr() consumes 'and' chains as binary AND).
        // Statement-level `let x = expr;` desugars to `let x = expr in (remaining)`.
        let stmts = self.parse_statement_list()?;

        let body = Self::combine_with_and(stmts, start);

        self.expect(TokenKind::RBrace)?;
        let span = start.merge(self.prev_span());
        Ok(InitDecl { body, span })
    }

    fn parse_action_decl(&mut self) -> ParseResult<ActionDecl> {
        let start = self.current_span();
        self.expect(TokenKind::Action)?;
        let name = self.parse_ident()?;
        self.expect(TokenKind::LParen)?;
        let params = self.parse_params()?;
        self.expect(TokenKind::RParen)?;
        self.expect(TokenKind::LBrace)?;
        let body = self.parse_action_body()?;
        self.expect(TokenKind::RBrace)?;
        let span = start.merge(self.prev_span());
        Ok(ActionDecl {
            name,
            params,
            body,
            span,
        })
    }

    fn parse_params(&mut self) -> ParseResult<Vec<Param>> {
        let mut params = Vec::new();
        if !self.check(TokenKind::RParen) {
            loop {
                params.push(self.parse_param()?);
                if !self.match_token(TokenKind::Comma) {
                    break;
                }
            }
        }
        Ok(params)
    }

    fn parse_param(&mut self) -> ParseResult<Param> {
        let start = self.current_span();
        let name = self.parse_ident()?;
        self.expect(TokenKind::Colon)?;
        let ty = self.parse_type_expr()?;
        let span = start.merge(self.prev_span());
        Ok(Param { name, ty, span })
    }

    fn parse_action_body(&mut self) -> ParseResult<ActionBody> {
        let start = self.current_span();
        let mut requires = Vec::new();

        // Parse require statements (must come before effects)
        while self.check(TokenKind::Require) {
            self.advance();
            let expr = self.parse_expr()?;
            self.match_token(TokenKind::Semicolon); // accept optional trailing ;
            requires.push(expr);
        }

        // Parse effect statements separated by ; (also accepts old 'and' syntax
        // since parse_expr() consumes 'and' chains as binary AND).
        // Statement-level `let x = expr;` desugars to `let x = expr in (remaining)`.
        let effects = self.parse_statement_list()?;

        let effect = if effects.is_empty() {
            None
        } else {
            Some(Self::combine_with_and(effects, start))
        };

        let span = start.merge(self.prev_span());
        Ok(ActionBody {
            requires,
            effect,
            span,
        })
    }

    /// Parse a list of semicolon-separated statements, with support for
    /// statement-level `let x = expr;` which desugars to `let x = expr in (remaining)`.
    /// Stops at `}` (RBrace).
    fn parse_statement_list(&mut self) -> ParseResult<Vec<Expr>> {
        let mut stmts = Vec::new();
        while !self.check(TokenKind::RBrace) {
            if self.check(TokenKind::Let) {
                stmts.push(self.parse_statement_let()?);
                break; // statement-let consumed all remaining statements
            }
            stmts.push(self.parse_expr()?);
            if !self.match_token(TokenKind::Semicolon) {
                break;
            }
        }
        Ok(stmts)
    }

    /// Parse a `let` that may be statement-level (`let x = expr;`) or
    /// expression-level (`let x = expr in body`).
    ///
    /// Statement-level: desugars `let x = v; rest...` to `let x = v in (rest...)`.
    /// Handles nesting: `let x = 1; let y = x; z = y` works via recursion.
    fn parse_statement_let(&mut self) -> ParseResult<Expr> {
        let start = self.current_span();
        self.expect(TokenKind::Let)?;
        let var = self.parse_ident()?;
        self.expect(TokenKind::Assign)?;
        let value = self.parse_expr_no_in()?;

        if self.check(TokenKind::In) {
            // Traditional let..in expression
            self.advance();
            let body = self.parse_expr()?;
            let span = start.merge(body.span);
            return Ok(Expr::new(
                ExprKind::Let {
                    var,
                    value: Box::new(value),
                    body: Box::new(body),
                },
                span,
            ));
        }

        // Statement-level let: parse remaining statements as body
        self.match_token(TokenKind::Semicolon);

        let remaining = self.parse_statement_list()?;
        if remaining.is_empty() {
            return Err(ParseError::InvalidSyntax {
                message: "expected statements after let binding".to_string(),
                span: self.current_span(),
            });
        }

        let body = Self::combine_with_and(remaining, start);
        let span = start.merge(body.span);
        Ok(Expr::new(
            ExprKind::Let {
                var,
                value: Box::new(value),
                body: Box::new(body),
            },
            span,
        ))
    }

    /// Combine multiple expressions into a single AND chain.
    /// Produces the same AST shape as the old `x = 1 and y = 2` syntax.
    fn combine_with_and(stmts: Vec<Expr>, fallback_span: Span) -> Expr {
        stmts
            .into_iter()
            .reduce(|a, b| {
                let span = a.span.merge(b.span);
                Expr::new(
                    ExprKind::Binary {
                        op: BinOp::And,
                        left: Box::new(a),
                        right: Box::new(b),
                    },
                    span,
                )
            })
            .unwrap_or_else(|| Expr::new(ExprKind::Bool(true), fallback_span))
    }

    fn parse_invariant_decl(&mut self) -> ParseResult<InvariantDecl> {
        let start = self.current_span();
        self.expect(TokenKind::Invariant)?;
        let name = self.parse_ident()?;
        self.expect(TokenKind::LBrace)?;
        let body = self.parse_expr()?;
        self.expect(TokenKind::RBrace)?;
        let span = start.merge(self.prev_span());
        Ok(InvariantDecl { name, body, span })
    }

    fn parse_property_decl(&mut self) -> ParseResult<PropertyDecl> {
        let start = self.current_span();
        self.expect(TokenKind::Property)?;
        let name = self.parse_ident()?;
        self.expect(TokenKind::LBrace)?;
        let body = self.parse_expr()?;
        self.expect(TokenKind::RBrace)?;
        let span = start.merge(self.prev_span());
        Ok(PropertyDecl { name, body, span })
    }

    fn parse_view_decl(&mut self) -> ParseResult<ViewDecl> {
        let start = self.current_span();
        self.expect(TokenKind::View)?;
        self.expect(TokenKind::LBrace)?;

        let mut variables = Vec::new();
        if !self.check(TokenKind::RBrace) {
            variables.push(self.parse_ident()?);
            while self.match_token(TokenKind::Comma) {
                variables.push(self.parse_ident()?);
            }
        }

        self.expect(TokenKind::RBrace)?;
        let span = start.merge(self.prev_span());
        Ok(ViewDecl { variables, span })
    }

    fn parse_fairness_decl(&mut self) -> ParseResult<FairnessDecl> {
        let start = self.current_span();
        self.expect(TokenKind::Fairness)?;
        self.expect(TokenKind::LBrace)?;

        let mut constraints = Vec::new();
        while !self.check(TokenKind::RBrace) {
            constraints.push(self.parse_fairness_constraint()?);
        }

        self.expect(TokenKind::RBrace)?;
        let span = start.merge(self.prev_span());
        Ok(FairnessDecl { constraints, span })
    }

    fn parse_fairness_constraint(&mut self) -> ParseResult<FairnessConstraint> {
        let start = self.current_span();
        let kind = if self.match_token(TokenKind::WeakFair) {
            FairnessKind::Weak
        } else if self.match_token(TokenKind::StrongFair) {
            FairnessKind::Strong
        } else {
            return Err(ParseError::UnexpectedToken {
                expected: "weak_fair or strong_fair".to_string(),
                found: self.peek_kind().to_string(),
                span: self.current_span(),
            });
        };
        self.expect(TokenKind::LParen)?;
        let action = self.parse_ident()?;
        self.expect(TokenKind::RParen)?;
        let span = start.merge(self.prev_span());
        Ok(FairnessConstraint { kind, action, span })
    }

    // === Type expression parsing ===

    fn parse_type_expr(&mut self) -> ParseResult<TypeExpr> {
        let start = self.current_span();

        // Check for built-in parameterized types
        match self.peek_kind() {
            TokenKind::Set => {
                self.advance();
                self.expect(TokenKind::LBracket)?;
                let inner = self.parse_type_expr()?;
                self.expect(TokenKind::RBracket)?;
                let span = start.merge(self.prev_span());
                Ok(TypeExpr::Set(Box::new(inner), span))
            }
            TokenKind::Seq => {
                self.advance();
                self.expect(TokenKind::LBracket)?;
                let inner = self.parse_type_expr()?;
                self.expect(TokenKind::RBracket)?;
                let span = start.merge(self.prev_span());
                Ok(TypeExpr::Seq(Box::new(inner), span))
            }
            TokenKind::Dict => {
                self.advance();
                self.expect(TokenKind::LBracket)?;
                let key = self.parse_type_expr()?;
                self.expect(TokenKind::Comma)?;
                let value = self.parse_type_expr()?;
                self.expect(TokenKind::RBracket)?;
                let span = start.merge(self.prev_span());
                Ok(TypeExpr::Dict(Box::new(key), Box::new(value), span))
            }
            TokenKind::Option_ => {
                self.advance();
                self.expect(TokenKind::LBracket)?;
                let inner = self.parse_type_expr()?;
                self.expect(TokenKind::RBracket)?;
                let span = start.merge(self.prev_span());
                Ok(TypeExpr::Option(Box::new(inner), span))
            }
            TokenKind::Integer(_) => {
                // Range type like 0..10
                let lo = self.parse_primary_expr()?;
                self.expect(TokenKind::DotDot)?;
                let hi = self.parse_primary_expr()?;
                let span = start.merge(self.prev_span());
                Ok(TypeExpr::Range(Box::new(lo), Box::new(hi), span))
            }
            TokenKind::LParen => {
                // Tuple type like (T1, T2, ...)
                self.advance();
                let first = self.parse_type_expr()?;
                if self.match_token(TokenKind::Comma) {
                    // It's a tuple type
                    let mut elements = vec![first];
                    loop {
                        elements.push(self.parse_type_expr()?);
                        if !self.match_token(TokenKind::Comma) {
                            break;
                        }
                    }
                    self.expect(TokenKind::RParen)?;
                    let span = start.merge(self.prev_span());
                    Ok(TypeExpr::Tuple(elements, span))
                } else {
                    // Just a parenthesized type - unwrap it
                    self.expect(TokenKind::RParen)?;
                    Ok(first)
                }
            }
            _ => {
                // Named type or identifier that could start a range
                let name = self.parse_ident()?;

                // Check for range
                if self.check(TokenKind::DotDot) {
                    self.advance();
                    let hi = self.parse_primary_expr()?;
                    let span = start.merge(self.prev_span());
                    let lo = Expr::new(ExprKind::Ident(name.name), name.span);
                    Ok(TypeExpr::Range(Box::new(lo), Box::new(hi), span))
                } else {
                    Ok(TypeExpr::Named(name))
                }
            }
        }
    }

    // === Expression parsing with precedence climbing ===

    fn parse_expr(&mut self) -> ParseResult<Expr> {
        self.parse_expr_impl(0, true)
    }

    /// Parse an expression but don't treat `in` as a binary operator.
    /// Used in contexts where `in` is a keyword separator (let, fn, comprehensions).
    fn parse_expr_no_in(&mut self) -> ParseResult<Expr> {
        self.parse_expr_impl(0, false)
    }

    fn parse_expr_impl(&mut self, min_prec: u8, allow_in_op: bool) -> ParseResult<Expr> {
        let mut left = self.parse_unary_expr()?;

        // Handle assignment specially: `x = expr` becomes `x' == expr`
        if self.check(TokenKind::Assign) {
            let assign_span = self.current_span();
            self.advance(); // consume =

            // Left side must be an identifier
            let primed_left = match &left.kind {
                ExprKind::Ident(name) => {
                    let span = left.span.merge(assign_span);
                    Expr::new(ExprKind::Primed(name.clone()), span)
                }
                _ => {
                    return Err(ParseError::InvalidSyntax {
                        message: "left side of assignment must be a variable".to_string(),
                        span: left.span,
                    });
                }
            };

            // Parse RHS at precedence 5 (same as ==) so `and` stops it
            // This makes `x = 1 and y = 2` parse as `(x = 1) and (y = 2)`
            let right = self.parse_expr_impl(5, allow_in_op)?;
            let span = left.span.merge(right.span);
            left = Expr::new(
                ExprKind::Binary {
                    op: BinOp::Eq,
                    left: Box::new(primed_left),
                    right: Box::new(right),
                },
                span,
            );
        }

        while let Some(op) = self.peek_binop(allow_in_op) {
            let prec = op.precedence();
            if prec < min_prec {
                break;
            }

            self.advance(); // consume operator

            // Handle right-associativity
            let next_prec = if op.is_right_assoc() { prec } else { prec + 1 };
            let right = self.parse_expr_impl(next_prec, allow_in_op)?;

            let span = left.span.merge(right.span);
            left = Expr::new(
                ExprKind::Binary {
                    op,
                    left: Box::new(left),
                    right: Box::new(right),
                },
                span,
            );
        }

        // Handle leads_to specially (infix keyword)
        if self.check(TokenKind::LeadsTo) {
            self.advance();
            let right = self.parse_expr_impl(1, allow_in_op)?;
            let span = left.span.merge(right.span);
            left = Expr::new(
                ExprKind::LeadsTo {
                    left: Box::new(left),
                    right: Box::new(right),
                },
                span,
            );
        }

        Ok(left)
    }

    fn peek_binop(&self, allow_in_op: bool) -> Option<BinOp> {
        match self.peek_kind() {
            TokenKind::And => Some(BinOp::And),
            TokenKind::Or => Some(BinOp::Or),
            TokenKind::Implies => Some(BinOp::Implies),
            TokenKind::Iff => Some(BinOp::Iff),
            TokenKind::Eq => Some(BinOp::Eq),
            TokenKind::Ne => Some(BinOp::Ne),
            TokenKind::Lt => Some(BinOp::Lt),
            TokenKind::Le => Some(BinOp::Le),
            TokenKind::Gt => Some(BinOp::Gt),
            TokenKind::Ge => Some(BinOp::Ge),
            TokenKind::Plus => Some(BinOp::Add),
            TokenKind::Minus => Some(BinOp::Sub),
            TokenKind::Star => Some(BinOp::Mul),
            TokenKind::Slash => Some(BinOp::Div),
            TokenKind::Percent => Some(BinOp::Mod),
            TokenKind::In if allow_in_op => Some(BinOp::In),
            TokenKind::Union => Some(BinOp::Union),
            TokenKind::Intersect => Some(BinOp::Intersect),
            TokenKind::Diff => Some(BinOp::Diff),
            TokenKind::SubsetOf => Some(BinOp::SubsetOf),
            TokenKind::PlusPlus => Some(BinOp::Concat),
            TokenKind::Ampersand => Some(BinOp::Intersect),
            TokenKind::Pipe => Some(BinOp::Union),
            _ => None,
        }
    }

    fn parse_unary_expr(&mut self) -> ParseResult<Expr> {
        self.parse_unary_expr_with_in(true)
    }

    fn parse_unary_expr_with_in(&mut self, allow_in_op: bool) -> ParseResult<Expr> {
        let start = self.current_span();

        if self.match_token(TokenKind::Not) {
            // Parse operand at precedence 5 (comparison level) so `not m in S` parses as `not (m in S)`
            // but `not A and B` parses as `(not A) and B` since `and` has prec 4
            let operand = self.parse_expr_impl(5, allow_in_op)?;
            let span = start.merge(operand.span);
            return Ok(Expr::new(
                ExprKind::Unary {
                    op: UnaryOp::Not,
                    operand: Box::new(operand),
                },
                span,
            ));
        }

        if self.match_token(TokenKind::Minus) {
            // Negation binds tightly - just parse the next unary/postfix
            let operand = self.parse_unary_expr_with_in(allow_in_op)?;
            let span = start.merge(operand.span);
            return Ok(Expr::new(
                ExprKind::Unary {
                    op: UnaryOp::Neg,
                    operand: Box::new(operand),
                },
                span,
            ));
        }

        // Temporal prefix operators
        if self.match_token(TokenKind::Always) {
            let operand = self.parse_unary_expr_with_in(allow_in_op)?;
            let span = start.merge(operand.span);
            return Ok(Expr::new(ExprKind::Always(Box::new(operand)), span));
        }

        if self.match_token(TokenKind::Eventually) {
            let operand = self.parse_unary_expr_with_in(allow_in_op)?;
            let span = start.merge(operand.span);
            return Ok(Expr::new(ExprKind::Eventually(Box::new(operand)), span));
        }

        self.parse_postfix_expr()
    }

    fn parse_postfix_expr(&mut self) -> ParseResult<Expr> {
        let mut expr = self.parse_primary_expr()?;

        loop {
            if self.match_token(TokenKind::LBracket) {
                // Index or slice: suppress range parsing so `..` is available for slice
                self.in_bracket += 1;
                let index = self.parse_expr()?;
                self.in_bracket -= 1;
                if self.match_token(TokenKind::DotDot) {
                    let hi = self.parse_expr()?;
                    self.expect(TokenKind::RBracket)?;
                    let span = expr.span.merge(self.prev_span());
                    expr = Expr::new(
                        ExprKind::Slice {
                            base: Box::new(expr),
                            lo: Box::new(index),
                            hi: Box::new(hi),
                        },
                        span,
                    );
                } else {
                    self.expect(TokenKind::RBracket)?;
                    let span = expr.span.merge(self.prev_span());
                    expr = Expr::new(
                        ExprKind::Index {
                            base: Box::new(expr),
                            index: Box::new(index),
                        },
                        span,
                    );
                }
            } else if self.match_token(TokenKind::Dot) {
                let field = self.parse_ident()?;
                let span = expr.span.merge(field.span);
                expr = Expr::new(
                    ExprKind::Field {
                        base: Box::new(expr),
                        field,
                    },
                    span,
                );
            } else if self.check(TokenKind::LParen)
                && matches!(expr.kind, ExprKind::Ident(_) | ExprKind::Field { .. })
            {
                // Function call — only after identifiers and field accesses.
                // Without this guard, `10\n(x = x+1)` would parse as `10(x = x+1)`.
                self.advance();
                let args = self.parse_call_args()?;
                self.expect(TokenKind::RParen)?;
                let span = expr.span.merge(self.prev_span());
                expr = Expr::new(
                    ExprKind::Call {
                        func: Box::new(expr),
                        args,
                    },
                    span,
                );
            } else if self.match_token(TokenKind::Prime) {
                // Prime notation is deprecated - use assignment syntax instead
                return Err(ParseError::InvalidSyntax {
                    message: "prime notation (x') is deprecated, use assignment syntax: x = value"
                        .to_string(),
                    span: self.prev_span(),
                });
            } else if self.in_bracket == 0 && self.match_token(TokenKind::DotDot) {
                // Range expression (e.g., 0..10 or 1..m.field)
                // Suppressed inside brackets where `..` means slice.
                let hi = self.parse_postfix_expr()?;
                let span = expr.span.merge(hi.span);
                expr = Expr::new(
                    ExprKind::Range {
                        lo: Box::new(expr),
                        hi: Box::new(hi),
                    },
                    span,
                );
                // Range is terminal - don't allow chaining
                break;
            } else if self.match_token(TokenKind::With) {
                // Record/dict update: expr with { field: value, [key]: value, ... }
                self.expect(TokenKind::LBrace)?;
                let updates = self.parse_record_updates()?;
                self.expect(TokenKind::RBrace)?;
                let span = expr.span.merge(self.prev_span());
                expr = Expr::new(
                    ExprKind::RecordUpdate {
                        base: Box::new(expr),
                        updates,
                    },
                    span,
                );
            } else {
                break;
            }
        }

        Ok(expr)
    }

    fn parse_call_args(&mut self) -> ParseResult<Vec<Expr>> {
        let mut args = Vec::new();
        if !self.check(TokenKind::RParen) {
            loop {
                args.push(self.parse_expr()?);
                if !self.match_token(TokenKind::Comma) {
                    break;
                }
            }
        }
        Ok(args)
    }

    fn parse_primary_expr(&mut self) -> ParseResult<Expr> {
        let start = self.current_span();

        match self.peek_kind() {
            TokenKind::True => {
                self.advance();
                Ok(Expr::new(ExprKind::Bool(true), start))
            }
            TokenKind::False => {
                self.advance();
                Ok(Expr::new(ExprKind::Bool(false), start))
            }
            TokenKind::Integer(n) => {
                self.advance();
                Ok(Expr::new(ExprKind::Int(n), start))
            }
            TokenKind::StringLit(s) => {
                let s = s.clone();
                self.advance();
                Ok(Expr::new(ExprKind::String(s), start))
            }
            TokenKind::Ident(name) => {
                let name = name.clone();
                self.advance();
                // Check for range expression (suppressed inside brackets for slice)
                if self.in_bracket == 0 && self.check(TokenKind::DotDot) {
                    self.advance();
                    // Use parse_postfix_expr to handle field access on the right side (e.g., 1..m.field)
                    let hi = self.parse_postfix_expr()?;
                    let span = start.merge(hi.span);
                    let lo = Expr::new(ExprKind::Ident(name), start);
                    return Ok(Expr::new(
                        ExprKind::Range {
                            lo: Box::new(lo),
                            hi: Box::new(hi),
                        },
                        span,
                    ));
                }
                Ok(Expr::new(ExprKind::Ident(name), start))
            }
            // 'view' is a contextual keyword — treat as identifier in expressions
            TokenKind::View => {
                self.advance();
                Ok(Expr::new(ExprKind::Ident("view".into()), start))
            }
            TokenKind::LParen => {
                self.advance();
                let first = self.parse_expr()?;
                if self.match_token(TokenKind::Comma) {
                    // It's a tuple literal
                    let mut elements = vec![first];
                    loop {
                        elements.push(self.parse_expr()?);
                        if !self.match_token(TokenKind::Comma) {
                            break;
                        }
                    }
                    self.expect(TokenKind::RParen)?;
                    let span = start.merge(self.prev_span());
                    Ok(Expr::new(ExprKind::TupleLit(elements), span))
                } else {
                    // Just a parenthesized expression
                    self.expect(TokenKind::RParen)?;
                    let span = start.merge(self.prev_span());
                    Ok(Expr::new(ExprKind::Paren(Box::new(first)), span))
                }
            }
            TokenKind::LBrace => self.parse_set_or_record_lit(),
            TokenKind::LBracket => self.parse_seq_lit(),
            TokenKind::All => self.parse_quantifier(QuantifierKind::Forall),
            TokenKind::Any => self.parse_quantifier(QuantifierKind::Exists),
            TokenKind::Choose => self.parse_choose(),
            TokenKind::Let => self.parse_let(),
            TokenKind::If => self.parse_if(),
            TokenKind::Require => {
                self.advance();
                let expr = self.parse_expr()?;
                let span = start.merge(expr.span);
                Ok(Expr::new(ExprKind::Require(Box::new(expr)), span))
            }
            TokenKind::Changes => {
                self.advance();
                self.expect(TokenKind::LParen)?;
                let var = self.parse_ident()?;
                self.expect(TokenKind::RParen)?;
                let span = start.merge(self.prev_span());
                Ok(Expr::new(ExprKind::Changes(var), span))
            }
            TokenKind::Enabled => {
                self.advance();
                self.expect(TokenKind::LParen)?;
                let action = self.parse_ident()?;
                self.expect(TokenKind::RParen)?;
                let span = start.merge(self.prev_span());
                Ok(Expr::new(ExprKind::Enabled(action), span))
            }
            TokenKind::Head => {
                self.advance();
                self.expect(TokenKind::LParen)?;
                let seq = self.parse_expr()?;
                self.expect(TokenKind::RParen)?;
                let span = start.merge(self.prev_span());
                Ok(Expr::new(ExprKind::SeqHead(Box::new(seq)), span))
            }
            TokenKind::Tail => {
                self.advance();
                self.expect(TokenKind::LParen)?;
                let seq = self.parse_expr()?;
                self.expect(TokenKind::RParen)?;
                let span = start.merge(self.prev_span());
                Ok(Expr::new(ExprKind::SeqTail(Box::new(seq)), span))
            }
            TokenKind::Len => {
                self.advance();
                self.expect(TokenKind::LParen)?;
                let expr = self.parse_expr()?;
                self.expect(TokenKind::RParen)?;
                let span = start.merge(self.prev_span());
                Ok(Expr::new(ExprKind::Len(Box::new(expr)), span))
            }
            TokenKind::Keys => {
                self.advance();
                self.expect(TokenKind::LParen)?;
                let expr = self.parse_expr()?;
                self.expect(TokenKind::RParen)?;
                let span = start.merge(self.prev_span());
                Ok(Expr::new(ExprKind::Keys(Box::new(expr)), span))
            }
            TokenKind::Values => {
                self.advance();
                self.expect(TokenKind::LParen)?;
                let expr = self.parse_expr()?;
                self.expect(TokenKind::RParen)?;
                let span = start.merge(self.prev_span());
                Ok(Expr::new(ExprKind::Values(Box::new(expr)), span))
            }
            // Built-in type names can be used as identifiers for constructor calls
            TokenKind::Some_ => {
                self.advance();
                Ok(Expr::new(ExprKind::Ident("Some".to_string()), start))
            }
            TokenKind::None_ => {
                self.advance();
                Ok(Expr::new(ExprKind::Ident("None".to_string()), start))
            }
            TokenKind::Powerset => {
                self.advance();
                self.expect(TokenKind::LParen)?;
                let expr = self.parse_expr()?;
                self.expect(TokenKind::RParen)?;
                let span = start.merge(self.prev_span());
                Ok(Expr::new(ExprKind::Powerset(Box::new(expr)), span))
            }
            TokenKind::UnionAll => {
                self.advance();
                self.expect(TokenKind::LParen)?;
                let expr = self.parse_expr()?;
                self.expect(TokenKind::RParen)?;
                let span = start.merge(self.prev_span());
                Ok(Expr::new(ExprKind::BigUnion(Box::new(expr)), span))
            }
            _ => Err(ParseError::UnexpectedToken {
                expected: "expression".to_string(),
                found: self.peek_kind().to_string(),
                span: start,
            }),
        }
    }

    fn parse_set_or_record_lit(&mut self) -> ParseResult<Expr> {
        let start = self.current_span();
        self.expect(TokenKind::LBrace)?;

        // Empty dict {:}
        if self.check(TokenKind::Colon) {
            self.advance();
            self.expect(TokenKind::RBrace)?;
            let span = start.merge(self.prev_span());
            return Ok(Expr::new(ExprKind::DictLit(vec![]), span));
        }

        // Empty set {}
        if self.check(TokenKind::RBrace) {
            self.advance();
            let span = start.merge(self.prev_span());
            return Ok(Expr::new(ExprKind::SetLit(vec![]), span));
        }

        // Peek ahead to determine the form:
        // - Record: { field: value, ... }
        // - Set filter: { x in S if P } - starts with ident followed by `in`
        // - Set map: { expr for x in S }
        // - Set literal: { elem, ... }

        // Check for set filter form: { ident in ... if ... }
        // We need to detect this before parsing to avoid `in` being consumed as binop
        if self.is_set_filter_comprehension() {
            return self.parse_set_filter_comprehension(start);
        }

        // Parse first element (allow `in` as binop for cases like `{ a in S, b in T }`)
        let first = self.parse_expr()?;

        if self.check(TokenKind::Colon) {
            // Could be:
            // - Dict literal { key: value, ... }
            // - Dict comprehension { k: v for x in S }
            self.advance(); // consume :
            let value = self.parse_expr()?;

            // Check for dict comprehension: { k: v for x in S }
            if self.check(TokenKind::For) {
                self.advance(); // consume 'for'
                let var = self.parse_ident()?;
                self.expect(TokenKind::In)?;
                let domain = self.parse_expr()?;
                self.expect(TokenKind::RBrace)?;
                let span = start.merge(self.prev_span());

                // Verify that the key matches the variable (for dict comprehension)
                let key_name = match &first.kind {
                    ExprKind::Ident(s) => s.clone(),
                    _ => {
                        return Err(ParseError::InvalidSyntax {
                            message: "dict comprehension key must be an identifier".to_string(),
                            span: first.span,
                        })
                    }
                };
                if key_name != var.name {
                    return Err(ParseError::InvalidSyntax {
                        message: format!(
                            "dict comprehension key '{}' must match iteration variable '{}'",
                            key_name, var.name
                        ),
                        span: first.span,
                    });
                }

                // Convert to FnLit: { k: v for k in S } => fn(k in S) => v
                return Ok(Expr::new(
                    ExprKind::FnLit {
                        var,
                        domain: Box::new(domain),
                        body: Box::new(value),
                    },
                    span,
                ));
            }

            // Dict literal { key: value, ... } - keys are expressions
            let mut entries = vec![(first, value)];

            while self.match_token(TokenKind::Comma) {
                if self.check(TokenKind::RBrace) {
                    break; // trailing comma
                }
                let key = self.parse_expr()?;
                self.expect(TokenKind::Colon)?;
                let val = self.parse_expr()?;
                entries.push((key, val));
            }

            self.expect(TokenKind::RBrace)?;
            let span = start.merge(self.prev_span());
            Ok(Expr::new(ExprKind::DictLit(entries), span))
        } else if self.check(TokenKind::For) {
            // Set comprehension { expr for x in S } or { expr for x in S if P }
            self.advance(); // consume 'for'
            let var = self.parse_ident()?;
            self.expect(TokenKind::In)?;
            let domain = self.parse_expr()?;
            let filter = if self.match_token(TokenKind::If) {
                Some(Box::new(self.parse_expr()?))
            } else {
                None
            };
            self.expect(TokenKind::RBrace)?;
            let span = start.merge(self.prev_span());
            Ok(Expr::new(
                ExprKind::SetComprehension {
                    element: Box::new(first),
                    var,
                    domain: Box::new(domain),
                    filter,
                },
                span,
            ))
        } else {
            // Regular set literal { a, b, c }
            let mut elements = vec![first];
            while self.match_token(TokenKind::Comma) {
                if self.check(TokenKind::RBrace) {
                    break; // trailing comma
                }
                elements.push(self.parse_expr()?);
            }
            self.expect(TokenKind::RBrace)?;
            let span = start.merge(self.prev_span());
            Ok(Expr::new(ExprKind::SetLit(elements), span))
        }
    }

    /// Check if we're looking at a set filter comprehension: { ident in ... if ... }
    fn is_set_filter_comprehension(&self) -> bool {
        // Check pattern: identifier followed by `in`
        matches!(self.peek_kind(), TokenKind::Ident(_)) && self.peek_ahead_kind(1) == TokenKind::In
    }

    /// Parse set filter comprehension: { x in S if P }
    fn parse_set_filter_comprehension(&mut self, start: Span) -> ParseResult<Expr> {
        let var = self.parse_ident()?;
        self.expect(TokenKind::In)?;
        // Parse domain - use regular parse_expr since `in` after domain would be weird
        // and `if` is not a binop so it will stop there
        let domain = self.parse_expr()?;
        self.expect(TokenKind::If)?;
        let predicate = self.parse_expr()?;
        self.expect(TokenKind::RBrace)?;
        let span = start.merge(self.prev_span());
        // element is just the variable
        let element = Expr::new(ExprKind::Ident(var.name.clone()), var.span);
        Ok(Expr::new(
            ExprKind::SetComprehension {
                element: Box::new(element),
                var,
                domain: Box::new(domain),
                filter: Some(Box::new(predicate)),
            },
            span,
        ))
    }

    fn parse_seq_lit(&mut self) -> ParseResult<Expr> {
        let start = self.current_span();
        self.expect(TokenKind::LBracket)?;

        let mut elements = Vec::new();
        if !self.check(TokenKind::RBracket) {
            loop {
                elements.push(self.parse_expr()?);
                if !self.match_token(TokenKind::Comma) {
                    break;
                }
                if self.check(TokenKind::RBracket) {
                    break; // trailing comma
                }
            }
        }

        self.expect(TokenKind::RBracket)?;
        let span = start.merge(self.prev_span());
        Ok(Expr::new(ExprKind::SeqLit(elements), span))
    }

    fn parse_quantifier(&mut self, kind: QuantifierKind) -> ParseResult<Expr> {
        let start = self.current_span();
        self.advance(); // consume forall/exists

        let mut bindings = Vec::new();
        loop {
            let var = self.parse_ident()?;
            self.expect(TokenKind::In)?;
            // Don't allow `in` as binary op in domain to avoid ambiguity with outer `let...in`
            let domain = self.parse_expr_no_in()?;
            let span = var.span.merge(domain.span);
            bindings.push(Binding { var, domain, span });
            if !self.match_token(TokenKind::Comma) {
                break;
            }
        }

        self.expect(TokenKind::Colon)?;
        // Don't allow `in` as binary op to avoid ambiguity with outer `let...in`
        // Use parentheses for membership tests: `all x in S: (y in T)`
        let body = self.parse_expr_no_in()?;
        let span = start.merge(body.span);
        Ok(Expr::new(
            ExprKind::Quantifier {
                kind,
                bindings,
                body: Box::new(body),
            },
            span,
        ))
    }

    fn parse_choose(&mut self) -> ParseResult<Expr> {
        let start = self.current_span();
        self.expect(TokenKind::Choose)?;
        let var = self.parse_ident()?;
        self.expect(TokenKind::In)?;
        // Don't allow `in` as binary op in domain to avoid ambiguity with outer `let...in`
        let domain = self.parse_expr_no_in()?;
        self.expect(TokenKind::Colon)?;
        // Don't allow `in` as binary op to avoid ambiguity with outer `let...in`
        let predicate = self.parse_expr_no_in()?;
        let span = start.merge(predicate.span);
        Ok(Expr::new(
            ExprKind::Choose {
                var,
                domain: Box::new(domain),
                predicate: Box::new(predicate),
            },
            span,
        ))
    }

    fn parse_let(&mut self) -> ParseResult<Expr> {
        let start = self.current_span();
        self.expect(TokenKind::Let)?;
        let var = self.parse_ident()?;
        self.expect(TokenKind::Assign)?;
        // Use parse_expr_no_in so `in` is not consumed as binary operator
        let value = self.parse_expr_no_in()?;
        self.expect(TokenKind::In)?;
        let body = self.parse_expr()?;
        let span = start.merge(body.span);
        Ok(Expr::new(
            ExprKind::Let {
                var,
                value: Box::new(value),
                body: Box::new(body),
            },
            span,
        ))
    }

    fn parse_if(&mut self) -> ParseResult<Expr> {
        let start = self.current_span();
        self.expect(TokenKind::If)?;
        let cond = self.parse_expr()?;
        self.expect(TokenKind::Then)?;
        let then_branch = self.parse_expr()?;
        self.expect(TokenKind::Else)?;
        let else_branch = self.parse_expr()?;
        let span = start.merge(else_branch.span);
        Ok(Expr::new(
            ExprKind::If {
                cond: Box::new(cond),
                then_branch: Box::new(then_branch),
                else_branch: Box::new(else_branch),
            },
            span,
        ))
    }

    /// Parse record update fields: { field: value, [key]: value, ... }
    fn parse_record_updates(&mut self) -> ParseResult<Vec<RecordFieldUpdate>> {
        let mut updates = Vec::new();

        if self.check(TokenKind::RBrace) {
            return Ok(updates);
        }

        loop {
            let update = if self.match_token(TokenKind::LBracket) {
                // Dynamic key: [key]: value
                let key = self.parse_expr()?;
                self.expect(TokenKind::RBracket)?;
                self.expect(TokenKind::Colon)?;
                let value = self.parse_expr()?;
                RecordFieldUpdate::Dynamic { key, value }
            } else {
                // Static field: field: value
                let name = self.parse_ident()?;
                self.expect(TokenKind::Colon)?;
                let value = self.parse_expr()?;
                RecordFieldUpdate::Field { name, value }
            };
            updates.push(update);

            if !self.match_token(TokenKind::Comma) {
                break;
            }
            if self.check(TokenKind::RBrace) {
                break; // trailing comma
            }
        }

        Ok(updates)
    }

    // === Helper methods ===

    fn parse_ident(&mut self) -> ParseResult<Ident> {
        let span = self.current_span();
        match self.peek_kind() {
            TokenKind::Ident(name) => {
                let name = name.clone();
                self.advance();
                Ok(Ident::new(name, span))
            }
            // Allow built-in type names as identifiers in some contexts
            TokenKind::Nat => {
                self.advance();
                Ok(Ident::new("Nat", span))
            }
            TokenKind::Int => {
                self.advance();
                Ok(Ident::new("Int", span))
            }
            TokenKind::Bool => {
                self.advance();
                Ok(Ident::new("Bool", span))
            }
            TokenKind::String_ => {
                self.advance();
                Ok(Ident::new("String", span))
            }
            // Allow 'view' as identifier (contextual keyword)
            TokenKind::View => {
                self.advance();
                Ok(Ident::new("view", span))
            }
            _ => Err(ParseError::UnexpectedToken {
                expected: "identifier".to_string(),
                found: self.peek_kind().to_string(),
                span,
            }),
        }
    }

    fn peek(&self) -> &Token {
        self.tokens
            .get(self.pos)
            .unwrap_or_else(|| self.tokens.last().expect("tokens should have at least EOF"))
    }

    fn peek_kind(&self) -> TokenKind {
        self.peek().kind.clone()
    }

    /// Peek ahead by `offset` tokens (0 = current token).
    fn peek_ahead_kind(&self, offset: usize) -> TokenKind {
        self.tokens
            .get(self.pos + offset)
            .map(|t| t.kind.clone())
            .unwrap_or(TokenKind::Eof)
    }

    fn current_span(&self) -> Span {
        self.peek().span
    }

    fn prev_span(&self) -> Span {
        if self.pos > 0 {
            self.tokens[self.pos - 1].span
        } else {
            Span::dummy()
        }
    }

    fn is_at_end(&self) -> bool {
        matches!(self.peek_kind(), TokenKind::Eof)
    }

    fn check(&self, kind: TokenKind) -> bool {
        std::mem::discriminant(&self.peek_kind()) == std::mem::discriminant(&kind)
    }

    fn match_token(&mut self, kind: TokenKind) -> bool {
        if self.check(kind) {
            self.advance();
            true
        } else {
            false
        }
    }

    fn advance(&mut self) {
        if !self.is_at_end() {
            self.pos += 1;
        }
    }

    fn expect(&mut self, kind: TokenKind) -> ParseResult<()> {
        if self.check(kind.clone()) {
            self.advance();
            Ok(())
        } else {
            Err(ParseError::UnexpectedToken {
                expected: kind.to_string(),
                found: self.peek_kind().to_string(),
                span: self.current_span(),
            })
        }
    }
}

/// Parse source text into a module.
pub fn parse(source: &str) -> ParseResult<Module> {
    Parser::new(source).parse_module()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_expr_str(source: &str) -> Expr {
        // Wrap in minimal module for parsing
        let full = format!("module Test\ninit {{ {} }}", source);
        let module = parse(&full).unwrap();
        match &module.decls[0] {
            Decl::Init(init) => init.body.clone(),
            _ => panic!("expected init decl"),
        }
    }

    #[test]
    fn test_parse_empty_module() {
        let module = parse("module Empty").unwrap();
        assert_eq!(module.name.name, "Empty");
        assert!(module.decls.is_empty());
    }

    #[test]
    fn test_parse_var_decl() {
        let module = parse("module Test\nvar count: Nat").unwrap();
        assert_eq!(module.decls.len(), 1);
        match &module.decls[0] {
            Decl::Var(v) => {
                assert_eq!(v.name.name, "count");
            }
            _ => panic!("expected var decl"),
        }
    }

    #[test]
    fn test_parse_const_decl() {
        let module = parse("module Test\nconst MAX: Nat").unwrap();
        match &module.decls[0] {
            Decl::Const(c) => {
                assert_eq!(c.name.name, "MAX");
            }
            _ => panic!("expected const decl"),
        }
    }

    #[test]
    fn test_parse_type_decl() {
        let module = parse("module Test\ntype Balance = 0..100").unwrap();
        match &module.decls[0] {
            Decl::Type(t) => {
                assert_eq!(t.name.name, "Balance");
            }
            _ => panic!("expected type decl"),
        }
    }

    #[test]
    fn test_parse_init_block() {
        let module = parse("module Test\ninit { count == 0 }").unwrap();
        match &module.decls[0] {
            Decl::Init(i) => match &i.body.kind {
                ExprKind::Binary { op, .. } => {
                    assert_eq!(*op, BinOp::Eq);
                }
                _ => panic!("expected binary expr"),
            },
            _ => panic!("expected init decl"),
        }
    }

    #[test]
    fn test_parse_action() {
        let source = r#"
module Test
action Increment() {
    require count < MAX
    count = count + 1
}
"#;
        let module = parse(source).unwrap();
        match &module.decls[0] {
            Decl::Action(a) => {
                assert_eq!(a.name.name, "Increment");
                assert_eq!(a.body.requires.len(), 1);
                assert!(a.body.effect.is_some());
            }
            _ => panic!("expected action decl"),
        }
    }

    #[test]
    fn test_parse_assignment() {
        // Assignment syntax `x = x + 1` becomes `x' == x + 1` internally
        let expr = parse_expr_str("x = x + 1");
        match &expr.kind {
            ExprKind::Binary { left, .. } => match &left.kind {
                ExprKind::Primed(name) => assert_eq!(name, "x"),
                _ => panic!("expected primed var"),
            },
            _ => panic!("expected binary"),
        }
    }

    #[test]
    fn test_parse_quantifier() {
        let expr = parse_expr_str("all x in S: P(x)");
        match &expr.kind {
            ExprKind::Quantifier { kind, bindings, .. } => {
                assert_eq!(*kind, QuantifierKind::Forall);
                assert_eq!(bindings.len(), 1);
                assert_eq!(bindings[0].var.name, "x");
            }
            _ => panic!("expected quantifier"),
        }
    }

    #[test]
    fn test_parse_set_comprehension() {
        let expr = parse_expr_str("{ x in S if P(x) }");
        match &expr.kind {
            ExprKind::SetComprehension {
                var,
                filter: Some(_),
                ..
            } => {
                assert_eq!(var.name, "x");
            }
            _ => panic!("expected set comprehension"),
        }
    }

    #[test]
    fn test_parse_dict_merge() {
        // Dict merge uses | operator: r | {k: v}
        let expr = parse_expr_str("r | {a: 1, k: v}");
        match &expr.kind {
            ExprKind::Binary { op, right, .. } => {
                assert_eq!(*op, BinOp::Union);
                // Right side should be a dict literal
                match &right.kind {
                    ExprKind::DictLit(entries) => {
                        assert_eq!(entries.len(), 2);
                    }
                    _ => panic!("expected dict literal on right"),
                }
            }
            _ => panic!("expected binary union"),
        }
    }

    #[test]
    fn test_parse_if_then_else() {
        let expr = parse_expr_str("if x > 0 then 1 else 0");
        match &expr.kind {
            ExprKind::If { .. } => {}
            _ => panic!("expected if"),
        }
    }

    #[test]
    fn test_parse_let() {
        let expr = parse_expr_str("let x = 1 in x + 1");
        match &expr.kind {
            ExprKind::Let { var, .. } => {
                assert_eq!(var.name, "x");
            }
            _ => panic!("expected let"),
        }
    }

    #[test]
    fn test_parse_dict_comprehension() {
        // Dict comprehension { k: v for k in S } parses as FnLit
        let expr = parse_expr_str("{ x: x + 1 for x in S }");
        match &expr.kind {
            ExprKind::FnLit { var, .. } => {
                assert_eq!(var.name, "x");
            }
            _ => panic!("expected fn lit from dict comprehension"),
        }
    }

    #[test]
    fn test_parse_precedence() {
        // a + b * c should parse as a + (b * c)
        let expr = parse_expr_str("a + b * c");
        match &expr.kind {
            ExprKind::Binary { op, right, .. } => {
                assert_eq!(*op, BinOp::Add);
                match &right.kind {
                    ExprKind::Binary { op, .. } => {
                        assert_eq!(*op, BinOp::Mul);
                    }
                    _ => panic!("expected binary"),
                }
            }
            _ => panic!("expected binary"),
        }
    }

    #[test]
    fn test_parse_full_spec() {
        let source = r#"
module Counter

const MAX: Nat

var count: Nat

init {
    count == 0
}

action Increment() {
    require count < MAX
    count = count + 1
}

invariant Bounded {
    count <= MAX
}
"#;
        let module = parse(source).unwrap();
        assert_eq!(module.name.name, "Counter");
        assert_eq!(module.decls.len(), 5);
    }
}

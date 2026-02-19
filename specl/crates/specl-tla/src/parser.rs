//! TLA+ parser.

use crate::ast::*;
use crate::lexer::Lexer;
use crate::token::{Span, Token, TokenKind};
use thiserror::Error;

/// Parse error.
#[derive(Debug, Error)]
pub enum ParseError {
    #[error("unexpected token: expected {expected}, found {found} at position {position}")]
    UnexpectedToken {
        expected: String,
        found: String,
        position: usize,
    },
    #[error("unexpected end of file")]
    UnexpectedEof,
    #[error("invalid syntax: {message} at position {position}")]
    InvalidSyntax { message: String, position: usize },
}

/// TLA+ parser.
pub struct Parser {
    tokens: Vec<Token>,
    position: usize,
    /// When inside a bullet list, this is set to the bullet marker type to stop at.
    /// This allows nested expression parsing (like quantifier bodies) to respect bullet boundaries.
    bullet_stop_kind: Option<TokenKind>,
}

impl Parser {
    /// Create a new parser from source code.
    pub fn new(source: &str) -> Self {
        let tokens = Lexer::new(source).tokenize();
        Self {
            tokens,
            position: 0,
            bullet_stop_kind: None,
        }
    }

    /// Parse a TLA+ module.
    pub fn parse_module(&mut self) -> Result<TlaModule, ParseError> {
        // Some corpus files contain prose or wrapper text before the first module.
        // Skip forward until we see an actual module header: ---- MODULE Name ----
        while !self.is_at_end() {
            if self.check(&TokenKind::ModuleStart) && self.peek_is(&TokenKind::Module) {
                break;
            }
            self.advance();
        }

        let start = self.current_span().start;

        // ---- MODULE Name ----
        self.expect(TokenKind::ModuleStart)?;
        self.expect(TokenKind::Module)?;
        let name = match &self.current().kind {
            TokenKind::Ident(_) => self.expect_ident()?.name,
            TokenKind::Int(n) => {
                // Some corpus modules start with a digit (e.g. 2PCwithBTM).
                let mut module_name = n.to_string();
                self.advance();
                while let TokenKind::Ident(s) = &self.current().kind {
                    module_name.push_str(s);
                    self.advance();
                }
                module_name
            }
            _ => {
                return Err(ParseError::UnexpectedToken {
                    expected: "identifier".to_string(),
                    found: format!("{:?}", self.current().kind),
                    position: self.current_span().start,
                });
            }
        };
        self.expect(TokenKind::ModuleStart)?; // closing ----

        // EXTENDS
        let extends = if self.check(&TokenKind::Extends) {
            self.advance();
            self.parse_ident_list()?
                .into_iter()
                .map(|id| id.name)
                .collect()
        } else {
            Vec::new()
        };

        // Declarations
        let mut declarations = Vec::new();
        while !self.check(&TokenKind::ModuleEnd) && !self.is_at_end() {
            // Skip separator lines (---- used as visual dividers inside the module).
            // Also skip nested module blocks declared inside a parent module.
            if self.check(&TokenKind::ModuleStart) {
                if self.peek_is(&TokenKind::Module) {
                    self.skip_nested_module();
                    continue;
                }
                self.advance();
                continue;
            }
            declarations.push(self.parse_declaration()?);
        }

        // ====
        self.expect(TokenKind::ModuleEnd)?;

        let end = self.previous_span().end;
        Ok(TlaModule {
            name,
            extends,
            declarations,
            span: Span::new(start, end),
        })
    }

    fn parse_declaration(&mut self) -> Result<TlaDecl, ParseError> {
        let start = self.current_span().start;

        // LOCAL declarations are module-private wrappers around normal declarations.
        // Parse and retain the underlying declaration shape for translation.
        if self.check(&TokenKind::Local) {
            self.advance();
            return self.parse_declaration();
        }

        if self.check(&TokenKind::Constant) || self.check(&TokenKind::Constants) {
            self.advance();
            let names = match self.parse_ident_list() {
                Ok(names) => names,
                Err(_) => return self.recover_declaration(start),
            };
            let end = self.previous_span().end;
            return Ok(TlaDecl::Constant {
                names,
                span: Span::new(start, end),
            });
        }

        if self.check(&TokenKind::Variable) || self.check(&TokenKind::Variables) {
            self.advance();
            let names = match self.parse_ident_list() {
                Ok(names) => names,
                Err(_) => return self.recover_declaration(start),
            };
            let end = self.previous_span().end;
            return Ok(TlaDecl::Variable {
                names,
                span: Span::new(start, end),
            });
        }

        if self.check(&TokenKind::Assume) {
            self.advance();
            // Handle both "ASSUME expr" and "ASSUME name == expr" patterns
            // Check for named assumption: ASSUME name == expr
            if let TokenKind::Ident(_) = &self.current().kind {
                if self.peek_is(&TokenKind::DefEq) {
                    // Named assumption: skip the name and ==, then parse the expression
                    self.advance(); // skip name
                    self.advance(); // skip ==
                }
            }
            // Try to parse the ASSUME expression, but skip if it fails
            // (ASSUME is just an assertion about constants, not needed for model checking)
            match self.parse_expr() {
                Ok(expr) => {
                    let end = self.previous_span().end;
                    return Ok(TlaDecl::Assume {
                        expr,
                        span: Span::new(start, end),
                    });
                }
                Err(_) => {
                    // Skip to next declaration by consuming until we find a declaration keyword
                    self.skip_to_next_declaration();
                    return self.parse_declaration();
                }
            }
        }

        // RECURSIVE Name(_,_) just declares a recursive operator
        // Skip the entire RECURSIVE declaration and then parse the actual definition
        if self.check(&TokenKind::Recursive) {
            self.advance();
            // Skip the operator name
            if self.check_ident() {
                self.advance();
            }
            // Skip parameters if any: (_, _)
            if self.check(&TokenKind::LParen) {
                self.advance();
                // Skip until matching RParen
                let mut depth = 1;
                while depth > 0 && !self.is_at_end() {
                    if self.check(&TokenKind::LParen) {
                        depth += 1;
                    } else if self.check(&TokenKind::RParen) {
                        depth -= 1;
                    }
                    self.advance();
                }
            }
            // Now we should be at the actual operator definition
            if !self.is_at_end() && !self.check(&TokenKind::ModuleEnd) {
                return self.parse_declaration();
            }
        }

        if self.check(&TokenKind::Theorem) || self.check(&TokenKind::Lemma) {
            // THEOREM/LEMMA may have complex proof constructs (ASSUME NEW ... PROVE)
            // Skip them entirely since they're not needed for model checking.
            self.skip_to_next_declaration();
            // Skip separator lines that skip_to_next_declaration may stop at
            while self.check(&TokenKind::ModuleStart) {
                self.advance();
            }
            if !self.is_at_end() && !self.check(&TokenKind::ModuleEnd) {
                return self.parse_declaration();
            } else {
                // At end of module, return a dummy theorem
                return Ok(TlaDecl::Theorem {
                    name: None,
                    expr: TlaExpr::new(TlaExprKind::Bool(true), Span::new(start, start)),
                    span: Span::new(start, start),
                });
            }
        }

        if self.check(&TokenKind::Instance) {
            return self.parse_instance();
        }

        // Operator definition: Name(params) == body or Name == body
        let name = match self.expect_ident() {
            Ok(name) => name,
            Err(_) => return self.recover_declaration(start),
        };

        let params = if self.check(&TokenKind::LBracket) {
            // Operator function-style binding: Name[x \in S, y \in T] == ...
            // Keep parameter names; domain constraints remain in the body semantics.
            self.advance();
            let mut bound_params = Vec::new();
            loop {
                let var = match self.expect_ident() {
                    Ok(var) => var,
                    Err(_) => return self.recover_declaration(start),
                };
                bound_params.push(var);
                if self.expect(TokenKind::SetIn).is_err() {
                    return self.recover_declaration(start);
                }
                if self.parse_expr_prec(6).is_err() {
                    return self.recover_declaration(start);
                }
                if !self.check(&TokenKind::Comma) {
                    break;
                }
                self.advance();
            }
            if self.expect(TokenKind::RBracket).is_err() {
                return self.recover_declaration(start);
            }
            bound_params
        } else if self.check(&TokenKind::LParen) {
            self.advance();
            let params = if !self.check(&TokenKind::RParen) {
                match self.parse_ident_list() {
                    Ok(params) => params,
                    Err(_) => return self.recover_declaration(start),
                }
            } else {
                Vec::new()
            };
            if self.expect(TokenKind::RParen).is_err() {
                return self.recover_declaration(start);
            }
            params
        } else {
            Vec::new()
        };

        if self.expect(TokenKind::DefEq).is_err() {
            return self.recover_declaration(start);
        }

        // Check for named INSTANCE: Name == INSTANCE Module
        if self.check(&TokenKind::Instance) {
            self.advance();
            let module = match self.expect_ident() {
                Ok(module) => module,
                Err(_) => return self.recover_declaration(start),
            };

            let substitutions = if self.check(&TokenKind::With) {
                self.advance();
                let mut subs = Vec::new();
                loop {
                    let sub_name = match self.expect_ident() {
                        Ok(name) => name,
                        Err(_) => return self.recover_declaration(start),
                    };
                    if self.expect(TokenKind::LeftArrow).is_err() {
                        return self.recover_declaration(start);
                    }
                    let value = match self.parse_expr() {
                        Ok(value) => value,
                        Err(_) => return self.recover_declaration(start),
                    };
                    subs.push((sub_name, value));
                    if !self.check(&TokenKind::Comma) {
                        break;
                    }
                    self.advance();
                }
                subs
            } else {
                Vec::new()
            };

            let end = self.previous_span().end;
            return Ok(TlaDecl::Instance {
                name: Some(name),
                module,
                substitutions,
                span: Span::new(start, end),
            });
        }

        let body = match self.parse_expr() {
            Ok(body) => body,
            Err(_) => return self.recover_declaration(start),
        };
        let end = self.previous_span().end;

        Ok(TlaDecl::Operator {
            name,
            params,
            body,
            span: Span::new(start, end),
        })
    }

    fn parse_instance(&mut self) -> Result<TlaDecl, ParseError> {
        let start = self.current_span().start;
        self.expect(TokenKind::Instance)?;

        let module = self.expect_ident()?;

        let substitutions = if self.check(&TokenKind::With) {
            self.advance();
            let mut subs = Vec::new();
            loop {
                let name = self.expect_ident()?;
                self.expect(TokenKind::LeftArrow)?;
                let value = self.parse_expr()?;
                subs.push((name, value));
                if !self.check(&TokenKind::Comma) {
                    break;
                }
                self.advance();
            }
            subs
        } else {
            Vec::new()
        };

        let end = self.previous_span().end;
        Ok(TlaDecl::Instance {
            name: None,
            module,
            substitutions,
            span: Span::new(start, end),
        })
    }

    fn parse_ident_list(&mut self) -> Result<Vec<TlaIdent>, ParseError> {
        let mut idents = vec![self.expect_ident_with_signature()?];
        while self.check(&TokenKind::Comma) {
            self.advance();
            idents.push(self.expect_ident_with_signature()?);
        }
        Ok(idents)
    }

    // === Expression parsing ===

    fn parse_expr(&mut self) -> Result<TlaExpr, ParseError> {
        // Handle TLA+ bullet lists: leading /\ or \/ followed by a list
        // /\ e1
        // /\ e2
        // is equivalent to e1 /\ e2
        if self.check(&TokenKind::And) {
            return self.parse_bullet_list(TlaBinOp::And);
        }
        if self.check(&TokenKind::Or) {
            return self.parse_bullet_list(TlaBinOp::Or);
        }
        self.parse_expr_prec(0)
    }

    /// Parse an expression in a nested context (like set comprehension, function definition, etc.)
    /// where bullet list markers should NOT be recognized as such.
    fn parse_expr_nested(&mut self) -> Result<TlaExpr, ParseError> {
        let saved_stop_kind = self.bullet_stop_kind.take();
        let result = self.parse_expr();
        self.bullet_stop_kind = saved_stop_kind;
        result
    }

    fn parse_bullet_list(&mut self, op: TlaBinOp) -> Result<TlaExpr, ParseError> {
        let kind = if op == TlaBinOp::And {
            TokenKind::And
        } else {
            TokenKind::Or
        };

        let start = self.current_span().start;
        self.advance(); // consume first /\ or \/

        // Save the previous bullet_stop_kind and set the new one
        let prev_stop_kind = self.bullet_stop_kind.take();
        self.bullet_stop_kind = Some(kind.clone());

        // Parse each bullet item
        let mut exprs = vec![self.parse_bullet_item(op)?];

        // Continue while we see more bullets of the same type
        while self.check(&kind) {
            self.advance();
            exprs.push(self.parse_bullet_item(op)?);
        }

        // Restore the previous bullet_stop_kind
        self.bullet_stop_kind = prev_stop_kind;

        // Fold into binary tree
        let mut result = exprs.remove(0);
        for expr in exprs {
            let span = Span::new(start, expr.span.end);
            result = TlaExpr::new(
                TlaExprKind::Binary {
                    op,
                    left: Box::new(result),
                    right: Box::new(expr),
                },
                span,
            );
        }

        Ok(result)
    }

    /// Parse a bullet list item, potentially containing nested bullet lists.
    /// Uses self.bullet_stop_kind to know when to stop.
    fn parse_bullet_item(&mut self, current_op: TlaBinOp) -> Result<TlaExpr, ParseError> {
        // Check for nested bullet list of the opposite kind
        let nested_kind = if current_op == TlaBinOp::And {
            TokenKind::Or
        } else {
            TokenKind::And
        };
        let nested_op = if current_op == TlaBinOp::And {
            TlaBinOp::Or
        } else {
            TlaBinOp::And
        };

        // If we see the nested operator at the START of the item, parse it as a nested bullet list
        if self.check(&nested_kind) {
            return self.parse_bullet_list(nested_op);
        }

        // Parse expression - parse_expr_prec will use self.bullet_stop_kind
        self.parse_expr_prec(0)
    }
    fn parse_expr_prec(&mut self, min_prec: u8) -> Result<TlaExpr, ParseError> {
        // Handle bullet lists at the START of any expression context
        // This allows e.g. `A => /\ B /\ C` to have the /\ list as the right operand
        let mut left = if self.check(&TokenKind::And) {
            self.parse_bullet_list(TlaBinOp::And)?
        } else if self.check(&TokenKind::Or) {
            self.parse_bullet_list(TlaBinOp::Or)?
        } else {
            self.parse_unary()?
        };

        while let Some(op) = self.current_binop() {
            // If we're in a bullet list and see the bullet marker, stop
            if let Some(ref stop_kind) = self.bullet_stop_kind {
                if self.check(stop_kind) {
                    break;
                }
            }

            let prec = op.precedence();
            if prec < min_prec {
                break;
            }

            self.advance();
            let next_prec = if op.is_right_assoc() { prec } else { prec + 1 };
            let right = self.parse_expr_prec(next_prec)?;

            let span = left.span.merge(right.span);
            left = TlaExpr::new(
                TlaExprKind::Binary {
                    op,
                    left: Box::new(left),
                    right: Box::new(right),
                },
                span,
            );
        }

        // Handle ~> (leads-to) which we parse specially
        if self.check(&TokenKind::LeadsTo) {
            // Check bullet stop
            if self
                .bullet_stop_kind
                .as_ref()
                .is_some_and(|k| self.check(k))
            {
                return Ok(left);
            }
            self.advance();
            let right = self.parse_expr_prec(2)?;
            let span = left.span.merge(right.span);
            left = TlaExpr::new(
                TlaExprKind::LeadsTo {
                    left: Box::new(left),
                    right: Box::new(right),
                },
                span,
            );
        }

        // Handle @@ (function combine) - parse at high precedence
        while self.check(&TokenKind::AtAt) {
            // Check bullet stop
            if self
                .bullet_stop_kind
                .as_ref()
                .is_some_and(|k| self.check(k))
            {
                break;
            }
            self.advance();
            let right = self.parse_expr_prec(7)?; // Same as Add/Sub
            let span = left.span.merge(right.span);
            left = TlaExpr::new(
                TlaExprKind::FunctionCombine {
                    left: Box::new(left),
                    right: Box::new(right),
                },
                span,
            );
        }

        // Handle :> (singleton function) - parse at high precedence
        while self.check(&TokenKind::ColonGt) {
            // Check bullet stop
            if self
                .bullet_stop_kind
                .as_ref()
                .is_some_and(|k| self.check(k))
            {
                break;
            }
            self.advance();
            let right = self.parse_expr_prec(7)?; // Same as Add/Sub
            let span = left.span.merge(right.span);
            left = TlaExpr::new(
                TlaExprKind::SingletonFunction {
                    key: Box::new(left),
                    value: Box::new(right),
                },
                span,
            );
        }

        Ok(left)
    }

    fn current_binop(&self) -> Option<TlaBinOp> {
        match &self.current().kind {
            TokenKind::And => Some(TlaBinOp::And),
            TokenKind::Or => Some(TlaBinOp::Or),
            TokenKind::Implies => Some(TlaBinOp::Implies),
            TokenKind::Iff => Some(TlaBinOp::Iff),
            TokenKind::Eq => Some(TlaBinOp::Eq),
            TokenKind::Neq => Some(TlaBinOp::Ne),
            TokenKind::Lt => Some(TlaBinOp::Lt),
            TokenKind::Le => Some(TlaBinOp::Le),
            TokenKind::Gt => Some(TlaBinOp::Gt),
            TokenKind::Ge => Some(TlaBinOp::Ge),
            TokenKind::Plus => Some(TlaBinOp::Add),
            TokenKind::Minus => Some(TlaBinOp::Sub),
            TokenKind::Star => Some(TlaBinOp::Mul),
            TokenKind::Slash => Some(TlaBinOp::Div),
            TokenKind::Percent => Some(TlaBinOp::Mod),
            TokenKind::Div => Some(TlaBinOp::Div),
            TokenKind::Caret => Some(TlaBinOp::Exp),
            TokenKind::SetIn => Some(TlaBinOp::In),
            TokenKind::SetNotIn => Some(TlaBinOp::NotIn),
            TokenKind::Cup => Some(TlaBinOp::Cup),
            TokenKind::Cap => Some(TlaBinOp::Cap),
            TokenKind::SetMinus => Some(TlaBinOp::SetDiff),
            TokenKind::SubsetEq => Some(TlaBinOp::SubsetEq),
            TokenKind::Times => Some(TlaBinOp::Times),
            TokenKind::Concat => Some(TlaBinOp::Concat),
            TokenKind::DotDot => None, // Handled specially in range parsing
            _ => None,
        }
    }

    fn parse_unary(&mut self) -> Result<TlaExpr, ParseError> {
        let start = self.current_span().start;

        // Unary operators
        if self.check(&TokenKind::Not) {
            self.advance();
            // Support negation over bullet lists: ~ /\ e1 /\ e2
            let operand = if self.check(&TokenKind::And) {
                self.parse_bullet_list(TlaBinOp::And)?
            } else if self.check(&TokenKind::Or) {
                self.parse_bullet_list(TlaBinOp::Or)?
            } else {
                self.parse_unary()?
            };
            let span = Span::new(start, operand.span.end);
            return Ok(TlaExpr::new(
                TlaExprKind::Unary {
                    op: TlaUnaryOp::Not,
                    operand: Box::new(operand),
                },
                span,
            ));
        }

        if self.check(&TokenKind::Minus) {
            self.advance();
            let operand = self.parse_unary()?;
            let span = Span::new(start, operand.span.end);
            return Ok(TlaExpr::new(
                TlaExprKind::Unary {
                    op: TlaUnaryOp::Neg,
                    operand: Box::new(operand),
                },
                span,
            ));
        }

        // Temporal operators
        if self.check(&TokenKind::Always) {
            self.advance();
            let operand = self.parse_unary()?;
            let span = Span::new(start, operand.span.end);
            return Ok(TlaExpr::new(TlaExprKind::Always(Box::new(operand)), span));
        }

        if self.check(&TokenKind::Eventually) {
            self.advance();
            let operand = self.parse_unary()?;
            let span = Span::new(start, operand.span.end);
            return Ok(TlaExpr::new(
                TlaExprKind::Eventually(Box::new(operand)),
                span,
            ));
        }

        // ENABLED
        if self.check(&TokenKind::Enabled) {
            self.advance();
            let operand = self.parse_unary()?;
            let span = Span::new(start, operand.span.end);
            return Ok(TlaExpr::new(TlaExprKind::Enabled(Box::new(operand)), span));
        }

        // DOMAIN
        if self.check(&TokenKind::Domain) {
            self.advance();
            let operand = self.parse_unary()?;
            let span = Span::new(start, operand.span.end);
            return Ok(TlaExpr::new(TlaExprKind::Domain(Box::new(operand)), span));
        }

        // SUBSET (power set)
        if self.check(&TokenKind::Subset) {
            self.advance();
            let operand = self.parse_unary()?;
            let span = Span::new(start, operand.span.end);
            return Ok(TlaExpr::new(TlaExprKind::PowerSet(Box::new(operand)), span));
        }

        // UNION (distributed)
        if self.check(&TokenKind::Union) {
            self.advance();
            let operand = self.parse_unary()?;
            let span = Span::new(start, operand.span.end);
            return Ok(TlaExpr::new(TlaExprKind::BigUnion(Box::new(operand)), span));
        }

        // WF_vars(Action) - Weak fairness
        if self.check(&TokenKind::WeakFairness) {
            self.advance();
            // Parse the subscript expression (vars)
            let vars = self.parse_primary()?;
            // Parse the action in parentheses
            self.expect(TokenKind::LParen)?;
            let action = self.parse_expr_nested()?;
            let end = self.current_span().end;
            self.expect(TokenKind::RParen)?;
            let span = Span::new(start, end);
            return Ok(TlaExpr::new(
                TlaExprKind::WeakFairness {
                    vars: Box::new(vars),
                    action: Box::new(action),
                },
                span,
            ));
        }

        // SF_vars(Action) - Strong fairness
        if self.check(&TokenKind::StrongFairness) {
            self.advance();
            // Parse the subscript expression (vars)
            let vars = self.parse_primary()?;
            // Parse the action in parentheses
            self.expect(TokenKind::LParen)?;
            let action = self.parse_expr_nested()?;
            let end = self.current_span().end;
            self.expect(TokenKind::RParen)?;
            let span = Span::new(start, end);
            return Ok(TlaExpr::new(
                TlaExprKind::StrongFairness {
                    vars: Box::new(vars),
                    action: Box::new(action),
                },
                span,
            ));
        }

        self.parse_postfix()
    }

    fn parse_postfix(&mut self) -> Result<TlaExpr, ParseError> {
        let mut expr = self.parse_primary()?;

        loop {
            // Prime: e'
            if self.check(&TokenKind::Prime) {
                let end = self.current_span().end;
                self.advance();
                let span = Span::new(expr.span.start, end);
                expr = TlaExpr::new(TlaExprKind::Primed(Box::new(expr)), span);
                continue;
            }

            // Function application: f[x] or f[x, y]
            if self.check(&TokenKind::LBracket) {
                self.advance();
                let mut args = vec![self.parse_expr_nested()?];
                while self.check(&TokenKind::Comma) {
                    self.advance();
                    args.push(self.parse_expr_nested()?);
                }
                let end = self.current_span().end;
                self.expect(TokenKind::RBracket)?;
                let span = Span::new(expr.span.start, end);
                expr = TlaExpr::new(
                    TlaExprKind::FunctionApp {
                        func: Box::new(expr),
                        args,
                    },
                    span,
                );
                continue;
            }

            // Field access: r.field
            if self.check(&TokenKind::Dot) {
                self.advance();
                let field = self.expect_ident()?;
                let span = Span::new(expr.span.start, field.span.end);
                expr = TlaExpr::new(
                    TlaExprKind::FieldAccess {
                        base: Box::new(expr),
                        field,
                    },
                    span,
                );
                continue;
            }

            // Instance operator access: Instance!Operator or Instance!Operator(args)
            if self.check(&TokenKind::Bang) {
                self.advance();
                let name = self.expect_ident()?;

                // Check for operator call: Instance!Op(args)
                let args = if self.check(&TokenKind::LParen) {
                    self.advance();
                    let args = if !self.check(&TokenKind::RParen) {
                        self.parse_expr_list()?
                    } else {
                        Vec::new()
                    };
                    self.expect(TokenKind::RParen)?;
                    args
                } else {
                    Vec::new()
                };

                let span = Span::new(expr.span.start, self.previous_span().end);
                expr = TlaExpr::new(
                    TlaExprKind::InstanceOp {
                        instance: Box::new(expr),
                        name,
                        args,
                    },
                    span,
                );
                continue;
            }

            break;
        }

        Ok(expr)
    }

    fn parse_primary(&mut self) -> Result<TlaExpr, ParseError> {
        let start = self.current_span().start;

        // Boolean literals
        if self.check(&TokenKind::True) {
            let span = self.current_span();
            self.advance();
            return Ok(TlaExpr::new(TlaExprKind::Bool(true), span));
        }
        if self.check(&TokenKind::False) {
            let span = self.current_span();
            self.advance();
            return Ok(TlaExpr::new(TlaExprKind::Bool(false), span));
        }

        // BOOLEAN (the set {TRUE, FALSE})
        if self.check(&TokenKind::Boolean) {
            let span = self.current_span();
            self.advance();
            return Ok(TlaExpr::new(
                TlaExprKind::SetEnum {
                    elements: vec![
                        TlaExpr::new(TlaExprKind::Bool(true), span),
                        TlaExpr::new(TlaExprKind::Bool(false), span),
                    ],
                },
                span,
            ));
        }

        // Integer literal
        if let TokenKind::Int(n) = self.current().kind {
            let span = self.current_span();
            self.advance();

            // Check for range: n..m
            if self.check(&TokenKind::DotDot) {
                self.advance();
                let hi = self.parse_postfix()?;
                let full_span = Span::new(start, hi.span.end);
                return Ok(TlaExpr::new(
                    TlaExprKind::Range {
                        lo: Box::new(TlaExpr::new(TlaExprKind::Int(n), span)),
                        hi: Box::new(hi),
                    },
                    full_span,
                ));
            }

            return Ok(TlaExpr::new(TlaExprKind::Int(n), span));
        }

        // String literal
        if let TokenKind::String(s) = &self.current().kind {
            let s = s.clone();
            let span = self.current_span();
            self.advance();
            return Ok(TlaExpr::new(TlaExprKind::String(s), span));
        }

        // Quantifiers
        if self.check(&TokenKind::Forall) {
            return self.parse_quantifier(true);
        }
        if self.check(&TokenKind::Exists) {
            return self.parse_quantifier(false);
        }

        // CHOOSE
        if self.check(&TokenKind::Choose) {
            return self.parse_choose();
        }

        // UNCHANGED
        if self.check(&TokenKind::Unchanged) {
            return self.parse_unchanged();
        }

        // @ (old value in EXCEPT expression)
        if self.check(&TokenKind::At) {
            let span = self.current_span();
            self.advance();
            return Ok(TlaExpr::new(TlaExprKind::ExceptAt, span));
        }

        // IF-THEN-ELSE
        if self.check(&TokenKind::If) {
            return self.parse_if();
        }

        // CASE
        if self.check(&TokenKind::Case) {
            return self.parse_case();
        }

        // LET-IN
        if self.check(&TokenKind::Let) {
            return self.parse_let();
        }

        // Tuple: <<...>>
        if self.check(&TokenKind::LAngle) {
            return self.parse_tuple();
        }

        // Set or Record: {...} or [...]
        if self.check(&TokenKind::LBrace) {
            return self.parse_set_or_comprehension();
        }

        // Function/record: [...]
        if self.check(&TokenKind::LBracket) {
            return self.parse_bracket_expr();
        }

        // Parenthesized expression
        if self.check(&TokenKind::LParen) {
            self.advance();
            let inner = self.parse_expr_nested()?;
            let end = self.current_span().end;
            self.expect(TokenKind::RParen)?;
            let span = Span::new(start, end);
            return Ok(TlaExpr::new(TlaExprKind::Paren(Box::new(inner)), span));
        }

        // Identifier or operator call
        if self.check_ident() {
            let ident = self.expect_ident()?;

            // Label syntax: Name :: expr — discard label, parse the expression
            if self.check(&TokenKind::ColonColon) {
                self.advance();
                return self.parse_expr();
            }

            // Check for operator call: Op(args)
            if self.check(&TokenKind::LParen) {
                self.advance();
                let args = if !self.check(&TokenKind::RParen) {
                    self.parse_expr_list()?
                } else {
                    Vec::new()
                };
                let end = self.current_span().end;
                self.expect(TokenKind::RParen)?;
                let span = Span::new(start, end);
                return Ok(TlaExpr::new(
                    TlaExprKind::OpApp {
                        name: ident.name,
                        args,
                    },
                    span,
                ));
            }

            // Check for range: ident..expr
            if self.check(&TokenKind::DotDot) {
                self.advance();
                let hi = self.parse_postfix()?;
                let full_span = Span::new(start, hi.span.end);
                return Ok(TlaExpr::new(
                    TlaExprKind::Range {
                        lo: Box::new(TlaExpr::new(TlaExprKind::Ident(ident.name), ident.span)),
                        hi: Box::new(hi),
                    },
                    full_span,
                ));
            }

            return Ok(TlaExpr::new(TlaExprKind::Ident(ident.name), ident.span));
        }

        Err(ParseError::UnexpectedToken {
            expected: "expression".to_string(),
            found: format!("{:?}", self.current().kind),
            position: start,
        })
    }

    fn parse_quantifier(&mut self, is_forall: bool) -> Result<TlaExpr, ParseError> {
        let start = self.current_span().start;
        self.advance(); // \A or \E

        let bindings = self.parse_bindings()?;
        self.expect(TokenKind::Colon)?;
        let body = self.parse_expr()?;

        let span = Span::new(start, body.span.end);
        let kind = if is_forall {
            TlaExprKind::Forall {
                bindings,
                body: Box::new(body),
            }
        } else {
            TlaExprKind::Exists {
                bindings,
                body: Box::new(body),
            }
        };
        Ok(TlaExpr::new(kind, span))
    }

    fn parse_bindings(&mut self) -> Result<Vec<TlaBinding>, ParseError> {
        let mut bindings = Vec::new();
        loop {
            // Parse variable(s) - can be `x` or `x, y` sharing same domain
            // TLA+ syntax: x, y \in S (multiple vars share domain) vs x \in S, y \in T (separate domains)
            // Collect identifiers until we see \in
            let mut vars = vec![self.expect_ident()?];

            // Keep collecting vars while we see comma (not \in)
            while self.check(&TokenKind::Comma) {
                self.advance(); // comma
                vars.push(self.expect_ident()?);
            }

            self.expect(TokenKind::SetIn)?;
            let domain = self.parse_expr_prec(6)?; // Parse at higher precedence than comparison

            // Create a binding for each variable
            for var in vars {
                let span = var.span.merge(domain.span);
                bindings.push(TlaBinding {
                    var,
                    domain: domain.clone(),
                    span,
                });
            }

            // Check if there's another binding (comma followed by more vars)
            if !self.check(&TokenKind::Comma) {
                break;
            }
            self.advance(); // comma
        }
        Ok(bindings)
    }

    fn parse_choose(&mut self) -> Result<TlaExpr, ParseError> {
        let start = self.current_span().start;
        self.advance(); // CHOOSE

        let var = self.expect_ident()?;

        // Check if there's a domain: CHOOSE x \in S : P  vs  CHOOSE x : P
        let domain = if self.check(&TokenKind::SetIn) {
            self.advance();
            let dom = self.parse_expr_prec(6)?;
            Some(Box::new(dom))
        } else {
            None
        };

        self.expect(TokenKind::Colon)?;
        let predicate = self.parse_expr()?;

        let span = Span::new(start, predicate.span.end);
        Ok(TlaExpr::new(
            TlaExprKind::Choose {
                var,
                domain,
                predicate: Box::new(predicate),
            },
            span,
        ))
    }

    fn parse_unchanged(&mut self) -> Result<TlaExpr, ParseError> {
        let start = self.current_span().start;
        self.advance(); // UNCHANGED

        let vars = if self.check(&TokenKind::LAngle) {
            self.advance();
            let vars = self.parse_ident_list()?;
            self.expect(TokenKind::RAngle)?;
            vars
        } else {
            vec![self.expect_ident()?]
        };

        let end = self.previous_span().end;
        Ok(TlaExpr::new(
            TlaExprKind::Unchanged(vars),
            Span::new(start, end),
        ))
    }

    fn parse_if(&mut self) -> Result<TlaExpr, ParseError> {
        let start = self.current_span().start;
        self.advance(); // IF

        // Use parse_expr_nested for all parts to avoid bullet list issues inside IF
        let cond = self.parse_expr_nested()?;
        self.expect(TokenKind::Then)?;
        let then_branch = self.parse_expr_nested()?;
        self.expect(TokenKind::Else)?;
        let else_branch = self.parse_expr_nested()?;

        let span = Span::new(start, else_branch.span.end);
        Ok(TlaExpr::new(
            TlaExprKind::IfThenElse {
                cond: Box::new(cond),
                then_branch: Box::new(then_branch),
                else_branch: Box::new(else_branch),
            },
            span,
        ))
    }

    fn parse_case(&mut self) -> Result<TlaExpr, ParseError> {
        let start = self.current_span().start;
        self.advance(); // CASE

        let mut arms = Vec::new();
        let mut other = None;

        loop {
            if self.check(&TokenKind::Other) {
                self.advance();
                // CASE uses -> (Arrow), not |-> (MapsTo)
                self.expect(TokenKind::Arrow)?;
                other = Some(Box::new(self.parse_expr_nested()?));
                break;
            }

            let cond = self.parse_expr_nested()?;
            // CASE uses -> (Arrow), not |-> (MapsTo)
            self.expect(TokenKind::Arrow)?;
            let result = self.parse_expr_nested()?;
            arms.push((cond, result));

            // Check if there are more arms: must be preceded by [] (Always) or OTHER
            if !self.check(&TokenKind::Always) && !self.check(&TokenKind::Other) {
                break;
            }
            // Handle [] as arm separator (tokenized as Always)
            if self.check(&TokenKind::Always) {
                self.advance();
            }
        }

        let end = self.previous_span().end;
        Ok(TlaExpr::new(
            TlaExprKind::Case { arms, other },
            Span::new(start, end),
        ))
    }

    fn parse_let(&mut self) -> Result<TlaExpr, ParseError> {
        let start = self.current_span().start;
        self.advance(); // LET

        let mut defs = Vec::new();
        while !self.check(&TokenKind::In) {
            let name = self.expect_ident()?;

            // Check for recursive function syntax: Name[var \in Domain]
            let recursive_binding = if self.check(&TokenKind::LBracket) {
                self.advance(); // [
                let var = self.expect_ident()?;
                self.expect(TokenKind::SetIn)?;
                // Parse domain at high precedence to avoid consuming too much
                let domain = self.parse_expr_prec(6)?;
                let binding_span = var.span.merge(domain.span);
                self.expect(TokenKind::RBracket)?;
                Some(TlaBinding {
                    var,
                    domain,
                    span: binding_span,
                })
            } else {
                None
            };

            // Check for parameterized operator: Name(params)
            let params = if self.check(&TokenKind::LParen) {
                self.advance();
                let params = if !self.check(&TokenKind::RParen) {
                    self.parse_ident_list()?
                } else {
                    Vec::new()
                };
                self.expect(TokenKind::RParen)?;
                params
            } else {
                Vec::new()
            };

            self.expect(TokenKind::DefEq)?;
            // LET can bind an instance alias: Name == INSTANCE Module [WITH ...]
            // We retain module identity for downstream translation and ignore substitutions here.
            let body = if self.check(&TokenKind::Instance) {
                self.advance();
                let module = self.expect_ident()?;
                if self.check(&TokenKind::With) {
                    self.advance();
                    loop {
                        let _ = self.expect_ident()?;
                        self.expect(TokenKind::LeftArrow)?;
                        let _ = self.parse_expr_nested()?;
                        if !self.check(&TokenKind::Comma) {
                            break;
                        }
                        self.advance();
                    }
                }
                TlaExpr::new(TlaExprKind::Ident(module.name), module.span)
            } else {
                // Use parse_expr_nested for LET definition bodies to avoid treating
                // internal /\ or \/ as bullet markers
                self.parse_expr_nested()?
            };
            let span = name.span.merge(body.span);
            defs.push(TlaLetDef {
                name,
                params,
                recursive_binding,
                body,
                span,
            });
        }

        self.expect(TokenKind::In)?;
        let body = self.parse_expr()?;

        let span = Span::new(start, body.span.end);
        Ok(TlaExpr::new(
            TlaExprKind::LetIn {
                defs,
                body: Box::new(body),
            },
            span,
        ))
    }

    fn parse_tuple(&mut self) -> Result<TlaExpr, ParseError> {
        let start = self.current_span().start;
        self.advance(); // <<

        let elements = if !self.check(&TokenKind::RAngle) {
            self.parse_expr_list()?
        } else {
            Vec::new()
        };

        let end = self.current_span().end;
        self.expect(TokenKind::RAngle)?;

        Ok(TlaExpr::new(
            TlaExprKind::Tuple { elements },
            Span::new(start, end),
        ))
    }

    fn parse_set_or_comprehension(&mut self) -> Result<TlaExpr, ParseError> {
        let start = self.current_span().start;
        self.advance(); // {

        // Empty set
        if self.check(&TokenKind::RBrace) {
            let end = self.current_span().end;
            self.advance();
            return Ok(TlaExpr::new(
                TlaExprKind::SetEnum {
                    elements: Vec::new(),
                },
                Span::new(start, end),
            ));
        }

        // Parse first expression and determine if this is:
        // - Set filter: {x \in S: P(x)}
        // - Set map: {e: x \in S}
        // - Set enumeration: {a, b, c}
        // Use parse_expr_nested because we're inside braces
        let first = self.parse_expr_nested()?;

        // Check for set filter: {x \in S: P(x)}
        // This is recognized when first is `x \in S` (Binary In with Ident on left)
        if let TlaExprKind::Binary {
            op: TlaBinOp::In,
            left,
            right,
        } = &first.kind
        {
            if let TlaExprKind::Ident(var_name) = &left.kind {
                if self.check(&TokenKind::Colon) {
                    self.advance();
                    let predicate = self.parse_expr_nested()?;
                    let end = self.current_span().end;
                    self.expect(TokenKind::RBrace)?;
                    return Ok(TlaExpr::new(
                        TlaExprKind::SetFilter {
                            var: TlaIdent::new(var_name.clone(), left.span),
                            domain: right.clone(),
                            predicate: Box::new(predicate),
                        },
                        Span::new(start, end),
                    ));
                }
            }
        }

        // Check for set map: {e: x \in S}
        if self.check(&TokenKind::Colon) {
            self.advance();

            // Expect binding: x \in S
            if self.check_ident() {
                let var = self.expect_ident()?;
                if self.check(&TokenKind::SetIn) {
                    self.advance();
                    let domain = self.parse_expr_nested()?;
                    let end = self.current_span().end;
                    self.expect(TokenKind::RBrace)?;
                    return Ok(TlaExpr::new(
                        TlaExprKind::SetMap {
                            element: Box::new(first),
                            var,
                            domain: Box::new(domain),
                        },
                        Span::new(start, end),
                    ));
                }
            }
            // If we get here, it's a parse error - colon in unexpected position
            return Err(ParseError::InvalidSyntax {
                message: "expected set binding after colon".to_string(),
                position: self.current_span().start,
            });
        }

        // Regular set enumeration
        let mut elements = vec![first];
        while self.check(&TokenKind::Comma) {
            self.advance();
            if self.check(&TokenKind::RBrace) {
                break;
            }
            elements.push(self.parse_expr_nested()?);
        }

        let end = self.current_span().end;
        self.expect(TokenKind::RBrace)?;

        Ok(TlaExpr::new(
            TlaExprKind::SetEnum { elements },
            Span::new(start, end),
        ))
    }

    fn parse_bracket_expr(&mut self) -> Result<TlaExpr, ParseError> {
        let start = self.current_span().start;
        self.advance(); // [

        // First, try specialized forms that start with an identifier.
        if self.check_ident() {
            let saved_pos = self.position;

            // Function definition:
            //   [x \in S |-> e]
            //   [x, y \in S |-> e]
            //   [x \in S, y \in T |-> e]
            if let Ok(bindings) = self.parse_bindings() {
                if self.check(&TokenKind::MapsTo) {
                    self.advance();
                    let body = self.parse_expr_nested()?;
                    let end = self.current_span().end;
                    self.expect(TokenKind::RBracket)?;

                    // Build nested function definitions from inside out.
                    let mut result = body;
                    for binding in bindings.into_iter().rev() {
                        let span = Span::new(binding.var.span.start, result.span.end);
                        result = TlaExpr::new(
                            TlaExprKind::FunctionDef {
                                var: binding.var,
                                domain: Box::new(binding.domain),
                                body: Box::new(result),
                            },
                            span,
                        );
                    }

                    let full_span = Span::new(start, end);
                    return Ok(TlaExpr::new(result.kind, full_span));
                }
            }

            // Restore and try record / record-set forms.
            self.position = saved_pos;
            let name = self.expect_ident()?;

            // Record: [a |-> e, ...]
            if self.check(&TokenKind::MapsTo) {
                self.advance();
                let first_value = self.parse_expr_nested()?;
                let mut fields = vec![(name, first_value)];

                while self.check(&TokenKind::Comma) {
                    self.advance();
                    let field_name = self.expect_ident()?;
                    self.expect(TokenKind::MapsTo)?;
                    let field_value = self.parse_expr_nested()?;
                    fields.push((field_name, field_value));
                }

                let end = self.current_span().end;
                self.expect(TokenKind::RBracket)?;
                return Ok(TlaExpr::new(
                    TlaExprKind::Record { fields },
                    Span::new(start, end),
                ));
            }

            // Record set: [a: S, b: T]
            if self.check(&TokenKind::Colon) {
                self.advance();
                let first_type = self.parse_expr_nested()?;
                let mut fields = vec![(name, first_type)];

                while self.check(&TokenKind::Comma) {
                    self.advance();
                    let field_name = self.expect_ident()?;
                    self.expect(TokenKind::Colon)?;
                    let field_type = self.parse_expr_nested()?;
                    fields.push((field_name, field_type));
                }

                let end = self.current_span().end;
                self.expect(TokenKind::RBracket)?;
                return Ok(TlaExpr::new(
                    TlaExprKind::RecordSet { fields },
                    Span::new(start, end),
                ));
            }

            // Restore position if none of the above.
            self.position = saved_pos;
        }

        // Parse general bracket forms beginning with an expression:
        //   [base EXCEPT ![...] = ...]
        //   [Domain -> Range]
        //   [A]_vars
        let base = self.parse_expr_nested()?;

        // EXCEPT: [base EXCEPT ![k] = v]
        if self.check(&TokenKind::Except) {
            self.advance();
            let updates = self.parse_except_updates()?;
            let end = self.current_span().end;
            self.expect(TokenKind::RBracket)?;
            return Ok(TlaExpr::new(
                TlaExprKind::Except {
                    base: Box::new(base),
                    updates,
                },
                Span::new(start, end),
            ));
        }

        // Function set: [Domain -> Range]
        if self.check(&TokenKind::Arrow) {
            self.advance();
            let range = self.parse_expr_nested()?;
            let end = self.current_span().end;
            self.expect(TokenKind::RBracket)?;
            return Ok(TlaExpr::new(
                TlaExprKind::FunctionSet {
                    domain: Box::new(base),
                    range: Box::new(range),
                },
                Span::new(start, end),
            ));
        }

        // Box action: [A]_v
        if self.check(&TokenKind::RBracket) {
            self.advance();
            // Check for subscript: either Underscore token or identifier starting with _
            if self.check(&TokenKind::Underscore) {
                self.advance();
                let vars = self.parse_unary()?;
                let end = vars.span.end;
                return Ok(TlaExpr::new(
                    TlaExprKind::BoxAction {
                        action: Box::new(base),
                        vars: Box::new(vars),
                    },
                    Span::new(start, end),
                ));
            }
            // Handle case where _v is tokenized as a single identifier like "_vars"
            if let TokenKind::Ident(name) = &self.current().kind {
                if let Some(stripped) = name.strip_prefix('_') {
                    // Clone the name before advancing
                    let var_name = stripped.to_string();
                    let span = self.current_span();
                    self.advance();
                    let vars = TlaExpr::new(TlaExprKind::Ident(var_name), span);
                    let end = vars.span.end;
                    return Ok(TlaExpr::new(
                        TlaExprKind::BoxAction {
                            action: Box::new(base),
                            vars: Box::new(vars),
                        },
                        Span::new(start, end),
                    ));
                }
            }
        }

        Err(ParseError::InvalidSyntax {
            message: "unexpected bracket expression".to_string(),
            position: start,
        })
    }

    fn parse_except_updates(&mut self) -> Result<Vec<TlaExceptUpdate>, ParseError> {
        let mut updates = Vec::new();
        loop {
            let start = self.current_span().start;
            self.expect(TokenKind::Bang)?;

            let mut path = Vec::new();
            loop {
                if self.check(&TokenKind::LBracket) {
                    self.advance();
                    // Parse comma-separated indices: [a, b, c]
                    path.push(self.parse_expr_nested()?);
                    while self.check(&TokenKind::Comma) {
                        self.advance();
                        path.push(self.parse_expr_nested()?);
                    }
                    self.expect(TokenKind::RBracket)?;
                    continue;
                }

                // Handle .field access in EXCEPT and allow chaining with [index].
                if self.check(&TokenKind::Dot) {
                    self.advance();
                    let field = self.expect_ident()?;
                    path.push(TlaExpr::new(TlaExprKind::String(field.name), field.span));
                    continue;
                }
                break;
            }

            self.expect(TokenKind::Eq)?;
            let value = self.parse_expr_nested()?;
            let end = value.span.end;

            updates.push(TlaExceptUpdate {
                path,
                value,
                span: Span::new(start, end),
            });

            if !self.check(&TokenKind::Comma) {
                break;
            }
            self.advance();
        }
        Ok(updates)
    }

    fn parse_expr_list(&mut self) -> Result<Vec<TlaExpr>, ParseError> {
        let mut exprs = vec![self.parse_expr_nested()?];
        while self.check(&TokenKind::Comma) {
            self.advance();
            exprs.push(self.parse_expr_nested()?);
        }
        Ok(exprs)
    }

    // === Helper methods ===

    fn current(&self) -> &Token {
        static EOF_TOKEN: std::sync::LazyLock<Token> = std::sync::LazyLock::new(|| Token {
            kind: TokenKind::Eof,
            span: Span::new(0, 0),
        });
        self.tokens.get(self.position).unwrap_or(&EOF_TOKEN)
    }

    fn current_span(&self) -> Span {
        self.current().span
    }

    fn previous_span(&self) -> Span {
        if self.position > 0 {
            self.tokens[self.position - 1].span
        } else {
            Span::new(0, 0)
        }
    }

    fn check(&self, kind: &TokenKind) -> bool {
        std::mem::discriminant(&self.current().kind) == std::mem::discriminant(kind)
    }

    fn check_ident(&self) -> bool {
        matches!(self.current().kind, TokenKind::Ident(_))
    }

    fn peek_is(&self, kind: &TokenKind) -> bool {
        self.tokens
            .get(self.position + 1)
            .map(|t| std::mem::discriminant(&t.kind) == std::mem::discriminant(kind))
            .unwrap_or(false)
    }

    fn is_at_end(&self) -> bool {
        self.current().kind == TokenKind::Eof
    }

    /// Skip tokens until we find a declaration keyword (CONSTANT, VARIABLE, etc.)
    /// or an identifier at the start of a line (operator definition).
    /// Excludes THEOREM/LEMMA/ASSUME since we're usually skipping from one of those.
    fn skip_to_next_declaration(&mut self) {
        // First advance at least one token to ensure progress
        if !self.is_at_end() {
            self.advance();
        }
        while !self.is_at_end() {
            match &self.current().kind {
                TokenKind::Constant
                | TokenKind::Constants
                | TokenKind::Variable
                | TokenKind::Variables
                | TokenKind::Instance
                | TokenKind::ModuleEnd
                | TokenKind::ModuleStart => return,
                // Skip THEOREM/LEMMA/ASSUME since they may be nested or cause loops
                TokenKind::Theorem | TokenKind::Lemma | TokenKind::Assume => {
                    self.advance();
                    continue;
                }
                TokenKind::Ident(_) => {
                    // Check if this is an operator definition (followed by ==)
                    // Be strict: only return if directly followed by ==
                    // (Ident followed by ( might be a function call, not a definition)
                    if self.peek_is(&TokenKind::DefEq) {
                        return;
                    }
                    // Check for Ident(params) == pattern (operator with params)
                    // Save position and look ahead
                    if self.peek_is(&TokenKind::LParen) {
                        let saved_pos = self.position;
                        self.advance(); // past ident
                        self.advance(); // past (
                                        // Skip to closing )
                        let mut depth = 1;
                        while !self.is_at_end() && depth > 0 {
                            match &self.current().kind {
                                TokenKind::LParen => depth += 1,
                                TokenKind::RParen => depth -= 1,
                                _ => {}
                            }
                            self.advance();
                        }
                        // Check if followed by ==
                        if self.check(&TokenKind::DefEq) {
                            self.position = saved_pos;
                            return;
                        }
                        self.position = saved_pos;
                    }
                }
                _ => {}
            }
            self.advance();
        }
    }

    /// Skip a nested module block that starts at "---- MODULE ... ----".
    fn skip_nested_module(&mut self) {
        if !(self.check(&TokenKind::ModuleStart) && self.peek_is(&TokenKind::Module)) {
            return;
        }

        // Consume "---- MODULE"
        self.advance();
        self.advance();

        let mut depth = 1usize;
        while !self.is_at_end() && depth > 0 {
            if self.check(&TokenKind::ModuleStart) && self.peek_is(&TokenKind::Module) {
                self.advance();
                self.advance();
                depth += 1;
                continue;
            }
            if self.check(&TokenKind::ModuleEnd) {
                self.advance();
                depth -= 1;
                continue;
            }
            self.advance();
        }
    }

    fn recover_declaration(&mut self, start: usize) -> Result<TlaDecl, ParseError> {
        self.skip_to_next_declaration();
        while self.check(&TokenKind::ModuleStart) {
            if self.peek_is(&TokenKind::Module) {
                self.skip_nested_module();
            } else {
                self.advance();
            }
        }
        if !self.is_at_end() && !self.check(&TokenKind::ModuleEnd) {
            self.parse_declaration()
        } else {
            Ok(TlaDecl::Theorem {
                name: None,
                expr: TlaExpr::new(TlaExprKind::Bool(true), Span::new(start, start)),
                span: Span::new(start, start),
            })
        }
    }

    fn advance(&mut self) {
        if !self.is_at_end() {
            self.position += 1;
        }
    }

    fn expect(&mut self, kind: TokenKind) -> Result<(), ParseError> {
        if self.check(&kind) {
            self.advance();
            Ok(())
        } else {
            Err(ParseError::UnexpectedToken {
                expected: format!("{}", kind),
                found: format!("{:?}", self.current().kind),
                position: self.current_span().start,
            })
        }
    }

    fn expect_ident(&mut self) -> Result<TlaIdent, ParseError> {
        if let TokenKind::Ident(name) = &self.current().kind {
            let name = name.clone();
            let span = self.current_span();
            self.advance();
            Ok(TlaIdent::new(name, span))
        } else {
            Err(ParseError::UnexpectedToken {
                expected: "identifier".to_string(),
                found: format!("{:?}", self.current().kind),
                position: self.current_span().start,
            })
        }
    }

    /// Accept an identifier optionally followed by a signature-like argument list,
    /// e.g. `Ballot(_)`, `P(_,_)`. The signature is ignored for now.
    fn expect_ident_with_signature(&mut self) -> Result<TlaIdent, ParseError> {
        let ident = self.expect_ident()?;
        if self.check(&TokenKind::LParen) {
            self.advance();
            let mut depth = 1usize;
            while !self.is_at_end() && depth > 0 {
                if self.check(&TokenKind::LParen) {
                    depth += 1;
                } else if self.check(&TokenKind::RParen) {
                    depth -= 1;
                }
                self.advance();
            }
        }
        Ok(ident)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(input: &str) -> Result<TlaModule, ParseError> {
        Parser::new(input).parse_module()
    }

    #[test]
    fn test_minimal_module() {
        let input = r#"---- MODULE Test ----
====
"#;
        let module = parse(input).unwrap();
        assert_eq!(module.name, "Test");
        assert!(module.extends.is_empty());
        assert!(module.declarations.is_empty());
    }

    #[test]
    fn test_extends() {
        let input = r#"---- MODULE Test ----
EXTENDS Naturals, Sequences
====
"#;
        let module = parse(input).unwrap();
        assert_eq!(module.extends, vec!["Naturals", "Sequences"]);
    }

    #[test]
    fn test_constants_and_variables() {
        let input = r#"---- MODULE Test ----
CONSTANT N, M
VARIABLE x, y
====
"#;
        let module = parse(input).unwrap();
        assert_eq!(module.declarations.len(), 2);
    }

    #[test]
    fn test_operator_definition() {
        let input = r#"---- MODULE Test ----
Init == x = 0
====
"#;
        let module = parse(input).unwrap();
        assert_eq!(module.declarations.len(), 1);
        if let TlaDecl::Operator { name, params, .. } = &module.declarations[0] {
            assert_eq!(name.name, "Init");
            assert!(params.is_empty());
        } else {
            panic!("Expected operator");
        }
    }

    #[test]
    fn test_operator_with_params() {
        let input = r#"---- MODULE Test ----
Add(a, b) == a + b
====
"#;
        let module = parse(input).unwrap();
        if let TlaDecl::Operator { name, params, .. } = &module.declarations[0] {
            assert_eq!(name.name, "Add");
            assert_eq!(params.len(), 2);
        } else {
            panic!("Expected operator");
        }
    }

    #[test]
    fn test_primed_variable() {
        let input = r#"---- MODULE Test ----
Next == x' = x + 1
====
"#;
        let module = parse(input).unwrap();
        // Just check it parses without error
        assert_eq!(module.declarations.len(), 1);
    }

    #[test]
    fn test_quantifier() {
        let input = r#"---- MODULE Test ----
Inv == \A n \in S: n > 0
====
"#;
        let module = parse(input).unwrap();
        assert_eq!(module.declarations.len(), 1);
    }

    #[test]
    fn test_set_enumeration() {
        let input = r#"---- MODULE Test ----
S == {1, 2, 3}
====
"#;
        let module = parse(input).unwrap();
        if let TlaDecl::Operator { body, .. } = &module.declarations[0] {
            if let TlaExprKind::SetEnum { elements } = &body.kind {
                assert_eq!(elements.len(), 3);
            } else {
                panic!("Expected set enum");
            }
        }
    }

    #[test]
    fn test_function_definition() {
        let input = r#"---- MODULE Test ----
F == [x \in S |-> x * 2]
====
"#;
        let module = parse(input).unwrap();
        if let TlaDecl::Operator { body, .. } = &module.declarations[0] {
            assert!(matches!(body.kind, TlaExprKind::FunctionDef { .. }));
        } else {
            panic!("Expected operator");
        }
    }

    #[test]
    fn test_record() {
        let input = r#"---- MODULE Test ----
R == [a |-> 1, b |-> 2]
====
"#;
        let module = parse(input).unwrap();
        if let TlaDecl::Operator { body, .. } = &module.declarations[0] {
            if let TlaExprKind::Record { fields } = &body.kind {
                assert_eq!(fields.len(), 2);
            } else {
                panic!("Expected record");
            }
        }
    }

    #[test]
    fn test_if_then_else() {
        let input = r#"---- MODULE Test ----
Max(a, b) == IF a > b THEN a ELSE b
====
"#;
        let module = parse(input).unwrap();
        if let TlaDecl::Operator { body, .. } = &module.declarations[0] {
            assert!(matches!(body.kind, TlaExprKind::IfThenElse { .. }));
        }
    }

    #[test]
    fn test_tuple() {
        let input = r#"---- MODULE Test ----
T == <<1, 2, 3>>
====
"#;
        let module = parse(input).unwrap();
        if let TlaDecl::Operator { body, .. } = &module.declarations[0] {
            if let TlaExprKind::Tuple { elements } = &body.kind {
                assert_eq!(elements.len(), 3);
            } else {
                panic!("Expected tuple");
            }
        }
    }

    #[test]
    fn test_unchanged() {
        let input = r#"---- MODULE Test ----
Stutter == UNCHANGED <<x, y>>
====
"#;
        let module = parse(input).unwrap();
        if let TlaDecl::Operator { body, .. } = &module.declarations[0] {
            if let TlaExprKind::Unchanged(vars) = &body.kind {
                assert_eq!(vars.len(), 2);
            } else {
                panic!("Expected unchanged");
            }
        }
    }
}

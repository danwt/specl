//! TLA+ parser and translator to Specl.
//!
//! This crate provides:
//! - A lexer for TLA+ specifications
//! - An AST representation for TLA+
//! - A parser for TLA+ specifications
//! - A translator from TLA+ AST to Specl AST

mod ast;
mod lexer;
mod parser;
mod token;
mod translate;

pub use ast::*;
pub use lexer::Lexer;
pub use parser::{ParseError, Parser};
pub use token::{Token, TokenKind};
pub use translate::{translate, TranslateError};

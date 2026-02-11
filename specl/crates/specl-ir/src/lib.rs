//! Intermediate representation for Specl.

pub mod compile;
pub mod ir;

pub use compile::{compile, CompileError, CompileResult};
pub use ir::*;

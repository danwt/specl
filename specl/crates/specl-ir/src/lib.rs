//! Intermediate representation for Specl.

pub mod analyze;
pub mod compile;
pub mod from_ts;
pub mod ir;

pub use compile::{compile, CompileError, CompileResult};
pub use ir::*;

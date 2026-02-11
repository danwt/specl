//! Expression evaluator for Specl.

pub mod bytecode;
pub mod eval;
pub mod value;

pub use eval::{eval, eval_bool, eval_int, EvalContext, EvalError, EvalResult};
pub use value::Value;

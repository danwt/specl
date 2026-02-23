//! Type system and type checker for Specl.

pub mod checker;
pub mod env;
pub mod error;
pub mod types;

pub use checker::{check_module, TypeChecker};
pub use env::{ActionSig, TypeEnv};
pub use error::{TypeError, TypeResult};
pub use types::{Substitution, Type, TypeVar, TypeVarGen};

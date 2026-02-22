//! Generic transition system IR for the Specl model checker.
//!
//! This crate defines a language-agnostic transition system representation
//! that can be lowered to `CompiledSpec` for model checking. External
//! frontends (Solidity, Rust, Solana, etc.) produce `TransitionSystem` JSON
//! files which the CLI deserializes and checks directly.

mod types;

pub use types::*;

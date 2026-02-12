//! Symbolic model checking backend for Specl using Z3.
//!
//! Provides bounded model checking (BMC) and inductive invariant checking
//! as alternatives to the explicit-state BFS explorer in `specl-mc`.

pub mod bmc;
pub mod encoder;
pub mod fixedpoint;
pub mod ic3;
pub mod inductive;
pub mod k_induction;
pub mod smart;
pub mod state_vars;
pub mod trace;
pub mod transition;

use specl_eval::Value;
use specl_ir::CompiledSpec;
use thiserror::Error;

/// Symbolic checking error.
#[derive(Debug, Error)]
pub enum SymbolicError {
    #[error("unsupported construct for symbolic checking: {0}")]
    Unsupported(String),

    #[error("encoding error: {0}")]
    Encoding(String),

    #[error("Z3 error: {0}")]
    Z3(String),

    #[error("constant '{name}' not provided")]
    MissingConstant { name: String },
}

pub type SymbolicResult<T> = Result<T, SymbolicError>;

/// Result of symbolic model checking.
#[derive(Debug)]
pub enum SymbolicOutcome {
    /// All invariants hold (within bound for BMC, or inductively proven).
    Ok { method: &'static str },
    /// Invariant violation found.
    InvariantViolation {
        invariant: String,
        trace: Vec<TraceStep>,
    },
    /// Could not determine (solver timeout, unknown, etc).
    Unknown { reason: String },
}

/// A single step in a counterexample trace.
#[derive(Debug, Clone)]
pub struct TraceStep {
    /// Variable name-value pairs at this step.
    pub state: Vec<(String, String)>,
    /// Action that led to this state (None for init).
    pub action: Option<String>,
}

/// Configuration for symbolic checking.
#[derive(Debug, Clone)]
pub struct SymbolicConfig {
    pub mode: SymbolicMode,
    pub depth: usize,
    /// Maximum sequence length for Seq[T] variables (default: 5).
    pub seq_bound: usize,
}

/// Symbolic checking mode.
#[derive(Debug, Clone)]
pub enum SymbolicMode {
    /// Bounded model checking: unroll transitions for k steps.
    Bmc,
    /// Inductive invariant checking: single-step proof.
    Inductive,
    /// k-induction with given strengthening depth.
    KInduction(usize),
    /// IC3/CHC via Z3's Spacer engine (unbounded verification).
    Ic3,
    /// Smart mode: automatic strategy cascade.
    Smart,
}

/// Run symbolic model checking on a compiled spec.
pub fn check(
    spec: &CompiledSpec,
    consts: &[Value],
    config: &SymbolicConfig,
) -> SymbolicResult<SymbolicOutcome> {
    let sb = config.seq_bound;
    match config.mode {
        SymbolicMode::Bmc => bmc::check_bmc(spec, consts, config.depth, sb),
        SymbolicMode::Inductive => inductive::check_inductive(spec, consts, sb),
        SymbolicMode::KInduction(k) => k_induction::check_k_induction(spec, consts, k, sb),
        SymbolicMode::Ic3 => ic3::check_ic3(spec, consts, sb),
        SymbolicMode::Smart => smart::check_smart(spec, consts, config.depth, sb),
    }
}

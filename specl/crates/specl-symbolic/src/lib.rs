//! Symbolic model checking backend for Specl using Z3.
//!
//! Provides bounded model checking (BMC) and inductive invariant checking
//! as alternatives to the explicit-state BFS explorer in `specl-mc`.

pub mod bmc;
pub mod encoder;
pub mod fixedpoint;
pub mod golem;
pub mod ic3;
pub mod inductive;
pub mod k_induction;
pub mod portfolio;
pub mod smart;
pub mod state_vars;
pub mod trace;
pub mod transition;

pub use fixedpoint::SpacerProfile;
use specl_eval::Value;
use specl_ir::CompiledSpec;
use thiserror::Error;
use z3::Solver;

/// Apply timeout to a Z3 solver if configured.
pub(crate) fn apply_solver_timeout(solver: &Solver, timeout_ms: Option<u64>) {
    if let Some(ms) = timeout_ms {
        let mut params = z3::Params::new();
        params.set_u32("timeout", ms.min(u32::MAX as u64) as u32);
        solver.set_params(&params);
    }
}

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

    #[error("internal error: {0}")]
    Internal(String),
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

/// A candidate invariant lemma derived from CTI (counter-example to induction) analysis.
/// The body is the negation of the CTI state: NOT(var0 == val0 AND var1 == val1 AND ...).
/// These are NOT proven invariants — they must be verified by IC3 before being trusted.
#[derive(Debug, Clone)]
pub struct CtiLemma {
    pub description: String,
    pub body: specl_ir::CompiledExpr,
}

/// Extended result from k-induction that carries CTI lemmas alongside the outcome.
#[derive(Debug)]
pub struct KInductionResult {
    pub outcome: SymbolicOutcome,
    pub cti_lemmas: Vec<CtiLemma>,
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
    /// Spacer parameter profile for IC3/CHC solving.
    pub spacer_profile: SpacerProfile,
    /// Per-solver timeout in milliseconds (None = no timeout).
    pub timeout_ms: Option<u64>,
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
    /// Golem CHC solver (external process, complements Spacer).
    Golem,
    /// Smart mode: automatic strategy cascade (sequential).
    Smart,
    /// Portfolio mode: run BMC, k-induction, and IC3 in parallel threads.
    Portfolio,
}

/// Run symbolic model checking on a compiled spec.
pub fn check(
    spec: &CompiledSpec,
    consts: &[Value],
    config: &SymbolicConfig,
) -> SymbolicResult<SymbolicOutcome> {
    let sb = config.seq_bound;
    let timeout = config.timeout_ms;
    match config.mode {
        SymbolicMode::Bmc => bmc::check_bmc(spec, consts, config.depth, sb, timeout),
        SymbolicMode::Inductive => inductive::check_inductive(spec, consts, sb, timeout),
        SymbolicMode::KInduction(k) => k_induction::check_k_induction(spec, consts, k, sb, timeout),
        SymbolicMode::Ic3 => ic3::check_ic3(spec, consts, sb, config.spacer_profile, timeout),
        SymbolicMode::Golem => golem::check_golem(spec, consts, sb, timeout),
        SymbolicMode::Smart => smart::check_smart(
            spec,
            consts,
            config.depth,
            sb,
            config.spacer_profile,
            timeout,
        ),
        SymbolicMode::Portfolio => portfolio::check_portfolio(
            spec,
            consts,
            config.depth,
            sb,
            config.spacer_profile,
            timeout,
        ),
    }
}

//! Model checker for Specl specifications.

pub mod direct_eval;
pub mod explorer;
pub mod fpset;
pub mod state;
pub mod store;

pub use explorer::{
    CheckConfig, CheckError, CheckOutcome, CheckResult, Explorer, ProgressCounters, SimulateOutcome,
};
pub use state::{Fingerprint, State};
pub use store::{StateInfo, StateStore};

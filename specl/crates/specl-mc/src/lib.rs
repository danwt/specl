//! Model checker for Specl specifications.

use smallvec::SmallVec;

pub mod bloom;
pub mod cache;
pub mod direct_eval;
pub mod explorer;
pub mod fpset;
pub mod state;
pub mod store;
pub mod tree_table;

/// Compact storage for action parameter values (most actions have 0–2 params).
pub type ParamValues = SmallVec<[i64; 2]>;

pub use explorer::{
    CheckConfig, CheckError, CheckOutcome, CheckResult, Explorer, ProfileData, ProgressCounters,
    SimulateOutcome,
};
pub use state::{Fingerprint, State};
pub use store::{StateInfo, StateStore};

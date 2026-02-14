//! Smart mode: automatic strategy cascade for symbolic verification.
//!
//! Tries progressively stronger techniques:
//! 1. Inductive checking (fastest, but may fail for non-inductive invariants)
//! 2. k-induction with increasing K (2..5)
//! 3. IC3/CHC via Spacer (unbounded, most powerful)
//! 4. BMC fallback (bounded, catches real bugs)

use crate::{SymbolicOutcome, SymbolicResult};
use specl_eval::Value;
use specl_ir::CompiledSpec;
use tracing::info;

/// Run smart mode: try increasingly powerful strategies.
pub fn check_smart(
    spec: &CompiledSpec,
    consts: &[Value],
    bmc_depth: usize,
    seq_bound: usize,
    spacer_profile: crate::SpacerProfile,
) -> SymbolicResult<SymbolicOutcome> {
    // 1. Try simple induction
    info!("smart: trying inductive checking");
    match crate::inductive::check_inductive(spec, consts, seq_bound)? {
        SymbolicOutcome::Ok { .. } => {
            return Ok(SymbolicOutcome::Ok {
                method: "smart(inductive)",
            });
        }
        SymbolicOutcome::InvariantViolation { .. } => {
            // Inductive failure = CTI (counterexample to induction), not a real bug
            info!("smart: inductive check found CTI, trying k-induction");
        }
        SymbolicOutcome::Unknown { .. } => {
            info!("smart: inductive check returned unknown, trying k-induction");
        }
    }

    // 2. Try k-induction with increasing K
    for k in [2, 3, 4, 5] {
        info!(k, "smart: trying k-induction");
        match crate::k_induction::check_k_induction(spec, consts, k, seq_bound)? {
            SymbolicOutcome::Ok { .. } => {
                return Ok(SymbolicOutcome::Ok {
                    method: "smart(k-induction)",
                });
            }
            SymbolicOutcome::InvariantViolation { invariant, trace } => {
                // k-induction base case failure = real bug
                return Ok(SymbolicOutcome::InvariantViolation { invariant, trace });
            }
            SymbolicOutcome::Unknown { .. } => {
                // Inductive step failed at this K, try higher
            }
        }
    }

    // 3. Try IC3/CHC
    info!("smart: trying IC3/CHC");
    match crate::ic3::check_ic3(spec, consts, seq_bound, spacer_profile)? {
        SymbolicOutcome::Ok { .. } => {
            return Ok(SymbolicOutcome::Ok {
                method: "smart(IC3)",
            });
        }
        SymbolicOutcome::InvariantViolation { invariant, trace } => {
            return Ok(SymbolicOutcome::InvariantViolation { invariant, trace });
        }
        SymbolicOutcome::Unknown { .. } => {
            info!("smart: IC3 returned unknown, falling back to BMC");
        }
    }

    // 4. Fall back to BMC
    info!(depth = bmc_depth, "smart: falling back to BMC");
    match crate::bmc::check_bmc(spec, consts, bmc_depth, seq_bound)? {
        SymbolicOutcome::Ok { .. } => Ok(SymbolicOutcome::Ok {
            method: "smart(BMC)",
        }),
        other => Ok(other),
    }
}

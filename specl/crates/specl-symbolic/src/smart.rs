//! Smart mode: automatic strategy cascade for symbolic verification.
//!
//! Tries progressively stronger techniques with time budgets:
//! 1. Inductive checking (fastest, but may fail for non-inductive invariants)
//! 2. k-induction with increasing K (2..5)
//! 3. IC3/CHC via Spacer (unbounded, most powerful)
//! 4. BMC fallback (bounded, catches real bugs)

use crate::{SymbolicOutcome, SymbolicResult};
use specl_eval::Value;
use specl_ir::CompiledSpec;
use std::time::Instant;
use tracing::info;

/// Compute a per-strategy timeout from the total budget and elapsed time.
/// Returns None if no overall timeout is set.
fn strategy_timeout(
    overall_timeout_ms: Option<u64>,
    start: Instant,
    fraction_of_total: f64,
    min_ms: u64,
) -> Option<u64> {
    let total = overall_timeout_ms?;
    let elapsed = start.elapsed().as_millis() as u64;
    let remaining = total.saturating_sub(elapsed);
    if remaining == 0 {
        return Some(1); // minimal timeout to trigger Unknown quickly
    }
    let budget = ((total as f64) * fraction_of_total) as u64;
    Some(budget.max(min_ms).min(remaining))
}

/// Run smart mode: try increasingly powerful strategies with time budgets.
pub fn check_smart(
    spec: &CompiledSpec,
    consts: &[Value],
    bmc_depth: usize,
    seq_bound: usize,
    spacer_profile: crate::SpacerProfile,
    timeout_ms: Option<u64>,
) -> SymbolicResult<SymbolicOutcome> {
    let start = Instant::now();

    // 1. Try simple induction (budget: 10% of total, min 5s)
    info!("smart: trying inductive checking");
    let ind_timeout = strategy_timeout(timeout_ms, start, 0.10, 5_000);
    match crate::inductive::check_inductive(spec, consts, seq_bound, ind_timeout)? {
        SymbolicOutcome::Ok { .. } => {
            return Ok(SymbolicOutcome::Ok {
                method: "smart(inductive)",
            });
        }
        SymbolicOutcome::InvariantViolation { .. } => {
            info!("smart: inductive check found CTI, trying k-induction");
        }
        SymbolicOutcome::Unknown { .. } => {
            info!("smart: inductive check returned unknown, trying k-induction");
        }
    }

    // 2. Try k-induction with increasing K (budget: ~12.5% each, min 10s)
    for k in [2, 3, 4, 5] {
        info!(k, "smart: trying k-induction");
        let kind_timeout = strategy_timeout(timeout_ms, start, 0.125, 10_000);
        match crate::k_induction::check_k_induction(spec, consts, k, seq_bound, kind_timeout)? {
            SymbolicOutcome::Ok { .. } => {
                return Ok(SymbolicOutcome::Ok {
                    method: "smart(k-induction)",
                });
            }
            SymbolicOutcome::InvariantViolation { invariant, trace } => {
                return Ok(SymbolicOutcome::InvariantViolation { invariant, trace });
            }
            SymbolicOutcome::Unknown { .. } => {
                // Inductive step failed at this K, try higher
            }
        }
    }

    // 3. Try IC3/CHC (budget: 50% of total, min 30s)
    info!("smart: trying IC3/CHC");
    let ic3_timeout = strategy_timeout(timeout_ms, start, 0.50, 30_000);
    match crate::ic3::check_ic3(spec, consts, seq_bound, spacer_profile, ic3_timeout)? {
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

    // 4. Fall back to BMC (budget: remaining time)
    info!(depth = bmc_depth, "smart: falling back to BMC");
    let bmc_timeout = if let Some(total) = timeout_ms {
        let elapsed = start.elapsed().as_millis() as u64;
        Some(total.saturating_sub(elapsed).max(1))
    } else {
        None
    };
    match crate::bmc::check_bmc(spec, consts, bmc_depth, seq_bound, bmc_timeout)? {
        SymbolicOutcome::Ok { .. } => Ok(SymbolicOutcome::Ok {
            method: "smart(BMC)",
        }),
        other => Ok(other),
    }
}

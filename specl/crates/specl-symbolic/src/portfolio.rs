//! Portfolio symbolic checking: run multiple strategies in parallel.
//!
//! Spawns BMC, k-induction, and IC3/Spacer in separate threads.
//! The first strategy to produce a definitive result (Ok or InvariantViolation)
//! wins. Each thread creates its own Z3 context (Z3 is not thread-safe).

use crate::{SymbolicOutcome, SymbolicResult};
use specl_eval::Value;
use specl_ir::CompiledSpec;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::thread;
use tracing::info;

/// Result from a portfolio strategy thread.
enum StrategyResult {
    /// Definitive result.
    Done(SymbolicOutcome),
    /// Strategy could not determine (timeout, unknown, error).
    Inconclusive(String),
}

/// Run portfolio symbolic checking: BMC, k-induction, and IC3 in parallel.
/// First definitive result wins.
pub fn check_portfolio(
    spec: &CompiledSpec,
    consts: &[Value],
    bmc_depth: usize,
    seq_bound: usize,
    spacer_profile: crate::SpacerProfile,
) -> SymbolicResult<SymbolicOutcome> {
    info!("portfolio: launching parallel symbolic strategies");

    let done = Arc::new(AtomicBool::new(false));

    // Clone data for each thread (CompiledSpec and consts are Send)
    let spec_bmc = spec.clone();
    let consts_bmc = consts.to_vec();
    let done_bmc = Arc::clone(&done);

    let spec_kind = spec.clone();
    let consts_kind = consts.to_vec();
    let done_kind = Arc::clone(&done);

    let spec_ic3 = spec.clone();
    let consts_ic3 = consts.to_vec();
    let done_ic3 = Arc::clone(&done);

    let spec_golem = spec.clone();
    let consts_golem = consts.to_vec();
    let done_golem = Arc::clone(&done);

    // Thread 1: BMC (good at finding bugs quickly)
    let bmc_handle = thread::spawn(move || {
        if done_bmc.load(Ordering::Relaxed) {
            return StrategyResult::Inconclusive("cancelled".into());
        }
        match crate::bmc::check_bmc(&spec_bmc, &consts_bmc, bmc_depth, seq_bound) {
            Ok(SymbolicOutcome::Ok { .. }) => {
                done_bmc.store(true, Ordering::Relaxed);
                StrategyResult::Done(SymbolicOutcome::Ok {
                    method: "portfolio(BMC)",
                })
            }
            Ok(SymbolicOutcome::InvariantViolation { invariant, trace }) => {
                done_bmc.store(true, Ordering::Relaxed);
                StrategyResult::Done(SymbolicOutcome::InvariantViolation { invariant, trace })
            }
            Ok(SymbolicOutcome::Unknown { reason }) => {
                StrategyResult::Inconclusive(format!("BMC: {reason}"))
            }
            Err(e) => StrategyResult::Inconclusive(format!("BMC error: {e}")),
        }
    });

    // Thread 2: k-induction cascade (k=2,3,4,5) — proves properties
    let kind_handle = thread::spawn(move || {
        for k in [2, 3, 4, 5] {
            if done_kind.load(Ordering::Relaxed) {
                return StrategyResult::Inconclusive("cancelled".into());
            }
            match crate::k_induction::check_k_induction(&spec_kind, &consts_kind, k, seq_bound) {
                Ok(SymbolicOutcome::Ok { .. }) => {
                    done_kind.store(true, Ordering::Relaxed);
                    return StrategyResult::Done(SymbolicOutcome::Ok {
                        method: "portfolio(k-induction)",
                    });
                }
                Ok(SymbolicOutcome::InvariantViolation { invariant, trace }) => {
                    done_kind.store(true, Ordering::Relaxed);
                    return StrategyResult::Done(SymbolicOutcome::InvariantViolation {
                        invariant,
                        trace,
                    });
                }
                Ok(SymbolicOutcome::Unknown { .. }) => {
                    // Try higher k
                }
                Err(_) => {
                    // Try higher k
                }
            }
        }
        StrategyResult::Inconclusive("k-induction: all k exhausted".into())
    });

    // Thread 3: IC3/Spacer (unbounded, most powerful)
    let ic3_handle = thread::spawn(move || {
        if done_ic3.load(Ordering::Relaxed) {
            return StrategyResult::Inconclusive("cancelled".into());
        }
        match crate::ic3::check_ic3(&spec_ic3, &consts_ic3, seq_bound, spacer_profile) {
            Ok(SymbolicOutcome::Ok { .. }) => {
                done_ic3.store(true, Ordering::Relaxed);
                StrategyResult::Done(SymbolicOutcome::Ok {
                    method: "portfolio(IC3)",
                })
            }
            Ok(SymbolicOutcome::InvariantViolation { invariant, trace }) => {
                done_ic3.store(true, Ordering::Relaxed);
                StrategyResult::Done(SymbolicOutcome::InvariantViolation { invariant, trace })
            }
            Ok(SymbolicOutcome::Unknown { reason }) => {
                StrategyResult::Inconclusive(format!("IC3: {reason}"))
            }
            Err(e) => StrategyResult::Inconclusive(format!("IC3 error: {e}")),
        }
    });

    // Thread 4: Golem CHC solver (external, different algorithms from Spacer)
    let golem_handle = thread::spawn(move || {
        if done_golem.load(Ordering::Relaxed) {
            return StrategyResult::Inconclusive("cancelled".into());
        }
        match crate::golem::check_golem(&spec_golem, &consts_golem, seq_bound) {
            Ok(SymbolicOutcome::Ok { .. }) => {
                done_golem.store(true, Ordering::Relaxed);
                StrategyResult::Done(SymbolicOutcome::Ok {
                    method: "portfolio(Golem)",
                })
            }
            Ok(SymbolicOutcome::InvariantViolation { invariant, trace }) => {
                done_golem.store(true, Ordering::Relaxed);
                StrategyResult::Done(SymbolicOutcome::InvariantViolation { invariant, trace })
            }
            Ok(SymbolicOutcome::Unknown { reason }) => {
                StrategyResult::Inconclusive(format!("Golem: {reason}"))
            }
            Err(e) => StrategyResult::Inconclusive(format!("Golem error: {e}")),
        }
    });

    // Collect results: first definitive result wins
    let results = [
        bmc_handle.join().unwrap_or(StrategyResult::Inconclusive("BMC thread panic".into())),
        kind_handle
            .join()
            .unwrap_or(StrategyResult::Inconclusive("k-ind thread panic".into())),
        ic3_handle
            .join()
            .unwrap_or(StrategyResult::Inconclusive("IC3 thread panic".into())),
        golem_handle
            .join()
            .unwrap_or(StrategyResult::Inconclusive("Golem thread panic".into())),
    ];

    // Return first definitive result, preferring violations (real bugs) over Ok (proofs)
    let mut first_ok = None;
    let mut reasons = Vec::new();

    for result in results {
        match result {
            StrategyResult::Done(SymbolicOutcome::InvariantViolation { invariant, trace }) => {
                info!(invariant = %invariant, "portfolio: violation found");
                return Ok(SymbolicOutcome::InvariantViolation { invariant, trace });
            }
            StrategyResult::Done(outcome @ SymbolicOutcome::Ok { .. }) => {
                if first_ok.is_none() {
                    first_ok = Some(outcome);
                }
            }
            StrategyResult::Done(SymbolicOutcome::Unknown { reason }) => {
                reasons.push(reason);
            }
            StrategyResult::Inconclusive(reason) => {
                reasons.push(reason);
            }
        }
    }

    if let Some(ok) = first_ok {
        info!("portfolio: property proven");
        return Ok(ok);
    }

    Ok(SymbolicOutcome::Unknown {
        reason: format!("all strategies inconclusive: {}", reasons.join("; ")),
    })
}

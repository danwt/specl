//! Portfolio symbolic checking: run multiple strategies in parallel.
//!
//! Spawns BMC, k-induction, and multiple IC3/Spacer configurations in separate
//! threads. The first strategy to produce a definitive result (Ok or
//! InvariantViolation) wins. Each thread creates its own Z3 context (Z3 is not
//! thread-safe).

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

/// Run portfolio symbolic checking with diversified strategies.
/// Threads: BMC, k-induction, IC3(user profile), IC3(Fast), IC3(MbpAggressive), Golem.
pub fn check_portfolio(
    spec: &CompiledSpec,
    consts: &[Value],
    bmc_depth: usize,
    seq_bound: usize,
    spacer_profile: crate::SpacerProfile,
    timeout_ms: Option<u64>,
) -> SymbolicResult<SymbolicOutcome> {
    info!("portfolio: launching parallel symbolic strategies");

    let done = Arc::new(AtomicBool::new(false));

    // Helper to spawn an IC3 thread with a given profile and label
    fn spawn_ic3(
        spec: &CompiledSpec,
        consts: &[Value],
        seq_bound: usize,
        profile: crate::SpacerProfile,
        timeout_ms: Option<u64>,
        done: &Arc<AtomicBool>,
        label: &'static str,
    ) -> thread::JoinHandle<StrategyResult> {
        let spec = spec.clone();
        let consts = consts.to_vec();
        let done = Arc::clone(done);
        thread::spawn(move || {
            if done.load(Ordering::Relaxed) {
                return StrategyResult::Inconclusive("cancelled".into());
            }
            match crate::ic3::check_ic3(&spec, &consts, seq_bound, profile, timeout_ms) {
                Ok(SymbolicOutcome::Ok { .. }) => {
                    done.store(true, Ordering::Relaxed);
                    StrategyResult::Done(SymbolicOutcome::Ok { method: label })
                }
                Ok(SymbolicOutcome::InvariantViolation { invariant, trace }) => {
                    done.store(true, Ordering::Relaxed);
                    StrategyResult::Done(SymbolicOutcome::InvariantViolation { invariant, trace })
                }
                Ok(SymbolicOutcome::Unknown { reason }) => {
                    StrategyResult::Inconclusive(format!("{label}: {reason}"))
                }
                Err(e) => StrategyResult::Inconclusive(format!("{label} error: {e}")),
            }
        })
    }

    // Thread 1: BMC
    let spec_bmc = spec.clone();
    let consts_bmc = consts.to_vec();
    let done_bmc = Arc::clone(&done);
    let bmc_handle = thread::spawn(move || {
        if done_bmc.load(Ordering::Relaxed) {
            return StrategyResult::Inconclusive("cancelled".into());
        }
        match crate::bmc::check_bmc(&spec_bmc, &consts_bmc, bmc_depth, seq_bound, timeout_ms) {
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

    // Thread 2: k-induction cascade
    let spec_kind = spec.clone();
    let consts_kind = consts.to_vec();
    let done_kind = Arc::clone(&done);
    let kind_handle = thread::spawn(move || {
        for k in [2, 3, 4, 5] {
            if done_kind.load(Ordering::Relaxed) {
                return StrategyResult::Inconclusive("cancelled".into());
            }
            match crate::k_induction::check_k_induction(
                &spec_kind,
                &consts_kind,
                k,
                seq_bound,
                timeout_ms,
            ) {
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
                Ok(SymbolicOutcome::Unknown { .. }) => {}
                Err(_) => {}
            }
        }
        StrategyResult::Inconclusive("k-induction: all k exhausted".into())
    });

    // Thread 3: IC3 with user-selected profile
    let ic3_handle = spawn_ic3(
        spec,
        consts,
        seq_bound,
        spacer_profile,
        timeout_ms,
        &done,
        "portfolio(IC3)",
    );

    // Thread 4: IC3 with Fast profile (diversification)
    let ic3_fast_handle = spawn_ic3(
        spec,
        consts,
        seq_bound,
        crate::SpacerProfile::Fast,
        timeout_ms,
        &done,
        "portfolio(IC3-Fast)",
    );

    // Thread 5: IC3 with MbpAggressive profile (diversification)
    let ic3_mbp_handle = spawn_ic3(
        spec,
        consts,
        seq_bound,
        crate::SpacerProfile::MbpAggressive,
        timeout_ms,
        &done,
        "portfolio(IC3-MbpAggressive)",
    );

    // Thread 6: Golem
    let spec_golem = spec.clone();
    let consts_golem = consts.to_vec();
    let done_golem = Arc::clone(&done);
    let golem_handle = thread::spawn(move || {
        if done_golem.load(Ordering::Relaxed) {
            return StrategyResult::Inconclusive("cancelled".into());
        }
        match crate::golem::check_golem(&spec_golem, &consts_golem, seq_bound, timeout_ms) {
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

    // Collect results
    let results = [
        bmc_handle
            .join()
            .unwrap_or(StrategyResult::Inconclusive("BMC thread panic".into())),
        kind_handle
            .join()
            .unwrap_or(StrategyResult::Inconclusive("k-ind thread panic".into())),
        ic3_handle
            .join()
            .unwrap_or(StrategyResult::Inconclusive("IC3 thread panic".into())),
        ic3_fast_handle
            .join()
            .unwrap_or(StrategyResult::Inconclusive("IC3-Fast thread panic".into())),
        ic3_mbp_handle
            .join()
            .unwrap_or(StrategyResult::Inconclusive(
                "IC3-MbpAggressive thread panic".into(),
            )),
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

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
use std::sync::mpsc;
use std::sync::Arc;
use std::thread;
use std::time::Duration;
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
    let (tx, rx) = mpsc::channel::<StrategyResult>();
    let num_strategies = 6;

    // Helper to spawn an IC3 thread with a given profile and label
    fn spawn_ic3(
        spec: &CompiledSpec,
        consts: &[Value],
        seq_bound: usize,
        profile: crate::SpacerProfile,
        timeout_ms: Option<u64>,
        done: &Arc<AtomicBool>,
        label: &'static str,
        tx: mpsc::Sender<StrategyResult>,
    ) {
        let spec = spec.clone();
        let consts = consts.to_vec();
        let done = Arc::clone(done);
        thread::spawn(move || {
            let result = if done.load(Ordering::Relaxed) {
                StrategyResult::Inconclusive("cancelled".into())
            } else {
                match crate::ic3::check_ic3(&spec, &consts, seq_bound, profile, timeout_ms) {
                    Ok(SymbolicOutcome::Ok { .. }) => {
                        done.store(true, Ordering::Relaxed);
                        StrategyResult::Done(SymbolicOutcome::Ok { method: label })
                    }
                    Ok(SymbolicOutcome::InvariantViolation { invariant, trace }) => {
                        done.store(true, Ordering::Relaxed);
                        StrategyResult::Done(SymbolicOutcome::InvariantViolation {
                            invariant,
                            trace,
                        })
                    }
                    Ok(SymbolicOutcome::Unknown { reason }) => {
                        StrategyResult::Inconclusive(format!("{label}: {reason}"))
                    }
                    Err(e) => StrategyResult::Inconclusive(format!("{label} error: {e}")),
                }
            };
            let _ = tx.send(result);
        });
    }

    // Thread 1: BMC
    {
        let spec = spec.clone();
        let consts = consts.to_vec();
        let done = Arc::clone(&done);
        let tx = tx.clone();
        thread::spawn(move || {
            let result = if done.load(Ordering::Relaxed) {
                StrategyResult::Inconclusive("cancelled".into())
            } else {
                match crate::bmc::check_bmc(&spec, &consts, bmc_depth, seq_bound, timeout_ms) {
                    Ok(SymbolicOutcome::Ok { .. }) => {
                        done.store(true, Ordering::Relaxed);
                        StrategyResult::Done(SymbolicOutcome::Ok {
                            method: "portfolio(BMC)",
                        })
                    }
                    Ok(SymbolicOutcome::InvariantViolation { invariant, trace }) => {
                        done.store(true, Ordering::Relaxed);
                        StrategyResult::Done(SymbolicOutcome::InvariantViolation {
                            invariant,
                            trace,
                        })
                    }
                    Ok(SymbolicOutcome::Unknown { reason }) => {
                        StrategyResult::Inconclusive(format!("BMC: {reason}"))
                    }
                    Err(e) => StrategyResult::Inconclusive(format!("BMC error: {e}")),
                }
            };
            let _ = tx.send(result);
        });
    }

    // Thread 2: k-induction cascade
    {
        let spec = spec.clone();
        let consts = consts.to_vec();
        let done = Arc::clone(&done);
        let tx = tx.clone();
        thread::spawn(move || {
            for k in [2, 3, 4, 5] {
                if done.load(Ordering::Relaxed) {
                    let _ = tx.send(StrategyResult::Inconclusive("cancelled".into()));
                    return;
                }
                match crate::k_induction::check_k_induction(
                    &spec, &consts, k, seq_bound, timeout_ms,
                ) {
                    Ok(SymbolicOutcome::Ok { .. }) => {
                        done.store(true, Ordering::Relaxed);
                        let _ = tx.send(StrategyResult::Done(SymbolicOutcome::Ok {
                            method: "portfolio(k-induction)",
                        }));
                        return;
                    }
                    Ok(SymbolicOutcome::InvariantViolation { invariant, trace }) => {
                        done.store(true, Ordering::Relaxed);
                        let _ = tx.send(StrategyResult::Done(
                            SymbolicOutcome::InvariantViolation { invariant, trace },
                        ));
                        return;
                    }
                    Ok(SymbolicOutcome::Unknown { .. }) => {}
                    Err(_) => {}
                }
            }
            let _ = tx.send(StrategyResult::Inconclusive(
                "k-induction: all k exhausted".into(),
            ));
        });
    }

    // Thread 3: IC3 with user-selected profile
    spawn_ic3(
        spec,
        consts,
        seq_bound,
        spacer_profile,
        timeout_ms,
        &done,
        "portfolio(IC3)",
        tx.clone(),
    );

    // Thread 4: IC3 with Fast profile (diversification)
    spawn_ic3(
        spec,
        consts,
        seq_bound,
        crate::SpacerProfile::Fast,
        timeout_ms,
        &done,
        "portfolio(IC3-Fast)",
        tx.clone(),
    );

    // Thread 5: IC3 with MbpAggressive profile (diversification)
    spawn_ic3(
        spec,
        consts,
        seq_bound,
        crate::SpacerProfile::MbpAggressive,
        timeout_ms,
        &done,
        "portfolio(IC3-MbpAggressive)",
        tx.clone(),
    );

    // Thread 6: Golem
    {
        let spec = spec.clone();
        let consts = consts.to_vec();
        let done = Arc::clone(&done);
        let tx = tx.clone();
        thread::spawn(move || {
            let result = if done.load(Ordering::Relaxed) {
                StrategyResult::Inconclusive("cancelled".into())
            } else {
                match crate::golem::check_golem(&spec, &consts, seq_bound, timeout_ms) {
                    Ok(SymbolicOutcome::Ok { .. }) => {
                        done.store(true, Ordering::Relaxed);
                        StrategyResult::Done(SymbolicOutcome::Ok {
                            method: "portfolio(Golem)",
                        })
                    }
                    Ok(SymbolicOutcome::InvariantViolation { invariant, trace }) => {
                        done.store(true, Ordering::Relaxed);
                        StrategyResult::Done(SymbolicOutcome::InvariantViolation {
                            invariant,
                            trace,
                        })
                    }
                    Ok(SymbolicOutcome::Unknown { reason }) => {
                        StrategyResult::Inconclusive(format!("Golem: {reason}"))
                    }
                    Err(e) => StrategyResult::Inconclusive(format!("Golem error: {e}")),
                }
            };
            let _ = tx.send(result);
        });
    }

    // Drop the original sender so rx completes when all threads finish
    drop(tx);

    // Collect results as they arrive, return on first definitive result
    let overall_timeout = timeout_ms.unwrap_or(300_000); // 5 min default
    let deadline = std::time::Instant::now() + Duration::from_millis(overall_timeout);

    let mut first_ok = None;
    let mut reasons = Vec::new();
    let mut received = 0;

    while received < num_strategies {
        let remaining = deadline.saturating_duration_since(std::time::Instant::now());
        if remaining.is_zero() {
            reasons.push("portfolio timeout".into());
            break;
        }
        match rx.recv_timeout(remaining) {
            Ok(StrategyResult::Done(SymbolicOutcome::InvariantViolation {
                invariant,
                trace,
            })) => {
                info!(invariant = %invariant, "portfolio: violation found");
                done.store(true, Ordering::Relaxed);
                return Ok(SymbolicOutcome::InvariantViolation { invariant, trace });
            }
            Ok(StrategyResult::Done(outcome @ SymbolicOutcome::Ok { .. })) => {
                done.store(true, Ordering::Relaxed);
                if first_ok.is_none() {
                    first_ok = Some(outcome);
                }
                // Found a proof — return immediately (other strategies are hinted to stop)
                if let Some(ok) = first_ok {
                    info!("portfolio: property proven");
                    return Ok(ok);
                }
            }
            Ok(StrategyResult::Done(SymbolicOutcome::Unknown { reason })) => {
                reasons.push(reason);
            }
            Ok(StrategyResult::Inconclusive(reason)) => {
                reasons.push(reason);
            }
            Err(mpsc::RecvTimeoutError::Timeout) => {
                reasons.push("portfolio timeout".into());
                break;
            }
            Err(mpsc::RecvTimeoutError::Disconnected) => {
                break;
            }
        }
        received += 1;
    }

    if let Some(ok) = first_ok {
        info!("portfolio: property proven");
        return Ok(ok);
    }

    Ok(SymbolicOutcome::Unknown {
        reason: format!("all strategies inconclusive: {}", reasons.join("; ")),
    })
}

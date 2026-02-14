//! Golem CHC solver backend (external process).
//!
//! Encodes the spec as CHC clauses via Z3's fixedpoint API, exports the
//! SMT-LIB2 representation, and invokes the Golem solver as a subprocess.
//! Golem uses algorithms (TPA, LAWI) that complement Z3's Spacer engine.

use crate::ic3::build_chc_system;
use crate::state_vars::VarLayout;
use crate::{SymbolicOutcome, SymbolicResult};
use specl_eval::Value;
use specl_ir::CompiledSpec;
use std::io::Write;
use std::process::Command;
use tracing::info;

/// Check if the Golem solver is available on PATH.
pub fn golem_available() -> bool {
    Command::new("golem")
        .arg("--help")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

/// Run verification using the Golem CHC solver.
pub fn check_golem(
    spec: &CompiledSpec,
    consts: &[Value],
    seq_bound: usize,
) -> SymbolicResult<SymbolicOutcome> {
    info!("starting Golem CHC verification");

    if !golem_available() {
        return Ok(SymbolicOutcome::Unknown {
            reason: "Golem solver not found on PATH (install from https://github.com/usi-verification-and-security/golem)".to_string(),
        });
    }

    let layout = VarLayout::from_spec(spec, consts, seq_bound)?;
    let chc = build_chc_system(spec, consts, &layout)?;

    // Export CHC system as SMT-LIB2 and invoke Golem for each invariant
    for inv in &spec.invariants {
        let smt2 = chc.fp.to_smt2(&[chc.err_app]);

        if smt2.is_empty() {
            return Ok(SymbolicOutcome::Unknown {
                reason: format!(
                    "failed to export CHC system for invariant '{}'",
                    inv.name
                ),
            });
        }

        // Write SMT-LIB2 to temp file
        let mut tmpfile = tempfile::NamedTempFile::with_suffix(".smt2").map_err(|e| {
            crate::SymbolicError::Internal(format!("failed to create temp file: {e}"))
        })?;
        tmpfile.write_all(smt2.as_bytes()).map_err(|e| {
            crate::SymbolicError::Internal(format!("failed to write temp file: {e}"))
        })?;

        let path = tmpfile.path().to_str().unwrap_or("");
        info!(invariant = inv.name, path, "invoking Golem");

        let output = Command::new("golem")
            .arg("--engine")
            .arg("split-tpa")
            .arg("-l")
            .arg("QF_LIA")
            .arg("--input")
            .arg(path)
            .output()
            .map_err(|e| {
                crate::SymbolicError::Internal(format!("failed to invoke Golem: {e}"))
            })?;

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        info!(
            invariant = inv.name,
            stdout = %stdout.trim(),
            stderr = %stderr.trim(),
            "Golem finished"
        );

        let result_line = stdout.trim();

        if result_line.contains("unsat") {
            info!(invariant = inv.name, "invariant verified by Golem");
        } else if result_line.contains("sat") {
            info!(invariant = inv.name, "Golem found violation");
            // Golem confirms violation; use BMC to find trace
            let mut trace = Vec::new();
            for depth in [1, 2, 4, 8, 16, 32] {
                match crate::bmc::check_bmc(spec, consts, depth, seq_bound) {
                    Ok(SymbolicOutcome::InvariantViolation {
                        trace: bmc_trace, ..
                    }) => {
                        info!(depth, "trace reconstructed via BMC");
                        trace = bmc_trace;
                        break;
                    }
                    Ok(_) => continue,
                    Err(_) => break,
                }
            }
            return Ok(SymbolicOutcome::InvariantViolation {
                invariant: inv.name.clone(),
                trace,
            });
        } else {
            return Ok(SymbolicOutcome::Unknown {
                reason: format!(
                    "Golem returned unknown for invariant '{}': {}",
                    inv.name,
                    result_line
                ),
            });
        }
    }

    info!("all invariants verified by Golem");
    Ok(SymbolicOutcome::Ok { method: "Golem" })
}

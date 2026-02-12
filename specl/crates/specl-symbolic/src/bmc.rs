//! Bounded Model Checking: unroll transitions for k steps and check invariants.

use crate::encoder::{assert_range_constraints, create_step_vars};
use crate::state_vars::VarLayout;
use crate::trace::extract_trace;
use crate::transition::{encode_init, encode_transition};
use crate::{SymbolicOutcome, SymbolicResult};
use specl_eval::Value;
use specl_ir::CompiledSpec;
use tracing::info;
use z3::{SatResult, Solver};

/// Run bounded model checking up to the given depth.
pub fn check_bmc(
    spec: &CompiledSpec,
    consts: &[Value],
    max_depth: usize,
) -> SymbolicResult<SymbolicOutcome> {
    info!(depth = max_depth, "starting symbolic BMC");

    let layout = VarLayout::from_spec(spec)?;
    let solver = Solver::new();

    // Create Z3 variables for steps 0..=max_depth
    let mut all_step_vars = Vec::new();
    for step in 0..=max_depth {
        all_step_vars.push(create_step_vars(&layout, step));
    }

    // Assert range constraints for all steps
    for step in 0..=max_depth {
        assert_range_constraints(&solver, &layout, &all_step_vars, step);
    }

    // Assert init at step 0
    encode_init(&solver, spec, consts, &layout, &all_step_vars)?;

    // Assert transitions step by step and check invariants at each depth
    for k in 0..=max_depth {
        if k > 0 {
            let trans = encode_transition(spec, consts, &layout, &all_step_vars, k - 1)?;
            solver.assert(&trans);
        }

        // Check each invariant at step k
        for inv in &spec.invariants {
            solver.push();

            let mut enc = crate::encoder::EncoderCtx {
                layout: &layout,
                consts,
                step_vars: &all_step_vars,
                current_step: k,
                next_step: k,
                params: &[],
                locals: Vec::new(),
            };

            let inv_encoded = enc.encode_bool(&inv.body)?;
            solver.assert(&inv_encoded.not());

            match solver.check() {
                SatResult::Sat => {
                    info!(invariant = inv.name, depth = k, "invariant violation found");
                    let model = solver.get_model().unwrap();
                    let trace = extract_trace(&model, &layout, &all_step_vars, spec, consts, k);
                    return Ok(SymbolicOutcome::InvariantViolation {
                        invariant: inv.name.clone(),
                        trace,
                    });
                }
                SatResult::Unsat => {}
                SatResult::Unknown => {
                    solver.pop(1);
                    return Ok(SymbolicOutcome::Unknown {
                        reason: format!(
                            "Z3 returned unknown at depth {} for invariant '{}'",
                            k, inv.name
                        ),
                    });
                }
            }

            solver.pop(1);
        }
    }

    info!(depth = max_depth, "BMC complete, no violations found");
    Ok(SymbolicOutcome::Ok { method: "BMC" })
}

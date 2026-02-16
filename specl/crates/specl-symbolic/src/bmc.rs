//! Bounded Model Checking: unroll transitions for k steps and check invariants.

use crate::encoder::{assert_range_constraints, create_step_vars};
use crate::state_vars::VarLayout;
use crate::trace::extract_trace;
use crate::transition::{encode_init, encode_transition};
use crate::{SymbolicOutcome, SymbolicResult};
use specl_eval::Value;
use specl_ir::CompiledSpec;
use tracing::info;
use z3::ast::Ast;
use z3::{SatResult, Solver};

/// Maximum depth when no bound is specified (safety net).
const DEFAULT_MAX_DEPTH: usize = 500;

/// Run bounded model checking up to the given depth (0 = unbounded).
pub fn check_bmc(
    spec: &CompiledSpec,
    consts: &[Value],
    max_depth: usize,
    seq_bound: usize,
    timeout_ms: Option<u64>,
) -> SymbolicResult<SymbolicOutcome> {
    let effective_max = if max_depth == 0 {
        DEFAULT_MAX_DEPTH
    } else {
        max_depth
    };
    info!(depth = effective_max, "starting symbolic BMC");

    let layout = VarLayout::from_spec(spec, consts, seq_bound)?;
    let solver = Solver::new();
    crate::apply_solver_timeout(&solver, timeout_ms);

    let mut all_step_vars = Vec::new();

    for k in 0..=effective_max {
        // Incrementally add step variables
        all_step_vars.push(create_step_vars(&layout, k));
        assert_range_constraints(&solver, &layout, &all_step_vars, k);

        if k == 0 {
            encode_init(&solver, spec, consts, &layout, &all_step_vars)?;
        } else {
            let trans = encode_transition(spec, consts, &layout, &all_step_vars, k - 1)?;
            // Z3's built-in simplifier: constant folding, Boolean simplification,
            // redundant conjunct elimination. Free performance win.
            let simplified = trans.simplify();
            solver.assert(&simplified);
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
                compound_locals: Vec::new(),
                set_locals: Vec::new(),
                whole_var_locals: Vec::new(),
            };

            let inv_encoded = enc.encode_bool(&inv.body)?;
            solver.assert(inv_encoded.not());

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

    info!(depth = effective_max, "BMC complete, no violations found");
    Ok(SymbolicOutcome::Ok { method: "BMC" })
}

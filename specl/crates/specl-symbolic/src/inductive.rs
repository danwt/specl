//! Inductive invariant checking: prove invariants hold for all reachable states.

use crate::encoder::{assert_range_constraints, create_step_vars};
use crate::state_vars::VarLayout;
use crate::trace::extract_trace;
use crate::transition::encode_transition;
use crate::{SymbolicOutcome, SymbolicResult};
use specl_eval::Value;
use specl_ir::CompiledSpec;
use tracing::info;
use z3::{SatResult, Solver};

/// Check if all invariants are inductive.
///
/// For each invariant I, checks:
///   I(s) ∧ Transition(s, s') ∧ ¬I(s') is UNSAT
///
/// If UNSAT, I is inductive and holds for all reachable states.
/// If SAT, I is not inductive — the model gives a counterexample to induction (CTI).
pub fn check_inductive(
    spec: &CompiledSpec,
    consts: &[Value],
    seq_bound: usize,
    timeout_ms: Option<u64>,
) -> SymbolicResult<SymbolicOutcome> {
    info!("starting inductive invariant checking");

    let layout = VarLayout::from_spec(spec, consts, seq_bound)?;
    let solver = Solver::new();
    crate::apply_solver_timeout(&solver, timeout_ms);

    let step0_vars = create_step_vars(&layout, 0);
    let step1_vars = create_step_vars(&layout, 1);
    let all_step_vars = vec![step0_vars, step1_vars];

    assert_range_constraints(&solver, &layout, &all_step_vars, 0);
    assert_range_constraints(&solver, &layout, &all_step_vars, 1);

    let trans = encode_transition(spec, consts, &layout, &all_step_vars, 0)?;
    solver.assert(&trans);

    for inv in &spec.invariants {
        solver.push();

        let mut enc0 = crate::encoder::EncoderCtx {
            layout: &layout,
            consts,
            step_vars: &all_step_vars,
            current_step: 0,
            next_step: 0,
            params: &[],
            locals: Vec::new(),
            compound_locals: Vec::new(),
            set_locals: Vec::new(),
            whole_var_locals: Vec::new(),
        };
        let inv_at_0 = enc0.encode_bool(&inv.body)?;
        solver.assert(&inv_at_0);

        // Assert auxiliary invariants at step 0 as hypotheses
        for aux in &spec.auxiliary_invariants {
            let mut enc_aux = crate::encoder::EncoderCtx {
                layout: &layout,
                consts,
                step_vars: &all_step_vars,
                current_step: 0,
                next_step: 0,
                params: &[],
                locals: Vec::new(),
                compound_locals: Vec::new(),
                set_locals: Vec::new(),
                whole_var_locals: Vec::new(),
            };
            let aux_at_0 = enc_aux.encode_bool(&aux.body)?;
            solver.assert(&aux_at_0);
        }

        let mut enc1 = crate::encoder::EncoderCtx {
            layout: &layout,
            consts,
            step_vars: &all_step_vars,
            current_step: 1,
            next_step: 1,
            params: &[],
            locals: Vec::new(),
            compound_locals: Vec::new(),
            set_locals: Vec::new(),
            whole_var_locals: Vec::new(),
        };
        let inv_at_1 = enc1.encode_bool(&inv.body)?;
        solver.assert(inv_at_1.not());

        match solver.check() {
            SatResult::Sat => {
                info!(invariant = inv.name, "invariant is NOT inductive");
                let model = solver.get_model().unwrap();
                let trace = extract_trace(&model, &layout, &all_step_vars, spec, consts, 1);
                return Ok(SymbolicOutcome::InvariantViolation {
                    invariant: inv.name.clone(),
                    trace,
                });
            }
            SatResult::Unsat => {
                info!(invariant = inv.name, "invariant is inductive");
            }
            SatResult::Unknown => {
                solver.pop(1);
                return Ok(SymbolicOutcome::Unknown {
                    reason: format!("Z3 returned unknown for invariant '{}'", inv.name),
                });
            }
        }

        solver.pop(1);
    }

    info!("all invariants are inductive");
    Ok(SymbolicOutcome::Ok {
        method: "inductive",
    })
}

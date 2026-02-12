//! k-induction: strictly more powerful than simple induction.
//!
//! For each invariant I, checks two conditions:
//!   Base case: BMC to depth K finds no violation (init + transitions + ¬I is UNSAT for all steps)
//!   Inductive step: K+1 consecutive states where I holds for the first K,
//!     transitions hold between all, and ¬I at step K — must be UNSAT.
//!
//! Both UNSAT → proven for all reachable states.

use crate::encoder::{assert_range_constraints, create_step_vars, EncoderCtx};
use crate::state_vars::VarLayout;
use crate::trace::extract_trace;
use crate::transition::{encode_init, encode_transition};
use crate::{SymbolicOutcome, SymbolicResult};
use specl_eval::Value;
use specl_ir::CompiledSpec;
use tracing::info;
use z3::{SatResult, Solver};

/// Run k-induction checking with the given strengthening depth.
pub fn check_k_induction(
    spec: &CompiledSpec,
    consts: &[Value],
    k: usize,
) -> SymbolicResult<SymbolicOutcome> {
    info!(k, "starting k-induction");

    let layout = VarLayout::from_spec(spec, consts)?;

    // === Base case: BMC to depth K ===
    info!(k, "k-induction base case");
    if let Some(outcome) = check_base_case(spec, consts, &layout, k)? {
        return Ok(outcome);
    }

    // === Inductive step ===
    info!(k, "k-induction inductive step");
    check_inductive_step(spec, consts, &layout, k)
}

/// Base case: init + transitions for K steps, check ¬I at each step.
fn check_base_case(
    spec: &CompiledSpec,
    consts: &[Value],
    layout: &VarLayout,
    k: usize,
) -> SymbolicResult<Option<SymbolicOutcome>> {
    let solver = Solver::new();

    let mut all_step_vars = Vec::new();
    for step in 0..=k {
        all_step_vars.push(create_step_vars(layout, step));
    }

    for step in 0..=k {
        assert_range_constraints(&solver, layout, &all_step_vars, step);
    }

    encode_init(&solver, spec, consts, layout, &all_step_vars)?;

    for depth in 0..=k {
        if depth > 0 {
            let trans = encode_transition(spec, consts, layout, &all_step_vars, depth - 1)?;
            solver.assert(&trans);
        }

        for inv in &spec.invariants {
            solver.push();

            let mut enc = EncoderCtx {
                layout,
                consts,
                step_vars: &all_step_vars,
                current_step: depth,
                next_step: depth,
                params: &[],
                locals: Vec::new(),
            };
            let inv_encoded = enc.encode_bool(&inv.body)?;
            solver.assert(&inv_encoded.not());

            match solver.check() {
                SatResult::Sat => {
                    info!(invariant = inv.name, depth, "base case violation found");
                    let model = solver.get_model().unwrap();
                    let trace = extract_trace(&model, layout, &all_step_vars, spec, consts, depth);
                    return Ok(Some(SymbolicOutcome::InvariantViolation {
                        invariant: inv.name.clone(),
                        trace,
                    }));
                }
                SatResult::Unsat => {}
                SatResult::Unknown => {
                    solver.pop(1);
                    return Ok(Some(SymbolicOutcome::Unknown {
                        reason: format!(
                            "Z3 returned unknown at base depth {} for invariant '{}'",
                            depth, inv.name
                        ),
                    }));
                }
            }

            solver.pop(1);
        }
    }

    Ok(None)
}

/// Inductive step: K+1 states (0..=K), assert I at 0..K-1, transitions, ¬I at K.
fn check_inductive_step(
    spec: &CompiledSpec,
    consts: &[Value],
    layout: &VarLayout,
    k: usize,
) -> SymbolicResult<SymbolicOutcome> {
    let solver = Solver::new();

    // K+1 states: 0..=K
    let mut all_step_vars = Vec::new();
    for step in 0..=k {
        all_step_vars.push(create_step_vars(layout, step));
    }

    for step in 0..=k {
        assert_range_constraints(&solver, layout, &all_step_vars, step);
    }

    // Assert transitions between all consecutive pairs
    for step in 0..k {
        let trans = encode_transition(spec, consts, layout, &all_step_vars, step)?;
        solver.assert(&trans);
    }

    for inv in &spec.invariants {
        solver.push();

        // Assert I(s_0), ..., I(s_{K-1})
        for step in 0..k {
            let mut enc = EncoderCtx {
                layout,
                consts,
                step_vars: &all_step_vars,
                current_step: step,
                next_step: step,
                params: &[],
                locals: Vec::new(),
            };
            let inv_at_step = enc.encode_bool(&inv.body)?;
            solver.assert(&inv_at_step);
        }

        // Assert ¬I(s_K)
        let mut enc_k = EncoderCtx {
            layout,
            consts,
            step_vars: &all_step_vars,
            current_step: k,
            next_step: k,
            params: &[],
            locals: Vec::new(),
        };
        let inv_at_k = enc_k.encode_bool(&inv.body)?;
        solver.assert(&inv_at_k.not());

        match solver.check() {
            SatResult::Sat => {
                // CTI (counterexample to induction) — not a real bug, just not provable at K
                info!(invariant = inv.name, k, "inductive step failed (CTI)");
                solver.pop(1);
                return Ok(SymbolicOutcome::Unknown {
                    reason: format!("invariant '{}' not k-inductive at k={}", inv.name, k),
                });
            }
            SatResult::Unsat => {
                info!(invariant = inv.name, k, "invariant is k-inductive");
            }
            SatResult::Unknown => {
                solver.pop(1);
                return Ok(SymbolicOutcome::Unknown {
                    reason: format!(
                        "Z3 returned unknown for k-induction step for invariant '{}'",
                        inv.name
                    ),
                });
            }
        }

        solver.pop(1);
    }

    info!(k, "all invariants are k-inductive");
    Ok(SymbolicOutcome::Ok {
        method: "k-induction",
    })
}

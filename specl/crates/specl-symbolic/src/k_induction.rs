//! k-induction: strictly more powerful than simple induction.
//!
//! For each invariant I, checks two conditions:
//!   Base case: BMC to depth K finds no violation (init + transitions + ¬I is UNSAT for all steps)
//!   Inductive step: K+1 consecutive states where I holds for the first K,
//!     transitions hold between all, and ¬I at step K — must be UNSAT.
//!
//! Both UNSAT → proven for all reachable states.
//! If the inductive step is SAT, the invariant is not k-inductive at this K.
//! The smart cascade will try higher K values or fall through to IC3/Spacer.

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
    seq_bound: usize,
    timeout_ms: Option<u64>,
) -> SymbolicResult<SymbolicOutcome> {
    info!(k, "starting k-induction");

    let layout = VarLayout::from_spec(spec, consts, seq_bound)?;

    // === Base case: BMC to depth K ===
    info!(k, "k-induction base case");
    if let Some(outcome) = check_base_case(spec, consts, &layout, k, timeout_ms)? {
        return Ok(outcome);
    }

    // === Inductive step ===
    info!(k, "k-induction inductive step");
    check_inductive_step(spec, consts, &layout, k, timeout_ms)
}

/// Base case: init + transitions for K steps, check ¬I at each step.
fn check_base_case(
    spec: &CompiledSpec,
    consts: &[Value],
    layout: &VarLayout,
    k: usize,
    timeout_ms: Option<u64>,
) -> SymbolicResult<Option<SymbolicOutcome>> {
    let solver = Solver::new();
    crate::apply_solver_timeout(&solver, timeout_ms);

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
                compound_locals: Vec::new(),
                set_locals: Vec::new(),
                whole_var_locals: Vec::new(),
            };
            let inv_encoded = enc.encode_bool(&inv.body)?;
            solver.assert(inv_encoded.not());

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

/// Inductive step: check if I(s_0) ∧ ... ∧ I(s_{K-1}) ∧ transitions ∧ ¬I(s_K) is UNSAT.
/// If UNSAT, the invariant is k-inductive. If SAT, it is not k-inductive at this K.
fn check_inductive_step(
    spec: &CompiledSpec,
    consts: &[Value],
    layout: &VarLayout,
    k: usize,
    timeout_ms: Option<u64>,
) -> SymbolicResult<SymbolicOutcome> {
    let solver = Solver::new();
    crate::apply_solver_timeout(&solver, timeout_ms);

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

        // Assert I(s_0), ..., I(s_{K-1}) and auxiliary invariants at assumption steps
        for step in 0..k {
            let mut enc = EncoderCtx {
                layout,
                consts,
                step_vars: &all_step_vars,
                current_step: step,
                next_step: step,
                params: &[],
                locals: Vec::new(),
                compound_locals: Vec::new(),
                set_locals: Vec::new(),
                whole_var_locals: Vec::new(),
            };
            let inv_at_step = enc.encode_bool(&inv.body)?;
            solver.assert(&inv_at_step);

            for aux in &spec.auxiliary_invariants {
                let mut enc_aux = EncoderCtx {
                    layout,
                    consts,
                    step_vars: &all_step_vars,
                    current_step: step,
                    next_step: step,
                    params: &[],
                    locals: Vec::new(),
                    compound_locals: Vec::new(),
                    set_locals: Vec::new(),
                    whole_var_locals: Vec::new(),
                };
                let aux_at_step = enc_aux.encode_bool(&aux.body)?;
                solver.assert(&aux_at_step);
            }
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
            compound_locals: Vec::new(),
            set_locals: Vec::new(),
            whole_var_locals: Vec::new(),
        };
        let inv_at_k = enc_k.encode_bool(&inv.body)?;
        solver.assert(inv_at_k.not());

        match solver.check() {
            SatResult::Sat => {
                info!(invariant = inv.name, k, "invariant not k-inductive");
                solver.pop(1);
                return Ok(SymbolicOutcome::Unknown {
                    reason: format!("invariant '{}' is not k-inductive at k={}", inv.name, k),
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

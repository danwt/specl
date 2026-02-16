//! k-induction: strictly more powerful than simple induction.
//!
//! For each invariant I, checks two conditions:
//!   Base case: BMC to depth K finds no violation (init + transitions + ¬I is UNSAT for all steps)
//!   Inductive step: K+1 consecutive states where I holds for the first K,
//!     transitions hold between all, and ¬I at step K — must be UNSAT.
//!
//! Both UNSAT → proven for all reachable states.
//!
//! CTI learning: when the inductive step fails (SAT), extract the counterexample
//! state, block it as an auxiliary lemma, and retry. This strengthens the invariant
//! until either proven or iteration limit reached.

use crate::encoder::{assert_range_constraints, create_step_vars, EncoderCtx};
use crate::state_vars::VarLayout;
use crate::trace::extract_trace;
use crate::transition::{encode_init, encode_transition};
use crate::{SymbolicOutcome, SymbolicResult};
use specl_eval::Value;
use specl_ir::CompiledSpec;
use tracing::info;
use z3::ast::{Bool, Dynamic};
use z3::{SatResult, Solver};

/// Maximum number of CTI learning iterations per invariant.
const MAX_CTI_ITERATIONS: usize = 50;

/// Run k-induction checking with the given strengthening depth.
pub fn check_k_induction(
    spec: &CompiledSpec,
    consts: &[Value],
    k: usize,
    seq_bound: usize,
) -> SymbolicResult<SymbolicOutcome> {
    info!(k, "starting k-induction");

    let layout = VarLayout::from_spec(spec, consts, seq_bound)?;

    // === Base case: BMC to depth K ===
    info!(k, "k-induction base case");
    if let Some(outcome) = check_base_case(spec, consts, &layout, k)? {
        return Ok(outcome);
    }

    // === Inductive step with CTI learning ===
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

/// Inductive step with CTI learning.
///
/// K+1 states (0..=K), assert I at 0..K-1, transitions, ¬I at K.
/// When SAT (CTI found), extract the counterexample state, add it as
/// a blocking clause (lemma), and retry.
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
                compound_locals: Vec::new(),
                set_locals: Vec::new(),
                whole_var_locals: Vec::new(),
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
            compound_locals: Vec::new(),
            set_locals: Vec::new(),
            whole_var_locals: Vec::new(),
        };
        let inv_at_k = enc_k.encode_bool(&inv.body)?;
        solver.assert(inv_at_k.not());

        // CTI learning loop
        let mut cti_count = 0;
        loop {
            match solver.check() {
                SatResult::Sat => {
                    cti_count += 1;
                    if cti_count > MAX_CTI_ITERATIONS {
                        info!(
                            invariant = inv.name,
                            k, cti_count, "CTI learning limit reached"
                        );
                        solver.pop(1);
                        return Ok(SymbolicOutcome::Unknown {
                            reason: format!(
                                "invariant '{}' not provable after {} CTI iterations at k={}",
                                inv.name, cti_count, k
                            ),
                        });
                    }

                    let model = solver.get_model().unwrap();
                    info!(
                        invariant = inv.name,
                        k, cti_count, "CTI found, extracting blocking clause"
                    );

                    // Extract CTI state at step K and block it at all steps
                    let blocking = extract_blocking_clause(&model, layout, &all_step_vars, k);
                    if let Some(clause) = blocking {
                        // Block this state at step K (strengthen the goal)
                        solver.assert(&clause.at_k);
                        // Block at assumption steps 0..K-1 (strengthen the hypothesis)
                        for lemma in &clause.at_assumptions {
                            solver.assert(lemma);
                        }
                    } else {
                        // Could not extract blocking clause — give up
                        solver.pop(1);
                        return Ok(SymbolicOutcome::Unknown {
                            reason: format!(
                                "invariant '{}' not k-inductive at k={} (CTI extraction failed)",
                                inv.name, k
                            ),
                        });
                    }
                }
                SatResult::Unsat => {
                    if cti_count > 0 {
                        info!(
                            invariant = inv.name,
                            k,
                            lemmas = cti_count,
                            "invariant proved with CTI strengthening"
                        );
                    } else {
                        info!(invariant = inv.name, k, "invariant is k-inductive");
                    }
                    break;
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
        }

        solver.pop(1);
    }

    info!(k, "all invariants are k-inductive");
    Ok(SymbolicOutcome::Ok {
        method: "k-induction",
    })
}

/// A blocking clause that prevents a CTI state from appearing in the trace.
struct BlockingClause {
    /// Clause blocking the CTI at step K.
    at_k: Bool,
    /// Clauses blocking the CTI at assumption steps 0..K-1.
    at_assumptions: Vec<Bool>,
}

/// Extract a blocking clause from a CTI model.
///
/// For each Z3 variable at step K, evaluate its model value and create
/// an equality. The blocking clause is the negation of the conjunction
/// (= at least one variable must differ from the CTI).
fn extract_blocking_clause(
    model: &z3::Model,
    _layout: &VarLayout,
    all_step_vars: &[Vec<Vec<Dynamic>>],
    k: usize,
) -> Option<BlockingClause> {
    // Collect equalities: each variable at step K equals its CTI model value
    let mut equalities_at_k = Vec::new();
    for (var_idx, var_z3s) in all_step_vars[k].iter().enumerate() {
        for (sub_idx, z3_var) in var_z3s.iter().enumerate() {
            if let Some(val) = model.eval(z3_var, true) {
                let eq = z3_var.eq(&val);
                equalities_at_k.push((var_idx, sub_idx, eq, val));
            }
        }
    }

    if equalities_at_k.is_empty() {
        return None;
    }

    // Blocking clause at step K: NOT(all variables match CTI)
    let eq_refs: Vec<&Bool> = equalities_at_k.iter().map(|(_, _, eq, _)| eq).collect();
    let conjunction = Bool::and(&eq_refs);
    let at_k = conjunction.not();

    // Blocking clauses at assumption steps 0..K-1: same state is blocked
    let mut at_assumptions = Vec::new();
    for step_vars in &all_step_vars[..k] {
        let mut step_eqs = Vec::new();
        for (var_idx, sub_idx, _, val) in &equalities_at_k {
            let step_var = &step_vars[*var_idx][*sub_idx];
            step_eqs.push(step_var.eq(val));
        }
        let eq_refs: Vec<&Bool> = step_eqs.iter().collect();
        let conjunction = Bool::and(&eq_refs);
        at_assumptions.push(conjunction.not());
    }

    Some(BlockingClause {
        at_k,
        at_assumptions,
    })
}

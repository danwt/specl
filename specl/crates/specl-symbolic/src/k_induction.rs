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
//! state, generalize it via drop-literal minimization, block it as an auxiliary
//! lemma, and retry. This strengthens the invariant until either proven or
//! iteration limit reached.

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
/// With generalized blocking clauses each iteration blocks more states,
/// so fewer iterations are needed in practice.
const MAX_CTI_ITERATIONS: usize = 200;

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

    // === Inductive step with CTI learning ===
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

/// Inductive step with CTI learning and drop-literal generalization.
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

                    // Extract concrete equalities at step K
                    let equalities = extract_equalities(&model, &all_step_vars, k);
                    if equalities.is_empty() {
                        solver.pop(1);
                        return Ok(SymbolicOutcome::Unknown {
                            reason: format!(
                                "invariant '{}' not k-inductive at k={} (CTI extraction failed)",
                                inv.name, k
                            ),
                        });
                    }

                    // Generalize: drop inessential literals via push/pop probing
                    let essential_mask = generalize_blocking_clause(&solver, &equalities);

                    let total = equalities.len();
                    let essential_count = essential_mask.iter().filter(|&&e| e).count();
                    info!(
                        invariant = inv.name,
                        k,
                        cti_count,
                        total,
                        essential = essential_count,
                        dropped = total - essential_count,
                        "CTI generalized"
                    );

                    // Build and assert blocking clause from essential equalities
                    let blocking =
                        build_blocking_clause(&equalities, &essential_mask, &all_step_vars, k);
                    solver.assert(&blocking.at_k);
                    for lemma in &blocking.at_assumptions {
                        solver.assert(lemma);
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

/// A concrete equality: z3_var at step K = model value.
struct CtiEquality<'a> {
    var_idx: usize,
    sub_idx: usize,
    z3_var: &'a Dynamic,
    val: Dynamic,
}

/// Extract all concrete equalities from a CTI model at step K.
fn extract_equalities<'a>(
    model: &z3::Model,
    all_step_vars: &'a [Vec<Vec<Dynamic>>],
    k: usize,
) -> Vec<CtiEquality<'a>> {
    let mut equalities = Vec::new();
    for (var_idx, var_z3s) in all_step_vars[k].iter().enumerate() {
        for (sub_idx, z3_var) in var_z3s.iter().enumerate() {
            if let Some(val) = model.eval(z3_var, true) {
                equalities.push(CtiEquality {
                    var_idx,
                    sub_idx,
                    z3_var,
                    val,
                });
            }
        }
    }
    equalities
}

/// Drop-literal generalization: determine which equalities are essential.
///
/// For each equality, check if removing it still allows a CTI to exist.
/// Uses the solver's existing context (inductive hypothesis + transitions + ¬I).
///
/// Algorithm:
/// - For each equality i, assert all OTHER essential equalities (the "reduced pattern")
/// - If SAT: a CTI exists even without constraining variable i → i is inessential
/// - If UNSAT: no CTI matches the reduced pattern → i is essential (must keep it)
///
/// Returns a boolean mask: true = essential (keep), false = inessential (dropped).
fn generalize_blocking_clause(solver: &Solver, equalities: &[CtiEquality]) -> Vec<bool> {
    let n = equalities.len();
    let mut essential = vec![true; n];

    for i in 0..n {
        if !essential[i] {
            continue;
        }

        // Try without equality i: force step K to match the reduced pattern
        solver.push();

        // Assert all currently-essential equalities EXCEPT i
        for j in 0..n {
            if j == i || !essential[j] {
                continue;
            }
            let eq = equalities[j].z3_var.eq(&equalities[j].val);
            solver.assert(&eq);
        }

        match solver.check() {
            SatResult::Sat => {
                // A CTI exists even without constraining variable i
                // → variable i's specific value is inessential, drop it
                essential[i] = false;
            }
            SatResult::Unsat => {
                // No CTI matches without variable i → must keep it
            }
            SatResult::Unknown => {
                // Conservatively keep it
            }
        }

        solver.pop(1);
    }

    essential
}

/// A blocking clause that prevents a CTI state from appearing in the trace.
struct BlockingClause {
    /// Clause blocking the CTI at step K.
    at_k: Bool,
    /// Clauses blocking the CTI at assumption steps 0..K-1.
    at_assumptions: Vec<Bool>,
}

/// Build a blocking clause from essential equalities.
///
/// The blocking clause is NOT(AND(essential equalities)), applied at step K
/// and at each assumption step 0..K-1.
fn build_blocking_clause(
    equalities: &[CtiEquality],
    essential_mask: &[bool],
    all_step_vars: &[Vec<Vec<Dynamic>>],
    k: usize,
) -> BlockingClause {
    // Collect essential equalities at step K
    let mut eq_at_k = Vec::new();
    for (i, eq) in equalities.iter().enumerate() {
        if essential_mask[i] {
            eq_at_k.push(eq.z3_var.eq(&eq.val));
        }
    }

    let eq_refs: Vec<&Bool> = eq_at_k.iter().collect();
    let at_k = if eq_refs.is_empty() {
        Bool::from_bool(true).not() // shouldn't happen, but safe fallback
    } else {
        Bool::and(&eq_refs).not()
    };

    // Build blocking clauses at assumption steps 0..K-1
    let mut at_assumptions = Vec::new();
    for step_vars in &all_step_vars[..k] {
        let mut step_eqs = Vec::new();
        for (i, eq) in equalities.iter().enumerate() {
            if essential_mask[i] {
                let step_var = &step_vars[eq.var_idx][eq.sub_idx];
                step_eqs.push(step_var.eq(&eq.val));
            }
        }
        let eq_refs: Vec<&Bool> = step_eqs.iter().collect();
        if eq_refs.is_empty() {
            at_assumptions.push(Bool::from_bool(true).not());
        } else {
            at_assumptions.push(Bool::and(&eq_refs).not());
        }
    }

    BlockingClause {
        at_k,
        at_assumptions,
    }
}

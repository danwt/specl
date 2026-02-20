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
use crate::state_vars::{VarKind, VarLayout};
use crate::trace::extract_trace;
use crate::transition::{encode_init, encode_transition};
use crate::{CtiLemma, KInductionResult, SymbolicOutcome, SymbolicResult};
use specl_eval::Value;
use specl_ir::{BinOp, CompiledExpr, CompiledSpec, UnaryOp};
use tracing::info;
use z3::ast::Dynamic;
use z3::{Model, SatResult, Solver};

/// Maximum number of CTI lemmas to extract per k-induction invocation.
const MAX_CTI_ITERATIONS: usize = 5;

/// Run k-induction checking with the given strengthening depth.
pub fn check_k_induction(
    spec: &CompiledSpec,
    consts: &[Value],
    k: usize,
    seq_bound: usize,
    timeout_ms: Option<u64>,
) -> SymbolicResult<SymbolicOutcome> {
    let result = check_k_induction_with_cti(spec, consts, k, seq_bound, timeout_ms)?;
    Ok(result.outcome)
}

/// Run k-induction with CTI lemma extraction.
/// When the inductive step fails, extracts counterexample states and builds
/// blocking clauses that can be used as candidate auxiliary invariants.
pub fn check_k_induction_with_cti(
    spec: &CompiledSpec,
    consts: &[Value],
    k: usize,
    seq_bound: usize,
    timeout_ms: Option<u64>,
) -> SymbolicResult<KInductionResult> {
    info!(k, "starting k-induction with CTI extraction");

    let layout = VarLayout::from_spec(spec, consts, seq_bound)?;

    // === Base case: BMC to depth K ===
    info!(k, "k-induction base case");
    if let Some(outcome) = check_base_case(spec, consts, &layout, k, timeout_ms)? {
        return Ok(KInductionResult {
            outcome,
            cti_lemmas: Vec::new(),
        });
    }

    // === Inductive step with CTI extraction ===
    info!(k, "k-induction inductive step with CTI extraction");
    check_inductive_step_with_cti(spec, consts, &layout, k, timeout_ms)
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

/// Inductive step with CTI extraction.
/// When the step is SAT, extracts model values and builds blocking lemmas.
fn check_inductive_step_with_cti(
    spec: &CompiledSpec,
    consts: &[Value],
    layout: &VarLayout,
    k: usize,
    timeout_ms: Option<u64>,
) -> SymbolicResult<KInductionResult> {
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

    let mut cti_lemmas = Vec::new();

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

        // Check and extract CTIs iteratively
        for cti_iter in 0..MAX_CTI_ITERATIONS {
            match solver.check() {
                SatResult::Sat => {
                    info!(invariant = inv.name, k, cti_iter, "extracting CTI");
                    let model = solver.get_model().unwrap();

                    // Extract state at step k-1 (last assumption step)
                    let equalities =
                        extract_state_equalities(&model, layout, &all_step_vars, k - 1);

                    if equalities.is_empty() {
                        info!("CTI extraction yielded no equalities, skipping");
                        break;
                    }

                    // Build blocking clause: NOT(e1 AND e2 AND ... AND en)
                    let conjunction = build_conjunction(&equalities);
                    let blocking = CompiledExpr::Unary {
                        op: UnaryOp::Not,
                        operand: Box::new(conjunction.clone()),
                    };

                    cti_lemmas.push(CtiLemma {
                        description: format!("CTI-k{}-{}-{}", k, inv.name, cti_iter),
                        body: blocking.clone(),
                    });

                    // Add Z3 blocking clause to prevent re-finding this CTI
                    let mut enc_block = EncoderCtx {
                        layout,
                        consts,
                        step_vars: &all_step_vars,
                        current_step: k - 1,
                        next_step: k - 1,
                        params: &[],
                        locals: Vec::new(),
                        compound_locals: Vec::new(),
                        set_locals: Vec::new(),
                        whole_var_locals: Vec::new(),
                    };
                    if let Ok(block_encoded) = enc_block.encode_bool(&blocking) {
                        solver.assert(&block_encoded);
                    } else {
                        break;
                    }
                }
                SatResult::Unsat => {
                    if cti_iter == 0 {
                        // First check was UNSAT — invariant is k-inductive
                        info!(invariant = inv.name, k, "invariant is k-inductive");
                    } else {
                        // Blocked all CTIs — invariant might be provable with lemmas
                        info!(
                            invariant = inv.name,
                            k,
                            cti_count = cti_iter,
                            "all CTIs blocked"
                        );
                    }
                    break;
                }
                SatResult::Unknown => {
                    solver.pop(1);
                    return Ok(KInductionResult {
                        outcome: SymbolicOutcome::Unknown {
                            reason: format!(
                                "Z3 returned unknown for k-induction step for invariant '{}'",
                                inv.name
                            ),
                        },
                        cti_lemmas,
                    });
                }
            }
        }

        solver.pop(1);
    }

    // If we collected any CTI lemmas, the result is Unknown (needs IC3 verification)
    if !cti_lemmas.is_empty() {
        info!(
            lemma_count = cti_lemmas.len(),
            "collected CTI lemmas for IC3 verification"
        );
        return Ok(KInductionResult {
            outcome: SymbolicOutcome::Unknown {
                reason: format!("not k-inductive, collected {} CTI lemmas", cti_lemmas.len()),
            },
            cti_lemmas,
        });
    }

    info!(k, "all invariants are k-inductive");
    Ok(KInductionResult {
        outcome: SymbolicOutcome::Ok {
            method: "k-induction",
        },
        cti_lemmas: Vec::new(),
    })
}

/// Extract equalities from a Z3 model for all state variables at a given step.
/// Returns a list of `Var(idx) == value` or `Index { Var(idx), Int(k) } == value` expressions.
fn extract_state_equalities(
    model: &Model,
    layout: &VarLayout,
    step_vars: &[Vec<Vec<Dynamic>>],
    step: usize,
) -> Vec<CompiledExpr> {
    let mut equalities = Vec::new();
    for (var_idx, entry) in layout.entries.iter().enumerate() {
        let z3_vars = &step_vars[step][var_idx];
        extract_var_equalities(model, var_idx, &entry.kind, z3_vars, &mut equalities);
    }
    equalities
}

/// Extract equalities for a single variable from the Z3 model.
fn extract_var_equalities(
    model: &Model,
    var_idx: usize,
    kind: &VarKind,
    z3_vars: &[Dynamic],
    equalities: &mut Vec<CompiledExpr>,
) {
    match kind {
        VarKind::Bool => {
            if let Some(val) = model
                .eval(&z3_vars[0], true)
                .and_then(|v| v.as_bool())
                .and_then(|b| b.as_bool())
            {
                equalities.push(CompiledExpr::Binary {
                    op: BinOp::Eq,
                    left: Box::new(CompiledExpr::Var(var_idx)),
                    right: Box::new(CompiledExpr::Bool(val)),
                });
            }
        }
        VarKind::Int { .. } => {
            if let Some(val) = model
                .eval(&z3_vars[0], true)
                .and_then(|v| v.as_int())
                .and_then(|i| i.as_i64())
            {
                equalities.push(CompiledExpr::Binary {
                    op: BinOp::Eq,
                    left: Box::new(CompiledExpr::Var(var_idx)),
                    right: Box::new(CompiledExpr::Int(val)),
                });
            }
        }
        VarKind::ExplodedDict {
            key_lo,
            key_hi,
            value_kind,
        } => {
            let stride = value_kind.z3_var_count();
            for (i, k) in (*key_lo..=*key_hi).enumerate() {
                let offset = i * stride;
                match value_kind.as_ref() {
                    VarKind::Bool => {
                        if let Some(val) = model
                            .eval(&z3_vars[offset], true)
                            .and_then(|v| v.as_bool())
                            .and_then(|b| b.as_bool())
                        {
                            equalities.push(CompiledExpr::Binary {
                                op: BinOp::Eq,
                                left: Box::new(CompiledExpr::Index {
                                    base: Box::new(CompiledExpr::Var(var_idx)),
                                    index: Box::new(CompiledExpr::Int(k)),
                                }),
                                right: Box::new(CompiledExpr::Bool(val)),
                            });
                        }
                    }
                    VarKind::Int { .. } => {
                        if let Some(val) = model
                            .eval(&z3_vars[offset], true)
                            .and_then(|v| v.as_int())
                            .and_then(|i| i.as_i64())
                        {
                            equalities.push(CompiledExpr::Binary {
                                op: BinOp::Eq,
                                left: Box::new(CompiledExpr::Index {
                                    base: Box::new(CompiledExpr::Var(var_idx)),
                                    index: Box::new(CompiledExpr::Int(k)),
                                }),
                                right: Box::new(CompiledExpr::Int(val)),
                            });
                        }
                    }
                    // Skip compound value types (Seq, Set, nested Dict, etc.)
                    _ => {}
                }
            }
        }
        VarKind::ExplodedSet { lo, hi } => {
            // For sets, build per-element membership constraints.
            // k in var == true/false → Var(var_idx)[k] == true/false equivalent
            // Skip: set membership isn't expressible as simple Var==value equalities
            // in CompiledExpr without In/NotIn which the encoder handles differently.
            let _ = (lo, hi, z3_vars);
        }
        // Skip other compound types
        _ => {}
    }
}

/// Build a conjunction of expressions: e1 AND e2 AND ... AND en.
fn build_conjunction(exprs: &[CompiledExpr]) -> CompiledExpr {
    assert!(!exprs.is_empty());
    let mut result = exprs[0].clone();
    for expr in &exprs[1..] {
        result = CompiledExpr::Binary {
            op: BinOp::And,
            left: Box::new(result),
            right: Box::new(expr.clone()),
        };
    }
    result
}

//! IC3/CHC verification via Z3's Spacer engine.
//!
//! Encodes the spec as Constrained Horn Clauses and uses Z3's fixedpoint
//! engine (Spacer) to perform unbounded verification.

use crate::encoder::{assert_range_constraints, create_step_vars, EncoderCtx};
use crate::fixedpoint::Fixedpoint;
use crate::state_vars::{VarKind, VarLayout};
use crate::transition::{encode_init, encode_transition};
use crate::{SymbolicOutcome, SymbolicResult};
use specl_eval::Value;
use specl_ir::CompiledSpec;
use tracing::info;
use z3::ast::{Ast, Dynamic};
use z3::{Context, Solver};

/// Built CHC system ready for querying (used by IC3 and Golem backends).
pub struct ChcSystem {
    pub fp: Fixedpoint,
    pub err_app: z3_sys::Z3_ast,
}

/// Build a CHC system encoding the spec as Horn clauses with invariant error rules.
/// Returns the fixedpoint engine and the Error query app.
pub fn build_chc_system(
    spec: &CompiledSpec,
    consts: &[Value],
    layout: &VarLayout,
) -> SymbolicResult<ChcSystem> {
    let ctx = Context::thread_local().get_z3_context();
    let fp = Fixedpoint::new();

    // Collect sorts for all flattened state variables
    let sorts = collect_sorts(layout, ctx);
    let num_vars = sorts.len();

    // Declare Reach relation
    let reach_name = unsafe { z3_sys::Z3_mk_string_symbol(ctx, c"Reach".as_ptr()) }.unwrap();
    let bool_sort = unsafe { z3_sys::Z3_mk_bool_sort(ctx) }.unwrap();
    let reach_decl = unsafe {
        z3_sys::Z3_mk_func_decl(ctx, reach_name, num_vars as u32, sorts.as_ptr(), bool_sort)
    }
    .unwrap();
    fp.register_relation(reach_decl);

    // Create step vars for step 0 and step 1
    let step0_vars = create_step_vars(layout, 0);
    let step1_vars = create_step_vars(layout, 1);
    let all_step_vars = vec![step0_vars, step1_vars];

    // Collect all Z3 constants (as Z3_app) for quantification
    let flat0 = flatten_step_vars(&all_step_vars[0]);
    let flat1 = flatten_step_vars(&all_step_vars[1]);
    let apps0 = to_apps(ctx, &flat0);
    let apps1 = to_apps(ctx, &flat1);
    let all_apps: Vec<z3_sys::Z3_app> = apps0.iter().chain(apps1.iter()).copied().collect();

    let reach_0 = mk_app(ctx, reach_decl, &flat0);
    let reach_1 = mk_app(ctx, reach_decl, &flat1);

    // === Init rule: forall vars0. init(vars0) => Reach(vars0) ===
    let init_solver = Solver::new();
    assert_range_constraints(&init_solver, layout, &all_step_vars, 0);
    encode_init(&init_solver, spec, consts, layout, &all_step_vars)?;
    let init_formula = solver_conjunction_raw(ctx, &init_solver);
    let init_body = mk_implies(ctx, init_formula, reach_0);
    let init_rule = mk_forall(ctx, &apps0, init_body);
    fp.add_rule(init_rule);

    // === Transition rule: forall vars0,vars1. Reach(vars0) ∧ range(vars1) ∧ trans ∧ aux(vars1) => Reach(vars1) ===
    let trans = encode_transition(spec, consts, layout, &all_step_vars, 0)?;
    let trans_raw = trans.get_z3_ast();
    inc_ref(ctx, trans_raw);

    let range_solver = Solver::new();
    assert_range_constraints(&range_solver, layout, &all_step_vars, 1);
    let range_formula = solver_conjunction_raw(ctx, &range_solver);

    let mut trans_body = mk_and3(ctx, reach_0, range_formula, trans_raw);

    // Constrain Reach to states satisfying all auxiliary invariants (at step 1 = post-transition)
    for aux in &spec.auxiliary_invariants {
        let mut enc_aux = EncoderCtx {
            layout,
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
        let aux_encoded = enc_aux.encode_bool(&aux.body)?;
        let aux_raw = aux_encoded.get_z3_ast();
        inc_ref(ctx, aux_raw);
        trans_body = mk_and2(ctx, trans_body, aux_raw);
    }

    let trans_impl = mk_implies(ctx, trans_body, reach_1);
    let trans_rule = mk_forall(ctx, &all_apps, trans_impl);
    fp.add_rule(trans_rule);

    // === Error relation for invariant queries ===
    let err_name = unsafe { z3_sys::Z3_mk_string_symbol(ctx, c"Error".as_ptr()) }.unwrap();
    let err_decl =
        unsafe { z3_sys::Z3_mk_func_decl(ctx, err_name, 0, std::ptr::null(), bool_sort) }.unwrap();
    fp.register_relation(err_decl);
    let err_app = mk_app(ctx, err_decl, &[]);

    // Add error rules for each invariant: Reach(vars) ∧ ¬I(vars) => Error
    for inv in &spec.invariants {
        let mut enc = EncoderCtx {
            layout,
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
        let inv_encoded = enc.encode_bool(&inv.body)?;
        let inv_raw = inv_encoded.get_z3_ast();
        inc_ref(ctx, inv_raw);
        let neg_inv_raw = mk_not(ctx, inv_raw);

        let err_body = mk_and2(ctx, reach_0, neg_inv_raw);
        let err_impl = mk_implies(ctx, err_body, err_app);
        let err_rule = mk_forall(ctx, &apps0, err_impl);
        fp.add_rule(err_rule);
    }

    Ok(ChcSystem { fp, err_app })
}

/// Run IC3/CHC verification using Z3's Spacer engine.
pub fn check_ic3(
    spec: &CompiledSpec,
    consts: &[Value],
    seq_bound: usize,
    spacer_profile: crate::SpacerProfile,
    timeout_ms: Option<u64>,
) -> SymbolicResult<SymbolicOutcome> {
    info!(?spacer_profile, "starting IC3/CHC verification");

    let layout = VarLayout::from_spec(spec, consts, seq_bound)?;
    let ctx = Context::thread_local().get_z3_context();
    let fp = Fixedpoint::with_profile(spacer_profile, timeout_ms);

    // Collect sorts for all flattened state variables
    let sorts = collect_sorts(&layout, ctx);
    let num_vars = sorts.len();

    // Declare Reach relation
    let reach_name = unsafe { z3_sys::Z3_mk_string_symbol(ctx, c"Reach".as_ptr()) }.unwrap();
    let bool_sort = unsafe { z3_sys::Z3_mk_bool_sort(ctx) }.unwrap();
    let reach_decl = unsafe {
        z3_sys::Z3_mk_func_decl(ctx, reach_name, num_vars as u32, sorts.as_ptr(), bool_sort)
    }
    .unwrap();
    fp.register_relation(reach_decl);

    // Create step vars for step 0 and step 1
    let step0_vars = create_step_vars(&layout, 0);
    let step1_vars = create_step_vars(&layout, 1);
    let all_step_vars = vec![step0_vars, step1_vars];

    // Collect all Z3 constants (as Z3_app) for quantification
    let flat0 = flatten_step_vars(&all_step_vars[0]);
    let flat1 = flatten_step_vars(&all_step_vars[1]);
    let apps0 = to_apps(ctx, &flat0);
    let apps1 = to_apps(ctx, &flat1);
    let all_apps: Vec<z3_sys::Z3_app> = apps0.iter().chain(apps1.iter()).copied().collect();

    let reach_0 = mk_app(ctx, reach_decl, &flat0);
    let reach_1 = mk_app(ctx, reach_decl, &flat1);

    // === Init rule: forall vars0. init(vars0) => Reach(vars0) ===
    let init_solver = Solver::new();
    assert_range_constraints(&init_solver, &layout, &all_step_vars, 0);
    encode_init(&init_solver, spec, consts, &layout, &all_step_vars)?;
    let init_formula = solver_conjunction_raw(ctx, &init_solver);
    let init_body = mk_implies(ctx, init_formula, reach_0);
    let init_rule = mk_forall(ctx, &apps0, init_body);
    fp.add_rule(init_rule);

    // === Transition rule: forall vars0,vars1. Reach(vars0) ∧ range(vars1) ∧ trans ∧ aux(vars1) => Reach(vars1) ===
    let trans = encode_transition(spec, consts, &layout, &all_step_vars, 0)?;
    let trans_raw = trans.get_z3_ast();
    inc_ref(ctx, trans_raw);

    let range_solver = Solver::new();
    assert_range_constraints(&range_solver, &layout, &all_step_vars, 1);
    let range_formula = solver_conjunction_raw(ctx, &range_solver);

    let mut trans_body = mk_and3(ctx, reach_0, range_formula, trans_raw);

    // Constrain Reach to states satisfying all auxiliary invariants (at step 1 = post-transition)
    for aux in &spec.auxiliary_invariants {
        let mut enc_aux = EncoderCtx {
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
        let aux_encoded = enc_aux.encode_bool(&aux.body)?;
        let aux_raw = aux_encoded.get_z3_ast();
        inc_ref(ctx, aux_raw);
        trans_body = mk_and2(ctx, trans_body, aux_raw);
    }

    let trans_impl = mk_implies(ctx, trans_body, reach_1);
    let trans_rule = mk_forall(ctx, &all_apps, trans_impl);
    fp.add_rule(trans_rule);

    // === Query each invariant ===
    let err_name = unsafe { z3_sys::Z3_mk_string_symbol(ctx, c"Error".as_ptr()) }.unwrap();
    let err_decl =
        unsafe { z3_sys::Z3_mk_func_decl(ctx, err_name, 0, std::ptr::null(), bool_sort) }.unwrap();
    fp.register_relation(err_decl);
    let err_app = mk_app(ctx, err_decl, &[]);

    for inv in &spec.invariants {
        let mut enc = EncoderCtx {
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
        let inv_encoded = enc.encode_bool(&inv.body)?;
        let inv_raw = inv_encoded.get_z3_ast();
        inc_ref(ctx, inv_raw);
        let neg_inv_raw = mk_not(ctx, inv_raw);

        // Rule: forall vars0. Reach(vars0) ∧ ¬I(vars0) => Error
        let err_body = mk_and2(ctx, reach_0, neg_inv_raw);
        let err_impl = mk_implies(ctx, err_body, err_app);
        let err_rule = mk_forall(ctx, &apps0, err_impl);
        fp.add_rule(err_rule);

        match fp.query(err_app) {
            z3_sys::Z3_L_FALSE => {
                info!(invariant = inv.name, "invariant verified by IC3");
            }
            z3_sys::Z3_L_TRUE => {
                info!(
                    invariant = inv.name,
                    "IC3 found violation, reconstructing trace via BMC"
                );
                let mut trace = Vec::new();
                for depth in [1, 2, 4, 8, 16, 32] {
                    match crate::bmc::check_bmc(spec, consts, depth, seq_bound, timeout_ms) {
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
                if trace.is_empty() {
                    info!("could not reconstruct trace (violation may require depth > 32)");
                }
                return Ok(SymbolicOutcome::InvariantViolation {
                    invariant: inv.name.clone(),
                    trace,
                });
            }
            _ => {
                let reason = fp.get_reason_unknown();
                info!(
                    invariant = inv.name,
                    reason = reason,
                    "IC3 returned unknown"
                );
                return Ok(SymbolicOutcome::Unknown {
                    reason: format!(
                        "IC3 returned unknown for invariant '{}': {}",
                        inv.name, reason
                    ),
                });
            }
        }
    }

    info!("all invariants verified by IC3");
    Ok(SymbolicOutcome::Ok { method: "IC3" })
}

// === Raw z3-sys helper functions ===
// All helpers inc_ref their return values to prevent Z3 GC.

fn inc_ref(ctx: z3_sys::Z3_context, ast: z3_sys::Z3_ast) {
    unsafe { z3_sys::Z3_inc_ref(ctx, ast) };
}

fn mk_implies(ctx: z3_sys::Z3_context, a: z3_sys::Z3_ast, b: z3_sys::Z3_ast) -> z3_sys::Z3_ast {
    let r = unsafe { z3_sys::Z3_mk_implies(ctx, a, b) }.unwrap();
    inc_ref(ctx, r);
    r
}

fn mk_not(ctx: z3_sys::Z3_context, a: z3_sys::Z3_ast) -> z3_sys::Z3_ast {
    let r = unsafe { z3_sys::Z3_mk_not(ctx, a) }.unwrap();
    inc_ref(ctx, r);
    r
}

fn mk_and2(ctx: z3_sys::Z3_context, a: z3_sys::Z3_ast, b: z3_sys::Z3_ast) -> z3_sys::Z3_ast {
    let args = [a, b];
    let r = unsafe { z3_sys::Z3_mk_and(ctx, 2, args.as_ptr()) }.unwrap();
    inc_ref(ctx, r);
    r
}

fn mk_and3(
    ctx: z3_sys::Z3_context,
    a: z3_sys::Z3_ast,
    b: z3_sys::Z3_ast,
    c: z3_sys::Z3_ast,
) -> z3_sys::Z3_ast {
    let args = [a, b, c];
    let r = unsafe { z3_sys::Z3_mk_and(ctx, 3, args.as_ptr()) }.unwrap();
    inc_ref(ctx, r);
    r
}

fn mk_app(
    ctx: z3_sys::Z3_context,
    decl: z3_sys::Z3_func_decl,
    args: &[z3_sys::Z3_ast],
) -> z3_sys::Z3_ast {
    let r = unsafe { z3_sys::Z3_mk_app(ctx, decl, args.len() as u32, args.as_ptr()) }.unwrap();
    inc_ref(ctx, r);
    r
}

fn mk_forall(
    ctx: z3_sys::Z3_context,
    apps: &[z3_sys::Z3_app],
    body: z3_sys::Z3_ast,
) -> z3_sys::Z3_ast {
    if apps.is_empty() {
        return body;
    }
    let r = unsafe {
        z3_sys::Z3_mk_forall_const(
            ctx,
            0, // weight
            apps.len() as u32,
            apps.as_ptr(),
            0, // num_patterns
            std::ptr::null(),
            body,
        )
    }
    .unwrap();
    inc_ref(ctx, r);
    r
}

/// Convert Z3_ast constants to Z3_app for quantifier binding.
fn to_apps(ctx: z3_sys::Z3_context, asts: &[z3_sys::Z3_ast]) -> Vec<z3_sys::Z3_app> {
    asts.iter()
        .map(|a| unsafe { z3_sys::Z3_to_app(ctx, *a) }.unwrap())
        .collect()
}

/// Extract all solver assertions as a raw Z3_ast conjunction.
/// The returned AST is ref-counted (inc_ref called).
fn solver_conjunction_raw(ctx: z3_sys::Z3_context, solver: &Solver) -> z3_sys::Z3_ast {
    let assertions = solver.get_assertions();
    if assertions.is_empty() {
        let t = unsafe { z3_sys::Z3_mk_true(ctx) }.unwrap();
        inc_ref(ctx, t);
        return t;
    }
    let raw: Vec<z3_sys::Z3_ast> = assertions.iter().map(|a| a.get_z3_ast()).collect();
    let result = if raw.len() == 1 {
        raw[0]
    } else {
        unsafe { z3_sys::Z3_mk_and(ctx, raw.len() as u32, raw.as_ptr()) }.unwrap()
    };
    inc_ref(ctx, result);
    result
}

/// Collect Z3 sorts for all flattened state variables.
fn collect_sorts(layout: &VarLayout, ctx: z3_sys::Z3_context) -> Vec<z3_sys::Z3_sort> {
    let bool_sort = unsafe { z3_sys::Z3_mk_bool_sort(ctx) }.unwrap();
    let int_sort = unsafe { z3_sys::Z3_mk_int_sort(ctx) }.unwrap();

    let mut sorts = Vec::new();
    for entry in &layout.entries {
        collect_sorts_for_kind(&entry.kind, bool_sort, int_sort, &mut sorts);
    }
    sorts
}

fn collect_sorts_for_kind(
    kind: &VarKind,
    bool_sort: z3_sys::Z3_sort,
    int_sort: z3_sys::Z3_sort,
    out: &mut Vec<z3_sys::Z3_sort>,
) {
    match kind {
        VarKind::Bool => out.push(bool_sort),
        VarKind::Int { .. } => out.push(int_sort),
        VarKind::ExplodedDict {
            key_lo,
            key_hi,
            value_kind,
        } => {
            for _ in 0..(*key_hi - *key_lo + 1) {
                collect_sorts_for_kind(value_kind, bool_sort, int_sort, out);
            }
        }
        VarKind::ExplodedSet { lo, hi } => {
            for _ in 0..(*hi - *lo + 1) {
                out.push(bool_sort);
            }
        }
        VarKind::ExplodedSeq { max_len, elem_kind } => {
            out.push(int_sort); // len
            for _ in 0..*max_len {
                collect_sorts_for_kind(elem_kind, bool_sort, int_sort, out);
            }
        }
        VarKind::ExplodedOption { inner_kind } => {
            out.push(bool_sort); // present flag
            collect_sorts_for_kind(inner_kind, bool_sort, int_sort, out);
        }
        VarKind::ExplodedTuple { element_kinds } => {
            for kind in element_kinds {
                collect_sorts_for_kind(kind, bool_sort, int_sort, out);
            }
        }
        VarKind::ExplodedRecord { field_kinds, .. } => {
            for kind in field_kinds {
                collect_sorts_for_kind(kind, bool_sort, int_sort, out);
            }
        }
    }
}

/// Flatten step vars into a single vec of raw Z3 ASTs.
fn flatten_step_vars(step_vars: &[Vec<Dynamic>]) -> Vec<z3_sys::Z3_ast> {
    step_vars
        .iter()
        .flat_map(|vs| vs.iter().map(|v| v.get_z3_ast()))
        .collect()
}

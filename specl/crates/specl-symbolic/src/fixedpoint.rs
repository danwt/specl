//! Minimal safe wrapper around z3-sys fixedpoint (Spacer/IC3) API.

use z3::Context;

/// Spacer parameter profile controlling IC3/CHC solving strategy.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpacerProfile {
    /// Z3 defaults — no special tuning.
    Default,
    /// Optimized for small-medium protocol verification (5-20 state vars).
    /// Disables expensive normalizations and focuses on fast convergence.
    Fast,
    /// More thorough exploration for harder problems. Uses heavier
    /// model-based projection and ground POBs.
    Thorough,
}

/// Wrapper around Z3 fixedpoint engine (Spacer).
pub struct Fixedpoint {
    ctx: z3_sys::Z3_context,
    fp: z3_sys::Z3_fixedpoint,
}

impl Default for Fixedpoint {
    fn default() -> Self {
        Self::new()
    }
}

impl Fixedpoint {
    /// Create a new fixedpoint engine using the thread-local Z3 context.
    pub fn new() -> Self {
        Self::with_profile(SpacerProfile::Default)
    }

    /// Create a new fixedpoint engine with a specific Spacer parameter profile.
    pub fn with_profile(profile: SpacerProfile) -> Self {
        let ctx = Context::thread_local().get_z3_context();
        let fp = unsafe { z3_sys::Z3_mk_fixedpoint(ctx) }.unwrap();
        unsafe { z3_sys::Z3_fixedpoint_inc_ref(ctx, fp) };

        let params = unsafe { z3_sys::Z3_mk_params(ctx) }.unwrap();
        unsafe { z3_sys::Z3_params_inc_ref(ctx, params) };

        // Always use Spacer engine
        set_symbol_param(ctx, params, c"engine", c"spacer");

        match profile {
            SpacerProfile::Default => {}
            SpacerProfile::Fast => {
                // Skip pushing proof obligations up — faster for protocol-sized problems
                set_bool_param(ctx, params, c"spacer.push_pob", false);
                // Disable expensive quantifier normalization
                set_bool_param(ctx, params, c"spacer.q3.qgen.normalize", false);
                // Don't ground POBs (faster but less precise)
                set_bool_param(ctx, params, c"spacer.ground_pobs", false);
                // Use MBP (model-based projection) for faster generalization
                set_bool_param(ctx, params, c"spacer.use_bg_invs", false);
                // Limit restarts for convergence
                set_uint_param(ctx, params, c"spacer.max_level", 50);
            }
            SpacerProfile::Thorough => {
                // Use heavy model evaluation for stronger lemma generalization
                set_bool_param(ctx, params, c"spacer.use_heavy_mev", true);
                // Ground POBs for more precise reasoning
                set_bool_param(ctx, params, c"spacer.ground_pobs", true);
                // Enable inductive generalization
                set_bool_param(ctx, params, c"spacer.use_inductive_generalizer", true);
                // Higher level limit
                set_uint_param(ctx, params, c"spacer.max_level", 200);
            }
        }

        unsafe { z3_sys::Z3_fixedpoint_set_params(ctx, fp, params) };
        unsafe { z3_sys::Z3_params_dec_ref(ctx, params) };

        Fixedpoint { ctx, fp }
    }

    /// Register a relation (func_decl) with the fixedpoint engine.
    pub fn register_relation(&self, func_decl: z3_sys::Z3_func_decl) {
        unsafe { z3_sys::Z3_fixedpoint_register_relation(self.ctx, self.fp, func_decl) };
    }

    /// Add a rule (universally quantified Horn clause).
    pub fn add_rule(&self, rule: z3_sys::Z3_ast) {
        let name = unsafe { z3_sys::Z3_mk_string_symbol(self.ctx, c"rule".as_ptr()) }.unwrap();
        unsafe { z3_sys::Z3_fixedpoint_add_rule(self.ctx, self.fp, rule, name) };
    }

    /// Query whether the given relation is reachable. Returns Z3_lbool.
    pub fn query(&self, query: z3_sys::Z3_ast) -> z3_sys::Z3_lbool {
        unsafe { z3_sys::Z3_fixedpoint_query(self.ctx, self.fp, query) }
    }

    /// Export the CHC system as SMT-LIB2 string, including the given queries.
    pub fn to_smt2(&self, queries: &[z3_sys::Z3_ast]) -> String {
        let s = unsafe {
            z3_sys::Z3_fixedpoint_to_string(
                self.ctx,
                self.fp,
                queries.len() as u32,
                queries.as_ptr() as *mut z3_sys::Z3_ast,
            )
        };
        if s.is_null() {
            return String::new();
        }
        unsafe { std::ffi::CStr::from_ptr(s) }
            .to_str()
            .unwrap_or("")
            .to_string()
    }

    /// Get the reason for an unknown result.
    pub fn get_reason_unknown(&self) -> String {
        let s = unsafe { z3_sys::Z3_fixedpoint_get_reason_unknown(self.ctx, self.fp) };
        if s.is_null() {
            return "(null)".to_string();
        }
        unsafe { std::ffi::CStr::from_ptr(s) }
            .to_str()
            .unwrap_or("(invalid utf8)")
            .to_string()
    }
}

impl Drop for Fixedpoint {
    fn drop(&mut self) {
        unsafe { z3_sys::Z3_fixedpoint_dec_ref(self.ctx, self.fp) };
    }
}

// === Parameter helpers ===

fn set_symbol_param(
    ctx: z3_sys::Z3_context,
    params: z3_sys::Z3_params,
    key: &std::ffi::CStr,
    val: &std::ffi::CStr,
) {
    let k = unsafe { z3_sys::Z3_mk_string_symbol(ctx, key.as_ptr()) }.unwrap();
    let v = unsafe { z3_sys::Z3_mk_string_symbol(ctx, val.as_ptr()) }.unwrap();
    unsafe { z3_sys::Z3_params_set_symbol(ctx, params, k, v) };
}

fn set_bool_param(
    ctx: z3_sys::Z3_context,
    params: z3_sys::Z3_params,
    key: &std::ffi::CStr,
    val: bool,
) {
    let k = unsafe { z3_sys::Z3_mk_string_symbol(ctx, key.as_ptr()) }.unwrap();
    unsafe { z3_sys::Z3_params_set_bool(ctx, params, k, val) };
}

fn set_uint_param(
    ctx: z3_sys::Z3_context,
    params: z3_sys::Z3_params,
    key: &std::ffi::CStr,
    val: u32,
) {
    let k = unsafe { z3_sys::Z3_mk_string_symbol(ctx, key.as_ptr()) }.unwrap();
    unsafe { z3_sys::Z3_params_set_uint(ctx, params, k, val) };
}

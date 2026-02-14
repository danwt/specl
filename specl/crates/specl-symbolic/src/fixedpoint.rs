//! Minimal safe wrapper around z3-sys fixedpoint (Spacer/IC3) API.

use z3::Context;

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
        let ctx = Context::thread_local().get_z3_context();
        let fp = unsafe { z3_sys::Z3_mk_fixedpoint(ctx) }.unwrap();
        unsafe { z3_sys::Z3_fixedpoint_inc_ref(ctx, fp) };

        // Set engine to spacer (IC3)
        let params = unsafe { z3_sys::Z3_mk_params(ctx) }.unwrap();
        unsafe { z3_sys::Z3_params_inc_ref(ctx, params) };
        let key =
            unsafe { z3_sys::Z3_mk_string_symbol(ctx, c"engine".as_ptr()) }.unwrap();
        let val =
            unsafe { z3_sys::Z3_mk_string_symbol(ctx, c"spacer".as_ptr()) }.unwrap();
        unsafe { z3_sys::Z3_params_set_symbol(ctx, params, key, val) };
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
        let name = unsafe { z3_sys::Z3_mk_string_symbol(self.ctx, c"rule".as_ptr()) }
            .unwrap();
        unsafe { z3_sys::Z3_fixedpoint_add_rule(self.ctx, self.fp, rule, name) };
    }

    /// Query whether the given relation is reachable. Returns Z3_lbool.
    pub fn query(&self, query: z3_sys::Z3_ast) -> z3_sys::Z3_lbool {
        unsafe { z3_sys::Z3_fixedpoint_query(self.ctx, self.fp, query) }
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

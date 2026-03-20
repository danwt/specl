//! Static analysis of compiled specs for profiling and recommendations.

use crate::CompiledSpec;
use specl_types::Type;
use std::fmt;

/// Sentinel: values at or above this are treated as "effectively unbounded".
/// This avoids nonsensical estimates when saturating_mul produces u128::MAX.
const SATURATED_THRESHOLD: u128 = u128::MAX / 2;

/// Profile of a compiled spec for strategy selection and user guidance.
#[derive(Debug)]
pub struct SpecProfile {
    pub num_vars: usize,
    pub num_actions: usize,
    pub num_invariants: usize,
    /// Upper bound on state space size. None if unbounded types present.
    pub state_space_bound: Option<u128>,
    /// Per-variable: (name, type string, domain size). None domain = unbounded.
    pub var_domain_sizes: Vec<(String, String, Option<u128>)>,
    /// Per-variable nesting depth (name, depth). Only includes depth >= 2.
    pub var_nesting_depths: Vec<(String, usize)>,
    /// Per-action: (name, parameter combination count). None if unbounded.
    pub action_param_counts: Vec<(String, Option<u128>)>,
    /// Fraction of action pairs that are template-independent (0.0-1.0).
    pub independence_ratio: f64,
    /// Whether any symmetry groups were detected.
    pub has_symmetry: bool,
    /// Domain sizes of detected symmetry groups.
    pub symmetry_domain_sizes: Vec<usize>,
    /// Whether any refinable pairs exist (instance-level POR applicable).
    pub has_refinable_pairs: bool,
    /// Recommended storage mode string, if any.
    pub storage_recommendation: Option<String>,
    pub warnings: Vec<Warning>,
    pub recommendations: Vec<Recommendation>,
}

#[derive(Debug)]
pub enum Warning {
    UnboundedType { var: String, ty: String },
    LargeParamSpace { action: String, combos: u128 },
    ExponentialVar { var: String, reason: String },
}

#[derive(Debug)]
pub enum Recommendation {
    EnablePor {
        independence_pct: u32,
    },
    EnableSymmetry {
        domain_size: usize,
        reduction_factor: u64,
    },
    EnableFast {
        estimated_states: u128,
    },
    UseSymbolic {
        reason: String,
    },
}

impl fmt::Display for Warning {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Warning::UnboundedType { var, ty } => {
                write!(f, "Variable '{}' has unbounded type {}", var, ty)
            }
            Warning::LargeParamSpace { action, combos } => {
                write!(
                    f,
                    "Action '{}' has {} parameter combinations",
                    action,
                    format_number(*combos)
                )
            }
            Warning::ExponentialVar { var, reason } => {
                write!(f, "Variable '{}': {}", var, reason)
            }
        }
    }
}

impl Warning {
    pub fn fix_hint(&self) -> &'static str {
        match self {
            Warning::UnboundedType { .. } => {
                "use a bounded range, e.g. change 'var x: Int' to 'var x: 0..N' with a const N"
            }
            Warning::LargeParamSpace { .. } => {
                "add 'require' guards to prune invalid combinations, or reduce parameter ranges"
            }
            Warning::ExponentialVar { .. } => {
                "reduce the range of the variable or its components, or use a simpler encoding"
            }
        }
    }
}

impl fmt::Display for Recommendation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Recommendation::EnablePor { independence_pct } => {
                write!(
                    f,
                    "--por: {}% of action pairs are independent",
                    independence_pct
                )
            }
            Recommendation::EnableSymmetry {
                domain_size,
                reduction_factor,
            } => {
                write!(
                    f,
                    "--symmetry: symmetric domain of size {} detected (up to {}x reduction)",
                    domain_size, reduction_factor
                )
            }
            Recommendation::EnableFast { estimated_states } => {
                write!(
                    f,
                    "--fast: estimated {} states — fingerprint-only uses 10x less memory",
                    format_number(*estimated_states)
                )
            }
            Recommendation::UseSymbolic { reason } => {
                write!(f, "--bmc: {}", reason)
            }
        }
    }
}

/// Analyze a compiled spec and produce a profile with warnings and recommendations.
pub fn analyze(spec: &CompiledSpec) -> SpecProfile {
    let num_vars = spec.vars.len();
    let num_actions = spec.actions.len();
    let num_invariants = spec.invariants.len();

    // Compute per-variable domain sizes
    let mut state_space_bound: Option<u128> = Some(1);
    let mut warnings = Vec::new();
    let mut var_domain_sizes = Vec::new();

    for var in &spec.vars {
        let domain_size = type_domain_size(&var.ty);
        var_domain_sizes.push((var.name.clone(), format!("{}", var.ty), domain_size));
        match domain_size {
            Some(size) => {
                if let Some(ref mut bound) = state_space_bound {
                    *bound = bound.saturating_mul(size);
                }
                if size > 1_000_000 {
                    warnings.push(Warning::ExponentialVar {
                        var: var.name.clone(),
                        reason: format!(
                            "domain size {} — consider simpler encoding",
                            format_number(size)
                        ),
                    });
                }
            }
            None => {
                state_space_bound = None;
                warnings.push(Warning::UnboundedType {
                    var: var.name.clone(),
                    ty: format!("{}", var.ty),
                });
            }
        }
    }

    // Treat saturated values as effectively unbounded
    if let Some(bound) = state_space_bound {
        if bound >= SATURATED_THRESHOLD {
            state_space_bound = None;
        }
    }

    // Per-action parameter combination counts
    let action_param_counts: Vec<(String, Option<u128>)> = spec
        .actions
        .iter()
        .map(|action| {
            let mut combos: Option<u128> = Some(1);
            for (_, ty) in &action.params {
                match type_domain_size(ty) {
                    Some(size) => {
                        if let Some(ref mut c) = combos {
                            *c = c.saturating_mul(size);
                        }
                    }
                    None => combos = None,
                }
            }
            (action.name.clone(), combos)
        })
        .collect();

    for (name, combos) in &action_param_counts {
        if let Some(c) = combos {
            if *c > 10_000 {
                warnings.push(Warning::LargeParamSpace {
                    action: name.clone(),
                    combos: *c,
                });
            }
        }
    }

    // Independence ratio
    let n = spec.independent.n();
    let independence_ratio = if n > 1 {
        let total_pairs = n * (n - 1);
        let mut independent_pairs = 0usize;
        for i in 0..n {
            for j in 0..n {
                if i != j && spec.independent.get(i, j) {
                    independent_pairs += 1;
                }
            }
        }
        independent_pairs as f64 / total_pairs as f64
    } else {
        0.0
    };

    // Symmetry
    let has_symmetry = !spec.symmetry_groups.is_empty();
    let symmetry_domain_sizes: Vec<usize> =
        spec.symmetry_groups.iter().map(|g| g.domain_size).collect();

    // Refinable pairs
    let has_refinable_pairs = spec.refinable_pairs.any();

    // Recommendations
    let mut recommendations = Vec::new();

    let independence_pct = (independence_ratio * 100.0) as u32;
    if independence_pct >= 20 {
        recommendations.push(Recommendation::EnablePor { independence_pct });
    }

    for &domain_size in &symmetry_domain_sizes {
        let reduction_factor = factorial(domain_size as u64);
        recommendations.push(Recommendation::EnableSymmetry {
            domain_size,
            reduction_factor,
        });
    }

    if let Some(bound) = state_space_bound {
        if bound > 10_000_000 {
            recommendations.push(Recommendation::EnableFast {
                estimated_states: bound,
            });
        }
    } else {
        recommendations.push(Recommendation::UseSymbolic {
            reason: "spec has unbounded types — symbolic checking can handle infinite domains"
                .to_string(),
        });
    }

    // Nesting depth analysis
    let var_nesting_depths: Vec<(String, usize)> = spec
        .vars
        .iter()
        .filter_map(|var| {
            let depth = type_nesting_depth(&var.ty);
            if depth >= 2 {
                Some((var.name.clone(), depth))
            } else {
                None
            }
        })
        .collect();

    for (name, depth) in &var_nesting_depths {
        if *depth >= 3 {
            warnings.push(Warning::ExponentialVar {
                var: name.clone(),
                reason: format!(
                    "nesting depth {} — deeply nested dicts cause exponential state explosion",
                    depth
                ),
            });
        }
    }

    // Storage mode recommendation (only --collapse; --fast is covered by EnableFast)
    let storage_recommendation = match state_space_bound {
        Some(b) if b > 5_000_000 && b <= 50_000_000 => Some(format!(
            "--collapse: estimated {} states — compressed storage saves ~3x memory while keeping traces",
            format_number(b)
        )),
        _ => None,
    };

    SpecProfile {
        num_vars,
        num_actions,
        num_invariants,
        state_space_bound,
        var_domain_sizes,
        var_nesting_depths,
        action_param_counts,
        independence_ratio,
        has_symmetry,
        symmetry_domain_sizes,
        has_refinable_pairs,
        storage_recommendation,
        warnings,
        recommendations,
    }
}

/// Compute the domain size for a type. Returns None for unbounded types.
fn type_domain_size(ty: &Type) -> Option<u128> {
    match ty {
        Type::Bool => Some(2),
        Type::Range(lo, hi) => {
            if hi >= lo {
                // Use i128 arithmetic to avoid i64 overflow for extreme ranges
                // (e.g., Range(i64::MIN, i64::MAX) has 2^64 values)
                Some((*hi as i128 - *lo as i128 + 1) as u128)
            } else {
                Some(0)
            }
        }
        Type::Nat | Type::Int | Type::String => None,
        Type::Set(elem) => {
            let elem_size = type_domain_size(elem)?;
            if elem_size > 30 {
                return Some(u128::MAX); // saturate
            }
            Some(1u128 << elem_size)
        }
        Type::Fn(key, val) => {
            let key_size = type_domain_size(key)?;
            let val_size = type_domain_size(val)?;
            // val_size ^ key_size
            if key_size > 20 || val_size > 100 {
                return Some(u128::MAX);
            }
            Some(val_size.saturating_pow(key_size as u32))
        }
        Type::Seq(elem) => {
            let elem_size = type_domain_size(elem)?;
            // Default max length 4: sum of elem_size^k for k=0..4
            let mut total: u128 = 0;
            for k in 0..=4 {
                total = total.saturating_add(elem_size.saturating_pow(k));
            }
            Some(total)
        }
        Type::Option(inner) => {
            let inner_size = type_domain_size(inner)?;
            Some(inner_size + 1)
        }
        _ => None,
    }
}

/// Compute dict nesting depth. Dict[K, Dict[K2, V]] = 2, Dict[K, V] = 1, non-dict = 0.
fn type_nesting_depth(ty: &Type) -> usize {
    match ty {
        Type::Fn(_, val) => 1 + type_nesting_depth(val),
        _ => 0,
    }
}

fn factorial(n: u64) -> u64 {
    (1..=n).fold(1u64, |acc, x| acc.saturating_mul(x))
}

fn format_number(n: u128) -> String {
    if n >= SATURATED_THRESHOLD {
        "huge (effectively unbounded)".to_string()
    } else if n >= 1_000_000_000_000 {
        format!("{:.1}T", n as f64 / 1e12)
    } else if n >= 1_000_000_000 {
        format!("{:.1}B", n as f64 / 1e9)
    } else if n >= 1_000_000 {
        format!("{:.1}M", n as f64 / 1e6)
    } else if n >= 1_000 {
        format!("{:.1}K", n as f64 / 1e3)
    } else {
        n.to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compile;
    use specl_syntax::parse;
    use specl_types::check_module;

    fn compile_spec(source: &str) -> CompiledSpec {
        let module = parse(source).unwrap();
        check_module(&module).unwrap();
        compile(&module).unwrap()
    }

    #[test]
    fn test_simple_counter_profile() {
        let spec = compile_spec(
            "module Test\nconst MAX: Int\nvar x: 0..10\ninit { x = 0 }\naction Inc() {\nrequire x < MAX\nx = x + 1\n}\ninvariant Safe { x >= 0 }"
        );
        let profile = analyze(&spec);
        assert_eq!(profile.num_vars, 1);
        assert_eq!(profile.num_actions, 1);
        assert_eq!(profile.state_space_bound, Some(11)); // 0..10 = 11 values
        assert!(profile.warnings.is_empty());
    }

    #[test]
    fn test_transfer_independence() {
        let spec = compile_spec(
            "module Test\nconst N: Int\nvar balance: Dict[0..2, 0..10]\ninit { balance = {p: 5 for p in 0..2} }\naction Transfer(from: 0..2, to: 0..2, amt: 1..3) {\n  require from != to\n  require balance[from] >= amt\n  balance = balance | { from: balance[from] - amt, to: balance[to] + amt }\n}\ninvariant Pos { all p in 0..2: balance[p] >= 0 }"
        );
        let profile = analyze(&spec);
        assert_eq!(profile.num_actions, 1);
        // Single action — independence ratio is 0 (only 1 action, no pairs)
        assert_eq!(profile.independence_ratio, 0.0);
        // Dict[0..2, 0..10] = 11^3 = 1331
        assert_eq!(profile.state_space_bound, Some(1331));
        assert!(profile.has_refinable_pairs);
    }

    #[test]
    fn test_unbounded_warning() {
        let spec = compile_spec(
            "module Test\nvar x: Nat\ninit { x = 0 }\naction Inc() { x = x + 1 }\ninvariant Safe { x >= 0 }"
        );
        let profile = analyze(&spec);
        assert!(profile.state_space_bound.is_none());
        assert!(profile
            .warnings
            .iter()
            .any(|w| matches!(w, Warning::UnboundedType { .. })));
        assert!(profile
            .recommendations
            .iter()
            .any(|r| matches!(r, Recommendation::UseSymbolic { .. })));
    }

    #[test]
    fn test_symmetry_recommendation() {
        let spec = compile_spec(
            "module Test\nconst N: Int\nvar state: Dict[0..3, 0..1]\ninit { state = {p: 0 for p in 0..3} }\naction Act(i: 0..3) { state = state | {i: 1} }\ninvariant Safe { true }"
        );
        let profile = analyze(&spec);
        assert!(profile.has_symmetry);
        assert!(!profile.symmetry_domain_sizes.is_empty());
        assert!(profile
            .recommendations
            .iter()
            .any(|r| matches!(r, Recommendation::EnableSymmetry { .. })));
    }

    #[test]
    fn test_type_domain_size_bool() {
        assert_eq!(type_domain_size(&Type::Bool), Some(2));
    }

    #[test]
    fn test_type_domain_size_range_basic() {
        assert_eq!(type_domain_size(&Type::Range(0, 10)), Some(11));
        assert_eq!(type_domain_size(&Type::Range(-5, 5)), Some(11));
        assert_eq!(type_domain_size(&Type::Range(0, 0)), Some(1));
        assert_eq!(type_domain_size(&Type::Range(5, 3)), Some(0));
    }

    #[test]
    fn test_type_domain_size_range_extreme() {
        // Previously this would overflow i64 subtraction
        let size = type_domain_size(&Type::Range(i64::MIN, i64::MAX));
        assert_eq!(size, Some(1u128 << 64));
    }

    #[test]
    fn test_type_domain_size_set() {
        // Set[Bool] = 2^2 = 4 subsets
        assert_eq!(type_domain_size(&Type::Set(Box::new(Type::Bool))), Some(4));
        // Set[0..2] = 2^3 = 8
        assert_eq!(
            type_domain_size(&Type::Set(Box::new(Type::Range(0, 2)))),
            Some(8)
        );
    }

    #[test]
    fn test_type_domain_size_fn() {
        // Dict[Bool, Bool] = 2^2 = 4
        assert_eq!(
            type_domain_size(&Type::Fn(Box::new(Type::Bool), Box::new(Type::Bool))),
            Some(4)
        );
        // Dict[0..2, Bool] = 2^3 = 8
        assert_eq!(
            type_domain_size(&Type::Fn(Box::new(Type::Range(0, 2)), Box::new(Type::Bool))),
            Some(8)
        );
    }

    #[test]
    fn test_type_domain_size_option() {
        // Option[Bool] = 2 + 1 = 3
        assert_eq!(
            type_domain_size(&Type::Option(Box::new(Type::Bool))),
            Some(3)
        );
    }

    #[test]
    fn test_type_domain_size_seq() {
        // Seq[Bool] with default max length 4: sum(2^k for k=0..4) = 1+2+4+8+16 = 31
        assert_eq!(type_domain_size(&Type::Seq(Box::new(Type::Bool))), Some(31));
    }

    #[test]
    fn test_type_domain_size_unbounded() {
        assert_eq!(type_domain_size(&Type::Nat), None);
        assert_eq!(type_domain_size(&Type::Int), None);
        assert_eq!(type_domain_size(&Type::String), None);
    }

    #[test]
    fn test_type_domain_size_large_set_saturates() {
        // Set[0..100] has elem_size=101 > 30, should saturate to u128::MAX
        let size = type_domain_size(&Type::Set(Box::new(Type::Range(0, 100))));
        assert_eq!(size, Some(u128::MAX));
    }

    #[test]
    fn test_saturated_state_space_becomes_none() {
        // A spec with a very large Set type should have state_space_bound = None
        // because the saturated value exceeds SATURATED_THRESHOLD
        let spec = compile_spec(
            "module Test\nvar x: Set[0..100]\ninit { x = {} }\naction Add() { x = x }\ninvariant Safe { true }"
        );
        let profile = analyze(&spec);
        assert!(
            profile.state_space_bound.is_none(),
            "saturated state space bound should be treated as None"
        );
    }

    #[test]
    fn test_format_number_basic() {
        assert_eq!(format_number(42), "42");
        assert_eq!(format_number(1_500), "1.5K");
        assert_eq!(format_number(2_500_000), "2.5M");
        assert_eq!(format_number(3_000_000_000), "3.0B");
        assert_eq!(format_number(5_000_000_000_000), "5.0T");
    }

    #[test]
    fn test_format_number_saturated() {
        assert_eq!(format_number(u128::MAX), "huge (effectively unbounded)");
    }
}

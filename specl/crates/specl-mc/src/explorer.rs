//! BFS state space explorer for model checking.

use crate::direct_eval::{
    apply_action_direct, apply_effects_bytecode, extract_effect_assignments,
    generate_initial_states_direct,
};
use crate::state::{hash_var, Fingerprint, State};
use crate::store::StateStore;
use memory_stats::memory_stats;
use rayon::prelude::*;
use smallvec::SmallVec;
use specl_eval::bytecode::{compile_expr, vm_eval_bool, Bytecode};
use specl_eval::{eval, EvalContext, EvalError, Value};
use specl_ir::{BinOp, CompiledAction, CompiledExpr, CompiledSpec, KeySource, UnaryOp};
use specl_syntax::{ExprKind, TypeExpr};
use std::collections::BinaryHeap;
use std::collections::VecDeque;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};
use thiserror::Error;
use tracing::{debug, error, info, trace};

/// Returns current process memory usage in MB, or None if unavailable.
fn current_memory_mb() -> Option<usize> {
    memory_stats().map(|stats| stats.physical_mem / (1024 * 1024))
}

/// Model checking error.
#[derive(Debug, Error)]
pub enum CheckError {
    #[error("evaluation error: {0}")]
    Eval(#[from] EvalError),

    #[error("invariant '{name}' violated")]
    InvariantViolation { name: String, state: State },

    #[error("deadlock: no enabled actions")]
    Deadlock { state: State },

    #[error("no initial states satisfy init predicate")]
    NoInitialStates,

    #[error("constant '{name}' not provided")]
    MissingConstant { name: String },
}

pub type CheckResult<T> = Result<T, CheckError>;

/// Result of model checking.
#[derive(Debug)]
pub enum CheckOutcome {
    /// All states explored, no errors found.
    Ok {
        states_explored: usize,
        max_depth: usize,
    },
    /// Invariant violation found.
    InvariantViolation {
        invariant: String,
        trace: Vec<(State, Option<String>)>,
    },
    /// Deadlock found.
    Deadlock { trace: Vec<(State, Option<String>)> },
    /// Exploration stopped due to state limit.
    StateLimitReached {
        states_explored: usize,
        max_depth: usize,
    },
    /// Exploration stopped due to memory limit.
    MemoryLimitReached {
        states_explored: usize,
        max_depth: usize,
        memory_mb: usize,
    },
    /// Exploration stopped due to time limit.
    TimeLimitReached {
        states_explored: usize,
        max_depth: usize,
    },
}

/// Result of simulation.
#[derive(Debug)]
pub enum SimulateOutcome {
    /// Simulation completed without violations.
    Ok {
        steps: usize,
        trace: Vec<(State, Option<String>)>,
        var_names: Vec<String>,
    },
    /// Invariant violation found during simulation.
    InvariantViolation {
        invariant: String,
        trace: Vec<(State, Option<String>)>,
        var_names: Vec<String>,
    },
    /// Deadlock (no enabled actions).
    Deadlock {
        trace: Vec<(State, Option<String>)>,
        var_names: Vec<String>,
    },
}

/// BFS queue entry: (fingerprint, state, depth, change_mask, sleep_set).
/// sleep_set is a bitmask of action indices to skip (sleep set POR enhancement).
type QueueEntry = (Fingerprint, State, usize, u64, u64);

/// Result from parallel state processing.
enum ParallelResult {
    /// State was depth-limited, no further exploration.
    DepthLimited,
    /// Invariant violation found.
    InvariantViolation { fp: Fingerprint, invariant: String },
    /// Deadlock found.
    Deadlock { fp: Fingerprint },
    /// New states inserted into store by worker.
    NewStates {
        new_entries: Vec<QueueEntry>,
        max_depth: usize,
    },
}

/// Result of instance-level ample set computation.
enum AmpleResult {
    /// Fall back to template-level POR (standard path).
    Templates,
    /// Instance-level reduction: list of (action_idx, params) pairs.
    Instances(Vec<(usize, Vec<Value>)>),
}

/// Extract i64 parameter values from Value slice for trace storage.
fn params_to_i64s(params: &[Value]) -> Vec<i64> {
    params
        .iter()
        .map(|v| {
            if let Some(n) = v.as_int() {
                n
            } else if let Some(b) = v.as_bool() {
                if b { 1 } else { 0 }
            } else {
                0
            }
        })
        .collect()
}

/// Lock-free progress counters shared between the explorer and the CLI spinner.
pub struct ProgressCounters {
    pub states: AtomicUsize,
    pub depth: AtomicUsize,
    pub queue_len: AtomicUsize,
    /// States popped from queue and fully evaluated (always increasing, even when no new states found).
    pub checked: AtomicUsize,
}

impl Default for ProgressCounters {
    fn default() -> Self {
        Self::new()
    }
}

impl ProgressCounters {
    pub fn new() -> Self {
        Self {
            states: AtomicUsize::new(0),
            depth: AtomicUsize::new(0),
            queue_len: AtomicUsize::new(0),
            checked: AtomicUsize::new(0),
        }
    }
}

/// Configuration for the model checker.
pub struct CheckConfig {
    /// Whether to check for deadlocks.
    pub check_deadlock: bool,
    /// Maximum number of states to explore (0 = unlimited).
    pub max_states: usize,
    /// Maximum depth to explore (0 = unlimited).
    pub max_depth: usize,
    /// Maximum memory usage in MB (0 = unlimited).
    pub memory_limit_mb: usize,
    /// Whether to use parallel exploration.
    pub parallel: bool,
    /// Number of threads for parallel exploration (0 = use all available).
    pub num_threads: usize,
    /// Whether to use partial order reduction.
    pub use_por: bool,
    /// Whether to use symmetry reduction.
    pub use_symmetry: bool,
    /// Fast check mode: minimal memory, re-explore for traces on violation.
    /// When enabled, only stores fingerprints during exploration. If a violation
    /// is found, re-explores with full tracking to reconstruct the trace.
    /// Trade-off: Uses ~10x less memory but violations take 2x time to report.
    pub fast_check: bool,
    /// Shared progress counters: the explorer writes states/depth/queue_len atomically,
    /// and the CLI reads them on its own timer. Never blocks the explorer.
    pub progress: Option<Arc<ProgressCounters>>,
    /// If set, shuffle action exploration order using this seed (for swarm verification).
    pub action_shuffle_seed: Option<u64>,
    /// Enable profiling: collect per-action firing counts and phase timing.
    pub profile: bool,
    /// Use bloom filter for state storage (fixed memory, probabilistic dedup).
    pub bloom: bool,
    /// Bloom filter size as log2(bits). Default 30 = 128 MiB.
    pub bloom_bits: u32,
    /// Use directed model checking (priority BFS with heuristic distance to violation).
    pub directed: bool,
    /// Maximum time in seconds (0 = unlimited).
    pub max_time_secs: u64,
    /// Only check these invariants (empty = check all).
    pub check_only_invariants: Vec<String>,
    /// Use collapse compression: per-variable interning for reduced memory with traces.
    pub collapse: bool,
}

impl Default for CheckConfig {
    fn default() -> Self {
        Self {
            check_deadlock: true,
            max_states: 0,
            max_depth: 0,
            memory_limit_mb: 0,
            parallel: true,
            num_threads: 0,
            use_por: false,
            use_symmetry: false,
            fast_check: false,
            progress: None,
            action_shuffle_seed: None,
            profile: false,
            bloom: false,
            bloom_bits: 30,
            directed: false,
            max_time_secs: 0,
            check_only_invariants: Vec::new(),
            collapse: false,
        }
    }
}

impl Clone for CheckConfig {
    fn clone(&self) -> Self {
        Self {
            check_deadlock: self.check_deadlock,
            max_states: self.max_states,
            max_depth: self.max_depth,
            memory_limit_mb: self.memory_limit_mb,
            parallel: self.parallel,
            num_threads: self.num_threads,
            use_por: self.use_por,
            use_symmetry: self.use_symmetry,
            fast_check: self.fast_check,
            progress: self.progress.clone(),
            action_shuffle_seed: self.action_shuffle_seed,
            profile: self.profile,
            bloom: self.bloom,
            bloom_bits: self.bloom_bits,
            directed: self.directed,
            max_time_secs: self.max_time_secs,
            check_only_invariants: self.check_only_invariants.clone(),
            collapse: self.collapse,
        }
    }
}

impl std::fmt::Debug for CheckConfig {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CheckConfig")
            .field("check_deadlock", &self.check_deadlock)
            .field("max_states", &self.max_states)
            .field("max_depth", &self.max_depth)
            .field("memory_limit_mb", &self.memory_limit_mb)
            .field("parallel", &self.parallel)
            .field("num_threads", &self.num_threads)
            .field("use_por", &self.use_por)
            .field("use_symmetry", &self.use_symmetry)
            .field("fast_check", &self.fast_check)
            .field("progress", &self.progress.as_ref().map(|_| "..."))
            .field("action_shuffle_seed", &self.action_shuffle_seed)
            .field("profile", &self.profile)
            .field("bloom", &self.bloom)
            .field("bloom_bits", &self.bloom_bits)
            .field("directed", &self.directed)
            .field("max_time_secs", &self.max_time_secs)
            .field("check_only_invariants", &self.check_only_invariants)
            .field("collapse", &self.collapse)
            .finish()
    }
}

/// Profiling data collected during model checking.
#[derive(Debug, Clone)]
pub struct ProfileData {
    /// Per-action firing counts (number of successor states produced).
    pub action_fire_counts: Vec<usize>,
    /// Action names for display.
    pub action_names: Vec<String>,
    /// Time spent checking invariants.
    pub time_invariants: Duration,
    /// Time spent generating successors.
    pub time_successors: Duration,
    /// Time spent on store operations (insert, canonicalize, queue).
    pub time_store: Duration,
}

/// Model checker explorer.
pub struct Explorer {
    /// Compiled specification.
    spec: CompiledSpec,
    /// Constant values.
    consts: Vec<Value>,
    /// State store.
    store: StateStore,
    /// Configuration.
    config: CheckConfig,
    /// Precomputed effect assignments per action (None = needs enumeration).
    cached_effects: Vec<Option<CachedEffect>>,
    /// Cached parameter domains per action.
    cached_param_domains: Vec<Vec<Vec<Value>>>,
    /// Actions relevant to invariants (COI reduction). None = all actions relevant.
    relevant_actions: Option<Vec<usize>>,
    /// Compiled bytecode for action guards.
    compiled_guards: Vec<Bytecode>,
    /// Compiled bytecode for invariant bodies.
    compiled_invariants: Vec<Bytecode>,
    /// Bitmask of variables each invariant depends on.
    inv_dep_masks: Vec<u64>,
    /// Bitmask of variables each action writes.
    action_write_masks: Vec<u64>,
    /// Guard indexing for early parameter pruning (None = no indexing benefit).
    guard_indices: Vec<Option<GuardIndex>>,
    /// Action names for trace reconstruction (avoids formatting per-successor).
    action_names: Vec<String>,
    /// Default action exploration order (shuffled for swarm, sequential otherwise).
    default_action_order: Vec<usize>,
    /// For each action, for each param: Some(var_idx) if domain comes from state variable.
    /// Detected from `require param in var` guard patterns.
    state_dep_domains: Vec<Vec<Option<usize>>>,
    /// Precomputed bitmask: independent_masks[a] has bit b set iff action a is independent of b.
    /// Used for sleep set propagation.
    independent_masks: Vec<u64>,
    /// External stop flag (for swarm verification cancellation).
    stop_flag: Option<Arc<AtomicBool>>,
    /// For each action, for each param: Some(group_idx) if the param's domain size matches
    /// a symmetry group. Used for orbit representative filtering.
    sym_param_groups: Vec<Vec<Option<usize>>>,
    /// Whether any refinable pair exists (instance-level POR possible).
    has_refinable_pairs: bool,
    /// Per-action: participates in at least one refinable pair.
    action_has_refinable: Vec<bool>,
    /// Profile data accumulated during checking (only when config.profile is true).
    profile_data: Option<ProfileData>,
    /// Deadline for time-limited checking (None = unlimited).
    deadline: Option<Instant>,
    /// Which invariants are active (true = check, false = skip). Empty config = all active.
    active_invariants: Vec<bool>,
}

/// Precomputed effect assignments for an action.
struct CachedEffect {
    /// Pre-compiled bytecode for each assignment's RHS expression.
    compiled_assignments: Vec<(usize, Bytecode)>,
    /// Whether re-verification is needed (true if effect has current-state constraints).
    needs_reverify: bool,
}

/// Precomputed guard indexing for early parameter pruning.
/// Reorders parameter binding and checks guard conjuncts incrementally.
struct GuardIndex {
    /// binding_order[i] = original param index to bind at position i.
    binding_order: Vec<usize>,
    /// Prefix guard bytecode at each binding level.
    /// prefix_guards[i] checks conjuncts that become fully evaluable after binding position i.
    prefix_guards: Vec<Option<Bytecode>>,
    /// Pre-guard: conjuncts with no param refs, checked once before enumeration.
    pre_guard: Option<Bytecode>,
    /// If true, all guard conjuncts are covered by prefix guards; skip final full guard check.
    all_covered: bool,
}

/// Size of the per-action operation cache (must be power of 2).
const OP_CACHE_SIZE: usize = 1 << 14; // 16K entries

/// Sentinel value indicating guard failed or no transition.
const OP_NO_SUCCESSOR: u64 = u64::MAX;

/// Per-action direct-mapped operation cache with adaptive disabling.
/// Caches the write_new_hash (XOR of hash_var for changed variables in the successor)
/// keyed on (params, read_variables). Uses XOR-decomposable fingerprinting to
/// reconstruct the full successor fingerprint from any parent state:
///   predicted_fp = parent_fp ^ write_old_hash ^ write_new_hash
///
/// After a warmup period, disables itself if hit rate is too low (overhead > benefit).
struct OpCache {
    keys: Vec<u64>,
    write_new_hashes: Vec<u64>,
    mask: usize,
    hits: u32,
    probes: u32,
    disabled: bool,
}

/// Number of probes before evaluating whether to disable the cache.
const OP_CACHE_WARMUP: u32 = 2048;
/// Minimum hit rate (hits/probes) to keep cache enabled.
const OP_CACHE_MIN_HIT_RATE: u32 = 50; // 50/2048 ~= 2.4%

impl OpCache {
    fn new() -> Self {
        Self {
            keys: vec![0; OP_CACHE_SIZE],
            write_new_hashes: vec![0; OP_CACHE_SIZE],
            mask: OP_CACHE_SIZE - 1,
            hits: 0,
            probes: 0,
            disabled: false,
        }
    }

    #[inline]
    fn probe(&mut self, key: u64) -> Option<u64> {
        if self.disabled {
            return None;
        }
        let slot = key as usize & self.mask;
        let k = unsafe { *self.keys.get_unchecked(slot) };
        if k == key {
            self.hits += 1;
            Some(unsafe { *self.write_new_hashes.get_unchecked(slot) })
        } else {
            self.probes += 1;
            if self.probes == OP_CACHE_WARMUP && self.hits < OP_CACHE_MIN_HIT_RATE {
                self.disabled = true;
            }
            None
        }
    }

    #[inline]
    fn is_enabled(&self) -> bool {
        !self.disabled
    }

    #[inline]
    fn store(&mut self, key: u64, write_new_hash: u64) {
        let slot = key as usize & self.mask;
        unsafe {
            *self.keys.get_unchecked_mut(slot) = key;
            *self.write_new_hashes.get_unchecked_mut(slot) = write_new_hash;
        }
    }
}

/// Compute a cache key from action parameters and precomputed read-vars hash.
/// read_xor is precomputed once per (state, action) via xor_hash_vars.
#[inline]
fn op_cache_key(params: &[Value], read_xor: u64) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = ahash::AHasher::default();
    read_xor.hash(&mut hasher);
    for p in params {
        p.hash(&mut hasher);
    }
    let key = hasher.finish();
    if key == 0 {
        1
    } else {
        key
    }
}

/// Compute XOR of hash_var for a subset of variables (used for cache delta).
#[inline]
fn xor_hash_vars(vars: &[Value], indices: &[usize]) -> u64 {
    indices
        .iter()
        .fold(0u64, |acc, &i| acc ^ hash_var(i, &vars[i]))
}

/// Decompose a guard expression into top-level AND-conjuncts.
fn decompose_conjuncts(expr: &CompiledExpr) -> Vec<&CompiledExpr> {
    match expr {
        CompiledExpr::Binary {
            op: BinOp::And,
            left,
            right,
        } => {
            let mut conjuncts = decompose_conjuncts(left);
            conjuncts.extend(decompose_conjuncts(right));
            conjuncts
        }
        _ => vec![expr],
    }
}

/// Collect all Param indices referenced in an expression.
fn collect_param_refs_in_expr(expr: &CompiledExpr) -> std::collections::HashSet<usize> {
    let mut params = std::collections::HashSet::new();
    collect_param_refs_recursive(expr, &mut params);
    params
}

fn collect_param_refs_recursive(
    expr: &CompiledExpr,
    params: &mut std::collections::HashSet<usize>,
) {
    match expr {
        CompiledExpr::Param(idx) => {
            params.insert(*idx);
        }
        CompiledExpr::Binary { left, right, .. } => {
            collect_param_refs_recursive(left, params);
            collect_param_refs_recursive(right, params);
        }
        CompiledExpr::Unary { operand, .. } => {
            collect_param_refs_recursive(operand, params);
        }
        CompiledExpr::Index { base, index } => {
            collect_param_refs_recursive(base, params);
            collect_param_refs_recursive(index, params);
        }
        CompiledExpr::FnUpdate { base, key, value } => {
            collect_param_refs_recursive(base, params);
            collect_param_refs_recursive(key, params);
            collect_param_refs_recursive(value, params);
        }
        CompiledExpr::FnLit { domain, body } => {
            collect_param_refs_recursive(domain, params);
            collect_param_refs_recursive(body, params);
        }
        CompiledExpr::SetComprehension {
            element,
            domain,
            filter,
        } => {
            collect_param_refs_recursive(element, params);
            collect_param_refs_recursive(domain, params);
            if let Some(f) = filter {
                collect_param_refs_recursive(f, params);
            }
        }
        CompiledExpr::Forall { domain, body } | CompiledExpr::Exists { domain, body } => {
            collect_param_refs_recursive(domain, params);
            collect_param_refs_recursive(body, params);
        }
        CompiledExpr::If {
            cond,
            then_branch,
            else_branch,
        } => {
            collect_param_refs_recursive(cond, params);
            collect_param_refs_recursive(then_branch, params);
            collect_param_refs_recursive(else_branch, params);
        }
        CompiledExpr::Let { value, body } => {
            collect_param_refs_recursive(value, params);
            collect_param_refs_recursive(body, params);
        }
        CompiledExpr::Len(e)
        | CompiledExpr::Keys(e)
        | CompiledExpr::Values(e)
        | CompiledExpr::Powerset(e)
        | CompiledExpr::BigUnion(e) => {
            collect_param_refs_recursive(e, params);
        }
        CompiledExpr::Choose { domain, predicate } => {
            collect_param_refs_recursive(domain, params);
            collect_param_refs_recursive(predicate, params);
        }
        CompiledExpr::Range { lo, hi } => {
            collect_param_refs_recursive(lo, params);
            collect_param_refs_recursive(hi, params);
        }
        CompiledExpr::Call { func, args } => {
            collect_param_refs_recursive(func, params);
            for a in args {
                collect_param_refs_recursive(a, params);
            }
        }
        CompiledExpr::SetLit(elems)
        | CompiledExpr::SeqLit(elems)
        | CompiledExpr::TupleLit(elems) => {
            for e in elems {
                collect_param_refs_recursive(e, params);
            }
        }
        CompiledExpr::Field { base, .. } => {
            collect_param_refs_recursive(base, params);
        }
        // Leaves with no param refs
        CompiledExpr::Bool(_)
        | CompiledExpr::Int(_)
        | CompiledExpr::String(_)
        | CompiledExpr::Const(_)
        | CompiledExpr::Var(_)
        | CompiledExpr::PrimedVar(_)
        | CompiledExpr::Local(_)
        | CompiledExpr::Unchanged(_)
        | CompiledExpr::Changes(_)
        | CompiledExpr::Enabled(_) => {}
        // Remaining complex expressions
        _ => {
            // Conservative: don't collect from unknown patterns.
            // This means some conjuncts may not be attributed to params,
            // which is safe (just less optimization).
        }
    }
}

/// Heuristic selectivity score for a guard conjunct.
/// Higher = more selective (filters out more parameter combinations).
fn score_conjunct_selectivity(expr: &CompiledExpr) -> f64 {
    match expr {
        // dict[p1][p2] == const or const == dict[p1][p2]
        CompiledExpr::Binary {
            op: BinOp::Eq,
            left,
            right,
        } => {
            if has_index_chain(left) || has_index_chain(right) {
                10.0
            } else {
                1.0
            }
        }
        // dict[p1][p2] != const
        CompiledExpr::Binary {
            op: BinOp::Ne,
            left,
            right,
        } => {
            if has_index_chain(left) || has_index_chain(right) {
                5.0
            } else {
                1.0
            }
        }
        // not expr (e.g., not preAcceptReplied[o][s][r])
        CompiledExpr::Unary {
            op: UnaryOp::Not,
            operand,
        } => {
            if has_index_chain(operand) {
                5.0
            } else {
                2.0
            }
        }
        // Comparison operators with dict lookups
        CompiledExpr::Binary {
            op: BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge,
            left,
            right,
        } => {
            if has_index_chain(left) || has_index_chain(right) {
                8.0
            } else {
                2.0
            }
        }
        _ => 2.0,
    }
}

/// Check if an expression contains a dict index chain (var[...][...]).
fn has_index_chain(expr: &CompiledExpr) -> bool {
    match expr {
        CompiledExpr::Index { base, .. } => {
            matches!(
                base.as_ref(),
                CompiledExpr::Var(_) | CompiledExpr::Index { .. }
            )
        }
        _ => false,
    }
}

/// Build a conjunction (AND) of multiple expressions.
fn build_conjunction(conjuncts: &[&CompiledExpr]) -> CompiledExpr {
    assert!(!conjuncts.is_empty());
    let mut result = conjuncts[0].clone();
    for conj in &conjuncts[1..] {
        result = CompiledExpr::Binary {
            op: BinOp::And,
            left: Box::new(result),
            right: Box::new((*conj).clone()),
        };
    }
    result
}

/// Compute guard indexing for an action.
/// Returns None if the action has no params or indexing provides no benefit.
fn compute_guard_index(guard: &CompiledExpr, num_params: usize) -> Option<GuardIndex> {
    if num_params == 0 {
        return None;
    }

    let conjuncts = decompose_conjuncts(guard);
    if conjuncts.len() <= 1 {
        return None;
    }

    // Collect param references for each conjunct
    let conjunct_params: Vec<std::collections::HashSet<usize>> = conjuncts
        .iter()
        .map(|c| collect_param_refs_in_expr(c))
        .collect();

    // Compute selectivity score for each parameter
    let mut param_scores = vec![0.0f64; num_params];
    for (conj_idx, params) in conjunct_params.iter().enumerate() {
        if params.is_empty() {
            continue;
        }
        let selectivity = score_conjunct_selectivity(conjuncts[conj_idx]);
        let share = selectivity / params.len() as f64;
        for &p in params {
            if p < num_params {
                param_scores[p] += share;
            }
        }
    }

    // Sort params by score descending to get binding order
    let mut binding_order: Vec<usize> = (0..num_params).collect();
    binding_order.sort_by(|&a, &b| {
        param_scores[b]
            .partial_cmp(&param_scores[a])
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    // Build pre-guard from conjuncts with no param refs
    let pre_guard_conjuncts: Vec<&CompiledExpr> = conjuncts
        .iter()
        .enumerate()
        .filter(|(i, _)| conjunct_params[*i].is_empty())
        .map(|(_, c)| *c)
        .collect();
    let pre_guard = if pre_guard_conjuncts.is_empty() {
        None
    } else {
        Some(compile_expr(&build_conjunction(&pre_guard_conjuncts)))
    };

    // Build prefix guards at each binding level
    let mut bound_params = std::collections::HashSet::new();
    let mut used_conjuncts = std::collections::HashSet::new();
    // Mark pre-guard conjuncts as used
    for (i, params) in conjunct_params.iter().enumerate() {
        if params.is_empty() {
            used_conjuncts.insert(i);
        }
    }

    let mut prefix_guards = Vec::new();
    for &orig_idx in &binding_order {
        bound_params.insert(orig_idx);

        // Find conjuncts that are now fully evaluable
        let new_conjuncts: Vec<usize> = conjunct_params
            .iter()
            .enumerate()
            .filter(|(i, params)| {
                !used_conjuncts.contains(i)
                    && !params.is_empty()
                    && params.iter().all(|p| bound_params.contains(p))
            })
            .map(|(i, _)| i)
            .collect();

        if new_conjuncts.is_empty() {
            prefix_guards.push(None);
        } else {
            let conjs: Vec<&CompiledExpr> = new_conjuncts.iter().map(|&i| conjuncts[i]).collect();
            let bc = compile_expr(&build_conjunction(&conjs));
            prefix_guards.push(Some(bc));
            for i in new_conjuncts {
                used_conjuncts.insert(i);
            }
        }
    }

    let all_covered = used_conjuncts.len() == conjuncts.len();

    // Check if we got any useful prefix guards before the last level
    let has_useful_prefix = prefix_guards
        .iter()
        .take(num_params.saturating_sub(1))
        .any(|pg| pg.is_some())
        || pre_guard.is_some();

    if !has_useful_prefix {
        return None;
    }

    debug!(
        binding_order = ?binding_order,
        prefix_count = prefix_guards.iter().filter(|p| p.is_some()).count(),
        all_covered,
        has_pre_guard = pre_guard.is_some(),
        "guard index computed"
    );

    Some(GuardIndex {
        binding_order,
        prefix_guards,
        pre_guard,
        all_covered,
    })
}

/// Detect `require param in var` patterns in guard conjuncts.
/// Returns a vec of length `num_params` where `Some(var_idx)` means the param's
/// domain should be extracted from `state.vars[var_idx]` at runtime.
fn detect_state_dep_domains(guard: &CompiledExpr, num_params: usize) -> Vec<Option<usize>> {
    let mut result = vec![None; num_params];
    if num_params == 0 {
        return result;
    }
    for conjunct in decompose_conjuncts(guard) {
        if let CompiledExpr::Binary {
            op: BinOp::In,
            left,
            right,
        } = conjunct
        {
            if let (CompiledExpr::Param(param_idx), CompiledExpr::Var(var_idx)) =
                (left.as_ref(), right.as_ref())
            {
                if *param_idx < num_params {
                    result[*param_idx] = Some(*var_idx);
                }
            }
        }
    }
    result
}

/// Enumerate parameter combinations with guard indexing for early pruning.
/// `params_buf` must be pre-allocated to `num_params` size.
fn enumerate_params_indexed<F>(
    domains: &[Vec<Value>],
    guard_index: &GuardIndex,
    guard_bc: &Bytecode,
    vars: &[Value],
    consts: &[Value],
    params_buf: &mut Vec<Value>,
    level: usize,
    callback: &mut F,
) where
    F: FnMut(&[Value]),
{
    if level >= domains.len() {
        // All params bound
        if !guard_index.all_covered {
            // Check full guard for any remaining conjuncts
            if !vm_eval_bool(guard_bc, vars, vars, consts, params_buf).unwrap_or(false) {
                return;
            }
        }
        callback(params_buf);
        return;
    }

    let orig_idx = guard_index.binding_order[level];
    for value in &domains[orig_idx] {
        params_buf[orig_idx] = value.clone();

        // Check prefix guard at this level
        if let Some(ref prefix_bc) = guard_index.prefix_guards[level] {
            if !vm_eval_bool(prefix_bc, vars, vars, consts, params_buf).unwrap_or(false) {
                continue;
            }
        }

        enumerate_params_indexed(
            domains,
            guard_index,
            guard_bc,
            vars,
            consts,
            params_buf,
            level + 1,
            callback,
        );
    }
}

impl Explorer {
    /// Create a new explorer.
    pub fn new(spec: CompiledSpec, consts: Vec<Value>, config: CheckConfig) -> Self {
        // Choose storage backend: bloom > collapse > fast_check > full tracking
        let store = if config.bloom {
            StateStore::with_bloom(config.bloom_bits, 3)
        } else if config.collapse {
            StateStore::with_collapse(spec.vars.len())
        } else {
            StateStore::with_tracking(!config.fast_check)
        };

        // Precompute effect assignments for each action
        let cached_effects = spec
            .actions
            .iter()
            .map(|action| {
                extract_effect_assignments(&action.effect).map(|e| {
                    let compiled_assignments = e
                        .assignments
                        .iter()
                        .map(|(idx, expr)| (*idx, compile_expr(expr)))
                        .collect();
                    CachedEffect {
                        compiled_assignments,
                        needs_reverify: e.needs_reverify,
                    }
                })
            })
            .collect();

        // COI reduction computed after active_invariants below

        // Compile guard bytecode for each action
        let compiled_guards: Vec<Bytecode> = spec
            .actions
            .iter()
            .map(|action| compile_expr(&action.guard))
            .collect();

        // Compile invariant bytecode
        let compiled_invariants: Vec<Bytecode> = spec
            .invariants
            .iter()
            .map(|inv| compile_expr(&inv.body))
            .collect();

        // Compute invariant dependency bitmasks
        let inv_dep_masks: Vec<u64> = spec
            .invariants
            .iter()
            .map(|inv| {
                let mut vars = std::collections::HashSet::new();
                Self::collect_var_refs(&inv.body, &mut vars);
                vars.iter().fold(
                    0u64,
                    |mask, &v| {
                        if v < 64 {
                            mask | (1u64 << v)
                        } else {
                            mask
                        }
                    },
                )
            })
            .collect();

        // Compute action write bitmasks
        let action_write_masks: Vec<u64> = spec
            .actions
            .iter()
            .map(|action| {
                action.changes.iter().fold(
                    0u64,
                    |mask, &v| {
                        if v < 64 {
                            mask | (1u64 << v)
                        } else {
                            mask
                        }
                    },
                )
            })
            .collect();

        // Compute guard indexing for early parameter pruning
        let guard_indices: Vec<Option<GuardIndex>> = spec
            .actions
            .iter()
            .map(|action| compute_guard_index(&action.guard, action.params.len()))
            .collect();

        // Detect state-dependent parameter domains (require param in var)
        let state_dep_domains: Vec<Vec<Option<usize>>> = spec
            .actions
            .iter()
            .map(|action| detect_state_dep_domains(&action.guard, action.params.len()))
            .collect();

        let dep_count = state_dep_domains
            .iter()
            .filter(|d| d.iter().any(|p| p.is_some()))
            .count();
        if dep_count > 0 {
            debug!(
                dep_count,
                total = spec.actions.len(),
                "state-dependent parameter domains detected"
            );
        }

        let indexed_count = guard_indices.iter().filter(|g| g.is_some()).count();
        if indexed_count > 0 {
            debug!(
                indexed_count,
                total = spec.actions.len(),
                "guard indexing enabled"
            );
        }

        // Precompute independence bitmasks for sleep set propagation
        let n_actions = spec.actions.len();
        let independent_masks: Vec<u64> = (0..n_actions)
            .map(|a| {
                let mut mask = 0u64;
                for b in 0..n_actions.min(64) {
                    if spec.independent[a][b] {
                        mask |= 1u64 << b;
                    }
                }
                mask
            })
            .collect();

        // Precompute instance-level POR flags from refinable_pairs
        let has_refinable_pairs = spec
            .refinable_pairs
            .iter()
            .any(|row| row.iter().any(|&v| v));
        let action_has_refinable: Vec<bool> = (0..n_actions)
            .map(|i| spec.refinable_pairs[i].iter().any(|&v| v))
            .collect();
        if has_refinable_pairs {
            let count = action_has_refinable.iter().filter(|&&v| v).count();
            debug!(
                count,
                total = n_actions,
                "instance-level POR: actions with refinable pairs"
            );
        }

        let deadline = if config.max_time_secs > 0 {
            Some(Instant::now() + Duration::from_secs(config.max_time_secs))
        } else {
            None
        };

        // Compute which invariants are active (empty check_only = all active)
        let active_invariants: Vec<bool> = if config.check_only_invariants.is_empty() {
            vec![true; spec.invariants.len()]
        } else {
            let inv_names: Vec<&str> = spec.invariants.iter().map(|inv| inv.name.as_str()).collect();
            for name in &config.check_only_invariants {
                if !inv_names.contains(&name.as_str()) {
                    error!(
                        name,
                        available = ?inv_names,
                        "unknown invariant in --check-only"
                    );
                }
            }
            spec.invariants
                .iter()
                .map(|inv| config.check_only_invariants.contains(&inv.name))
                .collect()
        };

        // Compute COI with active invariant filter for tighter reduction
        let relevant_actions = Self::compute_coi(&spec, &active_invariants);

        let mut explorer = Self {
            spec,
            consts,
            store,
            config,
            cached_effects,
            cached_param_domains: Vec::new(),
            relevant_actions,
            compiled_guards,
            compiled_invariants,
            inv_dep_masks,
            action_write_masks,
            guard_indices,
            action_names: Vec::new(),
            default_action_order: Vec::new(),
            stop_flag: None,
            state_dep_domains,
            independent_masks,
            sym_param_groups: Vec::new(),
            has_refinable_pairs,
            action_has_refinable,
            profile_data: None,
            deadline,
            active_invariants,
        };

        // Precompute action names for trace reconstruction
        explorer.action_names = explorer
            .spec
            .actions
            .iter()
            .map(|action| action.name.clone())
            .collect();

        // Build default action exploration order
        // Sort by guard cost (cheapest first) for early rejection, then shuffle for swarm
        let num_actions = explorer.spec.actions.len();
        explorer.default_action_order = (0..num_actions).collect();
        explorer
            .default_action_order
            .sort_by_key(|&i| explorer.spec.actions[i].guard_cost);
        if let Some(seed) = explorer.config.action_shuffle_seed {
            use rand::rngs::StdRng;
            use rand::seq::SliceRandom;
            use rand::SeedableRng;
            let mut rng = StdRng::seed_from_u64(seed);
            explorer.default_action_order.shuffle(&mut rng);
            info!(seed, order = ?explorer.default_action_order, "swarm: shuffled action order");
        }

        // Precompute parameter domains for each action
        // State-dependent params get empty placeholder (domain extracted from state at runtime)
        explorer.cached_param_domains = explorer
            .spec
            .actions
            .iter()
            .enumerate()
            .map(|(action_idx, action)| {
                let deps = &explorer.state_dep_domains[action_idx];
                action
                    .params
                    .iter()
                    .enumerate()
                    .map(|(i, (_, ty))| {
                        if deps[i].is_some() {
                            // State-dependent: placeholder, will be replaced at runtime
                            Vec::new()
                        } else if let Some(type_expr) = action.param_type_exprs.get(i) {
                            if let Some(domain) = explorer.resolve_type_expr_domain(type_expr) {
                                return domain;
                            }
                            explorer.type_domain(ty)
                        } else {
                            explorer.type_domain(ty)
                        }
                    })
                    .collect()
            })
            .collect();

        // Precompute symmetry param -> group mapping.
        // A parameter matches a group if its domain size equals the group's domain_size.
        // NOTE: if multiple groups have the same domain_size, the first match wins.
        // This is safe because symmetry groups are detected from Dict[0..N, T] domains,
        // and groups with the same N are merged into one group by detect_symmetry_groups.
        explorer.sym_param_groups = explorer
            .spec
            .actions
            .iter()
            .enumerate()
            .map(|(action_idx, _action)| {
                let domains = &explorer.cached_param_domains[action_idx];
                domains
                    .iter()
                    .map(|domain| {
                        let domain_size = domain.len();
                        explorer
                            .spec
                            .symmetry_groups
                            .iter()
                            .position(|g| g.domain_size == domain_size)
                    })
                    .collect()
            })
            .collect();

        // Warn if symmetry is enabled but spec may be asymmetric
        if explorer.config.use_symmetry && !explorer.spec.symmetry_groups.is_empty() {
            explorer.check_symmetry_soundness();
        }

        explorer
    }

    /// Best-effort check for asymmetric patterns in a spec with symmetry enabled.
    /// Returns warnings if literal integers index into symmetric variables,
    /// which suggests the spec treats some domain elements specially.
    fn check_symmetry_soundness(&self) -> Vec<String> {
        let warnings = Self::find_symmetry_warnings(&self.spec);
        for w in &warnings {
            eprintln!("Warning: {}", w);
        }
        warnings
    }

    /// Scan compiled spec for literal indices into symmetric variables
    /// and literal comparisons with symmetric parameters.
    /// Returns a list of human-readable warning strings.
    pub fn find_symmetry_warnings(spec: &CompiledSpec) -> Vec<String> {
        use specl_ir::CompiledExpr;
        use specl_types::Type;

        // Map var index -> domain size for symmetric variables
        let mut sym_var_domain: std::collections::HashMap<usize, usize> =
            std::collections::HashMap::new();
        // Set of domain sizes that are symmetric
        let mut sym_domain_sizes: std::collections::HashSet<usize> =
            std::collections::HashSet::new();
        for group in &spec.symmetry_groups {
            sym_domain_sizes.insert(group.domain_size);
            for &var_idx in &group.variables {
                sym_var_domain.insert(var_idx, group.domain_size);
            }
        }

        if sym_var_domain.is_empty() {
            return vec![];
        }

        /// Check for asymmetric patterns in a compiled expression.
        /// `sym_params` maps param index -> domain size for params whose range matches a symmetry group.
        fn has_asymmetric_literal(
            expr: &CompiledExpr,
            sym_var_domain: &std::collections::HashMap<usize, usize>,
            sym_params: &std::collections::HashMap<usize, usize>,
        ) -> Option<String> {
            match expr {
                // Pattern 1: symmetric_var[literal_int]
                CompiledExpr::Index { base, index } => {
                    if let CompiledExpr::Var(var_idx) = base.as_ref() {
                        if let Some(&domain_size) = sym_var_domain.get(var_idx) {
                            if let CompiledExpr::Int(k) = index.as_ref() {
                                if *k >= 0 && (*k as usize) < domain_size {
                                    return Some(format!(
                                        "literal index {} into symmetric var (var_idx={})",
                                        k, var_idx
                                    ));
                                }
                            }
                        }
                    }
                    has_asymmetric_literal(base, sym_var_domain, sym_params)
                        .or_else(|| has_asymmetric_literal(index, sym_var_domain, sym_params))
                }
                // Pattern 2: symmetric_param == literal or literal == symmetric_param
                CompiledExpr::Binary {
                    op: BinOp::Eq,
                    left,
                    right,
                } => {
                    let check_param_literal = |param_expr: &CompiledExpr,
                                               lit_expr: &CompiledExpr|
                     -> Option<String> {
                        if let CompiledExpr::Param(p) = param_expr {
                            if let Some(&domain_size) = sym_params.get(p) {
                                if let CompiledExpr::Int(k) = lit_expr {
                                    if *k >= 0 && (*k as usize) < domain_size {
                                        return Some(format!("literal {} compared with symmetric param (param_idx={})", k, p));
                                    }
                                }
                            }
                        }
                        None
                    };
                    check_param_literal(left, right)
                        .or_else(|| check_param_literal(right, left))
                        .or_else(|| has_asymmetric_literal(left, sym_var_domain, sym_params))
                        .or_else(|| has_asymmetric_literal(right, sym_var_domain, sym_params))
                }
                CompiledExpr::Binary { left, right, .. } => {
                    has_asymmetric_literal(left, sym_var_domain, sym_params)
                        .or_else(|| has_asymmetric_literal(right, sym_var_domain, sym_params))
                }
                CompiledExpr::Unary { operand, .. } => {
                    has_asymmetric_literal(operand, sym_var_domain, sym_params)
                }
                CompiledExpr::Forall { domain, body, .. }
                | CompiledExpr::Exists { domain, body, .. }
                | CompiledExpr::FnLit { domain, body } => {
                    has_asymmetric_literal(domain, sym_var_domain, sym_params)
                        .or_else(|| has_asymmetric_literal(body, sym_var_domain, sym_params))
                }
                CompiledExpr::SetComprehension {
                    domain,
                    filter,
                    element,
                    ..
                } => has_asymmetric_literal(domain, sym_var_domain, sym_params)
                    .or_else(|| {
                        filter
                            .as_ref()
                            .and_then(|f| has_asymmetric_literal(f, sym_var_domain, sym_params))
                    })
                    .or_else(|| has_asymmetric_literal(element, sym_var_domain, sym_params)),
                CompiledExpr::If {
                    cond,
                    then_branch,
                    else_branch,
                } => has_asymmetric_literal(cond, sym_var_domain, sym_params)
                    .or_else(|| has_asymmetric_literal(then_branch, sym_var_domain, sym_params))
                    .or_else(|| has_asymmetric_literal(else_branch, sym_var_domain, sym_params)),
                CompiledExpr::FnUpdate { base, key, value } => {
                    has_asymmetric_literal(base, sym_var_domain, sym_params)
                        .or_else(|| has_asymmetric_literal(key, sym_var_domain, sym_params))
                        .or_else(|| has_asymmetric_literal(value, sym_var_domain, sym_params))
                }
                CompiledExpr::SetLit(elems)
                | CompiledExpr::SeqLit(elems)
                | CompiledExpr::TupleLit(elems) => elems
                    .iter()
                    .find_map(|e| has_asymmetric_literal(e, sym_var_domain, sym_params)),
                CompiledExpr::DictLit(pairs) => pairs.iter().find_map(|(k, v)| {
                    has_asymmetric_literal(k, sym_var_domain, sym_params)
                        .or_else(|| has_asymmetric_literal(v, sym_var_domain, sym_params))
                }),
                CompiledExpr::Choose { domain, predicate }
                | CompiledExpr::Let {
                    value: domain,
                    body: predicate,
                } => has_asymmetric_literal(domain, sym_var_domain, sym_params)
                    .or_else(|| has_asymmetric_literal(predicate, sym_var_domain, sym_params)),
                CompiledExpr::Slice { base, lo, hi } => {
                    has_asymmetric_literal(base, sym_var_domain, sym_params)
                        .or_else(|| has_asymmetric_literal(lo, sym_var_domain, sym_params))
                        .or_else(|| has_asymmetric_literal(hi, sym_var_domain, sym_params))
                }
                CompiledExpr::Range { lo, hi } => {
                    has_asymmetric_literal(lo, sym_var_domain, sym_params)
                        .or_else(|| has_asymmetric_literal(hi, sym_var_domain, sym_params))
                }
                CompiledExpr::RecordUpdate { base, updates } => {
                    has_asymmetric_literal(base, sym_var_domain, sym_params).or_else(|| {
                        updates.iter().find_map(|(_, v)| {
                            has_asymmetric_literal(v, sym_var_domain, sym_params)
                        })
                    })
                }
                CompiledExpr::Call { func, args } => {
                    has_asymmetric_literal(func, sym_var_domain, sym_params).or_else(|| {
                        args.iter()
                            .find_map(|a| has_asymmetric_literal(a, sym_var_domain, sym_params))
                    })
                }
                CompiledExpr::ActionCall { args, .. } => args
                    .iter()
                    .find_map(|a| has_asymmetric_literal(a, sym_var_domain, sym_params)),
                CompiledExpr::Len(e)
                | CompiledExpr::Keys(e)
                | CompiledExpr::Values(e)
                | CompiledExpr::SeqHead(e)
                | CompiledExpr::SeqTail(e)
                | CompiledExpr::BigUnion(e)
                | CompiledExpr::Powerset(e)
                | CompiledExpr::Fix { predicate: e } => {
                    has_asymmetric_literal(e, sym_var_domain, sym_params)
                }
                CompiledExpr::Field { base, .. } => {
                    has_asymmetric_literal(base, sym_var_domain, sym_params)
                }
                _ => None,
            }
        }

        let mut warnings = Vec::new();
        let empty_params = std::collections::HashMap::new();

        // Check init predicate (no params)
        if let Some(detail) = has_asymmetric_literal(&spec.init, &sym_var_domain, &empty_params) {
            warnings.push(format!("symmetry may be unsound: init has {}", detail));
        }

        for action in &spec.actions {
            // Build symmetric param set: params whose range matches a symmetry group domain
            let mut sym_params: std::collections::HashMap<usize, usize> =
                std::collections::HashMap::new();
            for (idx, (_name, ty)) in action.params.iter().enumerate() {
                if let Type::Range(lo, hi) = ty {
                    let size = (*hi - *lo + 1) as usize;
                    if sym_domain_sizes.contains(&size) {
                        sym_params.insert(idx, size);
                    }
                }
            }

            for (label, expr) in [("guard", &action.guard), ("effect", &action.effect)] {
                if let Some(detail) = has_asymmetric_literal(expr, &sym_var_domain, &sym_params) {
                    warnings.push(format!(
                        "symmetry may be unsound: action '{}' {} has {}",
                        action.name, label, detail
                    ));
                }
            }
        }
        warnings
    }

    /// Compute Cone-of-Influence reduction.
    /// Returns None if all actions are relevant (no reduction possible).
    /// When `active_invariants` filters to a subset, computes a tighter COI.
    fn compute_coi(spec: &CompiledSpec, active_invariants: &[bool]) -> Option<Vec<usize>> {
        if spec.invariants.is_empty() {
            return None;
        }

        // Collect variables referenced by active invariants only
        let mut coi_vars = std::collections::HashSet::new();
        for (idx, inv) in spec.invariants.iter().enumerate() {
            if active_invariants.get(idx).copied().unwrap_or(true) {
                Self::collect_var_refs(&inv.body, &mut coi_vars);
            }
        }

        // Transitive closure: if an action writes to a COI variable,
        // all variables it reads are also in the COI
        let mut changed = true;
        while changed {
            changed = false;
            for action in &spec.actions {
                let writes_coi = action.changes.iter().any(|v| coi_vars.contains(v));
                if writes_coi {
                    for &v in &action.reads {
                        if coi_vars.insert(v) {
                            changed = true;
                        }
                    }
                }
            }
        }

        // Collect relevant action indices
        let relevant: Vec<usize> = spec
            .actions
            .iter()
            .enumerate()
            .filter(|(_, action)| action.changes.iter().any(|v| coi_vars.contains(v)))
            .map(|(idx, _)| idx)
            .collect();

        if relevant.len() == spec.actions.len() {
            None // All actions relevant, no reduction
        } else {
            debug!(
                total = spec.actions.len(),
                relevant = relevant.len(),
                "COI reduction"
            );
            Some(relevant)
        }
    }

    /// Collect variable indices referenced in an expression.
    fn collect_var_refs(expr: &CompiledExpr, vars: &mut std::collections::HashSet<usize>) {
        match expr {
            CompiledExpr::Var(idx) | CompiledExpr::PrimedVar(idx) => {
                vars.insert(*idx);
            }
            CompiledExpr::Binary { left, right, .. } => {
                Self::collect_var_refs(left, vars);
                Self::collect_var_refs(right, vars);
            }
            CompiledExpr::Unary { operand, .. } => {
                Self::collect_var_refs(operand, vars);
            }
            CompiledExpr::Index { base, index } => {
                Self::collect_var_refs(base, vars);
                Self::collect_var_refs(index, vars);
            }
            CompiledExpr::FnUpdate { base, key, value } => {
                Self::collect_var_refs(base, vars);
                Self::collect_var_refs(key, vars);
                Self::collect_var_refs(value, vars);
            }
            CompiledExpr::FnLit { domain, body } => {
                Self::collect_var_refs(domain, vars);
                Self::collect_var_refs(body, vars);
            }
            CompiledExpr::SetComprehension {
                element,
                domain,
                filter,
            } => {
                Self::collect_var_refs(element, vars);
                Self::collect_var_refs(domain, vars);
                if let Some(f) = filter {
                    Self::collect_var_refs(f, vars);
                }
            }
            CompiledExpr::Forall { domain, body } | CompiledExpr::Exists { domain, body } => {
                Self::collect_var_refs(domain, vars);
                Self::collect_var_refs(body, vars);
            }
            CompiledExpr::Choose { domain, predicate } => {
                Self::collect_var_refs(domain, vars);
                Self::collect_var_refs(predicate, vars);
            }
            CompiledExpr::If {
                cond,
                then_branch,
                else_branch,
            } => {
                Self::collect_var_refs(cond, vars);
                Self::collect_var_refs(then_branch, vars);
                Self::collect_var_refs(else_branch, vars);
            }
            CompiledExpr::Let { value, body } => {
                Self::collect_var_refs(value, vars);
                Self::collect_var_refs(body, vars);
            }
            CompiledExpr::SetLit(elems)
            | CompiledExpr::SeqLit(elems)
            | CompiledExpr::TupleLit(elems) => {
                for e in elems {
                    Self::collect_var_refs(e, vars);
                }
            }
            CompiledExpr::DictLit(pairs) => {
                for (k, v) in pairs {
                    Self::collect_var_refs(k, vars);
                    Self::collect_var_refs(v, vars);
                }
            }
            CompiledExpr::RecordUpdate { base, updates } => {
                Self::collect_var_refs(base, vars);
                for (_, v) in updates {
                    Self::collect_var_refs(v, vars);
                }
            }
            CompiledExpr::Field { base, .. } => {
                Self::collect_var_refs(base, vars);
            }
            CompiledExpr::Range { lo, hi } => {
                Self::collect_var_refs(lo, vars);
                Self::collect_var_refs(hi, vars);
            }
            CompiledExpr::Slice { base, lo, hi } => {
                Self::collect_var_refs(base, vars);
                Self::collect_var_refs(lo, vars);
                Self::collect_var_refs(hi, vars);
            }
            CompiledExpr::Len(e)
            | CompiledExpr::Keys(e)
            | CompiledExpr::Values(e)
            | CompiledExpr::BigUnion(e)
            | CompiledExpr::Powerset(e)
            | CompiledExpr::SeqHead(e)
            | CompiledExpr::SeqTail(e)
            | CompiledExpr::Fix { predicate: e } => {
                Self::collect_var_refs(e, vars);
            }
            CompiledExpr::Call { func, args } => {
                Self::collect_var_refs(func, vars);
                for a in args {
                    Self::collect_var_refs(a, vars);
                }
            }
            CompiledExpr::ActionCall { args, .. } => {
                for a in args {
                    Self::collect_var_refs(a, vars);
                }
            }
            CompiledExpr::Unchanged(idx) | CompiledExpr::Changes(idx) => {
                vars.insert(*idx);
            }
            // Leaves with no var refs
            CompiledExpr::Bool(_)
            | CompiledExpr::Int(_)
            | CompiledExpr::String(_)
            | CompiledExpr::Const(_)
            | CompiledExpr::Local(_)
            | CompiledExpr::Param(_)
            | CompiledExpr::Enabled(_) => {}
        }
    }

    /// Canonicalize a state if symmetry reduction is enabled.
    fn maybe_canonicalize(&self, state: State) -> State {
        if self.config.use_symmetry && !self.spec.symmetry_groups.is_empty() {
            state.canonicalize(&self.spec.symmetry_groups)
        } else {
            state
        }
    }

    /// Run the model checker.
    pub fn check(&mut self) -> CheckResult<CheckOutcome> {
        // Configure rayon thread pool if specified
        if self.config.num_threads > 0 {
            if let Err(e) = rayon::ThreadPoolBuilder::new()
                .num_threads(self.config.num_threads)
                .build_global()
            {
                debug!(error = %e, "thread pool already initialized, using existing pool");
            }
        }

        info!(
            parallel = self.config.parallel,
            fast_check = self.config.fast_check,
            threads = if self.config.num_threads > 0 {
                self.config.num_threads
            } else {
                rayon::current_num_threads()
            },
            "starting model checking"
        );

        let result = if self.config.directed {
            self.check_directed()
        } else if self.config.fast_check {
            self.check_fast()
        } else {
            self.check_full()
        };

        let collisions = self.store.collisions();
        if collisions > 0 {
            error!(
                collisions,
                "hash collisions detected: results may be unsound, re-run to verify"
            );
        }

        result
    }

    /// Full model checking with trace reconstruction support.
    fn check_full(&mut self) -> CheckResult<CheckOutcome> {
        // Generate initial states
        let initial_states = self.generate_initial_states()?;
        if initial_states.is_empty() {
            return Err(CheckError::NoInitialStates);
        }

        info!(count = initial_states.len(), "generated initial states");

        if self.config.parallel {
            let mut queue: VecDeque<QueueEntry> = VecDeque::new();
            let mut max_depth = 0;

            for state in initial_states {
                let canonical = self.maybe_canonicalize(state);
                let fp = canonical.fingerprint();
                if self.store.insert(canonical.clone(), None, None, None, 0) {
                    queue.push_back((fp, canonical, 0, u64::MAX, 0));
                }
            }

            self.check_parallel(&mut queue, &mut max_depth)
        } else {
            // Sequential: carry state through queue to avoid store.get() cloning
            let mut queue: VecDeque<QueueEntry> = VecDeque::new();
            let mut max_depth = 0;

            for state in initial_states {
                let canonical = self.maybe_canonicalize(state);
                let fp = canonical.fingerprint();
                if self.store.insert(canonical.clone(), None, None, None, 0) {
                    queue.push_back((fp, canonical, 0, u64::MAX, 0));
                }
            }

            self.check_sequential(&mut queue, &mut max_depth)
        }
    }

    /// Directed model checking with priority BFS.
    ///
    /// Uses a heuristic to estimate "distance to invariant violation" and explores
    /// states with lower safety margins first. Finds bugs faster than BFS but
    /// counterexamples may not be shortest.
    fn check_directed(&mut self) -> CheckResult<CheckOutcome> {
        let initial_states = self.generate_initial_states()?;
        if initial_states.is_empty() {
            return Err(CheckError::NoInitialStates);
        }

        info!(count = initial_states.len(), "generated initial states (directed)");

        // Priority queue entry sorted by heuristic score (lower = closer to violation = higher priority)
        struct PQEntry {
            score: u32,
            fp: Fingerprint,
            state: State,
            depth: usize,
        }
        impl PartialEq for PQEntry {
            fn eq(&self, other: &Self) -> bool { self.score == other.score }
        }
        impl Eq for PQEntry {}
        impl PartialOrd for PQEntry {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> { Some(self.cmp(other)) }
        }
        impl Ord for PQEntry {
            fn cmp(&self, other: &Self) -> std::cmp::Ordering {
                other.score.cmp(&self.score) // min-heap: lower score = higher priority
            }
        }

        let mut queue: BinaryHeap<PQEntry> = BinaryHeap::new();
        let mut max_depth = 0usize;
        let mut next_vars_buf = Vec::new();

        for state in initial_states {
            let canonical = self.maybe_canonicalize(state);
            let fp = canonical.fingerprint();
            if self.store.insert(canonical.clone(), None, None, None, 0) {
                let h = self.invariant_heuristic(&canonical);
                queue.push(PQEntry { score: h, fp, state: canonical, depth: 0 });
            }
        }

        while let Some(PQEntry { fp, state, depth, .. }) = queue.pop() {
            // Check external stop flag
            if let Some(ref flag) = self.stop_flag {
                if flag.load(Ordering::Relaxed) {
                    break;
                }
            }

            if let Some(ref p) = self.config.progress {
                p.checked.fetch_add(1, Ordering::Relaxed);
            }

            if depth > max_depth {
                max_depth = depth;
                if let Some(ref p) = self.config.progress {
                    p.depth.store(max_depth, Ordering::Relaxed);
                }
            }

            // Check depth limit
            if self.config.max_depth > 0 && depth >= self.config.max_depth {
                continue;
            }

            // Check state limit
            if self.config.max_states > 0 && self.store.len() >= self.config.max_states {
                return Ok(CheckOutcome::StateLimitReached {
                    states_explored: self.store.len(),
                    max_depth,
                });
            }

            // Check memory limit (every 1000 states)
            if self.config.memory_limit_mb > 0 && self.store.len().is_multiple_of(1000) {
                if let Some(mem_mb) = current_memory_mb() {
                    if mem_mb >= self.config.memory_limit_mb {
                        return Ok(CheckOutcome::MemoryLimitReached {
                            states_explored: self.store.len(),
                            max_depth,
                            memory_mb: mem_mb,
                        });
                    }
                }
            }

            // Check time limit
            if self.deadline.is_some() && self.store.len().is_multiple_of(1000) && self.past_deadline() {
                return Ok(CheckOutcome::TimeLimitReached {
                    states_explored: self.store.len(),
                    max_depth,
                });
            }

            // Check invariants
            for (inv_idx, inv) in self.spec.invariants.iter().enumerate() {
                if !self.active_invariants[inv_idx] {
                    continue;
                }
                if !self.check_invariant_bc(inv_idx, &state)? {
                    let trace = self.store.trace_to(&fp, &self.action_names);
                    return Ok(CheckOutcome::InvariantViolation {
                        invariant: inv.name.clone(),
                        trace,
                    });
                }
            }

            // Generate successors
            let mut successors = Vec::new();
            self.generate_successors(&state, &mut successors, &mut next_vars_buf, 0)?;

            if successors.is_empty() && self.config.check_deadlock {
                let any_enabled = self.any_action_enabled(&state)?;
                if !any_enabled {
                    let trace = self.store.trace_to(&fp, &self.action_names);
                    return Ok(CheckOutcome::Deadlock { trace });
                }
            }

            // Insert successors with heuristic priority
            for (succ, action_idx, pvals) in successors {
                let canonical = self.maybe_canonicalize(succ);
                let succ_fp = canonical.fingerprint();
                if self.store.insert_with_fp(
                    succ_fp,
                    canonical.clone(),
                    Some(fp),
                    Some(action_idx),
                    Some(pvals),
                    depth + 1,
                ) {
                    if let Some(ref p) = self.config.progress {
                        p.states.store(self.store.len(), Ordering::Relaxed);
                        p.queue_len.store(queue.len(), Ordering::Relaxed);
                    }
                    let h = self.invariant_heuristic(&canonical);
                    queue.push(PQEntry { score: h, fp: succ_fp, state: canonical, depth: depth + 1 });
                }
            }
        }

        Ok(CheckOutcome::Ok {
            states_explored: self.store.len(),
            max_depth,
        })
    }

    /// Heuristic: estimate how "close" a state is to violating any invariant.
    /// Returns a safety margin score: 0 = violated, higher = safer.
    /// Used by directed model checking to prioritize states closer to violation.
    ///
    /// The heuristic counts how many invariants pass. States where fewer
    /// invariants pass (closer to violation) get lower scores and are explored
    /// first. States with equal invariant counts are differentiated by a
    /// fingerprint-based hash to ensure exploration diversity.
    fn invariant_heuristic(&self, state: &State) -> u32 {
        let mut passing = 0u32;
        for (inv_idx, _inv) in self.spec.invariants.iter().enumerate() {
            let result = vm_eval_bool(
                &self.compiled_invariants[inv_idx],
                &state.vars,
                &state.vars,
                &self.consts,
                &[],
            );
            match result {
                Ok(true) => passing += 1,
                Ok(false) => return 0,
                Err(_) => passing += 1,
            }
        }
        // Use fingerprint low bits for diversity within same invariant count
        let diversity = (state.fingerprint().as_u64() & 0xF) as u32;
        passing * 16 + diversity
    }

    /// Fast model checking with minimal memory.
    /// Only stores fingerprints during exploration. If a violation is found,
    /// re-explores with full tracking to reconstruct the trace.
    fn check_fast(&mut self) -> CheckResult<CheckOutcome> {
        // Phase 1: Fast check with minimal memory
        let result = self.check_fast_phase1()?;

        match &result {
            CheckOutcome::Ok { .. }
            | CheckOutcome::StateLimitReached { .. }
            | CheckOutcome::MemoryLimitReached { .. }
            | CheckOutcome::TimeLimitReached { .. } => Ok(result),
            CheckOutcome::InvariantViolation { invariant, .. } => {
                // Phase 2: Re-explore with full tracking to get trace
                info!(invariant = %invariant, "violation found, re-exploring for trace");
                self.check_fast_phase2(invariant.clone(), None)
            }
            CheckOutcome::Deadlock { .. } => {
                // Phase 2: Re-explore with full tracking to get trace
                info!("deadlock found, re-exploring for trace");
                self.check_fast_phase2_deadlock()
            }
        }
    }

    /// Phase 1: Fast exploration storing only fingerprints.
    /// Returns violation type (with empty trace) or Ok.
    fn check_fast_phase1(&mut self) -> CheckResult<CheckOutcome> {
        let mut queue: VecDeque<QueueEntry> = VecDeque::new();
        let mut max_depth = 0;
        let mut next_vars_buf = Vec::new();

        // Generate initial states
        let initial_states = self.generate_initial_states()?;
        if initial_states.is_empty() {
            return Err(CheckError::NoInitialStates);
        }

        info!(count = initial_states.len(), "generated initial states");

        // Add initial states
        for state in initial_states {
            let canonical = self.maybe_canonicalize(state);
            let fp = canonical.fingerprint();
            if self.store.insert(canonical.clone(), None, None, None, 0) {
                queue.push_back((fp, canonical, 0, u64::MAX, 0));
            }
        }

        while let Some((fp, state, depth, change_mask, _sleep)) = queue.pop_front() {
            if let Some(ref p) = self.config.progress {
                p.checked.fetch_add(1, Ordering::Relaxed);
            }

            trace!(depth, fp = %fp, "exploring state");

            // Check depth limit
            if self.config.max_depth > 0 && depth >= self.config.max_depth {
                continue;
            }

            // Check state limit
            if self.config.max_states > 0 && self.store.len() >= self.config.max_states {
                info!(states = self.store.len(), "reached state limit");
                return Ok(CheckOutcome::StateLimitReached {
                    states_explored: self.store.len(),
                    max_depth,
                });
            }

            // Check memory limit (every 1000 states to reduce overhead)
            if self.config.memory_limit_mb > 0 && self.store.len().is_multiple_of(1000) {
                if let Some(mem_mb) = current_memory_mb() {
                    if mem_mb >= self.config.memory_limit_mb {
                        info!(
                            memory_mb = mem_mb,
                            limit_mb = self.config.memory_limit_mb,
                            "reached memory limit"
                        );
                        return Ok(CheckOutcome::MemoryLimitReached {
                            states_explored: self.store.len(),
                            max_depth,
                            memory_mb: mem_mb,
                        });
                    }
                }
            }

            // Check time limit (every 1000 states to reduce overhead)
            if self.deadline.is_some() && self.store.len().is_multiple_of(1000) && self.past_deadline() {
                return Ok(CheckOutcome::TimeLimitReached {
                    states_explored: self.store.len(),
                    max_depth,
                });
            }

            // Check invariants (skip if no relevant variables changed)
            for (inv_idx, inv) in self.spec.invariants.iter().enumerate() {
                if !self.active_invariants[inv_idx] {
                    continue;
                }
                if change_mask & self.inv_dep_masks[inv_idx] == 0 {
                    continue;
                }
                if !self.check_invariant_bc(inv_idx, &state)? {
                    // Return violation with empty trace (phase 2 will find it)
                    return Ok(CheckOutcome::InvariantViolation {
                        invariant: inv.name.clone(),
                        trace: vec![],
                    });
                }
            }

            // Generate successor states
            let mut successors = Vec::new();
            self.generate_successors(&state, &mut successors, &mut next_vars_buf, 0)?;

            if successors.is_empty() && self.config.check_deadlock {
                let any_enabled = self.any_action_enabled(&state)?;
                if !any_enabled {
                    // Return deadlock with empty trace (phase 2 will find it)
                    return Ok(CheckOutcome::Deadlock { trace: vec![] });
                }
            }

            // Add successors to queue
            for (next_state, action_idx, _pvals) in successors {
                let canonical = self.maybe_canonicalize(next_state);
                let next_fp = canonical.fingerprint();
                if self.store.insert(canonical.clone(), None, None, None, depth + 1) {
                    max_depth = max_depth.max(depth + 1);
                    queue.push_back((
                        next_fp,
                        canonical,
                        depth + 1,
                        self.action_write_masks[action_idx],
                        0, // sleep sets not used in fast check
                    ));
                }
            }

            // Grow FPSet if load factor too high (between states, no concurrent access)
            self.store.maybe_grow_fpset();

            // Update progress counters (lock-free, near-zero overhead)
            if let Some(ref p) = self.config.progress {
                p.states.store(self.store.len(), Ordering::Relaxed);
                p.depth.store(max_depth, Ordering::Relaxed);
                p.queue_len.store(queue.len(), Ordering::Relaxed);
            }
        }

        info!(
            states = self.store.len(),
            max_depth, "model checking complete"
        );

        Ok(CheckOutcome::Ok {
            states_explored: self.store.len(),
            max_depth,
        })
    }

    /// Phase 2: Re-explore with full tracking to find invariant violation trace.
    fn check_fast_phase2(
        &mut self,
        target_invariant: String,
        _target_fp: Option<Fingerprint>,
    ) -> CheckResult<CheckOutcome> {
        // Reset store with full tracking
        self.store.clear(true);

        let mut queue: VecDeque<Fingerprint> = VecDeque::new();
        let mut next_vars_buf = Vec::new();

        // Generate initial states
        let initial_states = self.generate_initial_states()?;
        for state in initial_states {
            let canonical = self.maybe_canonicalize(state);
            let fp = canonical.fingerprint();
            if self.store.insert(canonical, None, None, None, 0) {
                queue.push_back(fp);
            }
        }

        while let Some(fp) = queue.pop_front() {
            let info = self.store.get(&fp).unwrap();
            let state = &info.state;
            let depth = info.depth;

            // Check target invariant
            for (inv_idx, inv) in self.spec.invariants.iter().enumerate() {
                if inv.name == target_invariant && !self.check_invariant_bc(inv_idx, state)? {
                    let trace = self.store.trace_to(&fp, &self.action_names);
                    return Ok(CheckOutcome::InvariantViolation {
                        invariant: inv.name.clone(),
                        trace,
                    });
                }
            }

            // Generate successors
            let mut successors = Vec::new();
            self.generate_successors(state, &mut successors, &mut next_vars_buf, 0)?;
            for (next_state, action_idx, pvals) in successors {
                let canonical = self.maybe_canonicalize(next_state);
                let next_fp = canonical.fingerprint();
                if self
                    .store
                    .insert(canonical, Some(fp), Some(action_idx), Some(pvals), depth + 1)
                {
                    queue.push_back(next_fp);
                }
            }
        }

        // Shouldn't reach here - violation should be found
        Err(CheckError::Eval(EvalError::Internal(
            "failed to reproduce violation in phase 2".to_string(),
        )))
    }

    /// Phase 2: Re-explore with full tracking to find deadlock trace.
    fn check_fast_phase2_deadlock(&mut self) -> CheckResult<CheckOutcome> {
        // Reset store with full tracking
        self.store.clear(true);

        let mut queue: VecDeque<Fingerprint> = VecDeque::new();
        let mut next_vars_buf = Vec::new();

        // Generate initial states
        let initial_states = self.generate_initial_states()?;
        for state in initial_states {
            let canonical = self.maybe_canonicalize(state);
            let fp = canonical.fingerprint();
            if self.store.insert(canonical, None, None, None, 0) {
                queue.push_back(fp);
            }
        }

        while let Some(fp) = queue.pop_front() {
            let info = self.store.get(&fp).unwrap();
            let state = &info.state;
            let depth = info.depth;

            // Check for deadlock
            let mut successors = Vec::new();
            self.generate_successors(state, &mut successors, &mut next_vars_buf, 0)?;
            if successors.is_empty() && self.config.check_deadlock {
                let any_enabled = self.any_action_enabled(state)?;
                if !any_enabled {
                    let trace = self.store.trace_to(&fp, &self.action_names);
                    return Ok(CheckOutcome::Deadlock { trace });
                }
            }

            // Generate successors
            for (next_state, action_idx, pvals) in successors {
                let canonical = self.maybe_canonicalize(next_state);
                let next_fp = canonical.fingerprint();
                if self
                    .store
                    .insert(canonical, Some(fp), Some(action_idx), Some(pvals), depth + 1)
                {
                    queue.push_back(next_fp);
                }
            }
        }

        // Shouldn't reach here - deadlock should be found
        Err(CheckError::Eval(EvalError::Internal(
            "failed to reproduce deadlock in phase 2".to_string(),
        )))
    }

    /// Sequential BFS exploration.
    fn check_sequential(
        &mut self,
        queue: &mut VecDeque<QueueEntry>,
        max_depth: &mut usize,
    ) -> CheckResult<CheckOutcome> {
        let mut hit_state_limit = false;
        let mut hit_memory_limit = false;
        let mut hit_time_limit = false;
        let mut memory_at_limit = 0usize;
        let mut next_vars_buf = Vec::new();

        // Profile accumulators (zero-cost when profiling disabled)
        let profiling = self.config.profile;
        let n_actions = self.spec.actions.len();
        let mut prof_action_counts = if profiling { vec![0usize; n_actions] } else { vec![] };
        let mut prof_time_inv = Duration::ZERO;
        let mut prof_time_succ = Duration::ZERO;
        let mut prof_time_store = Duration::ZERO;

        while let Some((fp, state, depth, change_mask, sleep_set)) = queue.pop_front() {
            // Check external stop flag (swarm cancellation)
            if let Some(ref flag) = self.stop_flag {
                if flag.load(Ordering::Relaxed) {
                    break;
                }
            }

            if let Some(ref p) = self.config.progress {
                p.checked.fetch_add(1, Ordering::Relaxed);
            }
            trace!(depth, fp = %fp, "exploring state");

            // Check depth limit
            if self.config.max_depth > 0 && depth >= self.config.max_depth {
                continue;
            }

            // Check state limit
            if self.config.max_states > 0 && self.store.len() >= self.config.max_states {
                info!(states = self.store.len(), "reached state limit");
                hit_state_limit = true;
                break;
            }

            // Check memory limit (every 1000 states to reduce overhead)
            if self.config.memory_limit_mb > 0 && self.store.len().is_multiple_of(1000) {
                if let Some(mem_mb) = current_memory_mb() {
                    if mem_mb >= self.config.memory_limit_mb {
                        info!(
                            memory_mb = mem_mb,
                            limit_mb = self.config.memory_limit_mb,
                            "reached memory limit"
                        );
                        hit_memory_limit = true;
                        memory_at_limit = mem_mb;
                        break;
                    }
                }
            }

            // Check time limit (every 1000 states to reduce overhead)
            if self.deadline.is_some() && self.store.len().is_multiple_of(1000) && self.past_deadline() {
                info!("reached time limit");
                hit_time_limit = true;
                break;
            }

            // --- Phase 1: Check invariants ---
            let t0 = Instant::now();
            for (inv_idx, inv) in self.spec.invariants.iter().enumerate() {
                if !self.active_invariants[inv_idx] {
                    continue;
                }
                if change_mask & self.inv_dep_masks[inv_idx] == 0 {
                    continue;
                }
                if !self.check_invariant_bc(inv_idx, &state)? {
                    if profiling {
                        self.profile_data = Some(ProfileData {
                            action_fire_counts: prof_action_counts,
                            action_names: self.action_names.clone(),
                            time_invariants: prof_time_inv,
                            time_successors: prof_time_succ,
                            time_store: prof_time_store,
                        });
                    }
                    let trace = self.store.trace_to(&fp, &self.action_names);
                    return Ok(CheckOutcome::InvariantViolation {
                        invariant: inv.name.clone(),
                        trace,
                    });
                }
            }
            if profiling { prof_time_inv += t0.elapsed(); }

            // --- Phase 2: Generate successor states ---
            let t1 = Instant::now();
            let mut successors = Vec::new();
            self.generate_successors(&state, &mut successors, &mut next_vars_buf, sleep_set)?;
            if profiling { prof_time_succ += t1.elapsed(); }

            if successors.is_empty() && self.config.check_deadlock {
                // Check if any action is enabled (ignoring sleep set — sleep doesn't cause deadlock)
                let any_enabled = self.any_action_enabled(&state)?;
                if !any_enabled {
                    if profiling {
                        self.profile_data = Some(ProfileData {
                            action_fire_counts: prof_action_counts,
                            action_names: self.action_names.clone(),
                            time_invariants: prof_time_inv,
                            time_successors: prof_time_succ,
                            time_store: prof_time_store,
                        });
                    }
                    let trace = self.store.trace_to(&fp, &self.action_names);
                    return Ok(CheckOutcome::Deadlock { trace });
                }
            }

            // --- Phase 3: Store insert + queue management ---
            let t2 = Instant::now();
            let use_sleep = self.config.use_por && self.spec.actions.len() <= 64;
            let mut accumulated_sleep = sleep_set;
            for (next_state, action_idx, pvals) in successors {
                if profiling { prof_action_counts[action_idx] += 1; }
                let successor_sleep = if use_sleep {
                    accumulated_sleep & self.independent_masks[action_idx]
                } else {
                    0
                };
                let canonical = self.maybe_canonicalize(next_state);
                let next_fp = canonical.fingerprint();
                if self
                    .store
                    .insert(canonical.clone(), Some(fp), Some(action_idx), Some(pvals), depth + 1)
                {
                    *max_depth = (*max_depth).max(depth + 1);
                    queue.push_back((
                        next_fp,
                        canonical,
                        depth + 1,
                        self.action_write_masks[action_idx],
                        successor_sleep,
                    ));
                }
                if use_sleep {
                    accumulated_sleep |= 1u64 << action_idx;
                }
            }

            // Grow FPSet between batches if needed (no concurrent inserts at this point)
            self.store.maybe_grow_fpset();
            if profiling { prof_time_store += t2.elapsed(); }

            // Update progress counters (lock-free, near-zero overhead)
            if let Some(ref p) = self.config.progress {
                p.states.store(self.store.len(), Ordering::Relaxed);
                p.depth.store(*max_depth, Ordering::Relaxed);
                p.queue_len.store(queue.len(), Ordering::Relaxed);
            }
        }

        // Store profile data
        if profiling {
            self.profile_data = Some(ProfileData {
                action_fire_counts: prof_action_counts,
                action_names: self.action_names.clone(),
                time_invariants: prof_time_inv,
                time_successors: prof_time_succ,
                time_store: prof_time_store,
            });
        }

        info!(
            states = self.store.len(),
            max_depth = *max_depth,
            "model checking complete"
        );

        if hit_memory_limit {
            Ok(CheckOutcome::MemoryLimitReached {
                states_explored: self.store.len(),
                max_depth: *max_depth,
                memory_mb: memory_at_limit,
            })
        } else if hit_time_limit {
            Ok(CheckOutcome::TimeLimitReached {
                states_explored: self.store.len(),
                max_depth: *max_depth,
            })
        } else if hit_state_limit {
            Ok(CheckOutcome::StateLimitReached {
                states_explored: self.store.len(),
                max_depth: *max_depth,
            })
        } else {
            Ok(CheckOutcome::Ok {
                states_explored: self.store.len(),
                max_depth: *max_depth,
            })
        }
    }

    /// Parallel BFS exploration.
    fn check_parallel(
        &self,
        queue: &mut VecDeque<QueueEntry>,
        max_depth: &mut usize,
    ) -> CheckResult<CheckOutcome> {
        // Flags to stop early
        let found_violation = AtomicBool::new(false);
        let batch_size = if self.config.num_threads > 0 {
            self.config.num_threads * 256
        } else {
            rayon::current_num_threads() * 256
        };
        let mut hit_state_limit = false;
        let mut hit_memory_limit = false;
        let mut hit_time_limit = false;
        let mut memory_at_limit = 0usize;

        while !queue.is_empty() && !found_violation.load(Ordering::Relaxed) {
            // Check state limit
            if self.config.max_states > 0 && self.store.len() >= self.config.max_states {
                info!(states = self.store.len(), "reached state limit");
                hit_state_limit = true;
                break;
            }

            // Check memory limit (every batch to reduce overhead)
            if self.config.memory_limit_mb > 0 {
                if let Some(mem_mb) = current_memory_mb() {
                    if mem_mb >= self.config.memory_limit_mb {
                        info!(
                            memory_mb = mem_mb,
                            limit_mb = self.config.memory_limit_mb,
                            "reached memory limit"
                        );
                        hit_memory_limit = true;
                        memory_at_limit = mem_mb;
                        break;
                    }
                }
            }

            // Check time limit
            if self.past_deadline() {
                info!("reached time limit");
                hit_time_limit = true;
                break;
            }

            // Take a batch of states from the queue
            let batch: Vec<QueueEntry> = queue.drain(..queue.len().min(batch_size)).collect();

            // Process batch in parallel
            let results: Vec<_> = batch
                .par_iter()
                .filter_map(|(fp, state, depth, change_mask, _sleep_set)| {
                    if found_violation.load(Ordering::Relaxed) {
                        return None;
                    }

                    let depth = *depth;

                    if let Some(ref p) = self.config.progress {
                        p.checked.fetch_add(1, Ordering::Relaxed);
                    }

                    // Check depth limit
                    if self.config.max_depth > 0 && depth >= self.config.max_depth {
                        return Some(Ok(ParallelResult::DepthLimited));
                    }

                    // Check invariants (skip if no relevant variables changed)
                    for (inv_idx, inv) in self.spec.invariants.iter().enumerate() {
                        if !self.active_invariants[inv_idx] {
                            continue;
                        }
                        if change_mask & self.inv_dep_masks[inv_idx] == 0 {
                            continue;
                        }
                        match self.check_invariant_bc(inv_idx, state) {
                            Ok(true) => {}
                            Ok(false) => {
                                found_violation.store(true, Ordering::Relaxed);
                                return Some(Ok(ParallelResult::InvariantViolation {
                                    fp: *fp,
                                    invariant: inv.name.clone(),
                                }));
                            }
                            Err(e) => return Some(Err(e)),
                        }
                    }

                    // Generate successor states
                    let mut successors = Vec::new();
                    let mut next_vars_buf = Vec::new();
                    match self.generate_successors(state, &mut successors, &mut next_vars_buf, 0) {
                        Ok(()) => {
                            if successors.is_empty() && self.config.check_deadlock {
                                match self.any_action_enabled(state) {
                                    Ok(false) => {
                                        found_violation.store(true, Ordering::Relaxed);
                                        return Some(Ok(ParallelResult::Deadlock { fp: *fp }));
                                    }
                                    Ok(true) => {}
                                    Err(e) => return Some(Err(e)),
                                }
                            }
                            // Insert successors into store directly (parallel)
                            let mut new_entries = Vec::new();
                            let mut batch_max_depth = 0;
                            for (next_state, action_idx, pvals) in successors {
                                let canonical = self.maybe_canonicalize(next_state);
                                let next_fp = canonical.fingerprint();
                                if self.store.contains(&next_fp) {
                                    continue;
                                }
                                if self.store.insert_with_fp(
                                    next_fp,
                                    canonical.clone(),
                                    Some(*fp),
                                    Some(action_idx),
                                    Some(pvals),
                                    depth + 1,
                                ) {
                                    batch_max_depth = batch_max_depth.max(depth + 1);
                                    // Update progress from inside par_iter so spinner never freezes
                                    if let Some(ref p) = self.config.progress {
                                        p.states.store(self.store.len(), Ordering::Relaxed);
                                        p.depth.fetch_max(depth + 1, Ordering::Relaxed);
                                    }
                                    new_entries.push((
                                        next_fp,
                                        canonical,
                                        depth + 1,
                                        self.action_write_masks[action_idx],
                                        0, // sleep sets not used in parallel mode
                                    ));
                                }
                            }
                            Some(Ok(ParallelResult::NewStates {
                                new_entries,
                                max_depth: batch_max_depth,
                            }))
                        }
                        Err(e) => Some(Err(e)),
                    }
                })
                .collect();

            // Process results
            for result in results {
                match result? {
                    ParallelResult::DepthLimited => {}
                    ParallelResult::InvariantViolation { fp, invariant } => {
                        let trace = self.store.trace_to(&fp, &self.action_names);
                        return Ok(CheckOutcome::InvariantViolation { invariant, trace });
                    }
                    ParallelResult::Deadlock { fp } => {
                        let trace = self.store.trace_to(&fp, &self.action_names);
                        return Ok(CheckOutcome::Deadlock { trace });
                    }
                    ParallelResult::NewStates {
                        new_entries,
                        max_depth: d,
                    } => {
                        *max_depth = (*max_depth).max(d);
                        queue.extend(new_entries);
                    }
                }
            }

            // Grow FPSet between batches if needed (no concurrent inserts at this point)
            self.store.maybe_grow_fpset();

            // Update progress counters (lock-free, near-zero overhead)
            if let Some(ref p) = self.config.progress {
                p.states.store(self.store.len(), Ordering::Relaxed);
                p.depth.store(*max_depth, Ordering::Relaxed);
                p.queue_len.store(queue.len(), Ordering::Relaxed);
            }
        }

        info!(
            states = self.store.len(),
            max_depth = *max_depth,
            "model checking complete"
        );

        if hit_memory_limit {
            Ok(CheckOutcome::MemoryLimitReached {
                states_explored: self.store.len(),
                max_depth: *max_depth,
                memory_mb: memory_at_limit,
            })
        } else if hit_time_limit {
            Ok(CheckOutcome::TimeLimitReached {
                states_explored: self.store.len(),
                max_depth: *max_depth,
            })
        } else if hit_state_limit {
            Ok(CheckOutcome::StateLimitReached {
                states_explored: self.store.len(),
                max_depth: *max_depth,
            })
        } else {
            Ok(CheckOutcome::Ok {
                states_explored: self.store.len(),
                max_depth: *max_depth,
            })
        }
    }

    /// Generate all initial states satisfying the init predicate.
    fn generate_initial_states(&self) -> CheckResult<Vec<State>> {
        // Try direct evaluation first (fast path)
        match generate_initial_states_direct(&self.spec, &self.consts) {
            Ok(states) => {
                debug!(
                    count = states.len(),
                    "generated initial states via direct evaluation"
                );
                return Ok(states);
            }
            Err(_) => {
                debug!("falling back to enumeration for initial states");
            }
        }

        // Fallback: enumerate all combinations (exponential but works for small domains)
        let mut states = Vec::new();
        let domains = self.get_variable_domains();

        self.enumerate_states(
            &domains,
            0,
            vec![Value::none(); self.spec.vars.len()],
            &mut |state: State| {
                let mut ctx = EvalContext::new(&state.vars, &state.vars, &self.consts, &[]);
                match eval(&self.spec.init, &mut ctx) {
                    Ok(ref v) if v.as_bool() == Some(true) => {
                        states.push(state);
                    }
                    Ok(_) => {}
                    Err(e) => {
                        debug!(error = %e, "error evaluating init");
                    }
                }
            },
        );

        Ok(states)
    }

    /// Enumerate all states from variable domains.
    fn enumerate_states<F>(
        &self,
        domains: &[Vec<Value>],
        var_idx: usize,
        current: Vec<Value>,
        callback: &mut F,
    ) where
        F: FnMut(State),
    {
        if var_idx >= domains.len() {
            callback(State::new(current));
            return;
        }

        for value in &domains[var_idx] {
            let mut next = current.clone();
            next[var_idx] = value.clone();
            self.enumerate_states(domains, var_idx + 1, next, callback);
        }
    }

    /// Get domains for each variable based on their types.
    fn get_variable_domains(&self) -> Vec<Vec<Value>> {
        self.spec
            .vars
            .iter()
            .map(|v| self.type_domain(&v.ty))
            .collect()
    }

    /// Get the domain of a type.
    fn type_domain(&self, ty: &specl_types::Type) -> Vec<Value> {
        match ty {
            specl_types::Type::Bool => vec![Value::bool(false), Value::bool(true)],
            specl_types::Type::Nat | specl_types::Type::Int => {
                unreachable!(
                    "unbounded type {:?} in explicit-state checking — should be caught by CLI before exploration",
                    ty
                )
            }
            specl_types::Type::Range(lo, hi) => (*lo..=*hi).map(Value::int).collect(),
            specl_types::Type::Set(elem_ty) => {
                // Generate power set of element domain (limited)
                let elem_domain = self.type_domain(elem_ty);
                self.power_set(&elem_domain)
            }
            specl_types::Type::Record(record_type) => {
                // Generate cartesian product of all field domains
                self.record_domain(record_type)
            }
            specl_types::Type::Tuple(elem_types) => {
                // Generate cartesian product of all element domains
                self.tuple_domain(elem_types)
            }
            specl_types::Type::Fn(key_ty, val_ty) => {
                // Generate all possible functions from key domain to value domain
                self.fn_domain(key_ty, val_ty)
            }
            specl_types::Type::Seq(elem_ty) => {
                // Generate sequences of lengths 0, 1, 2, 3 (limited to avoid explosion)
                self.seq_domain(elem_ty)
            }
            _ => {
                // Default domain
                vec![Value::none()]
            }
        }
    }

    /// Generate all possible record values for a record type.
    fn record_domain(&self, record_type: &specl_types::RecordType) -> Vec<Value> {
        use std::collections::BTreeMap;

        let field_names: Vec<&str> = record_type
            .fields
            .keys()
            .map(|name| name.as_str())
            .collect();
        let field_domains: Vec<Vec<Value>> = record_type
            .fields
            .values()
            .map(|ty| self.type_domain(ty))
            .collect();

        if field_domains.is_empty() {
            return vec![Value::record(BTreeMap::new())];
        }

        // Compute cartesian product
        let mut result = vec![];
        self.enumerate_record_fields(
            &field_names,
            &field_domains,
            0,
            BTreeMap::new(),
            &mut |record| {
                result.push(Value::record(record));
            },
        );
        result
    }

    fn enumerate_record_fields<F>(
        &self,
        field_names: &[&str],
        field_domains: &[Vec<Value>],
        idx: usize,
        current: std::collections::BTreeMap<String, Value>,
        callback: &mut F,
    ) where
        F: FnMut(std::collections::BTreeMap<String, Value>),
    {
        if idx >= field_names.len() {
            callback(current);
            return;
        }

        for value in &field_domains[idx] {
            let mut next = current.clone();
            next.insert(field_names[idx].to_string(), value.clone());
            self.enumerate_record_fields(field_names, field_domains, idx + 1, next, callback);
        }
    }

    /// Generate all possible tuple values (cartesian product of element domains).
    fn tuple_domain(&self, elem_types: &[specl_types::Type]) -> Vec<Value> {
        let elem_domains: Vec<Vec<Value>> =
            elem_types.iter().map(|ty| self.type_domain(ty)).collect();

        if elem_domains.is_empty() {
            return vec![Value::tuple(vec![])];
        }

        let mut result = vec![];
        self.enumerate_tuple_elements(&elem_domains, 0, vec![], &mut |tuple| {
            result.push(Value::tuple(tuple));
        });
        result
    }

    fn enumerate_tuple_elements<F>(
        &self,
        elem_domains: &[Vec<Value>],
        idx: usize,
        current: Vec<Value>,
        callback: &mut F,
    ) where
        F: FnMut(Vec<Value>),
    {
        if idx >= elem_domains.len() {
            callback(current);
            return;
        }

        for value in &elem_domains[idx] {
            let mut next = current.clone();
            next.push(value.clone());
            self.enumerate_tuple_elements(elem_domains, idx + 1, next, callback);
        }
    }

    /// Generate all possible functions from key domain to value domain.
    fn fn_domain(&self, key_ty: &specl_types::Type, val_ty: &specl_types::Type) -> Vec<Value> {
        let key_domain = self.type_domain(key_ty);
        let val_domain = self.type_domain(val_ty);

        if key_domain.is_empty() {
            return vec![Value::func(std::sync::Arc::new(Vec::new()))];
        }

        // Bail early for large key domains (e.g. Dict[Seq[Int], T])
        if key_domain.len() > 100 {
            info!(
                keys = key_domain.len(),
                "fn_domain key domain too large, returning empty"
            );
            return vec![];
        }

        // Guard against combinatorial explosion: val_domain^key_domain combinations
        let total = (val_domain.len() as f64).powi(key_domain.len() as i32);
        if total > 100_000.0 {
            info!(
                "fn_domain too large, returning empty domain: keys={} vals={} combinations={}",
                key_domain.len(),
                val_domain.len(),
                total
            );
            return vec![];
        }

        let mut result = vec![];
        self.enumerate_fn_values(&key_domain, &val_domain, 0, Vec::new(), &mut |map| {
            result.push(Value::func(std::sync::Arc::new(map)));
        });
        result
    }

    fn enumerate_fn_values<F>(
        &self,
        key_domain: &[Value],
        val_domain: &[Value],
        idx: usize,
        current: Vec<(Value, Value)>,
        callback: &mut F,
    ) where
        F: FnMut(Vec<(Value, Value)>),
    {
        if idx >= key_domain.len() {
            callback(current);
            return;
        }

        for value in val_domain {
            let mut next = current.clone();
            // key_domain is sorted so appending in order keeps the vec sorted
            next.push((key_domain[idx].clone(), value.clone()));
            self.enumerate_fn_values(key_domain, val_domain, idx + 1, next, callback);
        }
    }

    /// Generate all possible sequences of an element type up to a max length.
    fn seq_domain(&self, elem_ty: &specl_types::Type) -> Vec<Value> {
        let elem_domain = self.type_domain(elem_ty);
        let max_len = 4; // Limit sequence length to avoid explosion

        // Guard: total sequences = sum(elem^k for k=0..max_len)
        let total: f64 = (0..=max_len)
            .map(|k| (elem_domain.len() as f64).powi(k as i32))
            .sum();
        if total > 100_000.0 {
            info!(
                "seq_domain too large, returning only empty seq: elems={} max_len={} combinations={}",
                elem_domain.len(),
                max_len,
                total
            );
            return vec![Value::seq(vec![])];
        }

        let mut result = vec![Value::seq(vec![])]; // Empty sequence

        // Generate sequences of length 1, 2, ..., max_len
        for len in 1..=max_len {
            self.enumerate_seqs(&elem_domain, len, vec![], &mut |seq| {
                result.push(Value::seq(seq));
            });
        }

        result
    }

    fn enumerate_seqs<F>(
        &self,
        elem_domain: &[Value],
        len: usize,
        current: Vec<Value>,
        callback: &mut F,
    ) where
        F: FnMut(Vec<Value>),
    {
        if current.len() >= len {
            callback(current);
            return;
        }

        for elem in elem_domain {
            let mut next = current.clone();
            next.push(elem.clone());
            self.enumerate_seqs(elem_domain, len, next, callback);
        }
    }

    /// Generate power set of a domain (limited to small sets).
    fn power_set(&self, domain: &[Value]) -> Vec<Value> {
        let max_elems = domain.len().min(5); // Limit to avoid explosion
        let mut result = vec![Value::empty_set()];

        for elem in domain.iter().take(max_elems) {
            let mut new_sets = Vec::new();
            for set in &result {
                if let Some(s) = set.as_set() {
                    let mut new_set: Vec<Value> = s.to_vec();
                    Value::set_insert(&mut new_set, elem.clone());
                    new_sets.push(Value::set(std::sync::Arc::new(new_set)));
                }
            }
            result.extend(new_sets);
        }

        result
    }

    /// Generate successor states from a state.
    /// Successor: (next_state, action_index, params) - name formatting deferred.
    /// Uses per-thread operation cache to skip redundant evaluations.
    /// sleep_set: bitmask of action indices to skip (0 = no sleep set).
    fn generate_successors(
        &self,
        state: &State,
        buf: &mut Vec<(State, usize, Vec<i64>)>,
        next_vars_buf: &mut Vec<Value>,
        sleep_set: u64,
    ) -> CheckResult<()> {
        buf.clear();

        // Instance-level POR: apply specific (action, params) instances directly
        if self.config.use_por && self.has_refinable_pairs {
            if let AmpleResult::Instances(instances) =
                self.compute_ample_set_instance_level(state)?
            {
                // Apply concrete instances directly
                let mut template_actions: Vec<usize> = Vec::new();
                for (action_idx, params) in &instances {
                    if params.is_empty() {
                        // Non-refinable action group: apply via template path below
                        template_actions.push(*action_idx);
                    } else {
                        self.apply_single_instance(state, *action_idx, params, buf, next_vars_buf)?;
                    }
                }
                if template_actions.is_empty() {
                    return Ok(());
                }
                // Apply remaining template-level actions (sleep set disabled for
                // instance-level POR per plan — sleep sets are a secondary optimization)
                return self.apply_template_actions(
                    state,
                    &template_actions,
                    buf,
                    next_vars_buf,
                    0,
                );
            }
            // AmpleResult::Templates falls through to standard path below
        }

        // Standard path: determine which action templates to explore
        let actions_to_explore = if self.config.use_por {
            self.compute_ample_set(state)?
        } else if let Some(ref relevant) = self.relevant_actions {
            relevant.clone()
        } else {
            self.default_action_order.clone()
        };

        self.apply_template_actions(state, &actions_to_explore, buf, next_vars_buf, sleep_set)
    }

    /// Apply a set of action templates to a state, using the operation cache and
    /// orbit representative filtering. Shared by all exploration paths.
    fn apply_template_actions(
        &self,
        state: &State,
        actions: &[usize],
        buf: &mut Vec<(State, usize, Vec<i64>)>,
        next_vars_buf: &mut Vec<Value>,
        sleep_set: u64,
    ) -> CheckResult<()> {
        use std::cell::RefCell;

        thread_local! {
            static OP_CACHES: RefCell<Vec<OpCache>> = const { RefCell::new(Vec::new()) };
        }

        let orbit_reps: SmallVec<[Vec<usize>; 4]> =
            if self.config.use_symmetry && !self.spec.symmetry_groups.is_empty() {
                self.spec
                    .symmetry_groups
                    .iter()
                    .map(|group| crate::state::orbit_representatives(&state.vars, group))
                    .collect()
            } else {
                SmallVec::new()
            };

        let num_actions = self.spec.actions.len();
        OP_CACHES.with(|cell| {
            let mut caches = cell.borrow_mut();
            if caches.len() != num_actions {
                *caches = (0..num_actions).map(|_| OpCache::new()).collect();
            }
            for &action_idx in actions {
                if sleep_set != 0 && action_idx < 64 && sleep_set & (1u64 << action_idx) != 0 {
                    continue;
                }
                self.apply_action(
                    state,
                    action_idx,
                    buf,
                    next_vars_buf,
                    &mut caches[action_idx],
                    &orbit_reps,
                )?;
            }
            Ok::<(), CheckError>(())
        })?;

        Ok(())
    }

    /// Get indices of all enabled actions for a state.
    fn get_enabled_actions(&self, state: &State) -> CheckResult<Vec<usize>> {
        let mut enabled = Vec::new();

        for (idx, action) in self.spec.actions.iter().enumerate() {
            if self.is_action_enabled(state, action, idx)? {
                enabled.push(idx);
            }
        }

        Ok(enabled)
    }

    /// Check if an action is enabled (guard satisfied for some parameter values).
    fn is_action_enabled(
        &self,
        state: &State,
        _action: &CompiledAction,
        action_idx: usize,
    ) -> CheckResult<bool> {
        let dynamic;
        let param_domains = if let Some(d) = self.get_effective_domains(action_idx, state) {
            dynamic = d;
            &dynamic
        } else {
            &self.cached_param_domains[action_idx]
        };
        let guard_bc = &self.compiled_guards[action_idx];
        let mut enabled = false;

        if let Some(guard_index) = &self.guard_indices[action_idx] {
            if let Some(ref pre_guard) = guard_index.pre_guard {
                if !vm_eval_bool(pre_guard, &state.vars, &state.vars, &self.consts, &[])
                    .unwrap_or(false)
                {
                    return Ok(false);
                }
            }
            let mut params_buf = vec![Value::none(); param_domains.len()];
            enumerate_params_indexed(
                param_domains,
                guard_index,
                guard_bc,
                &state.vars,
                &self.consts,
                &mut params_buf,
                0,
                &mut |_params: &[Value]| {
                    enabled = true;
                },
            );
        } else {
            let mut params_buf = SmallVec::new();
            self.enumerate_params(param_domains, &mut params_buf, &mut |params: &[Value]| {
                if !enabled {
                    if let Ok(true) =
                        vm_eval_bool(guard_bc, &state.vars, &state.vars, &self.consts, params)
                    {
                        enabled = true;
                    }
                }
            });
        }

        Ok(enabled)
    }

    /// Compute the ample set for partial order reduction.
    /// Returns indices of actions to explore (a subset of enabled actions).
    ///
    /// For BFS with safety properties, we use a conservative stubborn set algorithm:
    /// - Start with each enabled action as a potential seed
    /// - Build closure under dependency (add all dependent enabled actions)
    /// - Pick the smallest non-singleton ample set
    ///
    /// Key constraint: For BFS soundness, we can only reduce when the ample set
    /// contains at least 2 actions due to dependencies. If an ample set is a
    /// singleton (all other actions are independent), we must explore all enabled
    /// actions to ensure we don't miss reachable states.
    fn compute_ample_set(&self, state: &State) -> CheckResult<Vec<usize>> {
        use std::collections::HashSet;

        let enabled = self.get_enabled_actions(state)?;
        if enabled.is_empty() {
            return Ok(vec![]);
        }

        // If only one action enabled, no reduction possible
        if enabled.len() == 1 {
            return Ok(enabled);
        }

        // Try each enabled action as a seed and find the smallest valid ample set
        let mut best_ample: Option<Vec<usize>> = None;

        for &seed in &enabled {
            let mut ample: HashSet<usize> = HashSet::new();
            let mut to_add = vec![seed];

            // Build closure under dependency
            while let Some(a) = to_add.pop() {
                if ample.insert(a) {
                    // Add all enabled actions that are dependent on a
                    for &b in &enabled {
                        if !self.spec.independent[a][b] && !ample.contains(&b) {
                            to_add.push(b);
                        }
                    }
                }
            }

            // For BFS soundness, only use ample sets that grew beyond the seed
            // (i.e., dependencies pulled in more actions). Singleton ample sets
            // would cause us to miss states reachable via independent actions.
            if ample.len() > 1 {
                let ample_vec: Vec<usize> = ample.into_iter().collect();
                if best_ample.is_none() || ample_vec.len() < best_ample.as_ref().unwrap().len() {
                    best_ample = Some(ample_vec);
                }
            }
        }

        // If we found a valid ample set (non-singleton), use it
        if let Some(result) = best_ample {
            if result.len() < enabled.len() {
                trace!(
                    enabled = enabled.len(),
                    ample = result.len(),
                    "POR: reduced action set"
                );
            }
            return Ok(result);
        }

        // No valid reduction found - all enabled actions are pairwise independent
        // Must explore all to ensure we find all reachable states
        Ok(enabled)
    }

    /// Enumerate all enabled instances (action_idx, params) for a given action template.
    fn get_enabled_instances(
        &self,
        state: &State,
        action_idx: usize,
    ) -> CheckResult<Vec<(usize, Vec<Value>)>> {
        let dynamic;
        let param_domains = if let Some(d) = self.get_effective_domains(action_idx, state) {
            dynamic = d;
            &dynamic
        } else {
            &self.cached_param_domains[action_idx]
        };
        let guard_bc = &self.compiled_guards[action_idx];
        let mut instances = Vec::new();

        if let Some(guard_index) = &self.guard_indices[action_idx] {
            if let Some(ref pre_guard) = guard_index.pre_guard {
                if !vm_eval_bool(pre_guard, &state.vars, &state.vars, &self.consts, &[])
                    .unwrap_or(false)
                {
                    return Ok(instances);
                }
            }
            let mut params_buf = vec![Value::none(); param_domains.len()];
            enumerate_params_indexed(
                param_domains,
                guard_index,
                guard_bc,
                &state.vars,
                &self.consts,
                &mut params_buf,
                0,
                &mut |params: &[Value]| {
                    instances.push((action_idx, params.to_vec()));
                },
            );
        } else {
            let mut params_buf = SmallVec::new();
            self.enumerate_params(param_domains, &mut params_buf, &mut |params: &[Value]| {
                if vm_eval_bool(guard_bc, &state.vars, &state.vars, &self.consts, params)
                    .unwrap_or(false)
                {
                    instances.push((action_idx, params.to_vec()));
                }
            });
        }

        Ok(instances)
    }

    /// Compute instance-level ample set for partial order reduction.
    /// Falls back to template-level when no refinable pairs are among enabled actions.
    fn compute_ample_set_instance_level(&self, state: &State) -> CheckResult<AmpleResult> {
        use std::collections::HashSet;

        let enabled_templates = self.get_enabled_actions(state)?;
        if enabled_templates.is_empty() {
            return Ok(AmpleResult::Templates);
        }
        if enabled_templates.len() == 1 {
            return Ok(AmpleResult::Templates);
        }

        // Fast path: check if any enabled pair is refinable
        let any_refinable = enabled_templates.iter().any(|&a| {
            self.action_has_refinable[a]
                && enabled_templates
                    .iter()
                    .any(|&b| self.spec.refinable_pairs[a][b])
        });
        if !any_refinable {
            return Ok(AmpleResult::Templates);
        }

        // Enumerate all enabled instances for refinable actions
        let mut all_instances: Vec<(usize, Vec<Value>)> = Vec::new();
        for &action_idx in &enabled_templates {
            if self.action_has_refinable[action_idx] {
                let instances = self.get_enabled_instances(state, action_idx)?;
                all_instances.extend(instances);
            } else {
                // Non-refinable actions: represent as single entry with empty params.
                // All instances of this action are treated as one node.
                all_instances.push((action_idx, Vec::new()));
            }
        }

        if all_instances.len() <= 1 {
            return Ok(AmpleResult::Templates);
        }

        // Fall back to template-level POR when instance count is large.
        // The stubborn set computation is O(n^3) in instances — at 64+ instances
        // the overhead exceeds any state space reduction.
        let n = all_instances.len();
        if n > 64 {
            return Ok(AmpleResult::Templates);
        }

        // Build instance-level dependency and find smallest non-singleton ample set.
        // Stubborn set closure: pick seed, expand with dependent instances.
        let mut best_ample: Option<Vec<usize>> = None;

        for seed in 0..n {
            let mut ample: HashSet<usize> = HashSet::new();
            let mut to_add = vec![seed];

            while let Some(idx_a) = to_add.pop() {
                if ample.insert(idx_a) {
                    let (act_a, ref params_a) = all_instances[idx_a];
                    for (idx_b, (act_b, params_b)) in all_instances.iter().enumerate() {
                        if ample.contains(&idx_b) {
                            continue;
                        }
                        // Check instance-level independence
                        let independent = if params_a.is_empty() || params_b.is_empty() {
                            // Non-refinable action represented as group: use template-level
                            self.spec.independent[act_a][*act_b]
                        } else {
                            self.instances_independent(act_a, params_a, *act_b, params_b)
                        };
                        if !independent {
                            to_add.push(idx_b);
                        }
                    }
                }
            }

            // BFS soundness: only use non-singleton ample sets
            if ample.len() > 1
                && (best_ample.is_none() || ample.len() < best_ample.as_ref().unwrap().len())
            {
                best_ample = Some(ample.into_iter().collect());
            }
        }

        if let Some(ample_indices) = best_ample {
            if ample_indices.len() < n {
                trace!(
                    total_instances = n,
                    ample = ample_indices.len(),
                    "POR instance-level: reduced instance set"
                );
            }
            let instances: Vec<(usize, Vec<Value>)> = ample_indices
                .into_iter()
                .map(|i| all_instances[i].clone())
                .collect();
            return Ok(AmpleResult::Instances(instances));
        }

        Ok(AmpleResult::Templates)
    }

    /// Resolve KeySource entries to concrete key values given action parameters.
    fn resolve_keys(sources: &[KeySource], params: &[Value]) -> SmallVec<[Value; 4]> {
        sources
            .iter()
            .map(|ks| match ks {
                KeySource::Param(idx) => params[*idx].clone(),
                KeySource::Literal(k) => Value::int(*k),
            })
            .collect()
    }

    /// Check if two resolved key sets are disjoint.
    /// Both sets are tiny (1-3 elements typically), so O(n*m) is fine.
    fn keys_disjoint(a: &[Value], b: &[Value]) -> bool {
        for ka in a {
            for kb in b {
                if ka == kb {
                    return false;
                }
            }
        }
        true
    }

    /// Check if two action instances are independent at the instance level.
    /// Returns true if the instances commute (disjoint key access on all shared variables).
    fn instances_independent(
        &self,
        act_a: usize,
        params_a: &[Value],
        act_b: usize,
        params_b: &[Value],
    ) -> bool {
        // Template-level independent => always independent
        if self.spec.independent[act_a][act_b] {
            return true;
        }
        // Not a refinable pair => must be dependent
        if !self.spec.refinable_pairs[act_a][act_b] {
            return false;
        }

        let action_a = &self.spec.actions[act_a];
        let action_b = &self.spec.actions[act_b];

        // For each shared variable, check key disjointness.
        // A variable is "shared" if one action writes it and the other reads or writes it.
        // We check: writes_a vs writes_b, writes_a vs reads_b, reads_a vs writes_b.
        for &(var_a, ref keys_a) in &action_a.write_key_params {
            let keys_a = match keys_a {
                Some(k) => k,
                None => return false, // unkeyed write => dependent
            };
            // Check against writes of b
            for &(var_b, ref keys_b) in &action_b.write_key_params {
                if var_a == var_b {
                    let keys_b = match keys_b {
                        Some(k) => k,
                        None => return false,
                    };
                    let resolved_a = Self::resolve_keys(keys_a, params_a);
                    let resolved_b = Self::resolve_keys(keys_b, params_b);
                    if !Self::keys_disjoint(&resolved_a, &resolved_b) {
                        return false;
                    }
                }
            }
            // Check against reads of b
            for &(var_b, ref keys_b) in &action_b.read_key_params {
                if var_a == var_b {
                    let keys_b = match keys_b {
                        Some(k) => k,
                        None => return false,
                    };
                    let resolved_a = Self::resolve_keys(keys_a, params_a);
                    let resolved_b = Self::resolve_keys(keys_b, params_b);
                    if !Self::keys_disjoint(&resolved_a, &resolved_b) {
                        return false;
                    }
                }
            }
        }
        // Check reads_a vs writes_b
        for &(var_a, ref keys_a) in &action_a.read_key_params {
            let keys_a = match keys_a {
                Some(k) => k,
                None => return false,
            };
            for &(var_b, ref keys_b) in &action_b.write_key_params {
                if var_a == var_b {
                    let keys_b = match keys_b {
                        Some(k) => k,
                        None => return false,
                    };
                    let resolved_a = Self::resolve_keys(keys_a, params_a);
                    let resolved_b = Self::resolve_keys(keys_b, params_b);
                    if !Self::keys_disjoint(&resolved_a, &resolved_b) {
                        return false;
                    }
                }
            }
        }

        true
    }

    /// Apply a single action instance (action_idx, params) to a state.
    /// Evaluates the effect and pushes the successor into buf.
    /// Simplified version of apply_action for a single parameter combination.
    fn apply_single_instance(
        &self,
        state: &State,
        action_idx: usize,
        params: &[Value],
        buf: &mut Vec<(State, usize, Vec<i64>)>,
        next_vars_buf: &mut Vec<Value>,
    ) -> CheckResult<()> {
        let action = &self.spec.actions[action_idx];

        let pvals = params_to_i64s(params);

        // Try bytecode effect path first
        if let Some(cached) = &self.cached_effects[action_idx] {
            if let Ok(result) = apply_effects_bytecode(
                state,
                params,
                &self.consts,
                &cached.compiled_assignments,
                cached.needs_reverify,
                next_vars_buf,
                &action.effect,
            ) {
                if let Some(next_state) = result {
                    buf.push((next_state, action_idx, pvals));
                }
                return Ok(());
            }
        }

        // Fallback: full eval path
        if let Ok(next_states) = self.find_next_states(state, action, params) {
            for next_state in next_states {
                buf.push((next_state, action_idx, pvals.clone()));
            }
        }
        Ok(())
    }

    /// Apply an action to a state and push successor states into buffer.
    /// Uses operation cache to skip redundant evaluations when the successor
    /// fingerprint is already in the seen set.
    fn apply_action(
        &self,
        state: &State,
        action_idx: usize,
        buf: &mut Vec<(State, usize, Vec<i64>)>,
        next_vars_buf: &mut Vec<Value>,
        cache: &mut OpCache,
        orbit_reps: &SmallVec<[Vec<usize>; 4]>,
    ) -> CheckResult<()> {
        let action = &self.spec.actions[action_idx];
        let dynamic;
        let orbit_filtered;
        let param_domains = if let Some(d) = self.get_effective_domains(action_idx, state) {
            dynamic = d;
            &dynamic
        } else if !orbit_reps.is_empty() {
            // Filter param domains to orbit representatives for symmetric params
            let sym_groups = &self.sym_param_groups[action_idx];
            if sym_groups.iter().any(|g| g.is_some()) {
                orbit_filtered = self.cached_param_domains[action_idx]
                    .iter()
                    .enumerate()
                    .map(|(param_idx, domain)| {
                        if let Some(group_idx) = sym_groups[param_idx] {
                            let reps = &orbit_reps[group_idx];
                            reps.iter()
                                .filter_map(|&rep| domain.get(rep).cloned())
                                .collect()
                        } else {
                            domain.clone()
                        }
                    })
                    .collect::<Vec<_>>();
                &orbit_filtered
            } else {
                &self.cached_param_domains[action_idx]
            }
        } else {
            &self.cached_param_domains[action_idx]
        };
        let guard_bc = &self.compiled_guards[action_idx];
        let reads = &action.reads;
        let changes = &action.changes;
        let use_cache = cache.is_enabled();

        // Precompute per-(state, action) hashes only when cache is active.
        let (write_old_hash, read_xor, parent_fp) = if use_cache {
            (
                xor_hash_vars(&state.vars, changes),
                xor_hash_vars(&state.vars, reads),
                state.fingerprint().as_u64(),
            )
        } else {
            (0, 0, 0)
        };

        // Use guard indexing when available for early parameter pruning
        if let Some(guard_index) = &self.guard_indices[action_idx] {
            // Check pre-guard (state-only conjuncts) once before enumeration
            if let Some(ref pre_guard) = guard_index.pre_guard {
                if !vm_eval_bool(pre_guard, &state.vars, &state.vars, &self.consts, &[])
                    .unwrap_or(false)
                {
                    return Ok(());
                }
            }

            let mut params_buf = vec![Value::none(); param_domains.len()];
            enumerate_params_indexed(
                param_domains,
                guard_index,
                guard_bc,
                &state.vars,
                &self.consts,
                &mut params_buf,
                0,
                &mut |params: &[Value]| {
                    // Guard already passed. Check operation cache.
                    if use_cache {
                        let key = op_cache_key(params, read_xor);
                        if let Some(cached_wnh) = cache.probe(key) {
                            if cached_wnh == OP_NO_SUCCESSOR {
                                return;
                            }
                            let predicted_fp = parent_fp ^ write_old_hash ^ cached_wnh;
                            if self.store.contains(&Fingerprint::from_u64(predicted_fp)) {
                                return;
                            }
                        }

                        // Cache miss or new state: evaluate effects
                        if let Some(cached) = &self.cached_effects[action_idx] {
                            if let Ok(result) = apply_effects_bytecode(
                                state,
                                params,
                                &self.consts,
                                &cached.compiled_assignments,
                                cached.needs_reverify,
                                next_vars_buf,
                                &action.effect,
                            ) {
                                if let Some(next_state) = result {
                                    cache.store(key, xor_hash_vars(&next_state.vars, changes));
                                    buf.push((next_state, action_idx, params_to_i64s(params)));
                                } else {
                                    cache.store(key, OP_NO_SUCCESSOR);
                                }
                                return;
                            }
                        }
                    } else {
                        // No cache: evaluate effects directly
                        if let Some(cached) = &self.cached_effects[action_idx] {
                            if let Ok(result) = apply_effects_bytecode(
                                state,
                                params,
                                &self.consts,
                                &cached.compiled_assignments,
                                cached.needs_reverify,
                                next_vars_buf,
                                &action.effect,
                            ) {
                                if let Some(next_state) = result {
                                    buf.push((next_state, action_idx, params_to_i64s(params)));
                                } else {
                                    // Guard reverification failed, no successor
                                }
                                return;
                            }
                        }
                    }

                    if let Ok(next_states) = self.find_next_states(state, action, params) {
                        let pvals = params_to_i64s(params);
                        for next_state in next_states {
                            buf.push((next_state, action_idx, pvals.clone()));
                        }
                    }
                },
            );
        } else {
            let mut params_buf = SmallVec::new();
            self.enumerate_params(param_domains, &mut params_buf, &mut |params: &[Value]| {
                if use_cache {
                    let key = op_cache_key(params, read_xor);
                    if let Some(cached_wnh) = cache.probe(key) {
                        if cached_wnh == OP_NO_SUCCESSOR {
                            return;
                        }
                        let predicted_fp = parent_fp ^ write_old_hash ^ cached_wnh;
                        if self.store.contains(&Fingerprint::from_u64(predicted_fp)) {
                            return;
                        }
                    }

                    let guard_ok =
                        vm_eval_bool(guard_bc, &state.vars, &state.vars, &self.consts, params)
                            .unwrap_or(false);
                    if !guard_ok {
                        cache.store(key, OP_NO_SUCCESSOR);
                        return;
                    }

                    if let Some(cached) = &self.cached_effects[action_idx] {
                        if let Ok(result) = apply_effects_bytecode(
                            state,
                            params,
                            &self.consts,
                            &cached.compiled_assignments,
                            cached.needs_reverify,
                            next_vars_buf,
                            &action.effect,
                        ) {
                            if let Some(next_state) = result {
                                cache.store(key, xor_hash_vars(&next_state.vars, changes));
                                buf.push((next_state, action_idx, params_to_i64s(params)));
                            } else {
                                cache.store(key, OP_NO_SUCCESSOR);
                            }
                            return;
                        }
                    }
                } else {
                    let guard_ok =
                        vm_eval_bool(guard_bc, &state.vars, &state.vars, &self.consts, params)
                            .unwrap_or(false);
                    if !guard_ok {
                        return;
                    }

                    if let Some(cached) = &self.cached_effects[action_idx] {
                        if let Ok(result) = apply_effects_bytecode(
                            state,
                            params,
                            &self.consts,
                            &cached.compiled_assignments,
                            cached.needs_reverify,
                            next_vars_buf,
                            &action.effect,
                        ) {
                            if let Some(next_state) = result {
                                buf.push((next_state, action_idx, params_to_i64s(params)));
                            }
                            return;
                        }
                    }
                }

                // Fallback: full eval path
                if let Ok(next_states) = self.find_next_states(state, action, params) {
                    let pvals = params_to_i64s(params);
                    for next_state in next_states {
                        buf.push((next_state, action_idx, pvals.clone()));
                    }
                }
            });
        }

        Ok(())
    }

    /// Enumerate all parameter combinations.
    fn enumerate_params<F>(
        &self,
        domains: &[Vec<Value>],
        buf: &mut SmallVec<[Value; 4]>,
        callback: &mut F,
    ) where
        F: FnMut(&[Value]),
    {
        let idx = buf.len();
        if idx >= domains.len() {
            callback(buf);
            return;
        }

        for value in &domains[idx] {
            buf.push(value.clone());
            self.enumerate_params(domains, buf, callback);
            buf.pop();
        }
    }

    /// Build effective parameter domains, substituting state-dependent domains at runtime.
    /// Returns None if no params are state-dependent (zero overhead fast path).
    fn get_effective_domains(&self, action_idx: usize, state: &State) -> Option<Vec<Vec<Value>>> {
        let deps = &self.state_dep_domains[action_idx];
        if !deps.iter().any(|d| d.is_some()) {
            return None;
        }
        let action = &self.spec.actions[action_idx];
        let static_domains = &self.cached_param_domains[action_idx];
        Some(
            static_domains
                .iter()
                .enumerate()
                .map(|(i, static_domain)| {
                    if let Some(var_idx) = deps[i] {
                        match state.vars[var_idx].as_set() {
                            Some(elems) => elems.to_vec(),
                            _ => {
                                // Non-Set runtime value: fall back to full type domain
                                // (static_domain is empty placeholder for state-dep params)
                                let (_, ty) = &action.params[i];
                                self.type_domain(ty)
                            }
                        }
                    } else {
                        static_domain.clone()
                    }
                })
                .collect(),
        )
    }

    /// Try to resolve a TypeExpr to a domain, evaluating constant references.
    fn resolve_type_expr_domain(&self, type_expr: &TypeExpr) -> Option<Vec<Value>> {
        match type_expr {
            TypeExpr::Range(lo, hi, _) => {
                let lo_val = self.eval_const_expr(lo)?;
                let hi_val = self.eval_const_expr(hi)?;
                Some((lo_val..=hi_val).map(Value::int).collect())
            }
            _ => None, // Other types fall through to type_domain
        }
    }

    /// Evaluate an expression that may reference constants.
    fn eval_const_expr(&self, expr: &specl_syntax::Expr) -> Option<i64> {
        match &expr.kind {
            ExprKind::Int(n) => Some(*n),
            ExprKind::Ident(name) => {
                // Look up constant by name
                for (i, c) in self.spec.consts.iter().enumerate() {
                    if c.name == *name {
                        return self.consts.get(i).and_then(|v| v.as_int());
                    }
                }
                None
            }
            _ => None, // Could extend to handle simple arithmetic
        }
    }

    /// Find all next states satisfying the effect relation.
    fn find_next_states(
        &self,
        state: &State,
        action: &CompiledAction,
        params: &[Value],
    ) -> CheckResult<Vec<State>> {
        // Try direct evaluation first (fast path)
        let mut buf = Vec::new();
        match apply_action_direct(
            state,
            action,
            params,
            &self.consts,
            self.spec.vars.len(),
            &mut buf,
        ) {
            Ok(Some(next_state)) => {
                return Ok(vec![next_state]);
            }
            Ok(None) => {
                // Guard not satisfied or effect not satisfied
                return Ok(vec![]);
            }
            Err(_) => {
                // Fall back to enumeration
                trace!(action = %action.name, "falling back to enumeration for successors");
            }
        }

        // Fallback: enumerate possible values for changed variables
        let changed_domains: Vec<Vec<Value>> = action
            .changes
            .iter()
            .map(|&idx| self.type_domain(&self.spec.vars[idx].ty))
            .collect();

        let mut next_states = Vec::new();

        self.enumerate_changed(
            &changed_domains,
            0,
            (*state.vars).clone(),
            &mut |next_vars: Vec<Value>| {
                let mut ctx = EvalContext::new(&state.vars, &next_vars, &self.consts, params);
                if eval(&action.effect, &mut ctx).ok().and_then(|v| v.as_bool()) == Some(true) {
                    next_states.push(State::new(next_vars));
                }
            },
            &action.changes,
        );

        Ok(next_states)
    }

    /// Enumerate changed variable combinations.
    fn enumerate_changed<F>(
        &self,
        domains: &[Vec<Value>],
        idx: usize,
        mut current: Vec<Value>,
        callback: &mut F,
        changes: &[usize],
    ) where
        F: FnMut(Vec<Value>),
    {
        if idx >= domains.len() {
            callback(current);
            return;
        }

        let var_idx = changes[idx];
        for value in &domains[idx] {
            current[var_idx] = value.clone();
            self.enumerate_changed(domains, idx + 1, current.clone(), callback, changes);
        }
    }

    /// Check if an invariant holds in a state using bytecode VM.
    fn check_invariant_bc(&self, inv_idx: usize, state: &State) -> CheckResult<bool> {
        let bc = &self.compiled_invariants[inv_idx];
        Ok(vm_eval_bool(
            bc,
            &state.vars,
            &state.vars,
            &self.consts,
            &[],
        )?)
    }

    /// Check if any action is enabled in a state.
    fn any_action_enabled(&self, state: &State) -> CheckResult<bool> {
        for (action_idx, action) in self.spec.actions.iter().enumerate() {
            if self.is_action_enabled(state, action, action_idx)? {
                return Ok(true);
            }
        }

        Ok(false)
    }

    /// Simulate a random trace through the state space.
    ///
    /// Picks one random enabled action per step. Checks invariants at each state.
    /// Returns the trace and outcome.
    pub fn simulate(&mut self, max_steps: usize, seed: u64) -> CheckResult<SimulateOutcome> {
        use rand::rngs::StdRng;
        use rand::seq::SliceRandom;
        use rand::SeedableRng;

        let mut rng = StdRng::seed_from_u64(seed);

        // Generate initial states, pick one randomly
        let initial_states = self.generate_initial_states()?;
        if initial_states.is_empty() {
            return Err(CheckError::NoInitialStates);
        }
        let state = initial_states.choose(&mut rng).unwrap().clone();

        let var_names: Vec<String> = self.spec.vars.iter().map(|v| v.name.clone()).collect();
        let mut trace: Vec<(State, Option<String>)> = vec![(state.clone(), None)];

        // Check invariants on initial state
        for (inv_idx, inv) in self.spec.invariants.iter().enumerate() {
            if !self.check_invariant_bc(inv_idx, &state)? {
                return Ok(SimulateOutcome::InvariantViolation {
                    invariant: inv.name.clone(),
                    trace,
                    var_names,
                });
            }
        }

        let mut current = state;
        let mut successors_buf: Vec<(State, usize, Vec<i64>)> = Vec::new();
        let mut next_vars_buf: Vec<Value> = Vec::new();

        for _step in 0..max_steps {
            // Generate all successors (no POR, no symmetry)
            self.generate_successors(&current, &mut successors_buf, &mut next_vars_buf, 0)?;

            if successors_buf.is_empty() {
                return Ok(SimulateOutcome::Deadlock { trace, var_names });
            }

            // Pick a random successor
            let (next_state, action_idx, pvals) = successors_buf.choose(&mut rng).unwrap().clone();

            let base_name = self.action_names[action_idx].clone();
            let action_name = if pvals.is_empty() {
                base_name
            } else {
                let param_str: Vec<String> = pvals.iter().map(|v| v.to_string()).collect();
                format!("{}({})", base_name, param_str.join(", "))
            };
            trace.push((next_state.clone(), Some(action_name)));

            // Check invariants
            for (inv_idx, inv) in self.spec.invariants.iter().enumerate() {
                if !self.check_invariant_bc(inv_idx, &next_state)? {
                    return Ok(SimulateOutcome::InvariantViolation {
                        invariant: inv.name.clone(),
                        trace,
                        var_names,
                    });
                }
            }

            current = next_state;
        }

        Ok(SimulateOutcome::Ok {
            steps: trace.len() - 1,
            trace,
            var_names,
        })
    }

    /// Check if the time limit has been exceeded.
    #[inline]
    fn past_deadline(&self) -> bool {
        self.deadline.is_some_and(|d| Instant::now() >= d)
    }

    /// Set an external stop flag (for swarm verification cancellation).
    pub fn set_stop_flag(&mut self, flag: Arc<AtomicBool>) {
        self.stop_flag = Some(flag);
    }

    /// Get the state store for inspection.
    pub fn store(&self) -> &StateStore {
        &self.store
    }

    /// Pre-seed the store with cached fingerprints for incremental checking.
    pub fn pre_seed_fingerprints(&self, fingerprints: &[u64]) {
        self.store.pre_seed_fingerprints(fingerprints);
    }

    /// Get profile data collected during checking (only available when config.profile is true).
    pub fn profile_data(&self) -> Option<&ProfileData> {
        self.profile_data.as_ref()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use specl_ir::compile;
    use specl_syntax::parse;

    fn check_spec(source: &str, consts: Vec<Value>) -> CheckResult<CheckOutcome> {
        check_spec_with_config(source, consts, CheckConfig::default())
    }

    fn check_spec_with_config(
        source: &str,
        consts: Vec<Value>,
        config: CheckConfig,
    ) -> CheckResult<CheckOutcome> {
        let module = parse(source).expect("parse failed");
        let spec = compile(&module).expect("compile failed");
        let mut explorer = Explorer::new(spec, consts, config);
        explorer.check()
    }

    #[test]
    fn test_simple_counter() {
        let source = r#"
module Counter
const MAX: 0..5
var count: 0..5
init { count == 0 }
action Inc() {
    require count < MAX
    count = count + 1
}
invariant Bounded { count <= MAX }
"#;

        // Disable deadlock checking since a bounded counter naturally deadlocks at MAX
        let config = CheckConfig {
            check_deadlock: false,
            ..Default::default()
        };
        let result = check_spec_with_config(source, vec![Value::int(3)], config);
        match result {
            Ok(CheckOutcome::Ok {
                states_explored, ..
            }) => {
                assert!(states_explored > 0);
                assert_eq!(states_explored, 4); // States: 0, 1, 2, 3
            }
            other => panic!("expected Ok, got {:?}", other),
        }
    }

    #[test]
    fn test_counter_deadlock() {
        let source = r#"
module Counter
const MAX: 0..5
var count: 0..5
init { count == 0 }
action Inc() {
    require count < MAX
    count = count + 1
}
"#;

        // With deadlock checking, should report deadlock when count reaches MAX
        let result = check_spec(source, vec![Value::int(2)]);
        match result {
            Ok(CheckOutcome::Deadlock { trace }) => {
                // Should deadlock after reaching count == 2
                assert!(!trace.is_empty());
            }
            other => panic!("expected Deadlock, got {:?}", other),
        }
    }

    #[test]
    fn test_invariant_violation() {
        let source = r#"
module BadCounter
const MAX: 0..5
var count: 0..10
init { count == 0 }
action Inc() {
    count = count + 1
}
invariant TooHigh { count <= 3 }
"#;

        let result = check_spec(source, vec![Value::int(5)]).unwrap();
        match result {
            CheckOutcome::InvariantViolation { invariant, trace } => {
                assert_eq!(invariant, "TooHigh");
                assert!(!trace.is_empty());
            }
            _ => panic!("expected invariant violation"),
        }
    }

    #[test]
    fn test_transfer_successors() {
        let source = r#"
module Test
var alice: 0..20
var bob: 0..20
init { alice == 10 and bob == 10 }
action BrokenDeposit() {
    bob = bob + 5
}
invariant MoneyConserved { alice + bob == 20 }
"#;
        let module = parse(source).unwrap();
        let spec = compile(&module).unwrap();

        println!("Spec vars: {:?}", spec.vars);
        println!("Spec actions: {:?}", spec.actions);

        let config = CheckConfig {
            check_deadlock: true,
            ..Default::default()
        };
        let mut explorer = Explorer::new(spec, vec![], config);
        let result = explorer.check();

        println!("Result: {:?}", result);
    }

    #[test]
    fn test_independence_matrix() {
        // Two counters x and y that are independent (different variables)
        let source = r#"
module TwoCounters
var x: 0..3
var y: 0..3
init { x == 0 and y == 0 }
action IncX() {
    require x < 3
    x = x + 1
}
action IncY() {
    require y < 3
    y = y + 1
}
"#;
        let module = parse(source).unwrap();
        let spec = compile(&module).unwrap();

        // Check that we have 2 actions
        assert_eq!(spec.actions.len(), 2);
        assert_eq!(spec.actions[0].name, "IncX");
        assert_eq!(spec.actions[1].name, "IncY");

        // Check reads and writes
        // IncX reads x (index 0), writes x (index 0)
        // IncY reads y (index 1), writes y (index 1)
        println!(
            "IncX changes: {:?}, reads: {:?}",
            spec.actions[0].changes, spec.actions[0].reads
        );
        println!(
            "IncY changes: {:?}, reads: {:?}",
            spec.actions[1].changes, spec.actions[1].reads
        );

        // Check independence matrix
        // IncX and IncY should be independent since they don't share variables
        println!("Independent matrix: {:?}", spec.independent);
        assert!(
            spec.independent[0][1],
            "IncX and IncY should be independent"
        );
        assert!(
            spec.independent[1][0],
            "IncY and IncX should be independent"
        );
    }

    #[test]
    fn test_por_reduces_states() {
        // With POR, exploring IncX->IncY is equivalent to IncY->IncX
        // So we should explore fewer states
        let source = r#"
module TwoCounters
var x: 0..2
var y: 0..2
init { x == 0 and y == 0 }
action IncX() {
    require x < 2
    x = x + 1
}
action IncY() {
    require y < 2
    y = y + 1
}
"#;
        // Without POR
        let config_no_por = CheckConfig {
            check_deadlock: false,
            use_por: false,
            parallel: false,
            ..Default::default()
        };
        let result_no_por = check_spec_with_config(source, vec![], config_no_por).unwrap();
        let states_no_por = match result_no_por {
            CheckOutcome::Ok {
                states_explored, ..
            } => states_explored,
            _ => panic!("expected Ok"),
        };

        // With POR
        let config_por = CheckConfig {
            check_deadlock: false,
            use_por: true,
            parallel: false,
            ..Default::default()
        };
        let result_por = check_spec_with_config(source, vec![], config_por).unwrap();
        let states_por = match result_por {
            CheckOutcome::Ok {
                states_explored, ..
            } => states_explored,
            _ => panic!("expected Ok"),
        };

        println!("States without POR: {}", states_no_por);
        println!("States with POR: {}", states_por);

        // Both should explore all reachable states (9 states: 3x3 grid)
        // But with POR, we should see the same number since all states are reachable
        // The reduction comes from exploring fewer transitions, not fewer states
        assert_eq!(states_no_por, 9, "Should have 9 states (3x3 grid)");
        assert_eq!(states_por, 9, "POR should also find all 9 states");
    }

    #[test]
    fn test_por_with_dependent_actions() {
        // Two counters where one action depends on the other's state
        // IncX increments x
        // IncY increments y but only if x > 0 (reads x)
        // These are DEPENDENT because IncX writes x and IncY reads x
        let source = r#"
module DependentCounters
var x: 0..2
var y: 0..2
init { x == 0 and y == 0 }
action IncX() {
    require x < 2
    x = x + 1
}
action IncY() {
    require y < 2
    require x > 0
    y = y + 1
}
"#;
        let module = parse(source).unwrap();
        let spec = compile(&module).unwrap();

        // IncX writes x, reads x
        // IncY writes y, reads x and y
        // They should be dependent because IncX writes x and IncY reads x
        println!(
            "IncX changes: {:?}, reads: {:?}",
            spec.actions[0].changes, spec.actions[0].reads
        );
        println!(
            "IncY changes: {:?}, reads: {:?}",
            spec.actions[1].changes, spec.actions[1].reads
        );
        println!("Independent matrix: {:?}", spec.independent);

        // Verify they are dependent
        assert!(!spec.independent[0][1], "IncX and IncY should be dependent");
        assert!(!spec.independent[1][0], "IncY and IncX should be dependent");

        // With dependent actions, POR should still find all reachable states
        // but may reduce transitions explored
        let config_por = CheckConfig {
            check_deadlock: false,
            use_por: true,
            parallel: false,
            ..Default::default()
        };
        let result = check_spec_with_config(source, vec![], config_por).unwrap();
        match result {
            CheckOutcome::Ok {
                states_explored, ..
            } => {
                println!("States with POR (dependent): {}", states_explored);
                // Should find states: (0,0), (1,0), (2,0), (1,1), (2,1), (2,2)
                // That's 6 reachable states (y can only increment when x > 0)
                assert!(states_explored >= 5, "Should find at least 5 states");
            }
            _ => panic!("expected Ok"),
        }
    }

    #[test]
    fn test_sleep_sets_find_all_states() {
        // Three independent counters: sleep sets should find all reachable states.
        // With sleep sets, successors inherit accumulated sleep, reducing redundant transitions
        // while still visiting every reachable state.
        let source = r#"
module ThreeCounters
var x: 0..2
var y: 0..2
var z: 0..2
init { x == 0 and y == 0 and z == 0 }
action IncX() {
    require x < 2
    x = x + 1
}
action IncY() {
    require y < 2
    y = y + 1
}
action IncZ() {
    require z < 2
    z = z + 1
}
"#;
        // Without POR (no sleep sets)
        let config_no_por = CheckConfig {
            check_deadlock: false,
            use_por: false,
            parallel: false,
            ..Default::default()
        };
        let result_no_por = check_spec_with_config(source, vec![], config_no_por).unwrap();
        let states_no_por = match result_no_por {
            CheckOutcome::Ok {
                states_explored, ..
            } => states_explored,
            _ => panic!("expected Ok"),
        };

        // With POR (includes sleep sets in sequential mode)
        let config_por = CheckConfig {
            check_deadlock: false,
            use_por: true,
            parallel: false,
            ..Default::default()
        };
        let result_por = check_spec_with_config(source, vec![], config_por).unwrap();
        let states_por = match result_por {
            CheckOutcome::Ok {
                states_explored, ..
            } => states_explored,
            _ => panic!("expected Ok"),
        };

        // All 27 states (3x3x3) must be found regardless of POR/sleep sets
        assert_eq!(states_no_por, 27, "Should have 27 states (3x3x3 grid)");
        assert_eq!(
            states_por, 27,
            "POR+sleep sets should also find all 27 states"
        );
    }

    #[test]
    fn test_symmetry_detection() {
        // Test that symmetry groups are detected for Dict[0..N, T] types
        let source = r#"
module SymmetricTest
var state: Dict[0..2, Bool]
var count: Dict[0..2, 0..3]
var other: Bool
init {
    state == {i: false for i in 0..2}
    and count == {i: 0 for i in 0..2}
    and other == true
}
action Toggle(i: 0..2) {
    state = state | { i: not state[i] }
}
"#;
        let module = parse(source).unwrap();
        let spec = compile(&module).unwrap();

        // Should detect one symmetry group with domain size 3 (0..2 means 0,1,2)
        // containing variables state and count
        println!("Symmetry groups: {:?}", spec.symmetry_groups);
        assert!(
            !spec.symmetry_groups.is_empty(),
            "Should detect symmetry groups"
        );

        // Find the group with domain size 3
        let group = spec.symmetry_groups.iter().find(|g| g.domain_size == 3);
        assert!(group.is_some(), "Should have a group with domain size 3");
        let group = group.unwrap();
        assert_eq!(
            group.variables.len(),
            2,
            "Should have 2 variables in the group"
        );
    }

    #[test]
    fn test_symmetry_reduces_states() {
        // Symmetric state space should be smaller with symmetry reduction
        let source = r#"
module SymmetricCounter
var state: Dict[0..2, Bool]
init { state == {i: false for i in 0..2} }
action Toggle(i: 0..2) {
    state = state | { i: not state[i] }
}
"#;
        // Without symmetry
        let config_no_sym = CheckConfig {
            check_deadlock: false,
            use_symmetry: false,
            parallel: false,
            ..Default::default()
        };
        let result_no_sym = check_spec_with_config(source, vec![], config_no_sym).unwrap();
        let states_no_sym = match result_no_sym {
            CheckOutcome::Ok {
                states_explored, ..
            } => states_explored,
            _ => panic!("expected Ok"),
        };

        // With symmetry
        let config_sym = CheckConfig {
            check_deadlock: false,
            use_symmetry: true,
            parallel: false,
            ..Default::default()
        };
        let result_sym = check_spec_with_config(source, vec![], config_sym).unwrap();
        let states_sym = match result_sym {
            CheckOutcome::Ok {
                states_explored, ..
            } => states_explored,
            _ => panic!("expected Ok"),
        };

        println!("States without symmetry: {}", states_no_sym);
        println!("States with symmetry: {}", states_sym);

        // Without symmetry: 2^3 = 8 states (each of 3 bools can be T/F)
        assert_eq!(states_no_sym, 8, "Should have 8 states without symmetry");

        // With symmetry: states are grouped by equivalence class
        // States differ by permutation of indices should be in same class
        // {F,F,F}, {T,F,F}/{F,T,F}/{F,F,T} -> 2 classes, {T,T,F}/{T,F,T}/{F,T,T} -> 1 class, {T,T,T} -> 1 class
        // Total: 4 equivalence classes
        assert!(
            states_sym < states_no_sym,
            "Symmetry should reduce state count"
        );
        assert!(
            states_sym >= 4,
            "Should have at least 4 equivalence classes"
        );
    }

    #[test]
    fn test_fast_check_finds_violation() {
        // Test that fast_check mode correctly finds violations and reconstructs traces
        let source = r#"
module BadCounter
var count: 0..10
init { count == 0 }
action Inc() {
    count = count + 1
}
invariant TooHigh { count <= 3 }
"#;

        let config = CheckConfig {
            check_deadlock: false,
            fast_check: true,
            parallel: false,
            ..Default::default()
        };
        let result = check_spec_with_config(source, vec![], config).unwrap();
        match result {
            CheckOutcome::InvariantViolation { invariant, trace } => {
                assert_eq!(invariant, "TooHigh");
                // Phase 2 should have reconstructed the trace
                assert!(!trace.is_empty(), "fast_check should reconstruct trace");
                assert!(trace.len() >= 4, "trace should show path to violation");
            }
            _ => panic!("expected invariant violation"),
        }
    }

    #[test]
    fn test_fast_check_ok_result() {
        // Test that fast_check mode works for specs with no violations
        let source = r#"
module SafeCounter
var count: 0..5
init { count == 0 }
action Inc() {
    require count < 3
    count = count + 1
}
invariant InRange { count <= 5 }
"#;

        let config = CheckConfig {
            check_deadlock: false,
            fast_check: true,
            parallel: false,
            ..Default::default()
        };
        let result = check_spec_with_config(source, vec![], config).unwrap();
        match result {
            CheckOutcome::Ok {
                states_explored, ..
            } => {
                assert_eq!(states_explored, 4, "should explore 4 states: 0,1,2,3");
            }
            _ => panic!("expected Ok"),
        }
    }

    #[test]
    fn test_large_domain_symmetry() {
        // Test symmetry reduction with domain size > 6 (previously unsupported)
        // Using 0..9 gives 10 elements - would be 10! = 3,628,800 permutations
        // The new O(n log n) algorithm handles this efficiently
        let source = r#"
module LargeSymmetry
var flags: Dict[0..9, Bool]
init { flags == {i: false for i in 0..9} }
action SetFlag(i: 0..9) {
    require flags[i] == false
    flags = flags | { i: true }
}
"#;
        // Without symmetry: 2^10 = 1024 states
        let config_no_sym = CheckConfig {
            check_deadlock: false,
            use_symmetry: false,
            parallel: false,
            max_states: 2000, // Limit to avoid long test
            ..Default::default()
        };
        let result_no_sym = check_spec_with_config(source, vec![], config_no_sym).unwrap();
        let states_no_sym = match result_no_sym {
            CheckOutcome::Ok {
                states_explored, ..
            } => states_explored,
            _ => panic!("expected Ok"),
        };

        // With symmetry: should have much fewer equivalence classes
        let config_sym = CheckConfig {
            check_deadlock: false,
            use_symmetry: true,
            parallel: false,
            max_states: 2000,
            ..Default::default()
        };
        let result_sym = check_spec_with_config(source, vec![], config_sym).unwrap();
        let states_sym = match result_sym {
            CheckOutcome::Ok {
                states_explored, ..
            } => states_explored,
            _ => panic!("expected Ok"),
        };

        println!("States without symmetry (10 flags): {}", states_no_sym);
        println!("States with symmetry (10 flags): {}", states_sym);

        // Symmetry should significantly reduce state count
        // With 10 boolean flags, states are characterized by the NUMBER of true flags
        // So equivalence classes: 0, 1, 2, ..., 10 flags set = 11 classes
        assert!(
            states_sym < states_no_sym,
            "Symmetry should reduce state count"
        );
        assert!(
            states_sym <= 15,
            "Should have at most ~11-15 equivalence classes (0-10 flags set)"
        );
    }

    #[test]
    fn test_orbit_representatives_same_state_count() {
        // With orbit representatives, the same canonical states should be found
        // as without them. The difference is fewer transitions explored.
        // 5 processes with a boolean flag = 2^5=32 states without symmetry,
        // 6 equivalence classes with symmetry (0..5 flags set).
        let source = r#"
module OrbitTest
var flags: Dict[0..4, Bool]
init { flags == {i: false for i in 0..4} }
action SetFlag(i: 0..4) {
    require flags[i] == false
    flags = flags | { i: true }
}
"#;
        let config = CheckConfig {
            check_deadlock: false,
            use_symmetry: true,
            parallel: false,
            ..Default::default()
        };
        let result = check_spec_with_config(source, vec![], config).unwrap();
        let states = match result {
            CheckOutcome::Ok {
                states_explored, ..
            } => states_explored,
            _ => panic!("expected Ok"),
        };

        // 6 equivalence classes: 0,1,2,3,4,5 flags set
        assert_eq!(
            states, 6,
            "orbit representatives + symmetry should find exactly 6 equivalence classes"
        );
    }

    #[test]
    fn test_symmetry_soundness_warning_fires() {
        // Spec where process 0 is treated specially — symmetry is unsound
        let source = r#"
module AsymmetricSpec
var role: Dict[0..2, 0..2]
init { role == {i: 0 for i in 0..2} }
action Promote(i: 0..2) {
    require i == 0
    role = role | { i: 1 }
}
"#;
        let module = parse(source).unwrap();
        let spec = compile(&module).unwrap();
        assert!(
            !spec.symmetry_groups.is_empty(),
            "should detect symmetry groups"
        );

        let warnings = Explorer::find_symmetry_warnings(&spec);
        assert!(
            !warnings.is_empty(),
            "should warn about literal index 0 in guard of asymmetric action"
        );
        assert!(
            warnings.iter().any(|w| w.contains("Promote")),
            "warning should mention the action name"
        );
    }

    #[test]
    fn test_symmetry_soundness_no_warning_for_symmetric_spec() {
        // Fully symmetric spec — no warnings expected
        let source = r#"
module SymmetricSpec
var role: Dict[0..2, 0..2]
init { role == {i: 0 for i in 0..2} }
action Promote(i: 0..2) {
    require role[i] == 0
    role = role | { i: 1 }
}
"#;
        let module = parse(source).unwrap();
        let spec = compile(&module).unwrap();
        assert!(!spec.symmetry_groups.is_empty());

        let warnings = Explorer::find_symmetry_warnings(&spec);
        assert!(
            warnings.is_empty(),
            "symmetric spec should produce no warnings, got: {:?}",
            warnings
        );
    }

    #[test]
    fn test_por_and_symmetry_combined() {
        // Verify that POR + symmetry together find the same states as no reduction.
        // Spec: 4 processes, each can toggle independently. Symmetric.
        let source = r#"
module PorSymCombined
var flags: Dict[0..3, Bool]
init { flags == {i: false for i in 0..3} }
action Toggle(i: 0..3) {
    flags = flags | { i: not flags[i] }
}
"#;
        // Baseline: no reductions
        let config_none = CheckConfig {
            check_deadlock: false,
            use_por: false,
            use_symmetry: false,
            parallel: false,
            ..Default::default()
        };
        let states_none = match check_spec_with_config(source, vec![], config_none).unwrap() {
            CheckOutcome::Ok {
                states_explored, ..
            } => states_explored,
            other => panic!("expected Ok, got {:?}", other),
        };

        // POR only
        let config_por = CheckConfig {
            check_deadlock: false,
            use_por: true,
            use_symmetry: false,
            parallel: false,
            ..Default::default()
        };
        let states_por = match check_spec_with_config(source, vec![], config_por).unwrap() {
            CheckOutcome::Ok {
                states_explored, ..
            } => states_explored,
            other => panic!("expected Ok, got {:?}", other),
        };

        // Symmetry only
        let config_sym = CheckConfig {
            check_deadlock: false,
            use_por: false,
            use_symmetry: true,
            parallel: false,
            ..Default::default()
        };
        let states_sym = match check_spec_with_config(source, vec![], config_sym).unwrap() {
            CheckOutcome::Ok {
                states_explored, ..
            } => states_explored,
            other => panic!("expected Ok, got {:?}", other),
        };

        // POR + Symmetry
        let config_both = CheckConfig {
            check_deadlock: false,
            use_por: true,
            use_symmetry: true,
            parallel: false,
            ..Default::default()
        };
        let states_both = match check_spec_with_config(source, vec![], config_both).unwrap() {
            CheckOutcome::Ok {
                states_explored, ..
            } => states_explored,
            other => panic!("expected Ok, got {:?}", other),
        };

        // 4 bools = 16 states without reduction
        assert_eq!(states_none, 16, "baseline: 2^4 = 16 states");
        // POR should find all 16 (these actions all read+write flags, so POR has limited effect here)
        assert_eq!(states_por, 16, "POR should find all 16 states");
        // Symmetry: 5 equivalence classes (0,1,2,3,4 flags set)
        assert_eq!(states_sym, 5, "symmetry: 5 equivalence classes");
        // POR + symmetry: same 5 classes
        assert_eq!(
            states_both, 5,
            "POR + symmetry should find same 5 equivalence classes"
        );
    }

    #[test]
    fn test_por_and_symmetry_with_independent_actions() {
        // Spec with both symmetry and truly independent actions.
        // Two separate groups of processes: each group has its own variable.
        let source = r#"
module PorSymIndependent
var x: 0..3
var flags: Dict[0..2, Bool]
init { x == 0 and flags == {i: false for i in 0..2} }
action IncX() {
    require x < 3
    x = x + 1
}
action Toggle(i: 0..2) {
    flags = flags | { i: not flags[i] }
}
"#;
        // Baseline: no reductions
        let config_none = CheckConfig {
            check_deadlock: false,
            use_por: false,
            use_symmetry: false,
            parallel: false,
            ..Default::default()
        };
        let states_none = match check_spec_with_config(source, vec![], config_none).unwrap() {
            CheckOutcome::Ok {
                states_explored, ..
            } => states_explored,
            other => panic!("expected Ok, got {:?}", other),
        };

        // POR + Symmetry
        let config_both = CheckConfig {
            check_deadlock: false,
            use_por: true,
            use_symmetry: true,
            parallel: false,
            ..Default::default()
        };
        let states_both = match check_spec_with_config(source, vec![], config_both).unwrap() {
            CheckOutcome::Ok {
                states_explored, ..
            } => states_explored,
            other => panic!("expected Ok, got {:?}", other),
        };

        // x: 0..3 = 4 values, flags: 2^3 = 8 states, total = 32
        // Symmetry reduces flags to 4 equivalence classes (0,1,2,3 set)
        // So with symmetry: 4 * 4 = 16 states
        assert_eq!(states_none, 32, "baseline: 4 * 8 = 32 states");
        assert_eq!(
            states_both, 16,
            "POR + symmetry should find 4*4 = 16 canonical states"
        );
    }

    #[test]
    fn test_parametric_independence_detection() {
        // Transfer spec: Transfer writes balance[from] and balance[to].
        // Transfer(0,1) and Transfer(1,0) share key 0 and key 1 — dependent.
        // The pair (Transfer, Transfer) should be marked as refinable.
        let source = r#"
module Transfer
const N: Int
var balance: Dict[0..N, Int]
init { balance == {i: 10 for i in 0..N} }
action Transfer(from: 0..N, to: 0..N) {
    require from != to
    require balance[from] >= 1
    balance = balance | { from: balance[from] - 1, to: balance[to] + 1 }
}
"#;
        let module = parse(source).unwrap();
        let spec = compile(&module).unwrap();

        assert_eq!(spec.actions.len(), 1, "one action template");
        assert_eq!(spec.actions[0].name, "Transfer");

        // Transfer writes balance (keyed by params from and to)
        let write_keys = &spec.actions[0].write_key_params;
        assert!(!write_keys.is_empty(), "should have write key info");
        // Should have keyed write (not None)
        for (_, keys) in write_keys {
            assert!(keys.is_some(), "write should be keyed");
        }

        // Transfer reads balance (keyed by params from and to)
        let read_keys = &spec.actions[0].read_key_params;
        assert!(!read_keys.is_empty(), "should have read key info");
        for (_, keys) in read_keys {
            assert!(keys.is_some(), "read should be keyed");
        }

        // Transfer(0,0) is template-dependent with Transfer(0,0)
        assert!(
            !spec.independent[0][0],
            "Transfer-Transfer is template-dependent"
        );
        // But it's refinable (keyed Dict access)
        assert!(
            spec.refinable_pairs[0][0],
            "Transfer-Transfer should be refinable"
        );
    }

    #[test]
    fn test_parametric_por_correctness() {
        // Transfer spec with N=1: instance-level POR should find the same
        // states as no POR. This is a correctness check.
        // 0..N with N=1 gives domain {0, 1} = 2 accounts.
        let source = r#"
module Transfer
const N: Int
var balance: Dict[0..N, Int]
init { balance == {i: 5 for i in 0..N} }
action Transfer(from: 0..N, to: 0..N) {
    require from != to
    require balance[from] >= 1
    balance = balance | { from: balance[from] - 1, to: balance[to] + 1 }
}
"#;
        // Without POR
        let config_no_por = CheckConfig {
            check_deadlock: false,
            use_por: false,
            parallel: false,
            ..Default::default()
        };
        let result_no_por =
            check_spec_with_config(source, vec![Value::int(1)], config_no_por).unwrap();
        let states_no_por = match result_no_por {
            CheckOutcome::Ok {
                states_explored, ..
            } => states_explored,
            _ => panic!("expected Ok"),
        };

        // With POR (instance-level will activate since refinable_pairs exist)
        let config_por = CheckConfig {
            check_deadlock: false,
            use_por: true,
            parallel: false,
            ..Default::default()
        };
        let result_por = check_spec_with_config(source, vec![Value::int(1)], config_por).unwrap();
        let states_por = match result_por {
            CheckOutcome::Ok {
                states_explored, ..
            } => states_explored,
            _ => panic!("expected Ok"),
        };

        // N=1 with balance sum=10, 2 accounts: states = 11 (balance[0] can be 0..10)
        assert_eq!(states_no_por, 11);
        // POR should find the same states (only one action template with 2 accounts,
        // Transfer(0,1) and Transfer(1,0) share key 0 and 1, so both are dependent)
        assert_eq!(states_por, states_no_por);
    }

    #[test]
    fn test_parametric_por_reduces_independent_transfers() {
        // Three accounts (0..2 = {0,1,2}), transfer between disjoint pairs should
        // be independent. Transfer(0,1) and Transfer(2,0) share key 0 — dependent.
        // Transfer(0,1) and Transfer(2,_) with no overlap — independent.
        // Instance-level POR should find the same reachable states as no POR.
        let source = r#"
module MultiTransfer
const N: Int
var balance: Dict[0..N, Int]
init { balance == {i: 3 for i in 0..N} }
action Transfer(from: 0..N, to: 0..N) {
    require from != to
    require balance[from] >= 1
    balance = balance | { from: balance[from] - 1, to: balance[to] + 1 }
}
"#;
        // Without POR
        let config_no_por = CheckConfig {
            check_deadlock: false,
            use_por: false,
            parallel: false,
            ..Default::default()
        };
        let result_no_por =
            check_spec_with_config(source, vec![Value::int(2)], config_no_por).unwrap();
        let states_no_por = match result_no_por {
            CheckOutcome::Ok {
                states_explored, ..
            } => states_explored,
            _ => panic!("expected Ok"),
        };

        // With POR (instance-level POR should detect disjoint transfers)
        let config_por = CheckConfig {
            check_deadlock: false,
            use_por: true,
            parallel: false,
            ..Default::default()
        };
        let result_por = check_spec_with_config(source, vec![Value::int(2)], config_por).unwrap();
        let states_por = match result_por {
            CheckOutcome::Ok {
                states_explored, ..
            } => states_explored,
            _ => panic!("expected Ok"),
        };

        println!(
            "N=2 (3 accounts) transfer: no POR={}, POR={}",
            states_no_por, states_por
        );
        // Both must find the same set of reachable states (correctness check)
        assert_eq!(states_por, states_no_por);
    }

    #[test]
    fn test_parametric_por_degenerate_no_dicts() {
        // Spec with no Dict variables. has_refinable_pairs should be false,
        // behavior identical to template POR.
        let source = r#"
module NoDicts
var x: 0..3
var y: 0..3
init { x == 0 and y == 0 }
action IncX() {
    require x < 3
    x = x + 1
}
action IncY() {
    require y < 3
    y = y + 1
}
"#;
        let module = parse(source).unwrap();
        let spec = compile(&module).unwrap();

        // No refinable pairs (no Dict-keyed actions)
        let has_refinable = spec
            .refinable_pairs
            .iter()
            .any(|row| row.iter().any(|&v| v));
        assert!(!has_refinable, "no refinable pairs for non-Dict spec");

        // POR should still work normally (template-level)
        let config = CheckConfig {
            check_deadlock: false,
            use_por: true,
            parallel: false,
            ..Default::default()
        };
        let result = check_spec_with_config(source, vec![], config).unwrap();
        match result {
            CheckOutcome::Ok {
                states_explored, ..
            } => {
                assert_eq!(states_explored, 16, "4x4 grid of states");
            }
            other => panic!("expected Ok, got {:?}", other),
        }
    }

    #[test]
    fn test_parametric_por_unkeyed_write() {
        // Spec where a variable is written without FnUpdate (e.g., x = x + 1).
        // The write should be unkeyed, so refinable_pairs should be false for
        // pairs involving that action.
        let source = r#"
module Mixed
var x: 0..3
var balance: Dict[0..2, Int]
init { x == 0 and balance == {i: 5 for i in 0..2} }
action IncX() {
    require x < 3
    x = x + 1
}
action Transfer(from: 0..2, to: 0..2) {
    require from != to
    require balance[from] >= 1
    balance = balance | { from: balance[from] - 1, to: balance[to] + 1 }
}
"#;
        let module = parse(source).unwrap();
        let spec = compile(&module).unwrap();

        assert_eq!(spec.actions.len(), 2);
        // IncX-Transfer: IncX writes x, Transfer writes balance.
        // They touch different variables, so they're template-independent.
        assert!(
            spec.independent[0][1],
            "IncX and Transfer are template-independent"
        );
        // Transfer-Transfer: same as before, should be refinable
        assert!(
            spec.refinable_pairs[1][1],
            "Transfer-Transfer should be refinable"
        );
        // IncX-IncX: writes unkeyed x, not refinable (but also self-dependent)
        assert!(
            !spec.refinable_pairs[0][0],
            "IncX-IncX should not be refinable"
        );

        // Verify POR still works with this mixed spec
        let config = CheckConfig {
            check_deadlock: false,
            use_por: true,
            parallel: false,
            ..Default::default()
        };
        let result = check_spec_with_config(source, vec![], config).unwrap();
        match result {
            CheckOutcome::Ok {
                states_explored, ..
            } => {
                assert!(states_explored > 0);
            }
            other => panic!("expected Ok, got {:?}", other),
        }
    }
}

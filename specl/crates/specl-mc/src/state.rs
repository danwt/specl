//! State representation and fingerprinting for model checking.

use specl_eval::Value;
use specl_ir::SymmetryGroup;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

/// A fingerprint is a 64-bit hash identifying a state.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Fingerprint(u64);

impl Fingerprint {
    #[inline]
    pub fn as_u64(self) -> u64 {
        self.0
    }

    #[inline]
    pub fn from_u64(v: u64) -> Self {
        Fingerprint(v)
    }
}

impl fmt::Debug for Fingerprint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Fingerprint({:016x})", self.0)
    }
}

impl fmt::Display for Fingerprint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:016x}", self.0)
    }
}

/// Hash a single variable at a given position.
/// Specialized fast path for Int/Bool (dominant types in protocol specs)
/// using splitmix64-style mixing. Falls back to AHash for composite types.
#[inline]
pub(crate) fn hash_var(idx: usize, val: &Value) -> u64 {
    match val {
        Value::Int(n) => {
            let h = ((idx as u64) ^ 0x2d358dccaa6c78a5).wrapping_mul(0x9e3779b97f4a7c15);
            let h = (h ^ (*n as u64)).wrapping_mul(0x517cc1b727220a95);
            h ^ (h >> 32)
        }
        Value::Bool(b) => {
            let h = ((idx as u64) ^ 0x2d358dccaa6c78a5).wrapping_mul(0x9e3779b97f4a7c15);
            let h = (h ^ (*b as u64)).wrapping_mul(0x517cc1b727220a95);
            h ^ (h >> 32)
        }
        _ => {
            let mut hasher = ahash::AHasher::default();
            idx.hash(&mut hasher);
            val.hash(&mut hasher);
            hasher.finish()
        }
    }
}

/// Compute a decomposable fingerprint from variable values.
/// fp = XOR of hash_var(i, var[i]) for all i.
fn compute_fingerprint(vars: &[Value]) -> Fingerprint {
    let mut h: u64 = 0;
    for (i, var) in vars.iter().enumerate() {
        h ^= hash_var(i, var);
    }
    Fingerprint(h)
}

/// Update a fingerprint after changing a single variable.
#[inline]
pub fn update_fingerprint(
    fp: Fingerprint,
    idx: usize,
    old_val: &Value,
    new_val: &Value,
) -> Fingerprint {
    Fingerprint(fp.0 ^ hash_var(idx, old_val) ^ hash_var(idx, new_val))
}

/// A state in the model, represented as a vector of variable values.
/// Uses Arc for cheap cloning — State::clone() is an atomic increment,
/// not a deep copy of the entire variable tree.
/// Fingerprint is cached at construction time.
#[derive(Debug, Clone)]
pub struct State {
    /// Variable values indexed by variable index.
    pub vars: Arc<Vec<Value>>,
    /// Cached fingerprint (XOR-based decomposable hash).
    fp: Fingerprint,
}

impl PartialEq for State {
    fn eq(&self, other: &Self) -> bool {
        self.fp == other.fp && self.vars == other.vars
    }
}

impl Eq for State {}

impl State {
    /// Create a new state from variable values.
    pub fn new(vars: Vec<Value>) -> Self {
        let fp = compute_fingerprint(&vars);
        Self {
            vars: Arc::new(vars),
            fp,
        }
    }

    /// Create a state with a pre-computed fingerprint (for incremental construction).
    pub fn with_fingerprint(vars: Vec<Value>, fp: Fingerprint) -> Self {
        Self {
            vars: Arc::new(vars),
            fp,
        }
    }

    /// Create an empty state with the given number of variables.
    pub fn empty(num_vars: usize) -> Self {
        let vars = vec![Value::None; num_vars];
        Self::new(vars)
    }

    /// Get the cached fingerprint.
    #[inline]
    pub fn fingerprint(&self) -> Fingerprint {
        self.fp
    }

    /// Get the number of variables.
    pub fn num_vars(&self) -> usize {
        self.vars.len()
    }

    /// Compute the canonical form of this state under the given symmetry groups.
    /// Two states that are equivalent under symmetry will have the same canonical form.
    pub fn canonicalize(&self, groups: &[SymmetryGroup]) -> State {
        if groups.is_empty() {
            return self.clone();
        }

        let mut vars = (*self.vars).clone();

        for group in groups {
            if group.domain_size == 0 || group.variables.is_empty() {
                continue;
            }

            // Use O(n log n) greedy algorithm for all domain sizes
            let perm = compute_canonical_permutation(&vars, group);
            apply_permutation(&mut vars, group, &perm);
        }

        State::new(vars)
    }
}

/// Compute a canonical permutation using greedy sorting.
///
/// Algorithm:
/// 1. For each element i in the domain, compute its "signature" - the tuple
///    of values (var[0][i], var[1][i], ...) across all symmetric variables
/// 2. Sort elements by their signatures
/// 3. The canonical permutation maps each element to its sorted position
///
/// Complexity: O(n log n) instead of O(n!)
/// Build serialized signatures for each domain element across all symmetric variables.
/// signature[i] = serialized values for element i across all vars in the group.
fn build_signatures(vars: &[Value], group: &SymmetryGroup) -> Vec<Vec<Vec<u8>>> {
    (0..group.domain_size)
        .map(|i| {
            group
                .variables
                .iter()
                .map(|&var_idx| match &vars[var_idx] {
                    Value::IntMap(arr) => {
                        if i < arr.len() {
                            Value::Int(arr[i]).to_bytes()
                        } else {
                            vec![]
                        }
                    }
                    Value::Fn(map) => Value::fn_get(map, &Value::Int(i as i64))
                        .map(|v| v.to_bytes())
                        .unwrap_or_default(),
                    _ => vec![],
                })
                .collect()
        })
        .collect()
}

fn compute_canonical_permutation(vars: &[Value], group: &SymmetryGroup) -> Vec<usize> {
    let n = group.domain_size;

    let mut signatures: Vec<(Vec<Vec<u8>>, usize)> = build_signatures(vars, group)
        .into_iter()
        .enumerate()
        .map(|(i, sig)| (sig, i))
        .collect();

    signatures.sort_by(|a, b| a.0.cmp(&b.0));

    let mut perm = vec![0; n];
    for (new_idx, (_, old_idx)) in signatures.iter().enumerate() {
        perm[*old_idx] = new_idx;
    }

    perm
}

/// Compute orbit representatives for a canonical state.
///
/// In a canonical state, elements are sorted by signature. Elements with identical
/// signatures (tied) are interchangeable under symmetry. Returns the set of
/// representative domain elements — the first element of each tied group.
///
/// Example: domain 0..4, signatures [A, A, B, B, C] -> representatives = {0, 2, 4}
pub fn orbit_representatives(vars: &[Value], group: &SymmetryGroup) -> Vec<usize> {
    let n = group.domain_size;
    if n == 0 {
        return vec![];
    }

    let signatures = build_signatures(vars, group);

    // Since state is canonical, signatures are already sorted.
    // Pick one representative per distinct signature.
    let mut reps = vec![0];
    for i in 1..n {
        if signatures[i] != signatures[i - 1] {
            reps.push(i);
        }
    }
    reps
}

/// Apply a permutation to the variables in a symmetry group.
fn apply_permutation(vars: &mut [Value], group: &SymmetryGroup, perm: &[usize]) {
    for &var_idx in &group.variables {
        match &vars[var_idx] {
            Value::IntMap(arr) => {
                let mut new_arr = vec![0i64; arr.len()];
                for (old_idx, val) in arr.iter().enumerate() {
                    let new_idx = perm.get(old_idx).copied().unwrap_or(old_idx);
                    new_arr[new_idx] = *val;
                }
                vars[var_idx] = Value::IntMap(Arc::new(new_arr));
            }
            Value::Fn(map) => {
                let mut new_map: Vec<(Value, Value)> = map
                    .iter()
                    .map(|(key, value)| {
                        if let Value::Int(k) = key {
                            let new_key = perm.get(*k as usize).copied().unwrap_or(*k as usize);
                            (Value::Int(new_key as i64), value.clone())
                        } else {
                            (key.clone(), value.clone())
                        }
                    })
                    .collect();
                new_map.sort_by(|a, b| a.0.cmp(&b.0));
                vars[var_idx] = Value::Fn(Arc::new(new_map));
            }
            _ => {}
        }
    }
}

impl fmt::Display for State {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        for (i, v) in self.vars.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", v)?;
        }
        write!(f, "]")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_state_fingerprint() {
        let s1 = State::new(vec![Value::Int(1), Value::Int(2)]);
        let s2 = State::new(vec![Value::Int(1), Value::Int(2)]);
        let s3 = State::new(vec![Value::Int(1), Value::Int(3)]);

        assert_eq!(s1.fingerprint(), s2.fingerprint());
        assert_ne!(s1.fingerprint(), s3.fingerprint());
    }

    #[test]
    fn test_state_display() {
        let s = State::new(vec![Value::Int(42), Value::Bool(true)]);
        assert_eq!(s.to_string(), "[42, true]");
    }

    #[test]
    fn test_incremental_fingerprint() {
        // Build state: [10, 20, 30]
        let s = State::new(vec![Value::Int(10), Value::Int(20), Value::Int(30)]);

        // Change var[1] from 20 to 99
        let new_fp = update_fingerprint(s.fingerprint(), 1, &Value::Int(20), &Value::Int(99));
        let expected = State::new(vec![Value::Int(10), Value::Int(99), Value::Int(30)]);

        assert_eq!(new_fp, expected.fingerprint());
    }

    #[test]
    fn test_incremental_fingerprint_multiple_changes() {
        let s = State::new(vec![Value::Int(1), Value::Int(2), Value::Int(3)]);

        // Change var[0] from 1 to 10, then var[2] from 3 to 30
        let fp1 = update_fingerprint(s.fingerprint(), 0, &Value::Int(1), &Value::Int(10));
        let fp2 = update_fingerprint(fp1, 2, &Value::Int(3), &Value::Int(30));
        let expected = State::new(vec![Value::Int(10), Value::Int(2), Value::Int(30)]);

        assert_eq!(fp2, expected.fingerprint());
    }

    #[test]
    fn test_cached_fingerprint() {
        let s = State::new(vec![Value::Int(42), Value::Bool(true)]);
        // Fingerprint should be consistent
        assert_eq!(s.fingerprint(), s.fingerprint());

        // with_fingerprint should use the provided fingerprint
        let fp = s.fingerprint();
        let s2 = State::with_fingerprint(vec![Value::Int(42), Value::Bool(true)], fp);
        assert_eq!(s.fingerprint(), s2.fingerprint());
        assert_eq!(s, s2);
    }
}

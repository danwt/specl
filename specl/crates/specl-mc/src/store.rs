//! State storage for model checking.

use crate::bloom::BloomFilter;
use crate::fpset::AtomicFPSet;
use crate::state::{Fingerprint, FingerprintBuildHasher, State};
use crate::tree_table::TreeTable;
use dashmap::DashMap;
use specl_eval::Value;
use std::cell::UnsafeCell;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;
use tracing::error;

/// Information about how a state was reached.
#[derive(Debug, Clone)]
pub struct StateInfo {
    /// The actual state (stored for trace reconstruction).
    pub state: State,
    /// Predecessor fingerprint (None for initial states).
    pub predecessor: Option<Fingerprint>,
    /// Index of the action that led to this state (None for initial states).
    pub action_idx: Option<usize>,
    /// Parameter values used when firing the action (for trace display).
    pub param_values: Option<Vec<i64>>,
    /// Depth from initial state.
    pub depth: usize,
}

/// Compressed state info for collapse compression mode.
/// Stores interned variable IDs instead of full Value objects.
#[derive(Clone)]
struct CompressedStateInfo {
    /// Interned variable IDs (one per variable position).
    compressed_vars: Vec<u32>,
    /// Predecessor fingerprint (None for initial states).
    predecessor: Option<Fingerprint>,
    /// Index of the action that led to this state.
    action_idx: Option<usize>,
    /// Parameter values used when firing the action.
    param_values: Option<Vec<i64>>,
    /// Depth from initial state.
    depth: usize,
}

/// Per-variable intern table for collapse compression.
/// Maps each variable position's distinct values to small integer IDs.
struct CollapseTable {
    /// Forward mapping: Value -> intern_id (per variable position).
    forward: Vec<DashMap<Value, u32>>,
    /// Reverse mapping: intern_id -> Value (per variable position).
    /// Append-only during exploration; reads for trace reconstruction.
    reverse: Vec<Mutex<Vec<Value>>>,
}

impl CollapseTable {
    fn new(num_vars: usize) -> Self {
        Self {
            forward: (0..num_vars).map(|_| DashMap::new()).collect(),
            reverse: (0..num_vars).map(|_| Mutex::new(Vec::new())).collect(),
        }
    }

    /// Intern a value at variable position `var_idx`, returning its ID.
    fn intern(&self, var_idx: usize, value: &Value) -> u32 {
        // Fast path: already interned
        if let Some(id) = self.forward[var_idx].get(value) {
            return *id;
        }
        // Slow path: intern under lock
        let mut reverse = self.reverse[var_idx].lock().unwrap();
        // Double-check after acquiring lock (another thread may have interned)
        if let Some(id) = self.forward[var_idx].get(value) {
            return *id;
        }
        let id = reverse.len() as u32;
        reverse.push(value.clone());
        self.forward[var_idx].insert(value.clone(), id);
        id
    }

    /// Look up the value for a given intern ID at variable position `var_idx`.
    fn lookup(&self, var_idx: usize, id: u32) -> Value {
        let reverse = self.reverse[var_idx].lock().unwrap();
        reverse[id as usize].clone()
    }

    /// Decompress a compressed state back to full values.
    fn decompress(&self, compressed: &[u32]) -> Vec<Value> {
        compressed
            .iter()
            .enumerate()
            .map(|(i, &id)| self.lookup(i, id))
            .collect()
    }
}

/// Compressed state info for tree compression mode.
/// Stores a single root node ID instead of the full state vector.
#[derive(Clone)]
struct TreeStateInfo {
    /// Root node ID in the tree table.
    root_id: u32,
    /// Predecessor fingerprint (None for initial states).
    predecessor: Option<Fingerprint>,
    /// Index of the action that led to this state.
    action_idx: Option<usize>,
    /// Parameter values used when firing the action.
    param_values: Option<Vec<i64>>,
    /// Depth from initial state.
    depth: usize,
}

/// Storage mode for state deduplication.
enum StorageBackend {
    /// Full tracking: DashMap stores complete state info for trace reconstruction.
    Full,
    /// Fingerprint-only: lockless AtomicFPSet for minimal memory (8 bytes/state).
    /// Wrapped in UnsafeCell to allow grow() from &self between batches.
    Fingerprint(UnsafeCell<AtomicFPSet>),
    /// Bloom filter: fixed memory, probabilistic deduplication for bug finding.
    Bloom(BloomFilter),
    /// Collapse compression: per-variable interning stores Vec<u32> per state.
    /// ~3-6x less memory than Full mode while supporting trace reconstruction.
    Collapse {
        compressed: DashMap<Fingerprint, CompressedStateInfo, FingerprintBuildHasher>,
        table: CollapseTable,
    },
    /// Tree compression (LTSmin-style): hierarchical hash table decomposes states
    /// into shared subtrees. Better compression than Collapse when states share
    /// common sub-vectors of variables.
    Tree {
        compressed: DashMap<Fingerprint, TreeStateInfo, FingerprintBuildHasher>,
        table: TreeTable,
    },
}

/// Thread-safe state storage using a single sharded hash map.
///
/// Supports five modes:
/// - Full tracking: Stores complete state info for trace reconstruction
/// - Fingerprint-only: Uses lockless AtomicFPSet for minimal memory and zero contention
/// - Bloom filter: Fixed memory probabilistic deduplication for bug finding
/// - Collapse compression: Per-variable interning for reduced memory with full traces
/// - Tree compression: LTSmin-style hierarchical hash table for maximum compression with traces
pub struct StateStore {
    /// Full tracking mode: map from fingerprint to state info.
    states: DashMap<Fingerprint, StateInfo, FingerprintBuildHasher>,
    /// Storage backend for deduplication.
    backend: StorageBackend,
    /// Number of hash collisions detected (different states, same fingerprint).
    collisions: AtomicUsize,
    /// Cached state count — incremented atomically on insert, avoids DashMap::len() overhead.
    count: AtomicUsize,
}

// SAFETY: AtomicFPSet uses AtomicU64 internally, which is Sync.
// BloomFilter uses AtomicU64 internally, which is Sync.
// The UnsafeCell is only mutated via maybe_grow_fpset() which is called
// between parallel batches when no concurrent access is happening.
// Collapse uses DashMap + Mutex, both Sync.
unsafe impl Sync for StateStore {}
unsafe impl Send for StateStore {}

impl StateStore {
    /// Create a new state store with full tracking enabled.
    pub fn new() -> Self {
        Self::with_tracking(true)
    }

    /// Create a state store with specified tracking mode.
    pub fn with_tracking(full_tracking: bool) -> Self {
        Self {
            states: DashMap::with_hasher(FingerprintBuildHasher),
            backend: if full_tracking {
                StorageBackend::Full
            } else {
                StorageBackend::Fingerprint(UnsafeCell::new(AtomicFPSet::new(1 << 23)))
            },
            collisions: AtomicUsize::new(0),
            count: AtomicUsize::new(0),
        }
    }

    /// Create a state store using a bloom filter with specified bit count and hash functions.
    pub fn with_bloom(log2_bits: u32, num_hashes: u32) -> Self {
        Self {
            states: DashMap::with_hasher(FingerprintBuildHasher),
            backend: StorageBackend::Bloom(BloomFilter::from_log2_bits(log2_bits, num_hashes)),
            collisions: AtomicUsize::new(0),
            count: AtomicUsize::new(0),
        }
    }

    /// Create a state store with collapse compression.
    /// `num_vars` is the number of state variables (for intern table sizing).
    pub fn with_collapse(num_vars: usize) -> Self {
        Self {
            states: DashMap::with_hasher(FingerprintBuildHasher),
            backend: StorageBackend::Collapse {
                compressed: DashMap::with_hasher(FingerprintBuildHasher),
                table: CollapseTable::new(num_vars),
            },
            collisions: AtomicUsize::new(0),
            count: AtomicUsize::new(0),
        }
    }

    /// Create a state store with tree compression (LTSmin-style).
    /// `num_vars` is the number of state variables.
    pub fn with_tree(num_vars: usize) -> Self {
        Self {
            states: DashMap::with_hasher(FingerprintBuildHasher),
            backend: StorageBackend::Tree {
                compressed: DashMap::with_hasher(FingerprintBuildHasher),
                table: TreeTable::new(num_vars),
            },
            collisions: AtomicUsize::new(0),
            count: AtomicUsize::new(0),
        }
    }

    /// Create a state store with pre-allocated capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            states: DashMap::with_capacity_and_hasher(capacity, FingerprintBuildHasher),
            backend: StorageBackend::Full,
            collisions: AtomicUsize::new(0),
            count: AtomicUsize::new(0),
        }
    }

    /// Check if a state has been seen before.
    #[inline]
    pub fn contains(&self, fp: &Fingerprint) -> bool {
        match &self.backend {
            StorageBackend::Full => self.states.contains_key(fp),
            StorageBackend::Fingerprint(cell) => {
                // SAFETY: contains() only reads AtomicU64 slots, safe with concurrent inserts
                unsafe { &*cell.get() }.contains(*fp)
            }
            StorageBackend::Bloom(bloom) => bloom.contains(*fp),
            StorageBackend::Collapse { ref compressed, .. } => compressed.contains_key(fp),
            StorageBackend::Tree { ref compressed, .. } => compressed.contains_key(fp),
        }
    }

    /// Try to insert a new state. Returns true if the state was new.
    /// Uses a single DashMap entry() call for atomic check-and-insert.
    pub fn insert(
        &self,
        state: State,
        predecessor: Option<Fingerprint>,
        action_idx: Option<usize>,
        param_values: Option<Vec<i64>>,
        depth: usize,
    ) -> bool {
        let fp = state.fingerprint();
        self.insert_with_fp(fp, state, predecessor, action_idx, param_values, depth)
    }

    /// Try to insert with a pre-computed fingerprint. Returns true if the state was new.
    pub fn insert_with_fp(
        &self,
        fp: Fingerprint,
        state: State,
        predecessor: Option<Fingerprint>,
        action_idx: Option<usize>,
        param_values: Option<Vec<i64>>,
        depth: usize,
    ) -> bool {
        match &self.backend {
            StorageBackend::Full => {
                use dashmap::mapref::entry::Entry;
                match self.states.entry(fp) {
                    Entry::Occupied(occupied) => {
                        if occupied.get().state != state {
                            let n = self.collisions.fetch_add(1, Ordering::Relaxed);
                            if n == 0 {
                                error!(
                                    fingerprint = %fp,
                                    "hash collision detected: different states share fingerprint, results may be unsound"
                                );
                            }
                        }
                        false
                    }
                    Entry::Vacant(entry) => {
                        entry.insert(StateInfo {
                            state,
                            predecessor,
                            action_idx,
                            param_values,
                            depth,
                        });
                        self.count.fetch_add(1, Ordering::Relaxed);
                        true
                    }
                }
            }
            StorageBackend::Fingerprint(cell) => {
                // SAFETY: insert() uses atomic CAS, safe with concurrent inserts
                let new = unsafe { &*cell.get() }.insert(fp);
                if new {
                    self.count.fetch_add(1, Ordering::Relaxed);
                }
                new
            }
            StorageBackend::Bloom(bloom) => {
                let new = bloom.insert(fp);
                if new {
                    self.count.fetch_add(1, Ordering::Relaxed);
                }
                new
            }
            StorageBackend::Collapse {
                ref compressed,
                ref table,
            } => {
                use dashmap::mapref::entry::Entry;
                let compressed_vars: Vec<u32> = state
                    .vars
                    .iter()
                    .enumerate()
                    .map(|(i, v)| table.intern(i, v))
                    .collect();
                match compressed.entry(fp) {
                    Entry::Occupied(occupied) => {
                        if occupied.get().compressed_vars != compressed_vars {
                            let n = self.collisions.fetch_add(1, Ordering::Relaxed);
                            if n == 0 {
                                error!(
                                    fingerprint = %fp,
                                    "hash collision detected: different states share fingerprint, results may be unsound"
                                );
                            }
                        }
                        false
                    }
                    Entry::Vacant(entry) => {
                        entry.insert(CompressedStateInfo {
                            compressed_vars,
                            predecessor,
                            action_idx,
                            param_values,
                            depth,
                        });
                        self.count.fetch_add(1, Ordering::Relaxed);
                        true
                    }
                }
            }
            StorageBackend::Tree {
                ref compressed,
                ref table,
            } => {
                use dashmap::mapref::entry::Entry;
                let root_id = table.insert(&state.vars);
                match compressed.entry(fp) {
                    Entry::Occupied(occupied) => {
                        if occupied.get().root_id != root_id {
                            let n = self.collisions.fetch_add(1, Ordering::Relaxed);
                            if n == 0 {
                                error!(
                                    fingerprint = %fp,
                                    "hash collision detected: different states share fingerprint, results may be unsound"
                                );
                            }
                        }
                        false
                    }
                    Entry::Vacant(entry) => {
                        entry.insert(TreeStateInfo {
                            root_id,
                            predecessor,
                            action_idx,
                            param_values,
                            depth,
                        });
                        self.count.fetch_add(1, Ordering::Relaxed);
                        true
                    }
                }
            }
        }
    }

    /// Insert by fingerprint only (no state data stored).
    /// For use with Fingerprint and Bloom backends where the state is not needed.
    /// Returns true if the fingerprint was new.
    #[inline]
    pub fn insert_fp_only(&self, fp: Fingerprint) -> bool {
        match &self.backend {
            StorageBackend::Fingerprint(cell) => {
                let new = unsafe { &*cell.get() }.insert(fp);
                if new {
                    self.count.fetch_add(1, Ordering::Relaxed);
                }
                new
            }
            StorageBackend::Bloom(bloom) => {
                let new = bloom.insert(fp);
                if new {
                    self.count.fetch_add(1, Ordering::Relaxed);
                }
                new
            }
            _ => panic!("insert_fp_only called on backend that requires state data"),
        }
    }

    /// Get the number of states stored. O(1) via cached atomic counter.
    #[inline]
    pub fn len(&self) -> usize {
        self.count.load(Ordering::Relaxed)
    }

    /// Check if the store is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Grow the fingerprint set if load factor exceeds threshold.
    /// Only applicable in fingerprint-only mode (no-op for other backends).
    ///
    /// # Safety contract
    /// Must be called when no concurrent inserts are happening (e.g., between
    /// parallel batches, or in single-threaded mode). The caller guarantees this.
    pub fn maybe_grow_fpset(&self) {
        if let StorageBackend::Fingerprint(ref cell) = self.backend {
            // SAFETY: should_grow() only reads an atomic counter
            let fpset = unsafe { &*cell.get() };
            if fpset.should_grow() {
                // SAFETY: Caller guarantees no concurrent inserts during grow.
                // Called between par_iter batches or in single-threaded mode.
                unsafe { &mut *cell.get() }.grow();
            }
        }
    }

    /// Check if full tracking is enabled (trace reconstruction supported).
    #[inline]
    pub fn has_full_tracking(&self) -> bool {
        matches!(
            self.backend,
            StorageBackend::Full | StorageBackend::Collapse { .. } | StorageBackend::Tree { .. }
        )
    }

    /// Check if bloom filter mode is enabled.
    #[inline]
    pub fn is_bloom(&self) -> bool {
        matches!(self.backend, StorageBackend::Bloom(_))
    }

    /// Get bloom filter false positive rate estimate (None if not in bloom mode).
    pub fn bloom_fp_rate(&self) -> Option<f64> {
        if let StorageBackend::Bloom(ref bloom) = self.backend {
            Some(bloom.estimated_fp_rate())
        } else {
            None
        }
    }

    /// Get bloom filter memory usage in bytes (None if not in bloom mode).
    pub fn bloom_memory_bytes(&self) -> Option<usize> {
        if let StorageBackend::Bloom(ref bloom) = self.backend {
            Some(bloom.memory_bytes())
        } else {
            None
        }
    }

    /// Get the number of hash collisions detected.
    #[inline]
    pub fn collisions(&self) -> usize {
        self.collisions.load(Ordering::Relaxed)
    }

    /// Get state info by fingerprint.
    /// Returns None if fingerprint not found or if full tracking is disabled.
    pub fn get(&self, fp: &Fingerprint) -> Option<StateInfo> {
        match &self.backend {
            StorageBackend::Full => self.states.get(fp).map(|r| r.value().clone()),
            StorageBackend::Collapse {
                ref compressed,
                ref table,
            } => compressed.get(fp).map(|r| {
                let info = r.value();
                let vars = table.decompress(&info.compressed_vars);
                StateInfo {
                    state: State::with_fingerprint(vars, *fp),
                    predecessor: info.predecessor,
                    action_idx: info.action_idx,
                    param_values: info.param_values.clone(),
                    depth: info.depth,
                }
            }),
            StorageBackend::Tree {
                ref compressed,
                ref table,
            } => compressed.get(fp).map(|r| {
                let info = r.value();
                let vars = table.reconstruct(info.root_id);
                StateInfo {
                    state: State::with_fingerprint(vars, *fp),
                    predecessor: info.predecessor,
                    action_idx: info.action_idx,
                    param_values: info.param_values.clone(),
                    depth: info.depth,
                }
            }),
            _ => None,
        }
    }

    /// Reconstruct a trace from an initial state to the given fingerprint.
    /// Action names are resolved using the provided action name list.
    /// Parameter values are appended to action names when available.
    /// Returns empty trace if full tracking is disabled.
    pub fn trace_to(
        &self,
        fp: &Fingerprint,
        action_names: &[String],
    ) -> Vec<(State, Option<String>)> {
        if !self.has_full_tracking() {
            return vec![];
        }

        let mut trace = Vec::new();
        let mut current = Some(*fp);

        while let Some(cfp) = current {
            if let Some(info) = self.get(&cfp) {
                let name = info.action_idx.map(|idx| {
                    let base = action_names
                        .get(idx)
                        .cloned()
                        .unwrap_or_else(|| format!("action_{}", idx));
                    if let Some(ref params) = info.param_values {
                        if params.is_empty() {
                            base
                        } else {
                            let param_str: Vec<String> =
                                params.iter().map(|v| v.to_string()).collect();
                            format!("{}({})", base, param_str.join(", "))
                        }
                    } else {
                        base
                    }
                });
                trace.push((info.state, name));
                current = info.predecessor;
            } else {
                break;
            }
        }

        trace.reverse();
        trace
    }

    /// Get all seen fingerprints.
    pub fn seen_fingerprints(&self) -> Vec<u64> {
        match &self.backend {
            StorageBackend::Full => self.states.iter().map(|r| r.key().as_u64()).collect(),
            StorageBackend::Collapse { ref compressed, .. } => {
                compressed.iter().map(|r| r.key().as_u64()).collect()
            }
            StorageBackend::Tree { ref compressed, .. } => {
                compressed.iter().map(|r| r.key().as_u64()).collect()
            }
            StorageBackend::Fingerprint(cell) => {
                let fpset = unsafe { &*cell.get() };
                fpset.fingerprints()
            }
            StorageBackend::Bloom(_) => Vec::new(),
        }
    }

    /// Pre-seed the store with cached fingerprints for incremental checking.
    /// Inserts fingerprints so that `is_known` returns true for previously explored states.
    pub fn pre_seed_fingerprints(&self, fingerprints: &[u64]) {
        match &self.backend {
            StorageBackend::Fingerprint(cell) => {
                let fpset = unsafe { &*cell.get() };
                for &fp in fingerprints {
                    fpset.insert(Fingerprint::from_u64(fp));
                }
            }
            StorageBackend::Bloom(bloom) => {
                for &fp in fingerprints {
                    bloom.insert(Fingerprint::from_u64(fp));
                }
            }
            _ => {
                // Full and Collapse modes can't be pre-seeded without state data.
                // Incremental checking is only effective with --fast or --bloom.
            }
        }
    }

    /// Clear the store and optionally change tracking mode.
    pub fn clear(&mut self, full_tracking: bool) {
        self.states.clear();
        self.collisions.store(0, Ordering::Relaxed);
        if full_tracking {
            self.backend = StorageBackend::Full;
        } else {
            self.backend = StorageBackend::Fingerprint(UnsafeCell::new(AtomicFPSet::new(1 << 23)));
        }
    }
}

impl Default for StateStore {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_store_insert() {
        let store = StateStore::new();
        let s1 = State::new(vec![Value::int(1)]);
        let s2 = State::new(vec![Value::int(2)]);

        assert!(store.insert(s1.clone(), None, None, None, 0));
        assert!(!store.insert(s1.clone(), None, None, None, 0)); // duplicate
        assert!(store.insert(s2, None, None, None, 0));

        assert_eq!(store.len(), 2);
    }

    #[test]
    fn test_trace_reconstruction() {
        let store = StateStore::new();

        let s0 = State::new(vec![Value::int(0)]);
        let s1 = State::new(vec![Value::int(1)]);
        let s2 = State::new(vec![Value::int(2)]);

        let fp0 = s0.fingerprint();
        let fp1 = s1.fingerprint();
        let fp2 = s2.fingerprint();

        store.insert(s0, None, Some(0), None, 0);
        store.insert(s1, Some(fp0), Some(1), Some(vec![1]), 1);
        store.insert(s2, Some(fp1), Some(2), Some(vec![2]), 2);

        let action_names = vec!["init".to_string(), "step1".to_string(), "step2".to_string()];
        let trace = store.trace_to(&fp2, &action_names);
        assert_eq!(trace.len(), 3);
        assert_eq!(*trace[0].0.vars, vec![Value::int(0)]);
        assert_eq!(*trace[1].0.vars, vec![Value::int(1)]);
        assert_eq!(*trace[2].0.vars, vec![Value::int(2)]);
    }

    #[test]
    fn test_fingerprint_only_mode() {
        let store = StateStore::with_tracking(false);
        let s1 = State::new(vec![Value::int(1)]);
        let s2 = State::new(vec![Value::int(2)]);

        // Should still track uniqueness
        assert!(store.insert(s1.clone(), None, None, None, 0));
        assert!(!store.insert(s1.clone(), None, None, None, 0)); // duplicate
        assert!(store.insert(s2, None, None, None, 0));
        assert_eq!(store.len(), 2);

        // But shouldn't be able to get state info
        let fp1 = State::new(vec![Value::int(1)]).fingerprint();
        assert!(store.get(&fp1).is_none());

        // Trace should be empty
        assert!(store.trace_to(&fp1, &[]).is_empty());
    }

    #[test]
    fn test_bloom_mode() {
        let store = StateStore::with_bloom(20, 3); // 1M bits
        let s1 = State::new(vec![Value::int(1)]);
        let s2 = State::new(vec![Value::int(2)]);

        assert!(store.insert(s1.clone(), None, None, None, 0));
        // Bloom filter: second insert should return false (probably seen)
        assert!(!store.insert(s1.clone(), None, None, None, 0));
        assert!(store.insert(s2, None, None, None, 0));
        assert_eq!(store.len(), 2);
        assert!(store.is_bloom());
        assert!(!store.has_full_tracking());

        // Trace not supported
        let fp1 = State::new(vec![Value::int(1)]).fingerprint();
        assert!(store.trace_to(&fp1, &[]).is_empty());
    }

    #[test]
    fn test_concurrent_insert() {
        use std::sync::Arc;
        use std::thread;

        let store = Arc::new(StateStore::new());
        let mut handles = vec![];

        // Spawn multiple threads inserting states
        for t in 0..4 {
            let store = Arc::clone(&store);
            handles.push(thread::spawn(move || {
                for i in 0..100 {
                    let value = (t * 1000 + i) as i64;
                    let state = State::new(vec![Value::int(value)]);
                    store.insert(state, None, None, None, 0);
                }
            }));
        }

        for handle in handles {
            handle.join().unwrap();
        }

        // Should have 400 unique states
        assert_eq!(store.len(), 400);
    }

    #[test]
    fn test_collapse_insert_and_dedup() {
        let store = StateStore::with_collapse(2);
        let s1 = State::new(vec![Value::int(1), Value::bool(true)]);
        let s2 = State::new(vec![Value::int(2), Value::bool(false)]);

        assert!(store.insert(s1.clone(), None, None, None, 0));
        assert!(!store.insert(s1.clone(), None, None, None, 0)); // duplicate
        assert!(store.insert(s2, None, None, None, 0));
        assert_eq!(store.len(), 2);
        assert!(store.has_full_tracking());
    }

    #[test]
    fn test_collapse_trace_reconstruction() {
        let store = StateStore::with_collapse(1);

        let s0 = State::new(vec![Value::int(0)]);
        let s1 = State::new(vec![Value::int(1)]);
        let s2 = State::new(vec![Value::int(2)]);

        let fp0 = s0.fingerprint();
        let fp1 = s1.fingerprint();
        let fp2 = s2.fingerprint();

        store.insert(s0, None, Some(0), None, 0);
        store.insert(s1, Some(fp0), Some(1), Some(vec![1]), 1);
        store.insert(s2, Some(fp1), Some(2), Some(vec![2]), 2);

        let action_names = vec!["init".to_string(), "step1".to_string(), "step2".to_string()];
        let trace = store.trace_to(&fp2, &action_names);
        assert_eq!(trace.len(), 3);
        assert_eq!(*trace[0].0.vars, vec![Value::int(0)]);
        assert_eq!(*trace[1].0.vars, vec![Value::int(1)]);
        assert_eq!(*trace[2].0.vars, vec![Value::int(2)]);
    }

    #[test]
    fn test_collapse_interning_shares_values() {
        let store = StateStore::with_collapse(2);

        // Insert many states that share values at position 1
        for i in 0..100 {
            let state = State::new(vec![Value::int(i), Value::bool(i % 2 == 0)]);
            store.insert(state, None, None, None, 0);
        }
        assert_eq!(store.len(), 100);

        // Position 1 only has 2 distinct values (true, false)
        if let StorageBackend::Collapse { ref table, .. } = store.backend {
            let rev1 = table.reverse[1].lock().unwrap();
            assert_eq!(rev1.len(), 2);
            // Position 0 has 100 distinct values
            let rev0 = table.reverse[0].lock().unwrap();
            assert_eq!(rev0.len(), 100);
        } else {
            panic!("expected Collapse backend");
        }
    }

    #[test]
    fn test_collapse_concurrent_insert() {
        use std::sync::Arc;
        use std::thread;

        let store = Arc::new(StateStore::with_collapse(1));
        let mut handles = vec![];

        for t in 0..4 {
            let store = Arc::clone(&store);
            handles.push(thread::spawn(move || {
                for i in 0..100 {
                    let value = (t * 1000 + i) as i64;
                    let state = State::new(vec![Value::int(value)]);
                    store.insert(state, None, None, None, 0);
                }
            }));
        }

        for handle in handles {
            handle.join().unwrap();
        }

        assert_eq!(store.len(), 400);
    }
}

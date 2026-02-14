//! State storage for model checking.

use crate::bloom::BloomFilter;
use crate::fpset::AtomicFPSet;
use crate::state::{Fingerprint, State};
use dashmap::DashMap;
use std::cell::UnsafeCell;
use std::collections::HashSet;
use std::sync::atomic::{AtomicUsize, Ordering};
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

/// Storage mode for state deduplication.
enum StorageBackend {
    /// Full tracking: DashMap stores complete state info for trace reconstruction.
    Full,
    /// Fingerprint-only: lockless AtomicFPSet for minimal memory (8 bytes/state).
    /// Wrapped in UnsafeCell to allow grow() from &self between batches.
    Fingerprint(UnsafeCell<AtomicFPSet>),
    /// Bloom filter: fixed memory, probabilistic deduplication for bug finding.
    Bloom(BloomFilter),
}

/// Thread-safe state storage using a single sharded hash map.
///
/// Supports three modes:
/// - Full tracking: Stores complete state info for trace reconstruction
/// - Fingerprint-only: Uses lockless AtomicFPSet for minimal memory and zero contention
/// - Bloom filter: Fixed memory probabilistic deduplication for bug finding
pub struct StateStore {
    /// Full tracking mode: map from fingerprint to state info.
    states: DashMap<Fingerprint, StateInfo>,
    /// Storage backend for deduplication.
    backend: StorageBackend,
    /// Number of hash collisions detected (different states, same fingerprint).
    collisions: AtomicUsize,
}

// SAFETY: AtomicFPSet uses AtomicU64 internally, which is Sync.
// BloomFilter uses AtomicU64 internally, which is Sync.
// The UnsafeCell is only mutated via maybe_grow_fpset() which is called
// between parallel batches when no concurrent access is happening.
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
            states: DashMap::new(),
            backend: if full_tracking {
                StorageBackend::Full
            } else {
                StorageBackend::Fingerprint(UnsafeCell::new(AtomicFPSet::new(1 << 23)))
            },
            collisions: AtomicUsize::new(0),
        }
    }

    /// Create a state store using a bloom filter with specified bit count and hash functions.
    pub fn with_bloom(log2_bits: u32, num_hashes: u32) -> Self {
        Self {
            states: DashMap::new(),
            backend: StorageBackend::Bloom(BloomFilter::from_log2_bits(log2_bits, num_hashes)),
            collisions: AtomicUsize::new(0),
        }
    }

    /// Create a state store with pre-allocated capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            states: DashMap::with_capacity(capacity),
            backend: StorageBackend::Full,
            collisions: AtomicUsize::new(0),
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
                        true
                    }
                }
            }
            StorageBackend::Fingerprint(cell) => {
                // SAFETY: insert() uses atomic CAS, safe with concurrent inserts
                unsafe { &*cell.get() }.insert(fp)
            }
            StorageBackend::Bloom(bloom) => bloom.insert(fp),
        }
    }

    /// Get the number of states stored.
    #[inline]
    pub fn len(&self) -> usize {
        match &self.backend {
            StorageBackend::Full => self.states.len(),
            StorageBackend::Fingerprint(cell) => unsafe { &*cell.get() }.len(),
            StorageBackend::Bloom(bloom) => bloom.len(),
        }
    }

    /// Check if the store is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Grow the fingerprint set if load factor exceeds threshold.
    /// Only applicable in fingerprint-only mode (no-op for bloom and full tracking).
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

    /// Check if full tracking is enabled.
    #[inline]
    pub fn has_full_tracking(&self) -> bool {
        matches!(self.backend, StorageBackend::Full)
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
        self.states.get(fp).map(|r| r.value().clone())
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
    pub fn seen_fingerprints(&self) -> HashSet<Fingerprint> {
        if self.has_full_tracking() {
            self.states.iter().map(|r| *r.key()).collect()
        } else {
            // Not supported for AtomicFPSet or BloomFilter (no iteration)
            HashSet::new()
        }
    }

    /// Clear the store and optionally change tracking mode.
    pub fn clear(&mut self, full_tracking: bool) {
        self.states.clear();
        self.collisions.store(0, Ordering::Relaxed);
        if full_tracking {
            self.backend = StorageBackend::Full;
        } else {
            self.backend =
                StorageBackend::Fingerprint(UnsafeCell::new(AtomicFPSet::new(1 << 23)));
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
    use specl_eval::Value;

    #[test]
    fn test_store_insert() {
        let store = StateStore::new();
        let s1 = State::new(vec![Value::Int(1)]);
        let s2 = State::new(vec![Value::Int(2)]);

        assert!(store.insert(s1.clone(), None, None, None, 0));
        assert!(!store.insert(s1.clone(), None, None, None, 0)); // duplicate
        assert!(store.insert(s2, None, None, None, 0));

        assert_eq!(store.len(), 2);
    }

    #[test]
    fn test_trace_reconstruction() {
        let store = StateStore::new();

        let s0 = State::new(vec![Value::Int(0)]);
        let s1 = State::new(vec![Value::Int(1)]);
        let s2 = State::new(vec![Value::Int(2)]);

        let fp0 = s0.fingerprint();
        let fp1 = s1.fingerprint();
        let fp2 = s2.fingerprint();

        store.insert(s0, None, Some(0), None, 0);
        store.insert(s1, Some(fp0), Some(1), Some(vec![1]), 1);
        store.insert(s2, Some(fp1), Some(2), Some(vec![2]), 2);

        let action_names = vec!["init".to_string(), "step1".to_string(), "step2".to_string()];
        let trace = store.trace_to(&fp2, &action_names);
        assert_eq!(trace.len(), 3);
        assert_eq!(*trace[0].0.vars, vec![Value::Int(0)]);
        assert_eq!(*trace[1].0.vars, vec![Value::Int(1)]);
        assert_eq!(*trace[2].0.vars, vec![Value::Int(2)]);
    }

    #[test]
    fn test_fingerprint_only_mode() {
        let store = StateStore::with_tracking(false);
        let s1 = State::new(vec![Value::Int(1)]);
        let s2 = State::new(vec![Value::Int(2)]);

        // Should still track uniqueness
        assert!(store.insert(s1.clone(), None, None, None, 0));
        assert!(!store.insert(s1.clone(), None, None, None, 0)); // duplicate
        assert!(store.insert(s2, None, None, None, 0));
        assert_eq!(store.len(), 2);

        // But shouldn't be able to get state info
        let fp1 = State::new(vec![Value::Int(1)]).fingerprint();
        assert!(store.get(&fp1).is_none());

        // Trace should be empty
        assert!(store.trace_to(&fp1, &[]).is_empty());
    }

    #[test]
    fn test_bloom_mode() {
        let store = StateStore::with_bloom(20, 3); // 1M bits
        let s1 = State::new(vec![Value::Int(1)]);
        let s2 = State::new(vec![Value::Int(2)]);

        assert!(store.insert(s1.clone(), None, None, None, 0));
        // Bloom filter: second insert should return false (probably seen)
        assert!(!store.insert(s1.clone(), None, None, None, 0));
        assert!(store.insert(s2, None, None, None, 0));
        assert_eq!(store.len(), 2);
        assert!(store.is_bloom());
        assert!(!store.has_full_tracking());

        // Trace not supported
        let fp1 = State::new(vec![Value::Int(1)]).fingerprint();
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
                    let state = State::new(vec![Value::Int(value)]);
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
}

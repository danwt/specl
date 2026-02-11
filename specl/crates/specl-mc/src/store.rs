//! State storage for model checking.

use crate::fpset::AtomicFPSet;
use crate::state::{Fingerprint, State};
use dashmap::DashMap;
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
    /// Depth from initial state.
    pub depth: usize,
}

/// Thread-safe state storage using a single sharded hash map.
///
/// Supports two modes:
/// - Full tracking: Stores complete state info for trace reconstruction
/// - Fingerprint-only: Uses lockless AtomicFPSet for minimal memory and zero contention
pub struct StateStore {
    /// Full tracking mode: map from fingerprint to state info.
    states: DashMap<Fingerprint, StateInfo>,
    /// Fingerprint-only mode: lockless atomic fingerprint set.
    seen: Option<AtomicFPSet>,
    /// Number of hash collisions detected (different states, same fingerprint).
    collisions: AtomicUsize,
    /// Whether to store full state info (true) or just fingerprints (false).
    full_tracking: bool,
}

impl StateStore {
    /// Create a new state store with full tracking enabled.
    pub fn new() -> Self {
        Self::with_tracking(true)
    }

    /// Create a state store with specified tracking mode.
    pub fn with_tracking(full_tracking: bool) -> Self {
        Self {
            states: DashMap::new(),
            seen: if full_tracking {
                None
            } else {
                Some(AtomicFPSet::new(1 << 20)) // 1M slots default
            },
            collisions: AtomicUsize::new(0),
            full_tracking,
        }
    }

    /// Create a state store with pre-allocated capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            states: DashMap::with_capacity(capacity),
            seen: None,
            collisions: AtomicUsize::new(0),
            full_tracking: true,
        }
    }

    /// Check if a state has been seen before.
    #[inline]
    pub fn contains(&self, fp: &Fingerprint) -> bool {
        if self.full_tracking {
            self.states.contains_key(fp)
        } else {
            self.seen.as_ref().unwrap().contains(*fp)
        }
    }

    /// Try to insert a new state. Returns true if the state was new.
    /// Uses a single DashMap entry() call for atomic check-and-insert.
    pub fn insert(
        &self,
        state: State,
        predecessor: Option<Fingerprint>,
        action_idx: Option<usize>,
        depth: usize,
    ) -> bool {
        let fp = state.fingerprint();
        self.insert_with_fp(fp, state, predecessor, action_idx, depth)
    }

    /// Try to insert with a pre-computed fingerprint. Returns true if the state was new.
    pub fn insert_with_fp(
        &self,
        fp: Fingerprint,
        state: State,
        predecessor: Option<Fingerprint>,
        action_idx: Option<usize>,
        depth: usize,
    ) -> bool {
        if self.full_tracking {
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
                        depth,
                    });
                    true
                }
            }
        } else {
            self.seen.as_ref().unwrap().insert(fp)
        }
    }

    /// Get the number of states stored.
    #[inline]
    pub fn len(&self) -> usize {
        if self.full_tracking {
            self.states.len()
        } else {
            self.seen.as_ref().unwrap().len()
        }
    }

    /// Check if the store is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Check if full tracking is enabled.
    #[inline]
    pub fn has_full_tracking(&self) -> bool {
        self.full_tracking
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
    /// Returns empty trace if full tracking is disabled.
    pub fn trace_to(
        &self,
        fp: &Fingerprint,
        action_names: &[String],
    ) -> Vec<(State, Option<String>)> {
        if !self.full_tracking {
            return vec![];
        }

        let mut trace = Vec::new();
        let mut current = Some(*fp);

        while let Some(cfp) = current {
            if let Some(info) = self.get(&cfp) {
                let name = info.action_idx.map(|idx| {
                    action_names
                        .get(idx)
                        .cloned()
                        .unwrap_or_else(|| format!("action_{}", idx))
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
        if self.full_tracking {
            self.states.iter().map(|r| *r.key()).collect()
        } else {
            // Not supported for AtomicFPSet (no iteration)
            HashSet::new()
        }
    }

    /// Clear the store and optionally change tracking mode.
    pub fn clear(&mut self, full_tracking: bool) {
        self.states.clear();
        self.collisions.store(0, Ordering::Relaxed);
        self.full_tracking = full_tracking;
        if full_tracking {
            self.seen = None;
        } else {
            self.seen = Some(AtomicFPSet::new(1 << 20));
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

        assert!(store.insert(s1.clone(), None, None, 0));
        assert!(!store.insert(s1.clone(), None, None, 0)); // duplicate
        assert!(store.insert(s2, None, None, 0));

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

        store.insert(s0, None, Some(0), 0);
        store.insert(s1, Some(fp0), Some(1), 1);
        store.insert(s2, Some(fp1), Some(2), 2);

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
        assert!(store.insert(s1.clone(), None, None, 0));
        assert!(!store.insert(s1.clone(), None, None, 0)); // duplicate
        assert!(store.insert(s2, None, None, 0));
        assert_eq!(store.len(), 2);

        // But shouldn't be able to get state info
        let fp1 = State::new(vec![Value::Int(1)]).fingerprint();
        assert!(store.get(&fp1).is_none());

        // Trace should be empty
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
                    store.insert(state, None, None, 0);
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

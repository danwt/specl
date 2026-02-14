//! LTSmin-style tree compression for state storage.
//!
//! States are decomposed into a balanced binary tree of hash tables.
//! Each leaf represents an individual variable value (interned to u32),
//! and interior nodes combine pairs of child IDs into a parent ID.
//!
//! Two states sharing a common sub-vector share the corresponding subtree
//! nodes, providing automatic structural deduplication beyond per-variable
//! interning (which is what Collapse mode does).
//!
//! Example for 4 variables [v0, v1, v2, v3]:
//! ```text
//!          root_id
//!         /       \
//!    pair_01    pair_23
//!    /    \     /    \
//!  id_0  id_1 id_2  id_3
//! ```

use dashmap::DashMap;
use specl_eval::Value;
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::Mutex;

/// Node ID in the tree table. Level-local namespace.
type NodeId = u32;

/// A single level in the tree table.
struct TreeLevel {
    /// Forward mapping: (left_child, right_child) → node_id.
    forward: DashMap<(u32, u32), u32>,
    /// Reverse mapping: node_id → (left_child, right_child).
    reverse: Mutex<Vec<(u32, u32)>>,
    /// Next available node ID.
    next_id: AtomicU32,
}

impl TreeLevel {
    fn new() -> Self {
        Self {
            forward: DashMap::new(),
            reverse: Mutex::new(Vec::new()),
            next_id: AtomicU32::new(0),
        }
    }

    /// Intern a pair of child IDs, returning the parent node ID.
    fn intern(&self, left: u32, right: u32) -> u32 {
        let key = (left, right);
        if let Some(id) = self.forward.get(&key) {
            return *id;
        }
        let mut reverse = self.reverse.lock().unwrap();
        // Double-check after lock
        if let Some(id) = self.forward.get(&key) {
            return *id;
        }
        let id = self.next_id.fetch_add(1, Ordering::Relaxed);
        reverse.push(key);
        self.forward.insert(key, id);
        id
    }

    /// Look up children for a node ID.
    #[inline]
    fn lookup(&self, id: u32) -> (u32, u32) {
        let reverse = self.reverse.lock().unwrap();
        reverse[id as usize]
    }

    /// Number of unique nodes at this level.
    fn len(&self) -> usize {
        self.next_id.load(Ordering::Relaxed) as usize
    }
}

/// Leaf level: interns individual Value objects to u32 IDs.
struct LeafLevel {
    forward: DashMap<Value, u32>,
    reverse: Mutex<Vec<Value>>,
    next_id: AtomicU32,
}

impl LeafLevel {
    fn new() -> Self {
        Self {
            forward: DashMap::new(),
            reverse: Mutex::new(Vec::new()),
            next_id: AtomicU32::new(0),
        }
    }

    /// Intern a value, returning its node ID.
    fn intern(&self, value: &Value) -> u32 {
        if let Some(id) = self.forward.get(value) {
            return *id;
        }
        let mut reverse = self.reverse.lock().unwrap();
        if let Some(id) = self.forward.get(value) {
            return *id;
        }
        let id = self.next_id.fetch_add(1, Ordering::Relaxed);
        reverse.push(value.clone());
        self.forward.insert(value.clone(), id);
        id
    }

    /// Look up a value by its node ID.
    fn lookup(&self, id: u32) -> Value {
        let reverse = self.reverse.lock().unwrap();
        reverse[id as usize].clone()
    }

    fn len(&self) -> usize {
        self.next_id.load(Ordering::Relaxed) as usize
    }
}

/// LTSmin-style tree table for hierarchical state compression.
///
/// States with N variables are stored as a balanced binary tree with
/// ceil(log2(N)) interior levels plus one leaf level.
pub struct TreeTable {
    /// Number of variables per state.
    num_vars: usize,
    /// Padded width (next power of 2 >= num_vars).
    padded_width: usize,
    /// Leaf level: Value → u32 ID.
    leaves: LeafLevel,
    /// Interior levels: (u32, u32) → u32 ID.
    /// levels[0] combines pairs of leaf IDs, levels[1] combines pairs of level-0 IDs, etc.
    levels: Vec<TreeLevel>,
}

impl TreeTable {
    /// Create a new tree table for states with `num_vars` variables.
    pub fn new(num_vars: usize) -> Self {
        let padded_width = num_vars.next_power_of_two().max(2);
        let num_levels = (padded_width as f64).log2() as usize;
        let levels = (0..num_levels).map(|_| TreeLevel::new()).collect();
        Self {
            num_vars,
            padded_width,
            leaves: LeafLevel::new(),
            levels,
        }
    }

    /// Insert a state into the tree table, returning the root node ID.
    pub fn insert(&self, vars: &[Value]) -> u32 {
        // Intern leaf values
        let mut current: Vec<u32> = Vec::with_capacity(self.padded_width);
        for v in vars.iter() {
            current.push(self.leaves.intern(v));
        }
        // Pad with None sentinel (ID for Value::none())
        let none_id = self.leaves.intern(&Value::none());
        while current.len() < self.padded_width {
            current.push(none_id);
        }

        // Build tree bottom-up
        for level in &self.levels {
            let mut next = Vec::with_capacity(current.len() / 2);
            for pair in current.chunks_exact(2) {
                next.push(level.intern(pair[0], pair[1]));
            }
            current = next;
        }

        debug_assert_eq!(current.len(), 1);
        current[0]
    }

    /// Reconstruct a state from a root node ID.
    pub fn reconstruct(&self, root_id: u32) -> Vec<Value> {
        // Traverse top-down
        let mut current = vec![root_id];

        for level in self.levels.iter().rev() {
            let mut next = Vec::with_capacity(current.len() * 2);
            for &id in &current {
                let (left, right) = level.lookup(id);
                next.push(left);
                next.push(right);
            }
            current = next;
        }

        // current now contains leaf IDs
        current
            .into_iter()
            .take(self.num_vars)
            .map(|id| self.leaves.lookup(id))
            .collect()
    }

    /// Memory statistics: total unique nodes across all levels.
    pub fn total_nodes(&self) -> usize {
        self.leaves.len() + self.levels.iter().map(|l| l.len()).sum::<usize>()
    }
}

// SAFETY: All internals use DashMap (Sync) and Mutex (Sync)
unsafe impl Sync for TreeTable {}
unsafe impl Send for TreeTable {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_insert_reconstruct() {
        let table = TreeTable::new(4);
        let vars = vec![Value::int(1), Value::int(2), Value::int(3), Value::int(4)];
        let root = table.insert(&vars);
        let reconstructed = table.reconstruct(root);
        assert_eq!(vars, reconstructed);
    }

    #[test]
    fn test_structural_sharing() {
        let table = TreeTable::new(4);
        // Two states differing only in var[0]
        let s1 = vec![Value::int(1), Value::int(2), Value::int(3), Value::int(4)];
        let s2 = vec![Value::int(99), Value::int(2), Value::int(3), Value::int(4)];

        let r1 = table.insert(&s1);
        let r2 = table.insert(&s2);

        // Root IDs should differ (states are different)
        assert_ne!(r1, r2);
        // But total nodes should be less than 2 * full tree (sharing right subtree)
        // Full tree for 4 vars = 4 leaves + 2 level-0 + 1 level-1 = 7 nodes
        // Two states sharing right subtree: 5 leaves + 3 level-0 + 2 level-1 = 10
        // vs 14 without sharing
        assert!(table.total_nodes() < 14);

        // Both reconstruct correctly
        assert_eq!(table.reconstruct(r1), s1);
        assert_eq!(table.reconstruct(r2), s2);
    }

    #[test]
    fn test_non_power_of_two() {
        let table = TreeTable::new(3);
        let vars = vec![Value::int(10), Value::int(20), Value::int(30)];
        let root = table.insert(&vars);
        let reconstructed = table.reconstruct(root);
        assert_eq!(vars, reconstructed);
    }

    #[test]
    fn test_single_var() {
        let table = TreeTable::new(1);
        let vars = vec![Value::int(42)];
        let root = table.insert(&vars);
        let reconstructed = table.reconstruct(root);
        assert_eq!(vars, reconstructed);
    }

    #[test]
    fn test_deduplication_identical_states() {
        let table = TreeTable::new(4);
        let vars = vec![Value::int(1), Value::int(2), Value::int(3), Value::int(4)];

        let r1 = table.insert(&vars);
        let r2 = table.insert(&vars);

        // Same state should get same root ID
        assert_eq!(r1, r2);
    }
}

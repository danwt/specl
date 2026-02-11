//! Lockless atomic fingerprint set using open addressing with linear probing.
//!
//! Replaces DashMap<Fingerprint, ()> for fingerprint-only mode with zero lock
//! contention and 8 bytes per entry instead of ~64.

use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

use crate::state::Fingerprint;

/// Sentinel value for empty slots.
const EMPTY: u64 = u64::MAX;

/// A lockless, fixed-capacity set of 64-bit fingerprints.
///
/// Uses open addressing with linear probing and atomic CAS for insertion.
/// Fingerprint value 0 is remapped to 1 to avoid collision with the empty sentinel.
pub struct AtomicFPSet {
    slots: Vec<AtomicU64>,
    mask: u64,
    count: AtomicUsize,
}

impl AtomicFPSet {
    /// Create a new set with the given capacity (rounded up to power of 2).
    /// Actual slot count is 2x capacity to maintain ~50% load factor.
    pub fn new(expected_capacity: usize) -> Self {
        let min_slots = (expected_capacity * 2).max(1024).next_power_of_two();
        let mut slots = Vec::with_capacity(min_slots);
        for _ in 0..min_slots {
            slots.push(AtomicU64::new(EMPTY));
        }
        Self {
            mask: (min_slots - 1) as u64,
            slots,
            count: AtomicUsize::new(0),
        }
    }

    /// Remap fingerprint to avoid collision with EMPTY sentinel.
    #[inline]
    fn remap(fp: u64) -> u64 {
        if fp == EMPTY {
            EMPTY - 1
        } else {
            fp
        }
    }

    /// Insert a fingerprint. Returns true if newly inserted, false if already present.
    #[inline]
    pub fn insert(&self, fp: Fingerprint) -> bool {
        let val = Self::remap(fp.as_u64());
        let mut idx = (val & self.mask) as usize;

        loop {
            let slot = unsafe { self.slots.get_unchecked(idx) };
            let current = slot.load(Ordering::Relaxed);

            if current == val {
                return false; // Already present
            }

            if current == EMPTY {
                // Try to claim this slot
                match slot.compare_exchange(EMPTY, val, Ordering::Relaxed, Ordering::Relaxed) {
                    Ok(_) => {
                        self.count.fetch_add(1, Ordering::Relaxed);
                        return true;
                    }
                    Err(actual) => {
                        if actual == val {
                            return false; // Another thread inserted same value
                        }
                        // Another thread inserted a different value, continue probing
                    }
                }
            }

            idx = ((idx + 1) as u64 & self.mask) as usize;
        }
    }

    /// Check if a fingerprint is in the set.
    #[inline]
    pub fn contains(&self, fp: Fingerprint) -> bool {
        let val = Self::remap(fp.as_u64());
        let mut idx = (val & self.mask) as usize;

        loop {
            let current = unsafe { self.slots.get_unchecked(idx) }.load(Ordering::Relaxed);

            if current == val {
                return true;
            }
            if current == EMPTY {
                return false;
            }

            idx = ((idx + 1) as u64 & self.mask) as usize;
        }
    }

    /// Get the number of entries in the set.
    #[inline]
    pub fn len(&self) -> usize {
        self.count.load(Ordering::Relaxed)
    }

    /// Check if the set is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_insert_contains() {
        let set = AtomicFPSet::new(1024);

        let fp1 = Fingerprint::from_u64(42);
        let fp2 = Fingerprint::from_u64(99);
        let fp3 = Fingerprint::from_u64(12345);

        assert!(set.insert(fp1));
        assert!(set.insert(fp2));
        assert!(!set.insert(fp1)); // duplicate
        assert!(set.insert(fp3));

        assert!(set.contains(fp1));
        assert!(set.contains(fp2));
        assert!(set.contains(fp3));
        assert!(!set.contains(Fingerprint::from_u64(999)));

        assert_eq!(set.len(), 3);
    }

    #[test]
    fn test_zero_fingerprint() {
        let set = AtomicFPSet::new(1024);

        let fp0 = Fingerprint::from_u64(0);
        assert!(set.insert(fp0));
        assert!(!set.insert(fp0));
        assert!(set.contains(fp0));
        assert_eq!(set.len(), 1);
    }

    #[test]
    fn test_concurrent_insert() {
        use std::sync::Arc;
        use std::thread;

        let set = Arc::new(AtomicFPSet::new(10000));
        let mut handles = vec![];

        for t in 0..4 {
            let set = Arc::clone(&set);
            handles.push(thread::spawn(move || {
                for i in 0..1000 {
                    let fp = Fingerprint::from_u64((t * 10000 + i) as u64);
                    set.insert(fp);
                }
            }));
        }

        for h in handles {
            h.join().unwrap();
        }

        assert_eq!(set.len(), 4000);
    }

    #[test]
    fn test_high_load() {
        let set = AtomicFPSet::new(512);
        let mut inserted = 0;
        for i in 1..=400 {
            if set.insert(Fingerprint::from_u64(i)) {
                inserted += 1;
            }
        }
        assert_eq!(inserted, 400);
        assert_eq!(set.len(), 400);

        for i in 1..=400 {
            assert!(set.contains(Fingerprint::from_u64(i)));
        }
    }
}

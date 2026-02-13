//! Lockless atomic fingerprint set using open addressing with linear probing.
//!
//! Replaces DashMap<Fingerprint, ()> for fingerprint-only mode with zero lock
//! contention and 8 bytes per entry instead of ~64.

use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

use crate::state::Fingerprint;

/// Sentinel value for empty slots.
const EMPTY: u64 = u64::MAX;

/// A set of 64-bit fingerprints using open addressing with linear probing.
///
/// Starts with an initial capacity and grows automatically when load exceeds 37.5%.
/// Uses atomic CAS for concurrent insertion within a generation; resizing
/// is single-threaded (requires &mut self or external synchronization).
/// Fingerprint value `u64::MAX` is remapped to avoid collision with the empty sentinel.
pub struct AtomicFPSet {
    slots: Vec<AtomicU64>,
    mask: u64,
    count: AtomicUsize,
}

impl AtomicFPSet {
    /// Create a new set with the given capacity (rounded up to power of 2).
    /// Actual slot count is ~2.67x capacity to maintain ~37.5% load factor.
    pub fn new(expected_capacity: usize) -> Self {
        let min_slots = (expected_capacity * 3).max(1024).next_power_of_two();
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

    /// Returns true if the load factor exceeds 37.5% and the set should be grown.
    /// Lower threshold than 50% reduces average probe length from ~2.0 to ~1.6
    /// and dramatically improves worst-case behavior under linear probing.
    #[inline]
    pub fn should_grow(&self) -> bool {
        self.count.load(Ordering::Relaxed) * 8 >= self.slots.len() * 3
    }

    /// Double the capacity and rehash all entries.
    /// NOT thread-safe — must be called from a single thread with no concurrent inserts.
    pub fn grow(&mut self) {
        let new_len = self.slots.len() * 2;
        let mut new_slots = Vec::with_capacity(new_len);
        for _ in 0..new_len {
            new_slots.push(AtomicU64::new(EMPTY));
        }
        let new_mask = (new_len - 1) as u64;

        // Rehash all existing entries
        for slot in &self.slots {
            let val = slot.load(Ordering::Relaxed);
            if val != EMPTY {
                let mut idx = (val & new_mask) as usize;
                loop {
                    let current = new_slots[idx].load(Ordering::Relaxed);
                    if current == EMPTY {
                        new_slots[idx].store(val, Ordering::Relaxed);
                        break;
                    }
                    idx = ((idx + 1) as u64 & new_mask) as usize;
                }
            }
        }

        self.slots = new_slots;
        self.mask = new_mask;
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
                        // Another thread inserted a different value — hint CPU to reduce
                        // contention before continuing probe sequence
                        std::hint::spin_loop();
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

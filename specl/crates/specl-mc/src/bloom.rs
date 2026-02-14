//! Bloom filter for probabilistic state deduplication.
//!
//! Fixed-memory alternative to AtomicFPSet for bug-finding mode.
//! Uses atomic bit-level operations for lock-free concurrent access.

use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

use crate::state::Fingerprint;

/// Concurrent bloom filter using atomic u64 words.
///
/// Memory is fixed at construction time. As more states are inserted,
/// the false positive rate increases but never exceeds the theoretical
/// bound for the chosen parameters. False positives cause states to be
/// skipped (incomplete exploration), which is acceptable for bug finding.
pub struct BloomFilter {
    bits: Vec<AtomicU64>,
    num_bits: u64,
    num_hashes: u32,
    count: AtomicUsize,
}

impl BloomFilter {
    /// Create a bloom filter with the given number of bits and hash functions.
    ///
    /// Recommended: 3 hash functions, bits = 8 * expected_states for ~2% FP rate.
    /// For 100M states at 3 hashes: 1 GiB gives ~0.004% FP rate.
    pub fn new(num_bits: usize, num_hashes: u32) -> Self {
        let num_words = num_bits.div_ceil(64);
        let mut bits = Vec::with_capacity(num_words);
        for _ in 0..num_words {
            bits.push(AtomicU64::new(0));
        }
        Self {
            bits,
            num_bits: num_bits as u64,
            num_hashes,
            count: AtomicUsize::new(0),
        }
    }

    /// Create a bloom filter from a power-of-2 bit count specification.
    /// E.g., `from_log2_bits(30, 3)` = 2^30 bits = 128 MiB, 3 hashes.
    pub fn from_log2_bits(log2_bits: u32, num_hashes: u32) -> Self {
        Self::new(1usize << log2_bits, num_hashes)
    }

    /// Insert a fingerprint. Returns true if the fingerprint was probably new.
    ///
    /// Due to concurrent races, multiple threads may both see a fingerprint as
    /// "new" — this is fine for model checking (worst case: exploring a state
    /// twice, which is harmless).
    pub fn insert(&self, fp: Fingerprint) -> bool {
        let mut was_new = false;
        let (h1, h2) = self.hash_pair(fp);
        for i in 0..self.num_hashes {
            let pos = self.bit_position(h1, h2, i);
            let word_idx = pos / 64;
            let bit_idx = pos % 64;
            let mask = 1u64 << bit_idx;
            let old = self.bits[word_idx].fetch_or(mask, Ordering::Relaxed);
            if old & mask == 0 {
                was_new = true;
            }
        }
        if was_new {
            self.count.fetch_add(1, Ordering::Relaxed);
        }
        was_new
    }

    /// Check if a fingerprint might be in the set (may return false positives).
    pub fn contains(&self, fp: Fingerprint) -> bool {
        let (h1, h2) = self.hash_pair(fp);
        for i in 0..self.num_hashes {
            let pos = self.bit_position(h1, h2, i);
            let word_idx = pos / 64;
            let bit_idx = pos % 64;
            let mask = 1u64 << bit_idx;
            if self.bits[word_idx].load(Ordering::Relaxed) & mask == 0 {
                return false;
            }
        }
        true
    }

    /// Number of items inserted (approximate due to concurrent races).
    pub fn len(&self) -> usize {
        self.count.load(Ordering::Relaxed)
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Memory usage in bytes.
    pub fn memory_bytes(&self) -> usize {
        self.bits.len() * 8
    }

    /// Estimated false positive rate at current fill level.
    pub fn estimated_fp_rate(&self) -> f64 {
        let n = self.count.load(Ordering::Relaxed) as f64;
        let m = self.num_bits as f64;
        let k = self.num_hashes as f64;
        (1.0 - (-k * n / m).exp()).powf(k)
    }

    /// Generate two base hashes from a fingerprint using double hashing.
    /// h_i(x) = (h1 + i * h2) mod num_bits
    #[inline]
    fn hash_pair(&self, fp: Fingerprint) -> (u64, u64) {
        let h1 = fp.as_u64();
        let h2 = h1
            .wrapping_mul(0x9E3779B97F4A7C15)
            .wrapping_add(0x6A09E667);
        (h1, h2)
    }

    /// Compute the bit position for the i-th hash function.
    #[inline]
    fn bit_position(&self, h1: u64, h2: u64, i: u32) -> usize {
        let h = h1.wrapping_add((i as u64).wrapping_mul(h2));
        (h % self.num_bits) as usize
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bloom_basic() {
        let bloom = BloomFilter::new(1024, 3);
        let fp1 = Fingerprint::from_u64(12345);
        let fp2 = Fingerprint::from_u64(67890);

        assert!(!bloom.contains(fp1));
        assert!(bloom.insert(fp1));
        assert!(bloom.contains(fp1));
        assert!(!bloom.insert(fp1)); // already present

        assert!(!bloom.contains(fp2));
        assert!(bloom.insert(fp2));
        assert!(bloom.contains(fp2));

        assert_eq!(bloom.len(), 2);
    }

    #[test]
    fn test_bloom_fp_rate() {
        // Insert 1000 items into a 100K-bit filter with 3 hashes
        let bloom = BloomFilter::new(100_000, 3);
        for i in 0..1000u64 {
            bloom.insert(Fingerprint::from_u64(i));
        }

        // Check 1000 items that were NOT inserted
        let mut false_positives = 0;
        for i in 1_000_000..1_001_000u64 {
            if bloom.contains(Fingerprint::from_u64(i)) {
                false_positives += 1;
            }
        }

        // At 1000/100K = 1% fill with 3 hashes, FP rate should be very low
        assert!(
            false_positives < 10,
            "too many false positives: {false_positives}"
        );
    }

    #[test]
    fn test_bloom_from_log2() {
        let bloom = BloomFilter::from_log2_bits(20, 3); // 2^20 = 1M bits = 128 KiB
        assert_eq!(bloom.memory_bytes(), 1 << 17); // 128 KiB
    }

    #[test]
    fn test_bloom_concurrent() {
        use std::sync::Arc;
        use std::thread;

        let bloom = Arc::new(BloomFilter::new(1_000_000, 3));
        let mut handles = vec![];

        for t in 0..4u64 {
            let bloom = Arc::clone(&bloom);
            handles.push(thread::spawn(move || {
                for i in 0..1000u64 {
                    bloom.insert(Fingerprint::from_u64(t * 10000 + i));
                }
            }));
        }

        for h in handles {
            h.join().unwrap();
        }

        // All 4000 items should be present
        for t in 0..4u64 {
            for i in 0..1000u64 {
                assert!(bloom.contains(Fingerprint::from_u64(t * 10000 + i)));
            }
        }
    }
}

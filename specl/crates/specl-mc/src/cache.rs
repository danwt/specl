//! Incremental checking: save/load fingerprint sets to disk.
//!
//! Caches the set of explored state fingerprints so that re-runs with the
//! same spec skip previously explored states. Cache is invalidated when the
//! spec source or constants change.

use std::collections::hash_map::DefaultHasher;
use std::fs;
use std::hash::{Hash, Hasher};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use tracing::{debug, info};

/// Compute a hash of the spec source and constant values for cache invalidation.
pub fn spec_hash(source: &str, const_values: &[(String, i64)]) -> u64 {
    let mut hasher = DefaultHasher::new();
    source.hash(&mut hasher);
    for (name, val) in const_values {
        name.hash(&mut hasher);
        val.hash(&mut hasher);
    }
    hasher.finish()
}

/// Resolve the cache directory for a given spec file.
fn cache_dir(spec_path: &Path) -> PathBuf {
    let parent = spec_path.parent().unwrap_or(Path::new("."));
    parent.join(".specl_cache")
}

/// Resolve the fingerprint file path for a given spec.
fn fp_path(spec_path: &Path, hash: u64) -> PathBuf {
    let dir = cache_dir(spec_path);
    dir.join(format!("{:016x}.fp", hash))
}

/// Load cached fingerprints from disk.
/// Returns None if cache doesn't exist or is invalid.
pub fn load_fingerprints(spec_path: &Path, hash: u64) -> Option<Vec<u64>> {
    let path = fp_path(spec_path, hash);
    if !path.exists() {
        return None;
    }

    let mut file = match fs::File::open(&path) {
        Ok(f) => f,
        Err(e) => {
            debug!(error = %e, "failed to open cache file");
            return None;
        }
    };

    // Read metadata: 8 bytes spec_hash + 8 bytes count
    let mut meta_buf = [0u8; 16];
    if file.read_exact(&mut meta_buf).is_err() {
        return None;
    }
    let stored_hash = u64::from_le_bytes(meta_buf[0..8].try_into().unwrap());
    let count = u64::from_le_bytes(meta_buf[8..16].try_into().unwrap());

    if stored_hash != hash {
        debug!("cache hash mismatch, ignoring");
        return None;
    }

    // Read fingerprints: count * 8 bytes
    let mut data = vec![0u8; count as usize * 8];
    if file.read_exact(&mut data).is_err() {
        return None;
    }

    let fps: Vec<u64> = data
        .chunks_exact(8)
        .map(|chunk| u64::from_le_bytes(chunk.try_into().unwrap()))
        .collect();

    info!(cached_states = fps.len(), "loaded incremental cache");
    Some(fps)
}

/// Save fingerprints to disk for incremental re-use.
pub fn save_fingerprints(spec_path: &Path, hash: u64, fingerprints: &[u64]) -> std::io::Result<()> {
    let dir = cache_dir(spec_path);
    fs::create_dir_all(&dir)?;

    let path = fp_path(spec_path, hash);
    let mut file = fs::File::create(&path)?;

    // Write metadata
    file.write_all(&hash.to_le_bytes())?;
    file.write_all(&(fingerprints.len() as u64).to_le_bytes())?;

    // Write fingerprints
    for &fp in fingerprints {
        file.write_all(&fp.to_le_bytes())?;
    }

    info!(
        states = fingerprints.len(),
        path = %path.display(),
        "saved incremental cache"
    );
    Ok(())
}

/// Clean up old cache files for the spec directory.
/// Keeps only the cache matching the current hash.
pub fn cleanup_old_caches(spec_path: &Path, current_hash: u64) {
    let dir = cache_dir(spec_path);
    if !dir.exists() {
        return;
    }

    if let Ok(entries) = fs::read_dir(&dir) {
        let current_name = format!("{:016x}.fp", current_hash);
        for entry in entries.flatten() {
            let name = entry.file_name();
            if name
                .to_str()
                .is_some_and(|n| n.ends_with(".fp") && n != current_name)
            {
                let _ = fs::remove_file(entry.path());
                debug!(file = %entry.path().display(), "removed old cache file");
            }
        }
    }
}

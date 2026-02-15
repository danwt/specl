#!/bin/bash
# Profile-Guided Optimization build for specl
# 1. Build instrumented binary
# 2. Run representative workloads to collect profiles
# 3. Merge profiles
# 4. Build optimized binary using profile data
set -euo pipefail

SPECL_DIR="$(cd "$(dirname "$0")/.." && pwd)"
EXAMPLES="$SPECL_DIR/examples/showcase"
PGO_DIR="$SPECL_DIR/target/pgo-data"

echo "=== PGO Build for Specl ==="
echo "Working directory: $SPECL_DIR"

# Step 1: Clean and build instrumented binary
echo ""
echo "--- Step 1: Building instrumented binary ---"
rm -rf "$PGO_DIR"
mkdir -p "$PGO_DIR"

RUSTFLAGS="-Cprofile-generate=$PGO_DIR" \
    cargo build --release --manifest-path="$SPECL_DIR/Cargo.toml" 2>&1 | tail -3

SPECL="$SPECL_DIR/target/release/specl"

# Step 2: Run representative workloads
echo ""
echo "--- Step 2: Collecting profile data ---"

# Raft N=2 (small, fast)
echo "  Running Raft N=2..."
$SPECL check "$EXAMPLES/raft.specl" \
    -c N=2 -c MaxVal=1 -c MaxElections=2 -c MaxRestarts=0 -c MaxLogLen=3 \
    --no-deadlock --no-auto --no-parallel --max-states 200000 2>/dev/null

# Raft N=3 (larger state space)
echo "  Running Raft N=3..."
$SPECL check "$EXAMPLES/raft.specl" \
    -c N=3 -c MaxVal=1 -c MaxElections=2 -c MaxRestarts=0 -c MaxLogLen=3 \
    --no-deadlock --no-auto --no-parallel --max-states 500000 2>/dev/null

# Paxos (different variable patterns)
echo "  Running Paxos..."
$SPECL check "$EXAMPLES/paxos.specl" \
    -c N=2 -c MaxBallot=3 -c V=2 --no-deadlock --no-auto --no-parallel --max-states 200000 2>/dev/null

# Lamport Mutex (small but complete)
echo "  Running Lamport Mutex..."
$SPECL check "$EXAMPLES/lamport-mutex.specl" \
    -c N=2 --no-deadlock --no-auto --no-parallel 2>/dev/null

# Peterson (tiny, exercises different paths)
echo "  Running Peterson..."
$SPECL check "$EXAMPLES/peterson.specl" --no-auto --no-parallel 2>/dev/null

# CometBFT (complex protocol)
echo "  Running CometBFT..."
$SPECL check "$EXAMPLES/comet.specl" \
    -c N=3 -c MaxRound=2 -c MaxHeight=1 --no-deadlock --no-auto --no-parallel --max-states 200000 2>/dev/null

# Ricart-Agrawala
echo "  Running Ricart-Agrawala..."
$SPECL check "$EXAMPLES/ricart-agrawala.specl" \
    -c N=2 --no-deadlock --no-auto --no-parallel 2>/dev/null

# EPaxos
echo "  Running EPaxos..."
$SPECL check "$EXAMPLES/epaxos.specl" \
    -c N=2 -c MaxBallot=2 -c C=2 --no-deadlock --no-auto --no-parallel --max-states 200000 2>/dev/null

echo "  Profile data collected in $PGO_DIR"
echo "  Files: $(ls "$PGO_DIR" | wc -l | tr -d ' ') profile files"

# Step 3: Merge profiles
echo ""
echo "--- Step 3: Merging profiles ---"
llvm-profdata merge -o "$PGO_DIR/merged.profdata" "$PGO_DIR"/*.profraw 2>&1 || {
    # Try with rustup's llvm-profdata
    LLVM_PROFDATA=$(find "$(rustc --print sysroot)" -name llvm-profdata 2>/dev/null | head -1)
    if [ -n "$LLVM_PROFDATA" ]; then
        echo "  Using $LLVM_PROFDATA"
        "$LLVM_PROFDATA" merge -o "$PGO_DIR/merged.profdata" "$PGO_DIR"/*.profraw
    else
        echo "ERROR: llvm-profdata not found"
        exit 1
    fi
}

echo "  Merged profile: $(ls -lh "$PGO_DIR/merged.profdata" | awk '{print $5}')"

# Step 4: Build optimized binary
echo ""
echo "--- Step 4: Building PGO-optimized binary ---"
RUSTFLAGS="-Cprofile-use=$PGO_DIR/merged.profdata -Cllvm-args=-pgo-warn-missing-function" \
    cargo build --release --manifest-path="$SPECL_DIR/Cargo.toml" 2>&1 | tail -3

echo ""
echo "=== PGO build complete ==="
echo "Optimized binary: $SPECL"

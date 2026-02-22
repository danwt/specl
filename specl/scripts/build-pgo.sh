#!/bin/bash
# Build specl with Profile-Guided Optimization (PGO)
# Achieves ~20-30% speedup over standard release build.
#
# Usage: ./scripts/build-pgo.sh
# Uses diverse showcase specs as training workloads.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$PROJECT_DIR"

SYSROOT=$(rustc --print sysroot)
TARGET=$(rustc -vV | sed -n 's/host: //p')
LLVM_PROFDATA="$SYSROOT/lib/rustlib/$TARGET/bin/llvm-profdata"

if [ ! -f "$LLVM_PROFDATA" ]; then
    echo "Installing llvm-tools..."
    rustup component add llvm-tools
    if [ ! -f "$LLVM_PROFDATA" ]; then
        echo "Error: llvm-profdata not found at $LLVM_PROFDATA"
        exit 1
    fi
fi

PGO_DIR="/tmp/specl-pgo-data"
PGO_MERGED="/tmp/specl-pgo-merged.profdata"

echo "=== Step 1/4: Building instrumented binary ==="
rm -rf "$PGO_DIR"
RUSTFLAGS="-Cprofile-generate=$PGO_DIR" cargo build --release

echo "=== Step 2/4: Collecting profile data (diverse workloads) ==="
SPECL=./target/release/specl
$SPECL check examples/showcase/raft.specl -c N=2 -c MaxVal=2 -c MaxElections=2 -c MaxRestarts=1 -c MaxLogLen=3 --no-deadlock --no-parallel --max-states 100000 -q || true
$SPECL check examples/showcase/paxos.specl -c N=2 -c MaxBallot=3 -c V=2 --no-deadlock --no-parallel --max-states 100000 -q || true
$SPECL check examples/showcase/comet.specl -c N=3 -c MaxRound=2 -c V=2 -c F=1 --no-deadlock --no-parallel --bfs --max-states 100000 -q || true
$SPECL check examples/showcase/ricart-agrawala.specl -c N=3 --no-deadlock --no-parallel --bfs --max-states 100000 -q || true
$SPECL check examples/showcase/lamport-mutex.specl -c N=3 --no-deadlock --no-parallel --bfs --max-states 100000 -q || true

echo "=== Step 3/4: Merging profile data ==="
"$LLVM_PROFDATA" merge -o "$PGO_MERGED" "$PGO_DIR/"

echo "=== Step 4/4: Building optimized binary ==="
RUSTFLAGS="-Cprofile-use=$PGO_MERGED" cargo build --release

echo "=== Done! PGO-optimized binary at target/release/specl ==="

#!/bin/bash
# Build specl with Profile-Guided Optimization (PGO)
# Achieves ~26% speedup over standard release build.
#
# Usage: ./scripts/build-pgo.sh [spec_file] [extra_args...]
# Default: uses raft.specl N=2 as training workload

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$PROJECT_DIR"

SYSROOT=$(rustc --print sysroot)
LLVM_PROFDATA="$SYSROOT/lib/rustlib/aarch64-apple-darwin/bin/llvm-profdata"

if [ ! -f "$LLVM_PROFDATA" ]; then
    echo "Installing llvm-tools..."
    rustup component add llvm-tools
fi

PGO_DIR="/tmp/specl-pgo-data"
PGO_MERGED="/tmp/specl-pgo-merged.profdata"

SPEC_FILE="${1:-examples/showcase/raft.specl}"
shift 2>/dev/null || true
EXTRA_ARGS="${*:--c N=2 -c MaxVal=1 -c MaxElections=2 -c MaxRestarts=0 -c MaxLogLen=3 --no-deadlock --max-states 2000000 --no-parallel -q}"

echo "=== Step 1/4: Building instrumented binary ==="
rm -rf "$PGO_DIR"
RUSTFLAGS="-Cprofile-generate=$PGO_DIR" cargo build --release

echo "=== Step 2/4: Collecting profile data ==="
./target/release/specl check "$SPEC_FILE" $EXTRA_ARGS || true

echo "=== Step 3/4: Merging profile data ==="
"$LLVM_PROFDATA" merge -o "$PGO_MERGED" "$PGO_DIR/"

echo "=== Step 4/4: Building optimized binary ==="
RUSTFLAGS="-Cprofile-use=$PGO_MERGED" cargo build --release

echo "=== Done! PGO-optimized binary at target/release/specl ==="

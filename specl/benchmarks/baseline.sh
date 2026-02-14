#!/bin/bash
# Baseline benchmark script for specl performance optimization
# All tests use --max-states to ensure consistent timing and prevent hangs

set -euo pipefail

SPECL="$(pwd)/target/release/specl"
EXAMPLES="$(pwd)/examples/showcase"
RESULTS_FILE="benchmarks/baseline-results.txt"

if [ ! -f "$SPECL" ]; then
    echo "ERROR: specl binary not found at $SPECL"
    echo "Run: cargo build --release"
    exit 1
fi

echo "=== Specl Baseline Benchmarks ===" | tee "$RESULTS_FILE"
echo "Date: $(date)" | tee -a "$RESULTS_FILE"
echo "Binary: $SPECL" | tee -a "$RESULTS_FILE"
echo "" | tee -a "$RESULTS_FILE"

run_bench() {
    local name="$1"
    local spec="$2"
    shift 2
    local args=("$@")

    echo "--- $name ---" | tee -a "$RESULTS_FILE"
    local output
    output=$(timeout 120 "$SPECL" check "$spec" "${args[@]}" 2>&1) || true
    echo "$output" | grep -E "(States explored|Distinct states|Max depth|Time:|states/s|Result:)" | tee -a "$RESULTS_FILE"
    echo "" | tee -a "$RESULTS_FILE"
}

# === Multi-threaded (full mode, default threads) ===
echo "=== Multi-threaded (full mode) ===" | tee -a "$RESULTS_FILE"

run_bench "Raft N=2 MT (500K)" \
    "$EXAMPLES/raft.specl" \
    -c N=2 -c MaxVal=1 -c MaxElections=2 -c MaxRestarts=0 -c MaxLogLen=3 \
    --no-deadlock --no-auto --max-states 500000

run_bench "Raft N=3 MT (2M)" \
    "$EXAMPLES/raft.specl" \
    -c N=3 -c MaxVal=1 -c MaxElections=2 -c MaxRestarts=0 -c MaxLogLen=3 \
    --no-deadlock --no-auto --max-states 2000000

run_bench "Lamport Mutex N=2 MT (500K)" \
    "$EXAMPLES/lamport-mutex.specl" \
    -c N=2 --no-deadlock --no-auto --max-states 500000

run_bench "Paxos N=2 MT (500K)" \
    "$EXAMPLES/paxos.specl" \
    -c N=2 -c MaxBallot=3 -c V=2 --no-deadlock --no-auto --max-states 500000

run_bench "Ricart-Agrawala N=2 MT (500K)" \
    "$EXAMPLES/ricart-agrawala.specl" \
    -c N=2 --no-deadlock --no-auto --max-states 500000

# === Single-threaded (full mode, --no-parallel) ===
echo "=== Single-threaded (full mode) ===" | tee -a "$RESULTS_FILE"

run_bench "Raft N=2 1T (500K)" \
    "$EXAMPLES/raft.specl" \
    -c N=2 -c MaxVal=1 -c MaxElections=2 -c MaxRestarts=0 -c MaxLogLen=3 \
    --no-deadlock --no-auto --no-parallel --max-states 500000

run_bench "Raft N=3 1T (2M)" \
    "$EXAMPLES/raft.specl" \
    -c N=3 -c MaxVal=1 -c MaxElections=2 -c MaxRestarts=0 -c MaxLogLen=3 \
    --no-deadlock --no-auto --no-parallel --max-states 2000000

run_bench "Lamport Mutex N=2 1T (500K)" \
    "$EXAMPLES/lamport-mutex.specl" \
    -c N=2 --no-deadlock --no-auto --no-parallel --max-states 500000

run_bench "Paxos N=2 1T (500K)" \
    "$EXAMPLES/paxos.specl" \
    -c N=2 -c MaxBallot=3 -c V=2 --no-deadlock --no-auto --no-parallel --max-states 500000

run_bench "Ricart-Agrawala N=2 1T (500K)" \
    "$EXAMPLES/ricart-agrawala.specl" \
    -c N=2 --no-deadlock --no-auto --no-parallel --max-states 500000

# === Fast mode (multi-threaded) ===
echo "=== Fast mode (multi-threaded) ===" | tee -a "$RESULTS_FILE"

run_bench "Raft N=2 --fast MT (500K)" \
    "$EXAMPLES/raft.specl" \
    -c N=2 -c MaxVal=1 -c MaxElections=2 -c MaxRestarts=0 -c MaxLogLen=3 \
    --no-deadlock --no-auto --fast --max-states 500000

run_bench "Raft N=3 --fast MT (2M)" \
    "$EXAMPLES/raft.specl" \
    -c N=3 -c MaxVal=1 -c MaxElections=2 -c MaxRestarts=0 -c MaxLogLen=3 \
    --no-deadlock --no-auto --fast --max-states 2000000

echo "" | tee -a "$RESULTS_FILE"
echo "=== Baseline complete ===" | tee -a "$RESULTS_FILE"

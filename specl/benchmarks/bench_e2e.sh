#!/bin/bash
# End-to-end benchmark: Specl vs TLC
# Compares state counts and wall time on identical specs

set -e
cd "$(dirname "$0")/.."

JAVA=/opt/homebrew/opt/openjdk/bin/java
TLC=.deps/tla2tools.jar
SPECL="./target/release/specl"

# Build specl in release mode
echo "Building specl..."
cargo build --release --bin specl 2>&1 | tail -1

echo ""
echo "=== Specl vs TLC Benchmark ==="
echo ""

# Create temp TLC config
create_counters_cfg() {
    local n=$1
    local max=$2
    cat > /tmp/specl_bench_counters.cfg << EOF
CONSTANTS
    N = $n
    MAX = $max
INIT Init
NEXT Next
INVARIANT AllInRange
EOF
}

create_ewd840_cfg() {
    local n=$1
    cat > /tmp/specl_bench_ewd840.cfg << EOF
CONSTANTS
    N = $n
SPECIFICATION Spec
CHECK_DEADLOCK FALSE
INVARIANTS
    TypeOK
    TerminationDetection
    Inv
EOF
}

benchmark_counters() {
    local n=$1
    local max=$2
    local expected=$(python3 -c "print(($max + 1) ** ($n + 1))")

    printf "%-30s" "Counters N=$n MAX=$max"
    printf "expected=%-8s" "$expected"

    # TLC
    create_counters_cfg $n $max
    tlc_start=$(date +%s%N)
    tlc_output=$($JAVA -XX:+UseParallelGC -jar $TLC -config /tmp/specl_bench_counters.cfg -workers auto -nowarning benchmarks/Counters.tla 2>&1) || true
    tlc_end=$(date +%s%N)
    tlc_ms=$(( ($tlc_end - $tlc_start) / 1000000 ))
    tlc_states=$(echo "$tlc_output" | grep "distinct states found" | grep -oE '[0-9]+ distinct' | cut -d' ' -f1)
    printf "TLC: %6s states %5dms  " "$tlc_states" "$tlc_ms"

    # Specl
    specl_start=$(date +%s%N)
    specl_output=$($SPECL check examples/benchmark/10-counters/counters.specl --no-deadlock -c N=$n -c MAX=$max 2>&1) || true
    specl_end=$(date +%s%N)
    specl_ms=$(( ($specl_end - $specl_start) / 1000000 ))
    specl_states=$(echo "$specl_output" | grep "States explored" | grep -oE '[0-9]+')
    printf "Specl: %6s states %5dms" "$specl_states" "$specl_ms"

    # Ratio
    if [ -n "$tlc_ms" ] && [ "$tlc_ms" -gt 0 ] && [ -n "$specl_ms" ] && [ "$specl_ms" -gt 0 ]; then
        ratio=$(python3 -c "print(f'{$tlc_ms / $specl_ms:.1f}x')")
        printf "  ratio: %s" "$ratio"
    fi
    echo ""
}

benchmark_ewd840() {
    local n=$1  # For TLC: N nodes. For specl: N-1 (last index)
    local specl_n=$(($n - 1))

    printf "%-30s" "EWD840 N=$n"

    # TLC
    create_ewd840_cfg $n
    tlc_start=$(date +%s%N)
    tlc_output=$($JAVA -XX:+UseParallelGC -jar $TLC -config /tmp/specl_bench_ewd840.cfg -workers auto -nowarning ../references/tla-dump-real/ewd840/EWD840.tla 2>&1) || true
    tlc_end=$(date +%s%N)
    tlc_ms=$(( ($tlc_end - $tlc_start) / 1000000 ))
    tlc_states=$(echo "$tlc_output" | grep "distinct states found" | grep -oE '[0-9]+ distinct' | cut -d' ' -f1)
    printf "TLC: %8s states %6dms  " "$tlc_states" "$tlc_ms"

    # Specl
    specl_start=$(date +%s%N)
    specl_output=$($SPECL check examples/realistic/EWD840.specl --no-deadlock -c N=$specl_n 2>&1) || true
    specl_end=$(date +%s%N)
    specl_ms=$(( ($specl_end - $specl_start) / 1000000 ))
    specl_states=$(echo "$specl_output" | grep "States explored" | grep -oE '[0-9]+')
    printf "Specl: %8s states %6dms" "$specl_states" "$specl_ms"

    echo ""
}

echo "--- Counters (matching init/actions, direct comparison) ---"
benchmark_counters 2 3     # 64 states
benchmark_counters 3 5     # 1296 states
benchmark_counters 3 10    # 14641 states
benchmark_counters 4 5     # 7776 states
benchmark_counters 4 8     # 59049 states
benchmark_counters 5 5     # 46656 states

echo ""
echo "--- EWD840 (different init: TLC has many initial states, specl has one) ---"
echo "(State counts will differ - TLC explores from all initial active/color combos)"
benchmark_ewd840 3
benchmark_ewd840 5
benchmark_ewd840 7

# Cleanup
rm -f /tmp/specl_bench_counters.cfg /tmp/specl_bench_ewd840.cfg

#!/bin/bash
# Benchmark Specl vs TLC

set -e
cd "$(dirname "$0")/.."

JAVA=/opt/homebrew/opt/openjdk/bin/java
TLC=.deps/tla2tools.jar
SPECL="cargo run --release --bin specl --"

echo "=== Specl vs TLC Benchmark ==="
echo ""

# Create temp config for TLC
create_tlc_config() {
    local n=$1
    local max=$2
    cat > benchmarks/Counters_bench.cfg << EOF
CONSTANTS
    N = $n
    MAX = $max
INIT Init
NEXT Next
INVARIANT AllInRange
EOF
}

# Benchmark function
benchmark() {
    local n=$1
    local max=$2
    local expected_states=$(( ($max + 1) ** ($n + 1) ))

    echo "--- N=$n, MAX=$max (expected ~$expected_states states) ---"

    # TLC
    create_tlc_config $n $max
    echo -n "TLC:   "
    tlc_start=$(date +%s.%N)
    tlc_output=$($JAVA -XX:+UseParallelGC -jar $TLC -config benchmarks/Counters_bench.cfg -workers auto -nowarning benchmarks/Counters.tla 2>&1)
    tlc_end=$(date +%s.%N)
    tlc_time=$(echo "$tlc_end - $tlc_start" | bc)
    tlc_states=$(echo "$tlc_output" | grep "distinct states found" | grep -oE '[0-9]+ distinct' | cut -d' ' -f1)
    echo "${tlc_states} states in ${tlc_time}s"

    # Specl
    echo -n "Specl: "
    specl_start=$(date +%s.%N)
    specl_output=$($SPECL check examples/benchmark/10-counters/counters.specl --constant N=$n --constant MAX=$max 2>&1)
    specl_end=$(date +%s.%N)
    specl_time=$(echo "$specl_end - $specl_start" | bc)
    specl_states=$(echo "$specl_output" | grep "States explored" | grep -oE '[0-9]+')
    echo "${specl_states} states in ${specl_time}s"

    # Specl with symmetry
    echo -n "Specl+sym: "
    specl_start=$(date +%s.%N)
    specl_output=$($SPECL check examples/benchmark/10-counters/counters.specl --constant N=$n --constant MAX=$max --symmetry 2>&1)
    specl_end=$(date +%s.%N)
    specl_time=$(echo "$specl_end - $specl_start" | bc)
    specl_states=$(echo "$specl_output" | grep "States explored" | grep -oE '[0-9]+')
    echo "${specl_states} states in ${specl_time}s"

    echo ""
}

# Run benchmarks
benchmark 2 3     # 64 states
benchmark 3 5     # 1296 states
benchmark 3 10    # 14641 states
benchmark 4 5     # 7776 states
benchmark 4 8     # 59049 states

# Cleanup
rm -f benchmarks/Counters_bench.cfg

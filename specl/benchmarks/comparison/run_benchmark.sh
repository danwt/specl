#!/bin/bash
# Benchmark Specl vs TLC on comparable specifications

set -e
cd "$(dirname "$0")/../.."

JAVA=.deps/jdk-21.0.5+11/Contents/Home/bin/java
TLC=.deps/tla2tools.jar
SPECL="./target/release/specl"
BENCH_DIR=benchmarks/comparison
COUNTERS_TLC_DIR=benchmarks
COUNTERS_SPECL_DIR=examples/benchmark/10-counters

# Build Specl
echo "Building Specl..."
cargo build --release --bin specl 2>/dev/null

echo ""
echo "================================================"
echo "          Specl vs TLC Benchmark"
echo "================================================"
echo ""

# Warmup TLC (JVM startup takes ~0.7s)
echo "Warming up JVM..."
$JAVA -XX:+UseParallelGC -Xmx4g -jar $TLC -h >/dev/null 2>&1 || true
echo ""

# Function to run TLC and extract metrics
run_tlc() {
    local spec=$1
    local cfg=$2
    local dir=${3:-$BENCH_DIR}

    local start_time=$(python3 -c "import time; print(time.time())")

    local output=$($JAVA -XX:+UseParallelGC -Xmx4g \
        -jar $TLC \
        -config "$dir/$cfg" \
        -workers auto \
        -nowarning \
        "$dir/$spec" 2>&1) || true

    local end_time=$(python3 -c "import time; print(time.time())")
    local elapsed=$(python3 -c "print(f'{$end_time - $start_time:.3f}')")

    # Extract distinct states
    local states=$(echo "$output" | grep -oE '[0-9]+ distinct states' | grep -oE '^[0-9]+')

    # Check result
    if echo "$output" | grep -q "Invariant.*violated"; then
        echo "  TLC:   ${states:-?} states, ${elapsed}s (violation)"
    elif echo "$output" | grep -q "Error:"; then
        local error=$(echo "$output" | grep "Error:" | head -1 | cut -c1-60)
        echo "  TLC:   ERROR: $error"
    else
        echo "  TLC:   ${states:-?} states, ${elapsed}s"
    fi
}

# Function to run Specl and extract metrics
run_specl() {
    local spec=$1
    local args=$2
    local dir=${3:-$BENCH_DIR}

    local start_time=$(python3 -c "import time; print(time.time())")

    local output=$($SPECL check "$dir/$spec" $args 2>&1) || true

    local end_time=$(python3 -c "import time; print(time.time())")
    local elapsed=$(python3 -c "print(f'{$end_time - $start_time:.3f}')")

    # Extract states
    local states=$(echo "$output" | grep -E "States explored:|states=" | grep -oE '[0-9]+' | head -1)

    if echo "$output" | grep -q "INVARIANT VIOLATION"; then
        echo "  Specl: ${states:-?} states, ${elapsed}s (violation)"
    elif echo "$output" | grep -q "DEADLOCK"; then
        echo "  Specl: ${states:-?} states, ${elapsed}s (deadlock)"
    elif echo "$output" | grep -q "Result: OK"; then
        echo "  Specl: ${states:-?} states, ${elapsed}s"
    else
        echo "  Specl: ${states:-?} states, ${elapsed}s"
    fi
}

# Create temp config for counters benchmark
create_counters_cfg() {
    local n=$1
    local max=$2
    cat > "$COUNTERS_TLC_DIR/Counters_bench.cfg" << EOF
CONSTANTS
    N = $n
    MAX = $max
INIT Init
NEXT Next
INVARIANT AllInRange
CHECK_DEADLOCK FALSE
EOF
}

# ============================================
# Standard Example Specs
# ============================================
echo "=== Standard Example Specifications ==="
echo ""

echo "--- DieHard (16 states) ---"
run_tlc "DieHard.tla" "DieHard.cfg"
run_specl "DieHard.specl" ""
echo ""

echo "--- TCommit (34 states) ---"
run_tlc "TCommit.tla" "TCommit.cfg"
run_specl "TCommit.specl" "--no-deadlock"
echo ""

echo "--- EWD840 (3646 states) ---"
run_tlc "EWD840.tla" "EWD840.cfg"
run_specl "EWD840.specl" ""
echo ""

# ============================================
# Scaling Benchmarks (Counters)
# ============================================
echo "=== Scaling Benchmarks (Counters) ==="
echo "  State space = (MAX+1)^(N+1)"
echo ""

echo "--- N=2, MAX=4 (125 states) ---"
create_counters_cfg 2 4
run_tlc "Counters.tla" "Counters_bench.cfg" "$COUNTERS_TLC_DIR"
run_specl "counters.specl" "-c N=2 -c MAX=4" "$COUNTERS_SPECL_DIR"
echo ""

echo "--- N=2, MAX=9 (1,000 states) ---"
create_counters_cfg 2 9
run_tlc "Counters.tla" "Counters_bench.cfg" "$COUNTERS_TLC_DIR"
run_specl "counters.specl" "-c N=2 -c MAX=9" "$COUNTERS_SPECL_DIR"
echo ""

echo "--- N=3, MAX=9 (10,000 states) ---"
create_counters_cfg 3 9
run_tlc "Counters.tla" "Counters_bench.cfg" "$COUNTERS_TLC_DIR"
run_specl "counters.specl" "-c N=3 -c MAX=9" "$COUNTERS_SPECL_DIR"
echo ""

echo "--- N=3, MAX=14 (50,625 states) ---"
create_counters_cfg 3 14
run_tlc "Counters.tla" "Counters_bench.cfg" "$COUNTERS_TLC_DIR"
run_specl "counters.specl" "-c N=3 -c MAX=14" "$COUNTERS_SPECL_DIR"
echo ""

echo "--- N=4, MAX=9 (100,000 states) ---"
create_counters_cfg 4 9
run_tlc "Counters.tla" "Counters_bench.cfg" "$COUNTERS_TLC_DIR"
run_specl "counters.specl" "-c N=4 -c MAX=9" "$COUNTERS_SPECL_DIR"
echo ""

echo "--- N=4, MAX=13 (537,824 states) ---"
create_counters_cfg 4 13
run_tlc "Counters.tla" "Counters_bench.cfg" "$COUNTERS_TLC_DIR"
run_specl "counters.specl" "-c N=4 -c MAX=13" "$COUNTERS_SPECL_DIR"
echo ""

echo "--- N=5, MAX=9 (1,000,000 states) ---"
create_counters_cfg 5 9
run_tlc "Counters.tla" "Counters_bench.cfg" "$COUNTERS_TLC_DIR"
run_specl "counters.specl" "-c N=5 -c MAX=9" "$COUNTERS_SPECL_DIR"
echo ""

# Cleanup
rm -f "$COUNTERS_TLC_DIR/Counters_bench.cfg"

echo "================================================"
echo "                  Summary"
echo "================================================"
echo "TLC times include ~0.7s JVM startup overhead."
echo "For fair comparison, subtract ~0.7s from TLC times."
echo ""

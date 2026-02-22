#!/bin/bash
# Benchmark Specl vs TLC on Realistic Specifications

set -e
cd "$(dirname "$0")/../.."

JAVA=.deps/jdk-21.0.5+11/Contents/Home/bin/java
TLC=.deps/tla2tools.jar
SPECL="./target/release/specl"
BENCH_DIR=benchmarks/comparison
REALISTIC_DIR=examples/realistic

# Build Specl
echo "Building Specl..."
cargo build --release --bin specl 2>/dev/null

echo ""
echo "================================================"
echo "   Realistic Specs: Specl vs TLC Benchmark"
echo "================================================"
echo ""

# Warmup JVM
$JAVA -version >/dev/null 2>&1

# Function to run TLC
run_tlc() {
    local spec=$1
    local cfg=$2
    local dir=$3

    local start_time=$(python3 -c "import time; print(time.time())")
    local output=$($JAVA -XX:+UseParallelGC -Xmx4g \
        -jar $TLC \
        -config "$dir/$cfg" \
        -workers auto \
        -nowarning \
        "$dir/$spec" 2>&1) || true
    local end_time=$(python3 -c "import time; print(time.time())")
    local elapsed=$(python3 -c "print(f'{$end_time - $start_time:.3f}')")
    local states=$(echo "$output" | /usr/bin/grep -oE '[0-9]+ distinct states' | /usr/bin/grep -oE '^[0-9]+')
    echo "  TLC:   ${states:-?} states, ${elapsed}s"
}

# Function to run Specl
run_specl() {
    local spec=$1
    local args=$2
    local dir=$3

    local start_time=$(python3 -c "import time; print(time.time())")
    local output=$($SPECL check "$dir/$spec" $args 2>&1) || true
    local end_time=$(python3 -c "import time; print(time.time())")
    local elapsed=$(python3 -c "print(f'{$end_time - $start_time:.3f}')")
    local states=$(echo "$output" | /usr/bin/grep -E "States explored:" | /usr/bin/grep -oE '[0-9]+')
    echo "  Specl: ${states:-?} states, ${elapsed}s"
}

# Create TLA+ config for TCommit
create_tcommit_cfg() {
    local n=$1
    local rms=""
    for i in $(seq 1 $n); do
        if [ -z "$rms" ]; then
            rms="$i"
        else
            rms="$rms, $i"
        fi
    done
    cat > "$BENCH_DIR/TCommit_${n}.cfg" << EOF
CONSTANTS
    RM = {$rms}
INIT TCInit
NEXT TCNext
INVARIANT TCTypeOK
INVARIANT TCConsistent
CHECK_DEADLOCK FALSE
EOF
}

# Create TCommit specl for different sizes
create_tcommit_specl() {
    local n=$1
    cat > "$BENCH_DIR/TCommit_${n}.specl" << EOF
module TCommit
var rmState: Dict[Int, String]
init { rmState == {rm: "working" for rm in 1..${n}} }
invariant TCTypeOK { all rm in 1..${n}: rmState[rm] in {"working", "prepared", "committed", "aborted"} }
invariant TCConsistent { all rm1 in 1..${n}: all rm2 in 1..${n}: not (rmState[rm1] == "aborted" and rmState[rm2] == "committed") }
action Prepare(rm: 1..${n}) { require rmState[rm] == "working"; rmState = rmState | { rm: "prepared" } }
action DecideCommit(rm: 1..${n}) { require rmState[rm] == "prepared"; require all r in 1..${n}: rmState[r] in {"prepared", "committed"}; rmState = rmState | { rm: "committed" } }
action DecideAbort(rm: 1..${n}) { require rmState[rm] in {"working", "prepared"}; require all r in 1..${n}: rmState[r] != "committed"; rmState = rmState | { rm: "aborted" } }
EOF
}

# Create EWD840 TLA+ config
create_ewd840_cfg() {
    local n=$1
    cat > "$BENCH_DIR/EWD840_${n}.cfg" << EOF
CONSTANTS
    N = $n
INIT Init
NEXT Next
INVARIANT TerminationDetection
CHECK_DEADLOCK FALSE
EOF
}

# Create EWD840 specl for different sizes
create_ewd840_specl() {
    local n=$1
    local range=$((n-1))
    cat > "$BENCH_DIR/EWD840_${n}.specl" << EOF
module EWD840
var active: Dict[Int, Bool]
var color: Dict[Int, String]
var tpos: Int
var tcolor: String
init {
    active == {i: true for i in 0..${range}}
    and color == {i: "white" for i in 0..${range}}
    and tpos == 0
    and tcolor == "black"
}
invariant TerminationDetection {
    (tpos == 0 and tcolor == "white" and color[0] == "white" and not active[0])
    implies (all i in 0..${range}: not active[i])
}
action InitiateProbe() {
    require tpos == 0
    require tcolor == "black" or color[0] == "black"
    tpos = ${range}
    and tcolor = "white"
    and color = color | { 0: "white" }
    and active = active
}
action PassToken(i: 1..${range}) {
    require tpos == i
    require not active[i] or color[i] == "black" or tcolor == "black"
    tpos = i - 1
    and tcolor = (if color[i] == "black" then "black" else tcolor)
    and color = color | { i: "white" }
    and active = active
}
action SendMsg(i: 0..${range}, j: 0..${range}) {
    require active[i]
    require i != j
    active = active | { j: true }
    and color = color | { i: (if j > i then "black" else color[i]) }
    and tpos = tpos
    and tcolor = tcolor
}
action Deactivate(i: 0..${range}) {
    require active[i]
    active = active | { i: false }
    and color = color
    and tpos = tpos
    and tcolor = tcolor
}
action Stutter() {
    require tpos == 0 and tcolor == "white" and color[0] == "white" and not active[0]
    active = active
    and color = color
    and tpos = tpos
    and tcolor = tcolor
}
EOF
}

# ============================================
# TCommit Scaling
# ============================================
echo "=== TCommit (Transaction Commit) ==="
echo ""

for n in 3 4 5 6; do
    echo "--- TCommit with $n Resource Managers ---"
    create_tcommit_cfg $n
    create_tcommit_specl $n
    run_tlc "TCommit.tla" "TCommit_${n}.cfg" "$BENCH_DIR"
    run_specl "TCommit_${n}.specl" "--no-deadlock" "$BENCH_DIR"
    echo ""
done

# ============================================
# EWD840 Scaling
# ============================================
echo "=== EWD840 (Termination Detection) ==="
echo ""

for n in 4 5 6; do
    echo "--- EWD840 with $n Nodes ---"
    create_ewd840_cfg $n
    create_ewd840_specl $n
    run_tlc "EWD840.tla" "EWD840_${n}.cfg" "$BENCH_DIR"
    run_specl "EWD840_${n}.specl" "" "$BENCH_DIR"
    echo ""
done

# ============================================
# Full TwoPhaseCommit (with messages)
# ============================================
echo "=== TwoPhaseCommit (with message passing) ==="
echo ""

for n in 2 3; do
    echo "--- TwoPhaseCommit with N=$n ---"
    run_specl "TwoPhaseCommit.specl" "-c N=$n --no-deadlock" "$REALISTIC_DIR"
    echo ""
done

# Cleanup temp files
rm -f "$BENCH_DIR"/TCommit_*.cfg "$BENCH_DIR"/TCommit_*.specl
rm -f "$BENCH_DIR"/EWD840_*.cfg "$BENCH_DIR"/EWD840_*.specl

echo "================================================"
echo "Notes:"
echo "- TLC times include ~0.7s JVM startup"
echo "- TCommit and EWD840 use matched spec semantics"
echo "================================================"

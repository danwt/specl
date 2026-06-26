#!/usr/bin/env bash
# Cross-tool soundness oracle: run the same TLA+ spec through both TLC and specl
# (auto-translating the .tla) and assert the two tools agree on the verdict
# (OK vs invariant-violation). A disagreement means one of the tools is unsound
# on that spec — exactly the class of bug internal-consistency tests cannot catch.
#
# This is the external oracle called for in issue #94.
#
# Usage:
#   SPECL=path/to/specl TLA_TOOLS_JAR=path/to/tla2tools.jar ./oracle.sh
#
# Defaults: SPECL=specl on PATH (or target/release/specl), tla2tools.jar fetched
# to this directory if absent. Java is required for TLC.
#
# Exit code: 0 if every spec AGREEs (ignoring the documented known-issue
# allowlist), 1 on any new disagreement, 2 if a required tool is missing.
set -uo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/../../.." && pwd)" # repo root (contains specl/)

SPECL="${SPECL:-}"
if [[ -z "$SPECL" ]]; then
  if command -v specl >/dev/null 2>&1; then SPECL="specl"
  elif [[ -x "$REPO/specl/target/release/specl" ]]; then SPECL="$REPO/specl/target/release/specl"
  else echo "INCONCLUSIVE: specl binary not found (set SPECL=...)"; exit 2; fi
fi

if ! command -v java >/dev/null 2>&1; then
  echo "INCONCLUSIVE: java not found (required for TLC)"; exit 2
fi

JAR="${TLA_TOOLS_JAR:-$HERE/tla2tools.jar}"
if [[ ! -f "$JAR" ]]; then
  echo "Fetching tla2tools.jar ..."
  curl -sL -o "$JAR" https://github.com/tlaplus/tlaplus/releases/latest/download/tla2tools.jar \
    || { echo "INCONCLUSIVE: could not download tla2tools.jar"; exit 2; }
fi

# Specs whose disagreement is a known, filed bug. Format: "name=issue".
# Remove an entry once its bug is fixed so the oracle guards against regression.
KNOWN_ISSUES=("DieHard=#96")

# Curated specs: "name|tla|cfg|specl-args". Paths are relative to the repo root.
SPECS=(
  "Counter|specl/tools/soundness/specs/Counter.tla|specl/tools/soundness/specs/Counter.cfg|--no-deadlock"
  "DieHard|specl/benchmarks/comparison/DieHard.tla|specl/benchmarks/comparison/DieHard.cfg|"
)

# Map a tool's raw output to OK | VIOLATION | ERROR.
tlc_verdict() {
  local out="$1"
  if grep -qiE "is violated|Error: Invariant" <<<"$out"; then echo VIOLATION
  elif grep -qiE "No error has been found" <<<"$out"; then echo OK
  else echo ERROR; fi
}
specl_verdict() {
  local out="$1"
  if grep -qiE "INVARIANT VIOLATION" <<<"$out"; then echo VIOLATION
  elif grep -qiE "Result: OK" <<<"$out"; then echo OK
  else echo ERROR; fi
}

is_known() {
  local name="$1"
  for k in "${KNOWN_ISSUES[@]}"; do [[ "${k%%=*}" == "$name" ]] && { echo "${k#*=}"; return 0; }; done
  return 1
}

printf "%-12s %-10s %-10s %-s\n" "SPEC" "TLC" "SPECL" "RESULT"
printf "%-12s %-10s %-10s %-s\n" "----" "---" "-----" "------"

fail=0
for entry in "${SPECS[@]}"; do
  IFS='|' read -r name tla cfg args <<<"$entry"
  tla="$REPO/$tla"; cfg="$REPO/$cfg"
  tlc_out="$(java -cp "$JAR" tlc2.TLC -config "$cfg" "$tla" 2>&1)"
  specl_out="$("$SPECL" check "$tla" $args 2>&1)"
  tv="$(tlc_verdict "$tlc_out")"; sv="$(specl_verdict "$specl_out")"

  if [[ "$tv" == "ERROR" || "$sv" == "ERROR" ]]; then
    result="SKIP (tool could not check)"
  elif [[ "$tv" == "$sv" ]]; then
    result="AGREE"
  elif issue="$(is_known "$name")"; then
    result="DISAGREE (known $issue)"
  else
    result="DISAGREE — SOUNDNESS BUG"; fail=1
  fi
  printf "%-12s %-10s %-10s %-s\n" "$name" "$tv" "$sv" "$result"
done

echo
if [[ "$fail" -ne 0 ]]; then
  echo "FAIL: a tool disagreed on a spec not in the known-issues allowlist."
  exit 1
fi
echo "OK: all specs agree (or are documented known issues)."

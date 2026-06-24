#!/bin/bash
set -euo pipefail

# Tests for disprove_artifact_txn.py (transactional append/drop/rollback).

: "${TMPDIR:=/tmp}"
export TMPDIR

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TXN="$SCRIPT_DIR/../lib/scripts/disprove_artifact_txn.py"

PASS=0
FAIL=0
WORK=""
trap 'rm -rf "$WORK"' EXIT
WORK=$(mktemp -d "${TMPDIR}/disprove_txn_test.XXXXXX")

pass() { echo "  PASS: $1"; PASS=$((PASS + 1)); }
fail() { echo "  FAIL: $1"; echo "        $2"; FAIL=$((FAIL + 1)); }

# run <stdin-string> <args...>  — runs the script in the PARENT shell (not piped
# into a function, so $? propagates).
LAST_EXIT=0
run() {
  local stdin="$1"; shift
  LAST_EXIT=0
  printf '%s' "$stdin" | python3 "$TXN" "$@" >"$WORK/out" 2>"$WORK/err" || LAST_EXIT=$?
}

assert_exit() {
  if [ "$LAST_EXIT" -eq "$2" ]; then pass "$1"
  else fail "$1" "expected exit $2 got $LAST_EXIT (err: $(cat "$WORK/err"))"; fi
}
# assert_count <desc> <file> <pattern> <expected-line-count>
assert_count() {
  local n; n=$(grep -c "$3" "$2" || true)
  if [ "$n" -eq "$4" ]; then pass "$1"; else fail "$1" "pattern '$3': expected $4 lines, got $n"; fi
}

F="$WORK/T.lean"
printf 'import Mathlib\ntheorem pre : True := trivial\n' > "$F"

echo "-- begin returns distinct txn ids --"
TXN1=$(python3 "$TXN" begin)
TXN2=$(python3 "$TXN" begin)
{ [ -n "$TXN1" ] && [ "$TXN1" != "$TXN2" ]; } && pass "1. begin gives distinct ids" \
  || fail "1. begin gives distinct ids" "txn1=$TXN1 txn2=$TXN2"

echo "-- append artifact + gate under txn1, a second artifact under txn2 --"
run 'theorem foo_counterexample : True := trivial' append --scope-file="$F" --txn="$TXN1" --role=artifact --decl=foo_counterexample --cycle=2
assert_exit "2. append artifact txn1" 0
run 'theorem foo_negates_target : True := trivial' append --scope-file="$F" --txn="$TXN1" --role=gate --decl=foo_negates_target
assert_exit "3. append gate txn1" 0
run 'theorem bar_counterexample : True := trivial' append --scope-file="$F" --txn="$TXN2" --role=artifact --decl=bar_counterexample
assert_exit "4. append artifact txn2" 0
assert_count "4b. foo_counterexample present" "$F" "^theorem foo_counterexample" 1
assert_count "4c. foo_negates_target present" "$F" "^theorem foo_negates_target" 1
assert_count "4d. bar_counterexample present" "$F" "^theorem bar_counterexample" 1

echo "-- idempotent re-append of same txn/role/decl --"
run 'theorem foo_counterexample : True := trivial' append --scope-file="$F" --txn="$TXN1" --role=artifact --decl=foo_counterexample --cycle=2
assert_exit "5. re-append idempotent (exit 0)" 0
assert_count "5b. still exactly one foo_counterexample" "$F" "^theorem foo_counterexample" 1

echo "-- collision: name already declared outside the txn (pre) --"
run 'theorem pre : True := trivial' append --scope-file="$F" --txn="$TXN1" --role=artifact --decl=pre
assert_exit "6. collision with pre-existing decl → exit 2" 2

echo "-- drop-role gate on txn1: gate gone, artifact stays, txn2 untouched --"
run "" drop-role --scope-file="$F" --txn="$TXN1" --role=gate
assert_exit "7. drop-role exit 0" 0
assert_count "7b. gate removed" "$F" "^theorem foo_negates_target" 0
assert_count "7c. txn1 artifact stays" "$F" "^theorem foo_counterexample" 1
assert_count "7d. txn2 artifact untouched" "$F" "^theorem bar_counterexample" 1

echo "-- rollback txn1: all txn1 gone, txn2 + pre-existing untouched --"
run "" rollback --scope-file="$F" --txn="$TXN1"
assert_exit "8. rollback exit 0" 0
assert_count "8b. txn1 artifact gone" "$F" "^theorem foo_counterexample" 0
assert_count "8c. txn2 artifact survives rollback of txn1" "$F" "^theorem bar_counterexample" 1
assert_count "8d. pre-existing decl untouched" "$F" "^theorem pre" 1
assert_count "8e. no txn1 markers remain" "$F" "txn=$TXN1" 0

echo ""
echo "=== Results: $PASS passed, $FAIL failed ==="
[ "$FAIL" -eq 0 ]

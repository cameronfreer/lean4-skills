#!/usr/bin/env bash
set -euo pipefail

# System /bin/bash smoke test for cycle_tracker.sh.
#
# On macOS, /bin/bash is 3.2 with BSD userland — this test exercises
# both Bash-syntax and BSD-tool portability (e.g. mktemp) on that
# platform. On Linux, /bin/bash is typically 5.x+ with GNU userland,
# so the test still validates Bash syntax but does NOT exercise
# BSD-specific behavior. BSD/macOS semantics are only fully covered
# when this test runs on macOS.
#
# Skips gracefully if /bin/bash doesn't exist (e.g. minimal containers).

# Resolve TMPDIR once (matches cycle_tracker.sh): honor caller's TMPDIR,
# fall back to /tmp. Export so the tracker subprocess sees the same value.
: "${TMPDIR:=/tmp}"
export TMPDIR

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TRACKER="$SCRIPT_DIR/../lib/scripts/cycle_tracker.sh"

if [[ ! -x /bin/bash ]]; then
  echo "SKIP: /bin/bash not found — cannot run Bash 3.2 smoke test"
  exit 0
fi

PASS=0
FAIL=0

BASH_VER=$(/bin/bash -c 'echo $BASH_VERSION')
echo "Running cycle_tracker.sh smoke tests under /bin/bash ($BASH_VER)"
echo ""

# Helper: run tracker under /bin/bash.
#   LAST_STDOUT — stdout only (init prints the session id here).
#   LAST_OUT    — merged, used by existing failure diagnostics.
#   LAST_EXIT   — exit code.
# Split-stream capture so init's stderr hint (LEAN4_SESSION_DIR=<dir> when
# no env file resolves) does not pollute the session-id capture.
LAST_OUT=""
LAST_STDOUT=""
LAST_EXIT=0
run() {
  local _stderr_file
  _stderr_file=$(mktemp)
  LAST_EXIT=0
  LAST_STDOUT=$(/bin/bash "$TRACKER" "$@" 2>"$_stderr_file") || LAST_EXIT=$?
  local _stderr
  _stderr=$(cat "$_stderr_file")
  rm -f "$_stderr_file"
  if [[ -n "$_stderr" ]]; then
    LAST_OUT="${LAST_STDOUT}"$'\n'"${_stderr}"
  else
    LAST_OUT="$LAST_STDOUT"
  fi
}

assert_exit() {
  local desc="$1" expected="$2"
  if [[ "$LAST_EXIT" -eq "$expected" ]]; then
    echo "  PASS: $desc"
    ((PASS++)) || true
  else
    echo "  FAIL: $desc (expected exit $expected, got $LAST_EXIT)"
    echo "  Output: $LAST_OUT"
    ((FAIL++)) || true
  fi
}

cleanup() {
  if [[ -n "${SESSION_ID:-}" ]]; then
    /bin/bash "$TRACKER" stop 2>/dev/null || true
    rm -f "${LEAN4_SESSION_DIR:-$TMPDIR}/${SESSION_ID}.json" 2>/dev/null || true
  fi
  unset LEAN4_SESSION_ID
}
trap cleanup EXIT

# ---------------------------------------------------------------------------
# Test 1: init with minute duration
# ---------------------------------------------------------------------------
echo "-- init + basic lifecycle --"

run init --max-cycles=3 --max-stuck=2 --max-runtime=60m
assert_exit "init with --max-runtime=60m" 0
SESSION_ID="$LAST_STDOUT"
export LEAN4_SESSION_ID="$SESSION_ID"

# ---------------------------------------------------------------------------
# Test 2: status after init
# ---------------------------------------------------------------------------
run status
assert_exit "status after init" 0

# ---------------------------------------------------------------------------
# Test 3: tick
# ---------------------------------------------------------------------------
run tick --stuck=no
assert_exit "tick --stuck=no" 0

# ---------------------------------------------------------------------------
# Test 4: stop
# ---------------------------------------------------------------------------
run stop
assert_exit "stop" 0
cleanup

# ---------------------------------------------------------------------------
# Test 5: init with second duration (the 30s case that broke with floor-to-minutes)
# ---------------------------------------------------------------------------
echo ""
echo "-- second-based duration --"

run init --max-cycles=3 --max-stuck=2 --max-runtime=30s
assert_exit "init with --max-runtime=30s" 0
SESSION_ID="$LAST_STDOUT"
export LEAN4_SESSION_ID="$SESSION_ID"
run stop
assert_exit "stop after 30s init" 0
cleanup

# ---------------------------------------------------------------------------
# Test 6: init with uppercase suffix (the ${suffix,,} case)
# ---------------------------------------------------------------------------
echo ""
echo "-- uppercase suffix --"

run init --max-cycles=3 --max-stuck=2 --max-runtime=60M
assert_exit "init with --max-runtime=60M (uppercase)" 0
SESSION_ID="$LAST_STDOUT"
export LEAN4_SESSION_ID="$SESSION_ID"
run stop
assert_exit "stop after 60M init" 0
cleanup

# ---------------------------------------------------------------------------
# Test 7: init with no runtime (optional omission)
# ---------------------------------------------------------------------------
echo ""
echo "-- optional runtime omission --"

run init --max-cycles=3 --max-stuck=2
assert_exit "init without --max-runtime" 0
SESSION_ID="$LAST_STDOUT"
export LEAN4_SESSION_ID="$SESSION_ID"
run stop
assert_exit "stop after no-runtime init" 0
cleanup

# ---------------------------------------------------------------------------
# Test 8: mktemp regression — two consecutive inits yield distinct non-literal IDs
# ---------------------------------------------------------------------------
echo ""
echo "-- mktemp regression (BSD portability) --"

run init --max-cycles=1 --max-stuck=1
assert_exit "first init for mktemp check" 0
ID1="$LAST_STDOUT"
export LEAN4_SESSION_ID="$ID1"
run stop
cleanup

run init --max-cycles=1 --max-stuck=1
assert_exit "second init for mktemp check" 0
ID2="$LAST_STDOUT"
export LEAN4_SESSION_ID="$ID2"
SESSION_ID="$ID2"
run stop
cleanup

# The broken BSD mktemp produced the literal "lean4-session-XXXXXX" every time.
if [[ "$ID1" == "lean4-session-XXXXXX" ]]; then
  echo "  FAIL: first session ID is the literal template 'lean4-session-XXXXXX' — mktemp is broken"
  ((FAIL++)) || true
else
  echo "  PASS: first session ID is not the literal template ($ID1)"
  ((PASS++)) || true
fi

if [[ "$ID1" == "$ID2" ]]; then
  echo "  FAIL: two consecutive inits produced the same session ID ($ID1) — mktemp not generating unique names"
  ((FAIL++)) || true
else
  echo "  PASS: two consecutive inits produced distinct IDs ($ID1 vs $ID2)"
  ((PASS++)) || true
fi

# ---------------------------------------------------------------------------
# Test 9: conclusion phase (#85) — reserve parsing (leading zeros stripped and
# magnitudes compared as text: nested ${x#"${x%%[!0]*}"}, [[ a > b ]]; ${x%\%}),
# the due tick, the latch, and startup validation errors
# ---------------------------------------------------------------------------
echo ""
echo "-- conclusion phase (#85) --"

assert_out() {
  local desc="$1" expected="$2"
  if [[ "$LAST_OUT" == *"$expected"* ]]; then
    echo "  PASS: $desc"
    ((PASS++)) || true
  else
    echo "  FAIL: $desc (output missing '$expected')"
    echo "  Output: $LAST_OUT"
    ((FAIL++)) || true
  fi
}

run init --max-cycles=4 --max-stuck=3 --max-runtime=60m --conclude-after=015%
assert_exit "init with --conclude-after=015% (leading zero)" 0
SESSION_ID="$LAST_STDOUT"
export LEAN4_SESSION_ID="$SESSION_ID"
run status
assert_out "15% of 60m reserves 540s" "conclude_reserve_runtime_seconds=540"
run tick --stuck=no
run tick --stuck=no
run tick --stuck=no
assert_out "cycle 3 of 4 is due" "conclude=yes"
run conclude
assert_exit "conclude latches" 0
assert_out "snapshot at cycle 3" "conclude_at_cycles=3"
run tick --stuck=yes
assert_exit "the conclusion cycle's tick reaches max-cycles" 1
assert_out "stop_reason names the limit" "stop_reason=max-cycles"
assert_out "still latched" "concluding=yes"
run stop
cleanup

run init --max-cycles=4 --max-stuck=3 --conclude-after=0c
assert_exit "--conclude-after=0c is a startup error" 2

run init --max-cycles=20 --max-stuck=3 --conclude-after=10000000000000000000c
assert_exit "an over-long count is refused, not wrapped" 2
assert_out "refused as larger than its budget" "reserve larger than its budget"
run init --max-cycles=20 --max-stuck=3 --conclude-after=20c
assert_exit "an equal-length count equal to the budget is refused" 2
run init --max-cycles=20 --max-stuck=3 --conclude-after=51%
assert_exit "51% is refused" 2
run init --max-cycles=20 --max-stuck=3 --max-runtime=60m --conclude-after=0000000000000000000019c
assert_exit "a long zero-padded count is accepted" 0
SESSION_ID="$LAST_STDOUT"
export LEAN4_SESSION_ID="$SESSION_ID"
run status
assert_out "padding stripped: 19 reserved cycles" "conclude_reserve_cycles=19"
run stop
cleanup

# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------
echo ""
echo "=== Results: $PASS passed, $FAIL failed (under /bin/bash $BASH_VER) ==="
[[ "$FAIL" -eq 0 ]]

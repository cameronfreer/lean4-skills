#!/bin/bash
set -euo pipefail

# Runtime smoke test for cycle_tracker.sh under /bin/bash.
#
# On macOS, /bin/bash is 3.2. On Linux, it's typically 5.x+.
# Either way, this test proves the tracker runs under the system's
# default /bin/bash — catching portability issues like ${suffix,,}
# and BSD mktemp that static lint alone cannot detect.
#
# Skips gracefully if /bin/bash doesn't exist (e.g. minimal containers).

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

# Helper: run tracker under /bin/bash
LAST_OUT=""
LAST_EXIT=0
run() {
  LAST_EXIT=0
  LAST_OUT=$(/bin/bash "$TRACKER" "$@" 2>&1) || LAST_EXIT=$?
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
    rm -f "/tmp/${SESSION_ID}.json" 2>/dev/null || true
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
SESSION_ID="$LAST_OUT"
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
SESSION_ID="$LAST_OUT"
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
SESSION_ID="$LAST_OUT"
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
SESSION_ID="$LAST_OUT"
export LEAN4_SESSION_ID="$SESSION_ID"
run stop
assert_exit "stop after no-runtime init" 0
cleanup

# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------
echo ""
echo "=== Results: $PASS passed, $FAIL failed (under /bin/bash $BASH_VER) ==="
[[ "$FAIL" -eq 0 ]]

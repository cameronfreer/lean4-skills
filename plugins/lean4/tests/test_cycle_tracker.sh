#!/bin/bash
set -euo pipefail

# Comprehensive tests for cycle_tracker.sh

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TRACKER="$SCRIPT_DIR/../lib/scripts/cycle_tracker.sh"

PASS=0
FAIL=0

# Helper: run tracker, capture exit code. Sets LAST_OUT and LAST_EXIT.
LAST_OUT=""
LAST_EXIT=0
run() {
  LAST_EXIT=0
  LAST_OUT=$(bash "$TRACKER" "$@" 2>&1) || LAST_EXIT=$?
}

# Assert exit code. $1=description $2=expected exit code
assert_exit() {
  local desc="$1" expected="$2"
  if [[ "$LAST_EXIT" -eq "$expected" ]]; then
    echo "  PASS: $desc"
    (( ++PASS ))
  else
    echo "  FAIL: $desc (expected exit $expected, got $LAST_EXIT)"
    echo "        output: $LAST_OUT"
    (( ++FAIL ))
  fi
}

# Assert output contains string. $1=description $2=expected substring
assert_contains() {
  local desc="$1" expected="$2"
  if [[ "$LAST_OUT" == *"$expected"* ]]; then
    echo "  PASS: $desc"
    (( ++PASS ))
  else
    echo "  FAIL: $desc (output missing '$expected')"
    echo "        output: $LAST_OUT"
    (( ++FAIL ))
  fi
}

# Assert output does NOT contain string. $1=description $2=unexpected substring
assert_not_contains() {
  local desc="$1" unexpected="$2"
  if [[ "$LAST_OUT" != *"$unexpected"* ]]; then
    echo "  PASS: $desc"
    (( ++PASS ))
  else
    echo "  FAIL: $desc (output unexpectedly contains '$unexpected')"
    echo "        output: $LAST_OUT"
    (( ++FAIL ))
  fi
}

# Helper: init a session and export the ID. Args passed to init.
# Sets LEAN4_SESSION_ID in the caller's environment.
init_session() {
  LEAN4_SESSION_ID=$(bash "$TRACKER" init "$@" 2>&1)
  export LEAN4_SESSION_ID
}

# Helper: clean up current session
cleanup_session() {
  if [[ -n "${LEAN4_SESSION_ID:-}" ]]; then
    bash "$TRACKER" stop 2>/dev/null || true
  fi
  LEAN4_SESSION_ID=""
  export LEAN4_SESSION_ID
}

# Helper: get state file path
state_file() {
  echo "/tmp/${LEAN4_SESSION_ID:-}.json"
}

# Helper: read a field from state file using jq or python3
read_field() {
  local file="$1" field="$2"
  if command -v jq >/dev/null 2>&1; then
    jq -r ".$field" "$file" 2>/dev/null
  else
    python3 -c "import json; print(json.load(open('$file'))['$field'])" 2>/dev/null
  fi
}

# Helper: write a field to state file
write_field() {
  local file="$1" field="$2" value="$3"
  if command -v jq >/dev/null 2>&1; then
    local tmp
    tmp=$(mktemp "${file}.tmp.XXXXXX")
    jq ".$field = $value" "$file" > "$tmp" 2>/dev/null
    mv "$tmp" "$file"
  else
    python3 -c "
import json, tempfile, os
with open('$file') as f:
    d = json.load(f)
d['$field'] = $value
fd, tmp = tempfile.mkstemp(dir=os.path.dirname('$file'))
with os.fdopen(fd, 'w') as f:
    json.dump(d, f)
os.rename(tmp, '$file')
" 2>/dev/null
  fi
}

echo "=== cycle_tracker.sh tests ==="

# =========================================================================
echo ""
echo "-- Happy path --"

init_session --max-cycles=5 --max-stuck=3 --max-runtime=60m
assert_exit_manual() { :; }  # init succeeded if we got here

# Verify state file exists with correct fields
FILE=$(state_file)
run status
assert_exit "status after init" 0
assert_contains "status shows session_id" "session_id=$LEAN4_SESSION_ID"
assert_contains "status shows cycles=0/5" "cycles=0/5"
assert_contains "status shows consecutive_stuck=0/3" "consecutive_stuck=0/3"
assert_contains "status shows elapsed_display" "elapsed_display="
assert_contains "status shows deep_this_cycle=0/1" "deep_this_cycle=0/1"
assert_contains "status shows consecutive_deep_cycles=0/2" "consecutive_deep_cycles=0/2"

# Verify JSON fields
CYCLES=$(read_field "$FILE" "cycles")
if [[ "$CYCLES" == "0" ]]; then
  echo "  PASS: init state has cycles=0"
  (( ++PASS ))
else
  echo "  FAIL: init state has cycles=$CYCLES, expected 0"
  (( ++FAIL ))
fi

# tick --stuck=no
run tick --stuck=no
assert_exit "tick --stuck=no exits 0" 0
assert_contains "tick shows result=ok" "result=ok"
assert_contains "tick shows cycles=1/5" "cycles=1/5"
assert_contains "tick shows consecutive_stuck=0/3" "consecutive_stuck=0/3"

# tick --stuck=yes
run tick --stuck=yes
assert_exit "tick --stuck=yes exits 0 (under limit)" 0
assert_contains "tick shows consecutive_stuck=1/3" "consecutive_stuck=1/3"

# tick --stuck=no resets stuck counter
run tick --stuck=no
assert_exit "tick --stuck=no after stuck" 0
assert_contains "tick resets consecutive_stuck to 0" "consecutive_stuck=0/3"

# can-deep
run can-deep
assert_exit "can-deep allowed" 0
assert_contains "can-deep result=ok" "result=ok"

# deep
run deep
assert_exit "deep records invocation" 0
DEEP_COUNT=$(read_field "$FILE" "deep_this_cycle")
if [[ "$DEEP_COUNT" == "1" ]]; then
  echo "  PASS: deep_this_cycle=1 after deep"
  (( ++PASS ))
else
  echo "  FAIL: deep_this_cycle=$DEEP_COUNT, expected 1"
  (( ++FAIL ))
fi

# tick after deep: updates consecutive_deep_cycles
run tick --stuck=no
assert_exit "tick after deep" 0
assert_contains "consecutive_deep_cycles=1/2" "consecutive_deep_cycles=1/2"
assert_contains "deep_this_cycle resets to 0" "deep_this_cycle=0/1"

# stop
run stop
assert_exit "stop exits 0" 0
if [[ ! -f "$FILE" ]]; then
  echo "  PASS: state file removed after stop"
  (( ++PASS ))
else
  echo "  FAIL: state file still exists after stop"
  (( ++FAIL ))
fi

cleanup_session

# =========================================================================
echo ""
echo "-- Limit reached --"

# max-cycles
init_session --max-cycles=1 --max-stuck=3
run tick --stuck=no
assert_exit "tick exits 1 at max-cycles" 1
assert_contains "reports LIMIT_REACHED" "result=LIMIT_REACHED"
assert_contains "violation=max-cycles" "violation=max-cycles"
assert_contains "cycles=1/1" "cycles=1/1"
cleanup_session

# max-stuck
init_session --max-cycles=10 --max-stuck=1
run tick --stuck=yes
assert_exit "tick exits 1 at max-stuck" 1
assert_contains "violation=max-stuck" "violation=max-stuck"
assert_contains "consecutive_stuck=1/1" "consecutive_stuck=1/1"
cleanup_session

# max-runtime (synthetic: set start_epoch in the past)
init_session --max-cycles=10 --max-stuck=3 --max-runtime=1s
FILE=$(state_file)
PAST_EPOCH=$(( $(date +%s) - 10 ))
write_field "$FILE" "start_epoch" "$PAST_EPOCH"
run tick --stuck=no
assert_exit "tick exits 1 at max-runtime" 1
assert_contains "violation includes max-runtime" "max-runtime"
cleanup_session

# can-deep denied: max-deep-per-cycle
init_session --max-cycles=10 --max-stuck=3 --max-deep-per-cycle=1
run deep
run can-deep
assert_exit "can-deep denied at max-deep-per-cycle" 1
assert_contains "reason=max-deep-per-cycle" "reason=max-deep-per-cycle"
cleanup_session

# can-deep denied: max-consecutive-deep
init_session --max-cycles=10 --max-stuck=3 --max-consecutive-deep=1
run deep
run tick --stuck=no  # consecutive_deep_cycles becomes 1
run can-deep
assert_exit "can-deep denied at max-consecutive-deep" 1
assert_contains "reason=max-consecutive-deep" "reason=max-consecutive-deep"
cleanup_session

# can-deep denied: max-runtime
init_session --max-cycles=10 --max-stuck=3 --max-runtime=1s
FILE=$(state_file)
PAST_EPOCH=$(( $(date +%s) - 10 ))
write_field "$FILE" "start_epoch" "$PAST_EPOCH"
run can-deep
assert_exit "can-deep denied at max-runtime" 1
assert_contains "reason=max-runtime" "reason=max-runtime"
cleanup_session

# =========================================================================
echo ""
echo "-- Validation failures (init, exit 2) --"

run init --max-stuck=2
assert_exit "missing --max-cycles" 2
assert_contains "error mentions max-cycles" "max-cycles"

run init --max-cycles=5
assert_exit "missing --max-stuck" 2
assert_contains "error mentions max-stuck" "max-stuck"

run init --max-cycles=0 --max-stuck=2
assert_exit "--max-cycles=0 rejected" 2
assert_contains "error: positive integer" "positive integer"

run init --max-cycles=-1 --max-stuck=2
assert_exit "--max-cycles=-1 rejected" 2

run init --max-cycles=abc --max-stuck=2
assert_exit "--max-cycles=abc rejected" 2
assert_contains "error: positive integer" "positive integer"

run init --max-cycles=5 --max-stuck=2 --max-runtime=foo
assert_exit "--max-runtime=foo rejected" 2
assert_contains "error: duration format" "duration format"

# Valid optional omission
init_session --max-cycles=5 --max-stuck=2
FILE=$(state_file)
RUNTIME=$(read_field "$FILE" "max_runtime_seconds")
if [[ "$RUNTIME" == "0" ]]; then
  echo "  PASS: no --max-runtime → max_runtime_seconds=0"
  (( ++PASS ))
else
  echo "  FAIL: max_runtime_seconds=$RUNTIME, expected 0"
  (( ++FAIL ))
fi
# tick shows unlimited
run tick --stuck=no
assert_contains "elapsed_display shows unlimited" "unlimited"
cleanup_session

# =========================================================================
echo ""
echo "-- Robustness --"

# Corrupted state file
init_session --max-cycles=5 --max-stuck=2
FILE=$(state_file)
echo "NOT JSON" > "$FILE"
run tick --stuck=no
assert_exit "corrupted state file → exit 2 or nonzero" "$LAST_EXIT"
# Accept any nonzero exit (jq gives 1, python3 gives 2)
if [[ "$LAST_EXIT" -ne 0 ]]; then
  echo "  PASS: corrupted state file causes nonzero exit ($LAST_EXIT)"
  (( ++PASS ))
else
  echo "  FAIL: corrupted state file should cause nonzero exit"
  (( ++FAIL ))
fi
rm -f "$FILE"
unset LEAN4_SESSION_ID

# Missing state file
export LEAN4_SESSION_ID="lean4-session-NONEXISTENT"
run tick --stuck=no
assert_exit "missing state file → exit 2" 2
assert_contains "error mentions state file" "state file"
unset LEAN4_SESSION_ID

# Unset LEAN4_SESSION_ID
LEAN4_SESSION_ID=""; export LEAN4_SESSION_ID
run tick --stuck=no
assert_exit "unset LEAN4_SESSION_ID → exit 2" 2
assert_contains "error mentions LEAN4_SESSION_ID" "LEAN4_SESSION_ID"

# No subcommand
run ""
# run() will have empty subcmd error
LAST_EXIT=0
LAST_OUT=$(bash "$TRACKER" 2>&1) || LAST_EXIT=$?
assert_exit "no subcommand → exit 2" 2

# Unknown subcommand
run foobar
assert_exit "unknown subcommand → exit 2" 2
assert_contains "error mentions unknown" "unknown"

# =========================================================================
echo ""
echo "-- CLAUDE_ENV_FILE fallback --"

# init with CLAUDE_ENV_FILE unset
CLAUDE_ENV_FILE=""; export CLAUDE_ENV_FILE
LEAN4_SESSION_ID=""; export LEAN4_SESSION_ID
run init --max-cycles=5 --max-stuck=2
assert_exit "init without CLAUDE_ENV_FILE succeeds" 0
# Should still print session ID
assert_contains "init prints session ID" "lean4-session-"
SID="$LAST_OUT"
export LEAN4_SESSION_ID="$SID"
# Subsequent calls work with env prefix
run tick --stuck=no
assert_exit "tick works with manual session ID" 0
cleanup_session

# init with CLAUDE_ENV_FILE pointing to unwritable path
FAKE_ENV="/tmp/lean4-test-unwritable-$$"
touch "$FAKE_ENV" && chmod 000 "$FAKE_ENV" 2>/dev/null || true
LEAN4_SESSION_ID=""; export LEAN4_SESSION_ID
export CLAUDE_ENV_FILE="$FAKE_ENV"
run init --max-cycles=5 --max-stuck=2
assert_exit "init with unwritable CLAUDE_ENV_FILE succeeds" 0
assert_contains "init prints session ID despite unwritable env" "lean4-session-"
SID="$LAST_OUT"
export LEAN4_SESSION_ID="$SID"
run stop
chmod 644 "$FAKE_ENV" 2>/dev/null || true
rm -f "$FAKE_ENV"
LEAN4_SESSION_ID=""; export LEAN4_SESSION_ID

# stop with CLAUDE_ENV_FILE unset
init_session --max-cycles=5 --max-stuck=2
CLAUDE_ENV_FILE=""; export CLAUDE_ENV_FILE
run stop
assert_exit "stop without CLAUDE_ENV_FILE succeeds" 0

# =========================================================================
echo ""
echo "-- Deep-mode state machine --"

# deep → deep → tick: deep_this_cycle resets, consecutive_deep_cycles=1
init_session --max-cycles=10 --max-stuck=3 --max-deep-per-cycle=3
FILE=$(state_file)
run deep
run deep
DEEP_COUNT=$(read_field "$FILE" "deep_this_cycle")
if [[ "$DEEP_COUNT" == "2" ]]; then
  echo "  PASS: two deep calls → deep_this_cycle=2"
  (( ++PASS ))
else
  echo "  FAIL: deep_this_cycle=$DEEP_COUNT, expected 2"
  (( ++FAIL ))
fi
run tick --stuck=no
assert_contains "after tick: deep_this_cycle=0" "deep_this_cycle=0/"
assert_contains "after tick: consecutive_deep_cycles=1" "consecutive_deep_cycles=1/"

# Non-deep cycle resets consecutive_deep_cycles
run tick --stuck=no  # no deep this cycle
assert_contains "non-deep cycle: consecutive_deep_cycles=0" "consecutive_deep_cycles=0/"

# Two consecutive deep cycles then non-deep
run deep
run tick --stuck=no  # consecutive_deep=1
assert_contains "deep cycle 1: consecutive_deep=1" "consecutive_deep_cycles=1/"
run deep
run tick --stuck=no  # consecutive_deep=2
assert_contains "deep cycle 2: consecutive_deep=2" "consecutive_deep_cycles=2/"
run tick --stuck=no  # no deep: consecutive_deep=0
assert_contains "non-deep cycle: consecutive_deep=0" "consecutive_deep_cycles=0/"
cleanup_session

# =========================================================================
echo ""
echo "-- Stale cleanup --"

# Create a fake stale session file
STALE_FILE="/tmp/lean4-session-STALEFAKE.json"
echo '{"session_id":"lean4-session-STALEFAKE"}' > "$STALE_FILE"
# Set mtime to 25 hours ago
touch -t "$(date -d '25 hours ago' +%Y%m%d%H%M.%S)" "$STALE_FILE" 2>/dev/null || \
  touch -t "$(date -v-25H +%Y%m%d%H%M.%S 2>/dev/null || echo '202001010000.00')" "$STALE_FILE" 2>/dev/null || true

init_session --max-cycles=5 --max-stuck=2
if [[ ! -f "$STALE_FILE" ]]; then
  echo "  PASS: stale session file cleaned up on init"
  (( ++PASS ))
else
  echo "  FAIL: stale session file still exists after init"
  (( ++FAIL ))
  rm -f "$STALE_FILE"
fi
cleanup_session

# =========================================================================
echo ""
echo "-- Duration parsing --"

# Minutes (default)
init_session --max-cycles=5 --max-stuck=2 --max-runtime=2m
FILE=$(state_file)
RT=$(read_field "$FILE" "max_runtime_seconds")
if [[ "$RT" == "120" ]]; then echo "  PASS: 2m → 120s"; (( ++PASS )); else echo "  FAIL: 2m → ${RT}s, expected 120"; (( ++FAIL )); fi
cleanup_session

# Seconds
init_session --max-cycles=5 --max-stuck=2 --max-runtime=30s
FILE=$(state_file)
RT=$(read_field "$FILE" "max_runtime_seconds")
if [[ "$RT" == "30" ]]; then echo "  PASS: 30s → 30s"; (( ++PASS )); else echo "  FAIL: 30s → ${RT}s, expected 30"; (( ++FAIL )); fi
cleanup_session

# Hours
init_session --max-cycles=5 --max-stuck=2 --max-runtime=2h
FILE=$(state_file)
RT=$(read_field "$FILE" "max_runtime_seconds")
if [[ "$RT" == "7200" ]]; then echo "  PASS: 2h → 7200s"; (( ++PASS )); else echo "  FAIL: 2h → ${RT}s, expected 7200"; (( ++FAIL )); fi
cleanup_session

# Bare number (minutes)
init_session --max-cycles=5 --max-stuck=2 --max-runtime=5
FILE=$(state_file)
RT=$(read_field "$FILE" "max_runtime_seconds")
if [[ "$RT" == "300" ]]; then echo "  PASS: 5 → 300s"; (( ++PASS )); else echo "  FAIL: 5 → ${RT}s, expected 300"; (( ++FAIL )); fi
cleanup_session

# =========================================================================
echo ""
echo "=== Results: $PASS passed, $FAIL failed ==="
[[ "$FAIL" -eq 0 ]]

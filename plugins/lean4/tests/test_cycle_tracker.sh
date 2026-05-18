#!/usr/bin/env bash
set -euo pipefail

# Comprehensive tests for cycle_tracker.sh

# Resolve TMPDIR once (matches cycle_tracker.sh): honor caller's TMPDIR,
# fall back to /tmp. Export so the tracker subprocess sees the same value.
: "${TMPDIR:=/tmp}"
export TMPDIR

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TRACKER="$SCRIPT_DIR/../lib/scripts/cycle_tracker.sh"

PASS=0
FAIL=0

# Helper: run tracker, capture exit code and both stdout/stderr.
#   LAST_STDOUT  — stdout only (use for extracting the session id from init)
#   LAST_STDERR  — stderr only (use to check error/diagnostic lines)
#   LAST_OUT     — merged, preserved for existing assert_contains callers
#   LAST_EXIT    — exit code
LAST_OUT=""
LAST_STDOUT=""
LAST_STDERR=""
LAST_EXIT=0
run() {
  local _stderr_file
  _stderr_file=$(mktemp)
  LAST_EXIT=0
  LAST_STDOUT=$(bash "$TRACKER" "$@" 2>"$_stderr_file") || LAST_EXIT=$?
  LAST_STDERR=$(cat "$_stderr_file")
  rm -f "$_stderr_file"
  # Merge for backward compat with existing assert_contains callers that
  # expect both streams in LAST_OUT.
  if [[ -n "$LAST_STDERR" ]]; then
    LAST_OUT="${LAST_STDOUT}"$'\n'"${LAST_STDERR}"
  else
    LAST_OUT="$LAST_STDOUT"
  fi
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
# stderr is intentionally discarded: init may emit a LEAN4_SESSION_DIR=<dir>
# hint on stderr when no env file is configured (see top-of-script comment).
# Capturing stderr into the sid capture would pollute it; callers that need
# to see init errors should run the tracker directly.
init_session() {
  LEAN4_SESSION_ID=$(bash "$TRACKER" init "$@" 2>/dev/null)
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
  # Mirror cycle_tracker.sh's resolution: persisted LEAN4_SESSION_DIR wins
  # over ambient TMPDIR. Tests that run under a non-default TMPDIR must
  # agree with the tracker's own lookup rule.
  local dir="${LEAN4_SESSION_DIR:-$TMPDIR}"
  echo "${dir}/${LEAN4_SESSION_ID:-}.json"
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

# Uppercase suffix (Bash 3.2 portability — ${suffix,,} was Bash 4+ only)
init_session --max-cycles=5 --max-stuck=2 --max-runtime=60M
FILE=$(state_file)
RUNTIME=$(read_field "$FILE" "max_runtime_seconds")
if [[ "$RUNTIME" == "3600" ]]; then
  echo "  PASS: --max-runtime=60M → 3600 seconds (uppercase suffix)"
  (( ++PASS ))
else
  echo "  FAIL: --max-runtime=60M → $RUNTIME, expected 3600"
  (( ++FAIL ))
fi
cleanup_session

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

# Corrupted state file — tick
init_session --max-cycles=5 --max-stuck=2
FILE=$(state_file)
echo "NOT JSON" > "$FILE"
run tick --stuck=no
assert_exit "corrupted state file tick → exit 2" 2
assert_contains "corrupted tick error message" "corrupted state file"

# Corrupted state file — can-deep
echo "NOT JSON" > "$FILE"
run can-deep
assert_exit "corrupted state file can-deep → exit 2" 2
assert_contains "corrupted can-deep error message" "corrupted state file"

# Corrupted state file — deep
echo "NOT JSON" > "$FILE"
run deep
assert_exit "corrupted state file deep → exit 2" 2
assert_contains "corrupted deep error message" "corrupted state file"

# Corrupted state file — status
echo "NOT JSON" > "$FILE"
run status
assert_exit "corrupted state file status → exit 2" 2
assert_contains "corrupted status error message" "corrupted state file"
rm -f "$FILE"
LEAN4_SESSION_ID=""; export LEAN4_SESSION_ID

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
echo "-- Env-file fallback (LEAN4_ENV_FILE → CLAUDE_ENV_FILE → none) --"

# init with neither env file set — stdout fallback
LEAN4_ENV_FILE=""; export LEAN4_ENV_FILE
CLAUDE_ENV_FILE=""; export CLAUDE_ENV_FILE
LEAN4_SESSION_ID=""; export LEAN4_SESSION_ID
run init --max-cycles=5 --max-stuck=2
assert_exit "init without any env file succeeds" 0
assert_contains "init prints session ID" "lean4-session-"
SID="$LAST_STDOUT"
export LEAN4_SESSION_ID="$SID"
run tick --stuck=no
assert_exit "tick works with manual session ID" 0
cleanup_session

# LEAN4_ENV_FILE takes priority over CLAUDE_ENV_FILE
LEAN4_ENVF="$TMPDIR/lean4-test-envfile-$$"
CLAUDE_ENVF="$TMPDIR/lean4-test-claude-envfile-$$"
: > "$LEAN4_ENVF"; : > "$CLAUDE_ENVF"
LEAN4_SESSION_ID=""; export LEAN4_SESSION_ID
export LEAN4_ENV_FILE="$LEAN4_ENVF"
export CLAUDE_ENV_FILE="$CLAUDE_ENVF"
run init --max-cycles=5 --max-stuck=2
assert_exit "init with LEAN4_ENV_FILE set succeeds" 0
if grep -q 'LEAN4_SESSION_ID' "$LEAN4_ENVF" 2>/dev/null; then
  echo "  PASS: LEAN4_ENV_FILE used (has session ID)"
  (( ++PASS ))
else
  echo "  FAIL: LEAN4_ENV_FILE not used (missing session ID)"
  (( ++FAIL ))
fi
if grep -q 'LEAN4_SESSION_ID' "$CLAUDE_ENVF" 2>/dev/null; then
  echo "  FAIL: CLAUDE_ENV_FILE was written when LEAN4_ENV_FILE was set"
  (( ++FAIL ))
else
  echo "  PASS: CLAUDE_ENV_FILE untouched when LEAN4_ENV_FILE set"
  (( ++PASS ))
fi
SID="$LAST_STDOUT"
export LEAN4_SESSION_ID="$SID"
run stop
# Verify stop cleaned the right file (LEAN4_ENVF, not CLAUDE_ENVF)
if grep -q 'LEAN4_SESSION_ID' "$LEAN4_ENVF" 2>/dev/null; then
  echo "  FAIL: stop did not clean LEAN4_ENV_FILE"
  (( ++FAIL ))
else
  echo "  PASS: stop cleaned LEAN4_ENV_FILE"
  (( ++PASS ))
fi
rm -f "$LEAN4_ENVF" "$CLAUDE_ENVF"
LEAN4_ENV_FILE=""; export LEAN4_ENV_FILE

# Cross-env-file cleanup: init under CLAUDE_ENV_FILE, stop under LEAN4_ENV_FILE
# stop must clean the file init actually wrote to (CLAUDE_ENVF), not the newly resolved one
CLAUDE_ENVF2="$TMPDIR/lean4-test-claude-envfile2-$$"
LEAN4_ENVF2="$TMPDIR/lean4-test-lean4-envfile2-$$"
: > "$CLAUDE_ENVF2"; : > "$LEAN4_ENVF2"
LEAN4_SESSION_ID=""; export LEAN4_SESSION_ID
LEAN4_ENV_FILE=""; export LEAN4_ENV_FILE
export CLAUDE_ENV_FILE="$CLAUDE_ENVF2"
run init --max-cycles=5 --max-stuck=2
assert_exit "cross-env init succeeds" 0
SID="$LAST_STDOUT"
export LEAN4_SESSION_ID="$SID"
# Now switch env resolution: set LEAN4_ENV_FILE so _resolve_env_file would return it
export LEAN4_ENV_FILE="$LEAN4_ENVF2"
run stop
# stop should have cleaned CLAUDE_ENVF2 (where init wrote), not LEAN4_ENVF2
if grep -q 'LEAN4_SESSION_ID' "$CLAUDE_ENVF2" 2>/dev/null; then
  echo "  FAIL: cross-env stop did not clean original env file (CLAUDE_ENV_FILE)"
  (( ++FAIL ))
else
  echo "  PASS: cross-env stop cleaned original env file (CLAUDE_ENV_FILE)"
  (( ++PASS ))
fi
if grep -q 'LEAN4_SESSION_ID' "$LEAN4_ENVF2" 2>/dev/null; then
  echo "  FAIL: cross-env stop polluted new env file (LEAN4_ENV_FILE)"
  (( ++FAIL ))
else
  echo "  PASS: cross-env stop did not pollute new env file (LEAN4_ENV_FILE)"
  (( ++PASS ))
fi
rm -f "$CLAUDE_ENVF2" "$LEAN4_ENVF2"
LEAN4_ENV_FILE=""; export LEAN4_ENV_FILE
CLAUDE_ENV_FILE=""; export CLAUDE_ENV_FILE

# Unwritable env file — must be left untouched
FAKE_ENV="$TMPDIR/lean4-test-unwritable-$$"
echo "# original content" > "$FAKE_ENV"
chmod 000 "$FAKE_ENV" 2>/dev/null || true
FAKE_ENV_BEFORE=$(stat -c '%a %s' "$FAKE_ENV" 2>/dev/null || stat -f '%p %z' "$FAKE_ENV" 2>/dev/null)
LEAN4_SESSION_ID=""; export LEAN4_SESSION_ID
export CLAUDE_ENV_FILE="$FAKE_ENV"
run init --max-cycles=5 --max-stuck=2
assert_exit "init with unwritable env file succeeds" 0
assert_contains "init prints session ID despite unwritable env" "lean4-session-"
FAKE_ENV_AFTER=$(stat -c '%a %s' "$FAKE_ENV" 2>/dev/null || stat -f '%p %z' "$FAKE_ENV" 2>/dev/null)
if [[ "$FAKE_ENV_BEFORE" == "$FAKE_ENV_AFTER" ]]; then
  echo "  PASS: unwritable env file left untouched"
  (( ++PASS ))
else
  echo "  FAIL: unwritable env file was modified (before='$FAKE_ENV_BEFORE' after='$FAKE_ENV_AFTER')"
  (( ++FAIL ))
fi
SID="$LAST_STDOUT"
export LEAN4_SESSION_ID="$SID"
run stop
chmod 644 "$FAKE_ENV" 2>/dev/null || true
rm -f "$FAKE_ENV"
LEAN4_SESSION_ID=""; export LEAN4_SESSION_ID

# stop with no env file set
init_session --max-cycles=5 --max-stuck=2
LEAN4_ENV_FILE=""; export LEAN4_ENV_FILE
CLAUDE_ENV_FILE=""; export CLAUDE_ENV_FILE
run stop
assert_exit "stop without env file succeeds" 0

# Env file with missing parent directory — init must not leak shell errors to stdout
MISSING_DIR_ENV="$TMPDIR/lean4-test-nodir-$$/subdir/env.sh"
LEAN4_SESSION_ID=""; export LEAN4_SESSION_ID
LEAN4_ENV_FILE=""; export LEAN4_ENV_FILE
export CLAUDE_ENV_FILE="$MISSING_DIR_ENV"
run init --max-cycles=5 --max-stuck=2
assert_exit "init with missing-dir env file succeeds" 0
# stdout must be exactly one line: the session ID, no shell errors
LINE_COUNT=$(echo "$LAST_STDOUT" | wc -l | tr -d ' ')
if [[ "$LINE_COUNT" == "1" && "$LAST_STDOUT" == lean4-session-* ]]; then
  echo "  PASS: init stdout is clean (single session ID line)"
  (( ++PASS ))
else
  echo "  FAIL: init stdout is polluted ($LINE_COUNT lines, content: '$LAST_STDOUT')"
  (( ++FAIL ))
fi
SID="$LAST_STDOUT"
export LEAN4_SESSION_ID="$SID"
run stop
LEAN4_SESSION_ID=""; export LEAN4_SESSION_ID
CLAUDE_ENV_FILE=""; export CLAUDE_ENV_FILE

# Env file in unwritable directory — init must not leak shell errors to stdout
NOWRITE_DIR="$TMPDIR/lean4-test-nowritedir-$$"
mkdir -p "$NOWRITE_DIR" && chmod 555 "$NOWRITE_DIR" 2>/dev/null || true
NOWRITE_ENV="$NOWRITE_DIR/env.sh"
LEAN4_SESSION_ID=""; export LEAN4_SESSION_ID
export CLAUDE_ENV_FILE="$NOWRITE_ENV"
run init --max-cycles=5 --max-stuck=2
assert_exit "init with unwritable-dir env file succeeds" 0
LINE_COUNT=$(echo "$LAST_STDOUT" | wc -l | tr -d ' ')
if [[ "$LINE_COUNT" == "1" && "$LAST_STDOUT" == lean4-session-* ]]; then
  echo "  PASS: init stdout clean with unwritable dir"
  (( ++PASS ))
else
  echo "  FAIL: init stdout polluted with unwritable dir ($LINE_COUNT lines, content: '$LAST_STDOUT')"
  (( ++FAIL ))
fi
SID="$LAST_STDOUT"
export LEAN4_SESSION_ID="$SID"
run stop
chmod 755 "$NOWRITE_DIR" 2>/dev/null || true
rm -rf "$NOWRITE_DIR"
LEAN4_SESSION_ID=""; export LEAN4_SESSION_ID
CLAUDE_ENV_FILE=""; export CLAUDE_ENV_FILE

# Env file pointing to a directory — init must not leak shell errors to stdout
LEAN4_SESSION_ID=""; export LEAN4_SESSION_ID
export CLAUDE_ENV_FILE="$TMPDIR"
run init --max-cycles=5 --max-stuck=2
assert_exit "init with directory env file succeeds" 0
LINE_COUNT=$(echo "$LAST_STDOUT" | wc -l | tr -d ' ')
if [[ "$LINE_COUNT" == "1" && "$LAST_STDOUT" == lean4-session-* ]]; then
  echo "  PASS: init stdout clean with directory env file"
  (( ++PASS ))
else
  echo "  FAIL: init stdout polluted with directory env file ($LINE_COUNT lines, content: '$LAST_STDOUT')"
  (( ++FAIL ))
fi
SID="$LAST_STDOUT"
export LEAN4_SESSION_ID="$SID"
run stop
LEAN4_SESSION_ID=""; export LEAN4_SESSION_ID
CLAUDE_ENV_FILE=""; export CLAUDE_ENV_FILE

# Env file pointing to a FIFO — init must not block or leak errors
FIFO_PATH="$TMPDIR/lean4-test-fifo-$$"
mkfifo "$FIFO_PATH" 2>/dev/null || true
if [[ -p "$FIFO_PATH" ]]; then
  LEAN4_SESSION_ID=""; export LEAN4_SESSION_ID
  export CLAUDE_ENV_FILE="$FIFO_PATH"
  run init --max-cycles=5 --max-stuck=2
  assert_exit "init with FIFO env file succeeds" 0
  LINE_COUNT=$(echo "$LAST_STDOUT" | wc -l | tr -d ' ')
  if [[ "$LINE_COUNT" == "1" && "$LAST_STDOUT" == lean4-session-* ]]; then
    echo "  PASS: init stdout clean with FIFO env file"
    (( ++PASS ))
  else
    echo "  FAIL: init stdout polluted with FIFO env file ($LINE_COUNT lines, content: '$LAST_STDOUT')"
    (( ++FAIL ))
  fi
  SID="$LAST_STDOUT"
  export LEAN4_SESSION_ID="$SID"
  run stop
  LEAN4_SESSION_ID=""; export LEAN4_SESSION_ID
  CLAUDE_ENV_FILE=""; export CLAUDE_ENV_FILE
  rm -f "$FIFO_PATH"
else
  echo "  SKIP: could not create FIFO for testing"
fi

# Broken symlink env file — must fall back cleanly, not create the target
BROKEN_LINK="$TMPDIR/lean4-test-broken-link-$$"
BROKEN_TARGET="$TMPDIR/lean4-test-no-such-target-$$"
rm -f "$BROKEN_TARGET"  # ensure target does not exist
ln -sf "$BROKEN_TARGET" "$BROKEN_LINK" 2>/dev/null || true
if [[ -L "$BROKEN_LINK" ]]; then
  LEAN4_SESSION_ID=""; export LEAN4_SESSION_ID
  export CLAUDE_ENV_FILE="$BROKEN_LINK"
  run init --max-cycles=5 --max-stuck=2
  assert_exit "init with broken symlink env file succeeds" 0
  LINE_COUNT=$(echo "$LAST_STDOUT" | wc -l | tr -d ' ')
  if [[ "$LINE_COUNT" == "1" && "$LAST_STDOUT" == lean4-session-* ]]; then
    echo "  PASS: init stdout clean with broken symlink env file"
    (( ++PASS ))
  else
    echo "  FAIL: init stdout polluted with broken symlink ($LINE_COUNT lines, content: '$LAST_STDOUT')"
    (( ++FAIL ))
  fi
  # Target file must NOT have been created
  if [[ -e "$BROKEN_TARGET" ]]; then
    echo "  FAIL: init created the broken symlink's target file"
    (( ++FAIL ))
    rm -f "$BROKEN_TARGET"
  else
    echo "  PASS: broken symlink target not created by init"
    (( ++PASS ))
  fi
  # Link must still be broken (unchanged)
  if [[ -L "$BROKEN_LINK" && ! -e "$BROKEN_LINK" ]]; then
    echo "  PASS: broken symlink remains broken after init"
    (( ++PASS ))
  else
    echo "  FAIL: broken symlink was modified by init"
    (( ++FAIL ))
  fi
  SID="$LAST_STDOUT"
  export LEAN4_SESSION_ID="$SID"
  run stop
  # Post-stop: target still must not exist, link still broken
  if [[ -e "$BROKEN_TARGET" ]]; then
    echo "  FAIL: stop created the broken symlink's target file"
    (( ++FAIL ))
  else
    echo "  PASS: broken symlink target not created by stop"
    (( ++PASS ))
  fi
  if [[ -L "$BROKEN_LINK" && ! -e "$BROKEN_LINK" ]]; then
    echo "  PASS: broken symlink remains broken after stop"
    (( ++PASS ))
  else
    echo "  FAIL: broken symlink was modified by stop"
    (( ++FAIL ))
  fi
  LEAN4_SESSION_ID=""; export LEAN4_SESSION_ID
  CLAUDE_ENV_FILE=""; export CLAUDE_ENV_FILE
  rm -f "$BROKEN_LINK" "$BROKEN_TARGET"
else
  echo "  SKIP: could not create broken symlink for testing"
fi

# Symlink to regular file — init must write to the real target, not destroy the link
REAL_TARGET="$TMPDIR/lean4-test-real-target-$$"
LINK_PATH="$TMPDIR/lean4-test-symlink-$$"
: > "$REAL_TARGET"
ln -sf "$REAL_TARGET" "$LINK_PATH" 2>/dev/null || true
if [[ -L "$LINK_PATH" ]]; then
  LEAN4_SESSION_ID=""; export LEAN4_SESSION_ID
  export CLAUDE_ENV_FILE="$LINK_PATH"
  run init --max-cycles=5 --max-stuck=2
  assert_exit "init with symlink-to-file env file succeeds" 0
  SID="$LAST_STDOUT"
  export LEAN4_SESSION_ID="$SID"
  # The symlink must still be a symlink (not replaced by a regular file)
  if [[ -L "$LINK_PATH" ]]; then
    echo "  PASS: symlink preserved after init"
    (( ++PASS ))
  else
    echo "  FAIL: symlink was destroyed by init"
    (( ++FAIL ))
  fi
  # The real target must contain the session ID
  if grep -q "$SID" "$REAL_TARGET" 2>/dev/null; then
    echo "  PASS: session ID written to real target through symlink"
    (( ++PASS ))
  else
    echo "  FAIL: session ID not found in real target"
    (( ++FAIL ))
  fi
  run stop
  LEAN4_SESSION_ID=""; export LEAN4_SESSION_ID
  CLAUDE_ENV_FILE=""; export CLAUDE_ENV_FILE
  rm -f "$LINK_PATH" "$REAL_TARGET"
else
  echo "  SKIP: could not create symlink for testing"
fi

# stop with missing state file — must clean stale export but not clobber another session
FALLBACK_ENV="$TMPDIR/lean4-test-fallback-env-$$"
cat > "$FALLBACK_ENV" <<'ENVEOF'
export LEAN4_SESSION_ID="lean4-session-GHOST"
export LEAN4_SESSION_ID="lean4-session-ACTIVE"
ENVEOF
export LEAN4_SESSION_ID="lean4-session-GHOST"
export CLAUDE_ENV_FILE="$FALLBACK_ENV"
run stop
assert_exit "stop with missing state file succeeds" 0
if grep -q 'lean4-session-GHOST' "$FALLBACK_ENV" 2>/dev/null; then
  echo "  FAIL: stop with missing state leaked stale session in env file"
  (( ++FAIL ))
else
  echo "  PASS: stop with missing state cleaned stale session (best-effort)"
  (( ++PASS ))
fi
if grep -q 'lean4-session-ACTIVE' "$FALLBACK_ENV" 2>/dev/null; then
  echo "  PASS: stop with missing state preserved other session's export"
  (( ++PASS ))
else
  echo "  FAIL: stop with missing state clobbered other session's export"
  (( ++FAIL ))
fi
rm -f "$FALLBACK_ENV"
LEAN4_SESSION_ID=""; export LEAN4_SESSION_ID
CLAUDE_ENV_FILE=""; export CLAUDE_ENV_FILE

# stop with corrupted state file — must clean stale export but not clobber another session
CORRUPT_ENV="$TMPDIR/lean4-test-corrupt-env-$$"
cat > "$CORRUPT_ENV" <<'ENVEOF'
export LEAN4_SESSION_ID="lean4-session-CORRUPT"
export LEAN4_SESSION_ID="lean4-session-ALIVE"
ENVEOF
CORRUPT_STATE="$TMPDIR/lean4-session-CORRUPT.json"
echo "NOT JSON" > "$CORRUPT_STATE"
export LEAN4_SESSION_ID="lean4-session-CORRUPT"
export CLAUDE_ENV_FILE="$CORRUPT_ENV"
run stop
assert_exit "stop with corrupted state file succeeds" 0
if grep -q 'lean4-session-CORRUPT' "$CORRUPT_ENV" 2>/dev/null; then
  echo "  FAIL: stop with corrupted state leaked stale session in env file"
  (( ++FAIL ))
else
  echo "  PASS: stop with corrupted state cleaned stale session (best-effort)"
  (( ++PASS ))
fi
if grep -q 'lean4-session-ALIVE' "$CORRUPT_ENV" 2>/dev/null; then
  echo "  PASS: stop with corrupted state preserved other session's export"
  (( ++PASS ))
else
  echo "  FAIL: stop with corrupted state clobbered other session's export"
  (( ++FAIL ))
fi
rm -f "$CORRUPT_ENV" "$CORRUPT_STATE"
LEAN4_SESSION_ID=""; export LEAN4_SESSION_ID
CLAUDE_ENV_FILE=""; export CLAUDE_ENV_FILE

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
echo "-- Claim lifecycle (start-claim / reset-claim / session totals) --"

# Basic lifecycle: init → start-claim → ticks → reset-claim → start-claim → ticks → status
init_session --max-cycles=5 --max-stuck=3
run start-claim
assert_exit "start-claim succeeds" 0
run status
assert_contains "claim_active=true after start-claim" "claim_active=true"
assert_contains "claims_attempted=1 (in-progress)" "claims_attempted=1"

# Tick some cycles with stuck
run tick --stuck=yes
run tick --stuck=yes
run tick --stuck=no
run status
assert_contains "cycles_total=3 after 3 ticks" "cycles_total=3"
assert_contains "stuck_cycles_total=2 after 2 stuck ticks" "stuck_cycles_total=2"

# Deep
run deep
run status
assert_contains "deep_total=1 after 1 deep" "deep_total=1"

# Reset claim
run reset-claim
assert_exit "reset-claim succeeds" 0
run status
assert_contains "claim_active=false after reset" "claim_active=false"
assert_contains "claims_attempted=1 (completed)" "claims_attempted=1"
assert_contains "per-claim cycles=0 after reset" "cycles=0/"
assert_contains "per-claim consecutive_stuck=0 after reset" "consecutive_stuck=0/"
assert_contains "cycles_total=3 preserved after reset" "cycles_total=3"
assert_contains "stuck_cycles_total=2 preserved after reset" "stuck_cycles_total=2"
assert_contains "deep_total=1 preserved after reset" "deep_total=1"

# Second claim
run start-claim
run tick --stuck=no
run tick --stuck=yes
run deep
run status
assert_contains "cycles_total=5 after 2 more ticks" "cycles_total=5"
assert_contains "stuck_cycles_total=3 after 1 more stuck" "stuck_cycles_total=3"
assert_contains "deep_total=2 after 1 more deep" "deep_total=2"
assert_contains "claims_attempted=2 (1 completed + 1 in-progress)" "claims_attempted=2"
assert_contains "claim_active=true on second claim" "claim_active=true"
assert_contains "per-claim cycles=2 on second claim" "cycles=2/"
cleanup_session

# Status right after init (no claim started)
init_session --max-cycles=5 --max-stuck=3
run status
assert_contains "claims_attempted=0 after init" "claims_attempted=0"
assert_contains "claim_active=false after init" "claim_active=false"
cleanup_session

# start-claim with zero cycles then reset-claim
init_session --max-cycles=5 --max-stuck=3
run start-claim
run reset-claim
assert_exit "reset-claim with zero cycles" 0
run status
assert_contains "claims_attempted=1 after zero-cycle claim" "claims_attempted=1"
assert_contains "cycles_total=0 after zero-cycle claim" "cycles_total=0"
cleanup_session

# Invalid transition: double start-claim
init_session --max-cycles=5 --max-stuck=3
run start-claim
run start-claim
assert_exit "double start-claim → exit 2" 2
assert_contains "error mentions claim_active" "claim_active"
cleanup_session

# Invalid transition: reset-claim without start-claim
init_session --max-cycles=5 --max-stuck=3
run reset-claim
assert_exit "reset-claim without start-claim → exit 2" 2
assert_contains "error mentions claim_active" "claim_active"
cleanup_session

# Invalid transition: double reset-claim
init_session --max-cycles=5 --max-stuck=3
run start-claim
run reset-claim
run reset-claim
assert_exit "double reset-claim → exit 2" 2
assert_contains "error mentions claim_active" "claim_active"
cleanup_session

# =========================================================================
echo ""
echo "-- Python3 fallback (no jq) --"

# Force python3 backend by constructing a minimal PATH without jq
if command -v python3 >/dev/null 2>&1; then
  ORIG_PATH="$PATH"
  NOJQ_DIR=$(mktemp -d)
  # Symlink only python3, bash, and coreutils essentials — no jq
  for cmd in python3 bash date id find mktemp mv rm stat touch grep chmod ln readlink realpath dirname basename cat wc tr sed; do
    local_cmd=$(command -v "$cmd" 2>/dev/null || true)
    if [[ -n "$local_cmd" ]]; then ln -sf "$local_cmd" "$NOJQ_DIR/$cmd" 2>/dev/null || true; fi
  done
  export PATH="$NOJQ_DIR"

  if command -v jq >/dev/null 2>&1; then
    echo "  SKIP: could not hide jq from PATH"
  else
    # Basic lifecycle on python3 backend
    run init --max-cycles=5 --max-stuck=2
    assert_exit "py3: init succeeds" 0
    SID="$LAST_STDOUT"; export LEAN4_SESSION_ID="$SID"

    run start-claim
    assert_exit "py3: start-claim succeeds" 0

    run tick --stuck=yes
    assert_exit "py3: tick --stuck=yes succeeds" 0

    run tick --stuck=no
    assert_exit "py3: tick --stuck=no succeeds" 0

    run status
    assert_exit "py3: status succeeds" 0
    assert_contains "py3: status shows claim_active=true" "claim_active=true"
    assert_contains "py3: stuck_cycles_total=1" "stuck_cycles_total=1"
    assert_contains "py3: cycles_total=2" "cycles_total=2"

    # Double start-claim must fail
    run start-claim
    assert_exit "py3: double start-claim → exit 2" 2

    # Reset claim
    run reset-claim
    assert_exit "py3: reset-claim succeeds" 0

    # Double reset-claim must fail
    run reset-claim
    assert_exit "py3: double reset-claim → exit 2" 2

    # Deep tracking
    run start-claim
    run deep
    run status
    assert_contains "py3: deep_total=1" "deep_total=1"

    cleanup_session
  fi

  export PATH="$ORIG_PATH"
  rm -rf "$NOJQ_DIR"
else
  echo "  SKIP: python3 not available"
fi

# =========================================================================
echo ""
echo "-- Stale cleanup --"

# Create a fake stale session file
STALE_FILE="$TMPDIR/lean4-session-STALEFAKE.json"
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
echo "-- Init flag aliases --"

# Long user-facing form: --max-stuck-cycles
run init --max-cycles=5 --max-stuck-cycles=3
assert_exit "--max-stuck-cycles alias accepted" 0
SID="$LAST_STDOUT"; export LEAN4_SESSION_ID="$SID"
FILE=$(state_file)
VAL=$(read_field "$FILE" "max_stuck")
if [[ "$VAL" == "3" ]]; then echo "  PASS: --max-stuck-cycles=3 → max_stuck=3"; (( ++PASS )); else echo "  FAIL: max_stuck=$VAL, expected 3"; (( ++FAIL )); fi
cleanup_session

# Long user-facing form: --max-total-runtime
run init --max-cycles=5 --max-stuck=2 --max-total-runtime=60m
assert_exit "--max-total-runtime alias accepted" 0
SID="$LAST_STDOUT"; export LEAN4_SESSION_ID="$SID"
FILE=$(state_file)
VAL=$(read_field "$FILE" "max_runtime_seconds")
if [[ "$VAL" == "3600" ]]; then echo "  PASS: --max-total-runtime=60m → 3600s"; (( ++PASS )); else echo "  FAIL: max_runtime_seconds=$VAL, expected 3600"; (( ++FAIL )); fi
cleanup_session

# Long user-facing form: --max-consecutive-deep-cycles
run init --max-cycles=5 --max-stuck=2 --max-consecutive-deep-cycles=4
assert_exit "--max-consecutive-deep-cycles alias accepted" 0
SID="$LAST_STDOUT"; export LEAN4_SESSION_ID="$SID"
FILE=$(state_file)
VAL=$(read_field "$FILE" "max_consecutive_deep")
if [[ "$VAL" == "4" ]]; then echo "  PASS: --max-consecutive-deep-cycles=4 → max_consecutive_deep=4"; (( ++PASS )); else echo "  FAIL: max_consecutive_deep=$VAL, expected 4"; (( ++FAIL )); fi
cleanup_session

# Mixed short/long aliases in a single init call
run init --max-cycles=10 --max-stuck-cycles=2 --max-total-runtime=30m --max-consecutive-deep-cycles=3
assert_exit "mixed short/long aliases accepted" 0
SID="$LAST_STDOUT"; export LEAN4_SESSION_ID="$SID"
FILE=$(state_file)
V1=$(read_field "$FILE" "max_stuck")
V2=$(read_field "$FILE" "max_runtime_seconds")
V3=$(read_field "$FILE" "max_consecutive_deep")
if [[ "$V1" == "2" && "$V2" == "1800" && "$V3" == "3" ]]; then
  echo "  PASS: mixed aliases all parsed correctly"
  (( ++PASS ))
else
  echo "  FAIL: mixed aliases: max_stuck=$V1 (exp 2), max_runtime_seconds=$V2 (exp 1800), max_consecutive_deep=$V3 (exp 3)"
  (( ++FAIL ))
fi
cleanup_session

# Unknown args still fail (regression guard)
run init --max-cycles=5 --max-stuck=2 --max-bogus=7
assert_exit "unknown --max-bogus still rejected" 2
assert_contains "error mentions unknown" "unknown"

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

# Sub-minute display: 30s budget should show Xs/30s, not 0m/0m
init_session --max-cycles=5 --max-stuck=2 --max-runtime=30s
run tick --stuck=no
assert_contains "sub-minute display uses seconds" "/30s"
assert_not_contains "sub-minute display does not use 0m" "0m/0m"
cleanup_session

# Non-whole-minute display: 90s budget should show Xs/90s, not 0m/1m
init_session --max-cycles=5 --max-stuck=2 --max-runtime=90s
run tick --stuck=no
assert_contains "90s budget uses seconds format" "/90s"
assert_not_contains "90s budget does not truncate to minutes" "/1m"
cleanup_session

# =========================================================================
echo ""
echo "-- Cross-invocation TMPDIR robustness --"

# The tracker persists LEAN4_SESSION_DIR alongside LEAN4_SESSION_ID at init
# so later invocations (tick, status, stop) can find the same state file
# even if ambient TMPDIR changes. This test proves the persistence works:
#   1. init under a custom TMPDIR, capturing env exports in an env file
#   2. source the env file so LEAN4_SESSION_ID and LEAN4_SESSION_DIR are set
#   3. run tick/status/stop under a DIFFERENT ambient TMPDIR
#   4. verify all operations succeed — proving they used the persisted dir,
#      not the (now wrong) ambient TMPDIR

CROSS_TMPDIR=$(mktemp -d)
CROSS_ENVF="${TMPDIR:-/tmp}/lean4-test-cross-tmpdir-envfile-$$"
: > "$CROSS_ENVF"

# Step 1: init with TMPDIR=$CROSS_TMPDIR, persist to CROSS_ENVF
INIT_SID=$(TMPDIR="$CROSS_TMPDIR" CLAUDE_ENV_FILE="$CROSS_ENVF" \
  bash "$TRACKER" init --max-cycles=3 --max-stuck=2 2>&1)

if [[ -n "$INIT_SID" && -f "$CROSS_TMPDIR/${INIT_SID}.json" ]]; then
  echo "  PASS: init under custom TMPDIR wrote state file there"
  (( ++PASS ))
else
  echo "  FAIL: init under custom TMPDIR did not write expected state file"
  echo "        INIT_SID=$INIT_SID  CROSS_TMPDIR=$CROSS_TMPDIR"
  (( ++FAIL ))
fi

# Step 2: confirm env file got both persisted vars
if grep -q "^export LEAN4_SESSION_ID=\"$INIT_SID\"" "$CROSS_ENVF" \
   && grep -q "^export LEAN4_SESSION_DIR=\"$CROSS_TMPDIR\"" "$CROSS_ENVF"; then
  echo "  PASS: init persisted both LEAN4_SESSION_ID and LEAN4_SESSION_DIR"
  (( ++PASS ))
else
  echo "  FAIL: init did not persist LEAN4_SESSION_DIR correctly"
  echo "        env file contents:"
  sed 's/^/          /' "$CROSS_ENVF"
  (( ++FAIL ))
fi

# Step 3: source the env file (simulates Claude Code replaying persisted env)
# shellcheck disable=SC1090
source "$CROSS_ENVF"

# Step 4: tick/status/stop with TMPDIR explicitly set to something ELSE.
# If the tracker used ambient TMPDIR, it would look in the wrong place and fail.
TMPDIR="/tmp" bash "$TRACKER" tick --stuck=no >/dev/null 2>&1
TICK_EXIT=$?
if [[ "$TICK_EXIT" -eq 0 ]]; then
  echo "  PASS: tick under different ambient TMPDIR (used persisted LEAN4_SESSION_DIR)"
  (( ++PASS ))
else
  echo "  FAIL: tick under different ambient TMPDIR (exit $TICK_EXIT)"
  (( ++FAIL ))
fi

TMPDIR="/tmp" bash "$TRACKER" status >/dev/null 2>&1
STATUS_EXIT=$?
if [[ "$STATUS_EXIT" -eq 0 ]]; then
  echo "  PASS: status under different ambient TMPDIR"
  (( ++PASS ))
else
  echo "  FAIL: status under different ambient TMPDIR (exit $STATUS_EXIT)"
  (( ++FAIL ))
fi

TMPDIR="/tmp" CLAUDE_ENV_FILE="$CROSS_ENVF" bash "$TRACKER" stop >/dev/null 2>&1
STOP_EXIT=$?
if [[ "$STOP_EXIT" -eq 0 ]]; then
  echo "  PASS: stop under different ambient TMPDIR"
  (( ++PASS ))
else
  echo "  FAIL: stop under different ambient TMPDIR (exit $STOP_EXIT)"
  (( ++FAIL ))
fi

# Verify stop actually deleted the state file from its real location
if [[ ! -f "$CROSS_TMPDIR/${INIT_SID}.json" ]]; then
  echo "  PASS: stop cleaned up state file in persisted dir (not ambient TMPDIR)"
  (( ++PASS ))
else
  echo "  FAIL: state file still exists at $CROSS_TMPDIR/${INIT_SID}.json after stop"
  (( ++FAIL ))
fi

# Verify stop also unpersisted both env vars
if ! grep -q "LEAN4_SESSION_ID\|LEAN4_SESSION_DIR" "$CROSS_ENVF" 2>/dev/null; then
  echo "  PASS: stop unpersisted both LEAN4_SESSION_ID and LEAN4_SESSION_DIR"
  (( ++PASS ))
else
  echo "  FAIL: stop left stale exports in env file"
  sed 's/^/          /' "$CROSS_ENVF"
  (( ++FAIL ))
fi

# Cleanup
unset LEAN4_SESSION_ID LEAN4_SESSION_DIR CLAUDE_ENV_FILE
rm -rf "$CROSS_TMPDIR" "$CROSS_ENVF"

# =========================================================================
echo ""
echo "-- Stdout-only cross-TMPDIR reuse (no env file) --"

# When no env file is configured, init persists nothing — the caller gets
# the session id on stdout and the session dir on stderr. This test proves:
#   1. stdout contains ONLY the sid (backward-compat — no extra lines)
#   2. stderr contains a machine-parseable LEAN4_SESSION_DIR=<dir> hint
#   3. a caller who passes BOTH vars can run tick/status/stop even with
#      a different ambient TMPDIR
# Without (3), stdout-only manual reuse breaks across TMPDIR changes —
# exactly the residual gap that motivated this work.

STDOUT_TMPDIR=$(mktemp -d)
STDOUT_OUT=$(mktemp)
STDOUT_ERR=$(mktemp)

# Step 1+2: init with no env file at all, capture stdout and stderr separately
unset CLAUDE_ENV_FILE LEAN4_ENV_FILE
TMPDIR="$STDOUT_TMPDIR" bash "$TRACKER" init --max-cycles=3 --max-stuck=2 \
  >"$STDOUT_OUT" 2>"$STDOUT_ERR" || true

STDOUT_SID=$(cat "$STDOUT_OUT")
STDOUT_STDERR=$(cat "$STDOUT_ERR")

# Stdout must be exactly one line containing the sid — no extra output
STDOUT_LINES=$(wc -l < "$STDOUT_OUT" | tr -d ' ')
if [[ "$STDOUT_LINES" == "1" && -n "$STDOUT_SID" ]]; then
  echo "  PASS: stdout contains only the session id (backward compat)"
  (( ++PASS ))
else
  echo "  FAIL: stdout had $STDOUT_LINES lines or empty sid (expected 1 line with sid)"
  echo "        stdout: $(cat "$STDOUT_OUT")"
  (( ++FAIL ))
fi

# Stderr must contain the LEAN4_SESSION_DIR hint pointing at our custom TMPDIR
if [[ "$STDOUT_STDERR" == *"LEAN4_SESSION_DIR=$STDOUT_TMPDIR"* ]]; then
  echo "  PASS: stderr surfaces LEAN4_SESSION_DIR=<dir> for manual reuse"
  (( ++PASS ))
else
  echo "  FAIL: stderr missing LEAN4_SESSION_DIR=$STDOUT_TMPDIR hint"
  echo "        stderr: $STDOUT_STDERR"
  (( ++FAIL ))
fi

# Step 3: caller preserves both vars, runs under a different ambient TMPDIR
if LEAN4_SESSION_ID="$STDOUT_SID" LEAN4_SESSION_DIR="$STDOUT_TMPDIR" TMPDIR="/tmp" \
    bash "$TRACKER" tick --stuck=no >/dev/null 2>&1; then
  echo "  PASS: stdout-only caller can tick cross-TMPDIR by passing both vars"
  (( ++PASS ))
else
  echo "  FAIL: tick failed with explicit LEAN4_SESSION_DIR under different TMPDIR"
  (( ++FAIL ))
fi

if LEAN4_SESSION_ID="$STDOUT_SID" LEAN4_SESSION_DIR="$STDOUT_TMPDIR" TMPDIR="/tmp" \
    bash "$TRACKER" status >/dev/null 2>&1; then
  echo "  PASS: stdout-only caller can status cross-TMPDIR by passing both vars"
  (( ++PASS ))
else
  echo "  FAIL: status failed with explicit LEAN4_SESSION_DIR under different TMPDIR"
  (( ++FAIL ))
fi

LEAN4_SESSION_ID="$STDOUT_SID" LEAN4_SESSION_DIR="$STDOUT_TMPDIR" TMPDIR="/tmp" \
  bash "$TRACKER" stop >/dev/null 2>&1
if [[ "$?" -eq 0 && ! -f "$STDOUT_TMPDIR/${STDOUT_SID}.json" ]]; then
  echo "  PASS: stdout-only caller can stop cross-TMPDIR by passing both vars"
  (( ++PASS ))
else
  echo "  FAIL: stop failed or left state file behind"
  (( ++FAIL ))
fi

# Cleanup
rm -rf "$STDOUT_TMPDIR" "$STDOUT_OUT" "$STDOUT_ERR"
unset LEAN4_SESSION_ID LEAN4_SESSION_DIR

# =========================================================================
echo ""
echo "-- Superseded-session env-file cleanup --"

# Two sessions share the same env file and the same TMPDIR. When session B
# supersedes A (same dir string), stopping A must NOT remove B's persisted
# LEAN4_SESSION_DIR line — doing so would weaken cross-TMPDIR robustness for
# the still-active B. Regression: the old cleanup matched LEAN4_SESSION_DIR
# by value, which was identical across both sessions.

SUPERSEDE_TMPDIR=$(mktemp -d)
SUPERSEDE_ENVF="${TMPDIR:-/tmp}/lean4-test-supersede-envfile-$$"
: > "$SUPERSEDE_ENVF"
LEAN4_SESSION_ID=""; export LEAN4_SESSION_ID
LEAN4_SESSION_DIR=""; export LEAN4_SESSION_DIR
CLAUDE_ENV_FILE=""; export CLAUDE_ENV_FILE
export LEAN4_ENV_FILE="$SUPERSEDE_ENVF"

SID_A=$(TMPDIR="$SUPERSEDE_TMPDIR" bash "$TRACKER" init --max-cycles=5 --max-stuck=2 2>/dev/null)
SID_B=$(TMPDIR="$SUPERSEDE_TMPDIR" bash "$TRACKER" init --max-cycles=5 --max-stuck=2 2>/dev/null)

if [[ -n "$SID_A" && -n "$SID_B" && "$SID_A" != "$SID_B" ]]; then
  echo "  PASS: two sessions got distinct ids ($SID_A vs $SID_B)"
  (( ++PASS ))
else
  echo "  FAIL: could not init two distinct sessions (A=$SID_A B=$SID_B)"
  (( ++FAIL ))
fi

# Stop A explicitly (export its vars, not B's).
LEAN4_SESSION_ID="$SID_A" LEAN4_SESSION_DIR="$SUPERSEDE_TMPDIR" \
  bash "$TRACKER" stop >/dev/null 2>&1

if grep -qxF "export LEAN4_SESSION_ID=\"$SID_B\"" "$SUPERSEDE_ENVF"; then
  echo "  PASS: stop A preserved B's LEAN4_SESSION_ID"
  (( ++PASS ))
else
  echo "  FAIL: stop A removed B's LEAN4_SESSION_ID"
  echo "        env file contents:"
  sed 's/^/          /' "$SUPERSEDE_ENVF"
  (( ++FAIL ))
fi

if grep -qxF "export LEAN4_SESSION_DIR=\"$SUPERSEDE_TMPDIR\"" "$SUPERSEDE_ENVF"; then
  echo "  PASS: stop A preserved B's LEAN4_SESSION_DIR (superseded-session regression)"
  (( ++PASS ))
else
  echo "  FAIL: stop A clobbered B's LEAN4_SESSION_DIR"
  echo "        env file contents:"
  sed 's/^/          /' "$SUPERSEDE_ENVF"
  (( ++FAIL ))
fi

# A's state file should be gone; B's should still exist.
if [[ ! -f "$SUPERSEDE_TMPDIR/${SID_A}.json" && -f "$SUPERSEDE_TMPDIR/${SID_B}.json" ]]; then
  echo "  PASS: stop A removed A's state file and left B's intact"
  (( ++PASS ))
else
  echo "  FAIL: unexpected state-file layout after stop A"
  find "$SUPERSEDE_TMPDIR" -mindepth 1 -maxdepth 1 | sed 's|.*/|          |'
  (( ++FAIL ))
fi

# Now stop B and verify both vars are gone.
LEAN4_SESSION_ID="$SID_B" LEAN4_SESSION_DIR="$SUPERSEDE_TMPDIR" \
  bash "$TRACKER" stop >/dev/null 2>&1

if ! grep -q '^export LEAN4_SESSION_ID=' "$SUPERSEDE_ENVF" \
   && ! grep -q '^export LEAN4_SESSION_DIR=' "$SUPERSEDE_ENVF"; then
  echo "  PASS: stop B unpersisted both LEAN4_SESSION_ID and LEAN4_SESSION_DIR"
  (( ++PASS ))
else
  echo "  FAIL: stop B left stale exports in env file"
  sed 's/^/          /' "$SUPERSEDE_ENVF"
  (( ++FAIL ))
fi

# Cleanup
rm -rf "$SUPERSEDE_TMPDIR" "$SUPERSEDE_ENVF"
unset LEAN4_SESSION_ID LEAN4_SESSION_DIR LEAN4_ENV_FILE

# -------------------------------------------------------------------------
# Env file with only a LEAN4_SESSION_DIR line (no LEAN4_SESSION_ID line) —
# stop must exit 0 and clean the DIR line. Without the `|| true` guard on
# the "find current ID" grep pipeline, `set -euo pipefail` aborts stop
# before the empty-current_id branch runs.
NOIDENV="${TMPDIR:-/tmp}/lean4-test-noid-envfile-$$"
NOIDDIR=$(mktemp -d)
printf 'export LEAN4_SESSION_DIR="%s"\n' "$NOIDDIR" > "$NOIDENV"
NOID_SID="lean4-session-NOIDTEST"
printf '{"session_id":"%s","env_file":"%s"}' "$NOID_SID" "$NOIDENV" > "$NOIDDIR/$NOID_SID.json"
LEAN4_SESSION_ID=""; export LEAN4_SESSION_ID
LEAN4_SESSION_DIR=""; export LEAN4_SESSION_DIR
CLAUDE_ENV_FILE=""; export CLAUDE_ENV_FILE
LEAN4_ENV_FILE=""; export LEAN4_ENV_FILE
LEAN4_SESSION_ID="$NOID_SID" LEAN4_SESSION_DIR="$NOIDDIR" \
  bash "$TRACKER" stop >/dev/null 2>&1
NOID_RC=$?
if [[ "$NOID_RC" -eq 0 ]]; then
  echo "  PASS: stop with only DIR line (no ID line) exits 0"
  (( ++PASS ))
else
  echo "  FAIL: stop with only DIR line exited $NOID_RC (pipefail regression?)"
  (( ++FAIL ))
fi
if ! grep -q '^export LEAN4_SESSION_DIR=' "$NOIDENV" 2>/dev/null; then
  echo "  PASS: stop with only DIR line cleaned the DIR line"
  (( ++PASS ))
else
  echo "  FAIL: stop with only DIR line left the DIR line behind"
  sed 's/^/          /' "$NOIDENV"
  (( ++FAIL ))
fi
rm -rf "$NOIDDIR" "$NOIDENV"

# =========================================================================
echo ""
echo "=== Results: $PASS passed, $FAIL failed ==="
[[ "$FAIL" -eq 0 ]]

#!/bin/bash
set -euo pipefail

# Tests for disprove_target_resolve.py

: "${TMPDIR:=/tmp}"
export TMPDIR

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
RESOLVER="$SCRIPT_DIR/../lib/scripts/disprove_target_resolve.py"

PASS=0
FAIL=0

LAST_STDOUT=""
LAST_STDERR=""
LAST_EXIT=0

run() {
  local _stderr_file
  _stderr_file=$(mktemp "${TMPDIR}/disprove_resolve_test.XXXXXX")
  LAST_EXIT=0
  LAST_STDOUT=$(python3 "$RESOLVER" "$@" 2>"$_stderr_file") || LAST_EXIT=$?
  LAST_STDERR=$(cat "$_stderr_file")
  rm -f "$_stderr_file"
}

assert_exit() {
  local desc="$1" expected="$2"
  if [ "$LAST_EXIT" -eq "$expected" ]; then
    echo "  PASS: $desc"
    PASS=$((PASS + 1))
  else
    echo "  FAIL: $desc (expected exit $expected, got $LAST_EXIT)"
    echo "        stdout: $LAST_STDOUT"
    echo "        stderr: $LAST_STDERR"
    FAIL=$((FAIL + 1))
  fi
}

assert_stdout_contains() {
  local desc="$1" expected="$2"
  case "$LAST_STDOUT" in
    *"$expected"*)
      echo "  PASS: $desc"
      PASS=$((PASS + 1))
      ;;
    *)
      echo "  FAIL: $desc (expected to find '$expected' in stdout)"
      echo "        stdout: $LAST_STDOUT"
      FAIL=$((FAIL + 1))
      ;;
  esac
}

assert_stderr_contains() {
  local desc="$1" expected="$2"
  case "$LAST_STDERR" in
    *"$expected"*)
      echo "  PASS: $desc"
      PASS=$((PASS + 1))
      ;;
    *)
      echo "  FAIL: $desc (expected to find '$expected' in stderr)"
      echo "        stderr: $LAST_STDERR"
      FAIL=$((FAIL + 1))
      ;;
  esac
}

echo "-- File:line targets --"
run "Foo.lean:42"
assert_exit "1. Foo.lean:42 succeeds" 0
assert_stdout_contains "1b. Foo.lean:42 kind=file-line" '"kind": "file-line"'
assert_stdout_contains "1c. Foo.lean:42 file" '"file": "Foo.lean"'
assert_stdout_contains "1d. Foo.lean:42 line" '"line": 42'

run "Sub/Dir/Foo.lean:7"
assert_exit "2. Nested path succeeds" 0
assert_stdout_contains "2b. Nested path file" '"file": "Sub/Dir/Foo.lean"'

echo "-- Qualified-name targets --"
run "MyNs.SubNs.myThm"
assert_exit "3. Dotted name succeeds" 0
assert_stdout_contains "3b. Dotted name kind=qualified-name" '"kind": "qualified-name"'
assert_stdout_contains "3c. Dotted name value" '"name": "MyNs.SubNs.myThm"'

run "myThm"
assert_exit "4. Bare identifier succeeds" 0
assert_stdout_contains "4b. Bare identifier kind=qualified-name" '"kind": "qualified-name"'

echo "-- Rejection cases --"
run "Foo.lean"
assert_exit "5. .lean without line rejected" 2
assert_stderr_contains "5b. .lean-missing-line hint" "missing ':LINE'"

run "Foo.lean:abc"
assert_exit "6. Non-numeric line rejected" 2

run "Ns..Thm"
assert_exit "7. Double-dot rejected" 2

run "∀ n, n^2 ≥ n"
assert_exit "8. Inline Prop rejected" 2

run "Foo.lean:0"
assert_exit "9. Zero line rejected" 2

echo "-- Usage error --"
run
assert_exit "9. No args -> usage error" 2

echo ""
echo "=== Results: $PASS passed, $FAIL failed ==="
[ "$FAIL" -eq 0 ]

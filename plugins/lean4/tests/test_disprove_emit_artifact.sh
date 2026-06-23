#!/bin/bash
set -euo pipefail

# Tests for disprove_emit_artifact.py

: "${TMPDIR:=/tmp}"
export TMPDIR

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
EMIT="$SCRIPT_DIR/../lib/scripts/disprove_emit_artifact.py"

PASS=0
FAIL=0

WORK_DIR=""
trap 'rm -rf "$WORK_DIR"' EXIT
WORK_DIR=$(mktemp -d "${TMPDIR}/disprove_emit_test.XXXXXX")

LAST_STDOUT=""
LAST_STDERR=""
LAST_EXIT=0

run_with_stdin() {
  local stdin_payload="$1"
  shift
  local _stderr_file
  _stderr_file=$(mktemp "${TMPDIR}/disprove_emit_test.XXXXXX")
  LAST_EXIT=0
  LAST_STDOUT=$(printf '%s' "$stdin_payload" | python3 "$EMIT" "$@" 2>"$_stderr_file") || LAST_EXIT=$?
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

assert_file_contains() {
  local desc="$1" path="$2" expected="$3"
  if grep -q "$expected" "$path"; then
    echo "  PASS: $desc"
    PASS=$((PASS + 1))
  else
    echo "  FAIL: $desc (expected '$expected' in $path)"
    echo "        contents:"
    sed 's/^/          /' "$path"
    FAIL=$((FAIL + 1))
  fi
}

# Assert exactly one line in $path matches $pattern (egrep-style).
# Args: <desc> <path> <pattern>
assert_file_line_count() {
  local desc="$1" path="$2" pattern="$3"
  local actual
  actual=$(grep -c "$pattern" "$path" || true)
  if [ "$actual" -eq 1 ]; then
    echo "  PASS: $desc"
    PASS=$((PASS + 1))
  else
    echo "  FAIL: $desc (expected exactly 1 match for '$pattern' in $path, got $actual)"
    FAIL=$((FAIL + 1))
  fi
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

SNIPPET='theorem foo_counterexample : ∃ n : Nat, ¬ (n < 10) := ⟨10, by decide⟩
'

echo "-- Append to existing file --"
TARGET="$WORK_DIR/Foo.lean"
cat > "$TARGET" <<'EOF'
import Mathlib

theorem foo : ∀ n : Nat, n < 10 := by sorry
EOF

run_with_stdin "$SNIPPET" --scope-file="$TARGET" --theorem-name="foo_counterexample"
assert_exit "1. Append succeeds" 0
assert_file_contains "1b. Snippet present" "$TARGET" "foo_counterexample"
assert_file_contains "1c. Original theorem preserved" "$TARGET" "theorem foo :"

echo "-- Idempotency --"
run_with_stdin "$SNIPPET" --scope-file="$TARGET" --theorem-name="foo_counterexample"
assert_exit "2. Re-run is idempotent (exit 0)" 0
assert_stderr_contains "2b. Idempotency note" "already present"
assert_file_line_count "2c. Exactly one declaration of foo_counterexample" "$TARGET" "theorem foo_counterexample"

echo "-- Collision (same name, different body) --"
DIFF_SNIPPET='theorem foo_counterexample : ∃ n : Nat, ¬ (n < 10) := ⟨11, by decide⟩
'
run_with_stdin "$DIFF_SNIPPET" --scope-file="$TARGET" --theorem-name="foo_counterexample"
assert_exit "2d. Same name, different body → collision (exit 2)" 2
assert_stderr_contains "2e. Collision error message" "different body"
assert_file_line_count "2f. Still exactly one declaration of foo_counterexample" "$TARGET" "theorem foo_counterexample"
assert_file_contains "2g. Original body preserved (witness 10)" "$TARGET" "⟨10, by decide⟩"
if grep -q "⟨11, by decide⟩" "$TARGET"; then
  echo "  FAIL: 2h. Conflicting body must NOT be written"
  FAIL=$((FAIL + 1))
else
  echo "  PASS: 2h. Conflicting body not written"
  PASS=$((PASS + 1))
fi

echo "-- Idempotency when a docstring'd declaration follows --"
TARGET3="$WORK_DIR/Baz.lean"
cat > "$TARGET3" <<'EOF'
import Mathlib

theorem foo_counterexample : ∃ n : Nat, ¬ (n < 10) := ⟨10, by decide⟩
/-- a doc comment -/
theorem later_decl : True := trivial
EOF
run_with_stdin "$SNIPPET" --scope-file="$TARGET3" --theorem-name="foo_counterexample"
assert_exit "2i. Identical artifact before a docstring'd decl → idempotent (exit 0)" 0
assert_stderr_contains "2j. Treated as idempotent, not collision" "already present"

echo "-- Dry run --"
TARGET2="$WORK_DIR/Bar.lean"
cat > "$TARGET2" <<'EOF'
import Mathlib
EOF
run_with_stdin "$SNIPPET" --scope-file="$TARGET2" --theorem-name="foo_counterexample" --dry-run
assert_exit "3. Dry-run succeeds" 0
if grep -q "foo_counterexample" "$TARGET2"; then
  echo "  FAIL: 3b. Dry-run wrote to file (should not have)"
  FAIL=$((FAIL + 1))
else
  echo "  PASS: 3b. Dry-run did not modify file"
  PASS=$((PASS + 1))
fi

echo "-- Stdout mode (scope-file=-) --"
run_with_stdin "$SNIPPET" --scope-file="-" --theorem-name="foo_counterexample"
assert_exit "4. Stdout mode succeeds" 0
case "$LAST_STDOUT" in
  *"foo_counterexample"*)
    echo "  PASS: 4b. Snippet echoed to stdout"
    PASS=$((PASS + 1))
    ;;
  *)
    echo "  FAIL: 4b. Snippet not echoed to stdout"
    echo "        stdout: $LAST_STDOUT"
    FAIL=$((FAIL + 1))
    ;;
esac

echo "-- Refusal cases --"
NON_LEAN="$WORK_DIR/Foo.txt"
echo "anything" > "$NON_LEAN"
run_with_stdin "$SNIPPET" --scope-file="$NON_LEAN" --theorem-name="foo_counterexample"
assert_exit "5. Non-.lean path rejected" 2
assert_stderr_contains "5b. Non-.lean error message" "must end in .lean"

run_with_stdin "$SNIPPET" --scope-file="$WORK_DIR/Missing.lean" --theorem-name="foo_counterexample"
assert_exit "6. Missing file rejected" 2
assert_stderr_contains "6b. Missing-file error message" "does not exist"

run_with_stdin "" --scope-file="$TARGET" --theorem-name="foo_counterexample"
assert_exit "7. Empty stdin rejected" 2
assert_stderr_contains "7b. Empty-stdin error message" "empty snippet"

echo "-- Read-only target --"
READONLY="$WORK_DIR/ReadOnly.lean"
cat > "$READONLY" <<'EOF'
import Mathlib
EOF
chmod a-w "$READONLY"
run_with_stdin "$SNIPPET" --scope-file="$READONLY" --theorem-name="ro_counterexample"
assert_exit "8. Read-only target rejected" 2
assert_stderr_contains "8b. Read-only error message" "cannot append"
chmod u+w "$READONLY"   # restore for cleanup trap

echo ""
echo "=== Results: $PASS passed, $FAIL failed ==="
[ "$FAIL" -eq 0 ]

#!/bin/bash
set -euo pipefail

# Tests for disprove_target_profile.py (deterministic profile envelope).

: "${TMPDIR:=/tmp}"
export TMPDIR

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROFILE="$SCRIPT_DIR/../lib/scripts/disprove_target_profile.py"

PASS=0
FAIL=0

WORK=""
trap 'chmod -R u+w "$WORK" 2>/dev/null || true; rm -rf "$WORK"' EXIT
WORK=$(mktemp -d "${TMPDIR}/disprove_profile_test.XXXXXX")
PROJ="$WORK/proj"
mkdir -p "$PROJ"

LAST_OUT=""
LAST_ERR=""
LAST_EXIT=0
run() {
  LAST_EXIT=0
  LAST_OUT=$(python3 "$PROFILE" "$@" 2>"$WORK/err") || LAST_EXIT=$?
  LAST_ERR=$(cat "$WORK/err")
}

pass() { echo "  PASS: $1"; PASS=$((PASS + 1)); }
fail() { echo "  FAIL: $1"; echo "        $2"; FAIL=$((FAIL + 1)); }

assert_exit() {
  if [ "$LAST_EXIT" -eq "$2" ]; then pass "$1"
  else fail "$1" "expected exit $2, got $LAST_EXIT (stderr: $LAST_ERR)"; fi
}

# assert_json <desc> <key> <expected-python-str>
assert_json() {
  local got
  got=$(printf '%s' "$LAST_OUT" | python3 -c \
    "import json,sys; print(json.load(sys.stdin).get('$2'))" 2>/dev/null || echo "<parse-error>")
  if [ "$got" = "$3" ]; then pass "$1"
  else fail "$1" "key '$2': expected '$3', got '$got'"; fi
}

assert_err_contains() {
  case "$LAST_ERR" in
    *"$2"*) pass "$1" ;;
    *) fail "$1" "stderr lacks '$2': $LAST_ERR" ;;
  esac
}

printf 'theorem my_thm : True := trivial\n' > "$PROJ/Bar.lean"

echo "-- Qualified name, single grep hit --"
run "MyNs.my_thm" --root="$PROJ"
assert_exit "1. exit 0" 0
assert_json "1b. kind" kind "qualified-name"
assert_json "1c. source_file" source_file "Bar.lean"
assert_json "1d. decl_name" decl_name "my_thm"
assert_json "1e. authoritative false" authoritative "False"
assert_json "1f. path_class project" path_class "project"
assert_json "1g. no needs_lsp_resolution" needs_lsp_resolution "None"

echo "-- Qualified name, ambiguous (>=2 hits) → needs_lsp_resolution --"
printf 'theorem my_thm : True := trivial\n' > "$PROJ/Baz.lean"
run "MyNs.my_thm" --root="$PROJ"
assert_exit "2. exit 0" 0
assert_json "2b. needs_lsp_resolution true" needs_lsp_resolution "True"
assert_json "2c. no source_file" source_file "None"
rm "$PROJ/Baz.lean"

echo "-- Qualified name, no hit → needs_lsp_resolution --"
run "MyNs.nonexistent_decl" --root="$PROJ"
assert_exit "3. exit 0" 0
assert_json "3b. needs_lsp_resolution true" needs_lsp_resolution "True"

echo "-- File-line into a .lake dependency → refuse at profile time --"
mkdir -p "$PROJ/.lake/packages/x"
printf 'theorem dep : True := trivial\n' > "$PROJ/.lake/packages/x/Dep.lean"
run ".lake/packages/x/Dep.lean:1" --root="$PROJ"
assert_exit "4. exit 2 (dependency)" 2
assert_err_contains "4b. dependency message" "read-only dependency"

echo "-- Read-only PROJECT file → NOT refused at profile time (writable:false) --"
printf 'import X\ntheorem ro : True := trivial\n' > "$PROJ/RO.lean"
chmod a-w "$PROJ/RO.lean"
run "RO.lean:2" --root="$PROJ"
assert_exit "5. exit 0 (project, not refused)" 0
assert_json "5b. writable false" writable "False"
assert_json "5c. path_class project" path_class "project"
chmod u+w "$PROJ/RO.lean"

echo "-- File-line passthrough (writable project file) --"
run "Bar.lean:1" --root="$PROJ"
assert_exit "6. exit 0" 0
assert_json "6b. kind file-line" kind "file-line"
assert_json "6c. source_file" source_file "Bar.lean"
assert_json "6d. line" line "1"
assert_json "6e. writable true" writable "True"

echo "-- Inline Prop / malformed target rejected --"
run '"∀ n, n ≥ 0"' --root="$PROJ"
assert_exit "7. exit 2 (bad target)" 2

echo ""
echo "=== Results: $PASS passed, $FAIL failed ==="
[ "$FAIL" -eq 0 ]

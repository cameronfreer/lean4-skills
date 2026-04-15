#!/bin/bash
set -euo pipefail

# Self-test for lint_bash_compat.sh — verifies it actually catches
# the Bash 4+ constructs it claims to check.

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LINT="$SCRIPT_DIR/../tools/lint_bash_compat.sh"

PASS=0
FAIL=0

assert_exit() {
  local desc="$1" expected="$2" actual="$3"
  if [[ "$actual" -eq "$expected" ]]; then
    echo "  PASS: $desc"
    ((PASS++)) || true
  else
    echo "  FAIL: $desc (expected exit $expected, got $actual)"
    ((FAIL++)) || true
  fi
}

# ---------------------------------------------------------------------------
# Setup: create a tmpdir mimicking the plugin layout with probe scripts
# ---------------------------------------------------------------------------
TMPDIR_ROOT=$(mktemp -d)
trap 'rm -rf "$TMPDIR_ROOT"' EXIT

mkdir -p "$TMPDIR_ROOT/hooks" "$TMPDIR_ROOT/lib/scripts" "$TMPDIR_ROOT/tools"
cp "$LINT" "$TMPDIR_ROOT/tools/lint_bash_compat.sh"

# ---------------------------------------------------------------------------
# Test 1: Clean script → exit 0
# ---------------------------------------------------------------------------
echo "-- Clean script (no Bash 4+ constructs) --"

cat > "$TMPDIR_ROOT/lib/scripts/clean.sh" <<'PROBE'
#!/bin/bash
suffix="$(printf '%s' "$suffix" | tr '[:upper:]' '[:lower:]')"
echo "clean"
PROBE

exit_code=0
bash "$TMPDIR_ROOT/tools/lint_bash_compat.sh" >/dev/null 2>&1 || exit_code=$?
assert_exit "Clean script passes lint" 0 "$exit_code"
rm "$TMPDIR_ROOT/lib/scripts/clean.sh"

# ---------------------------------------------------------------------------
# Test 2: ${var,,} case modifier → caught
# ---------------------------------------------------------------------------
echo ""
echo "-- Bash 4+ construct: \${var,,} --"

cat > "$TMPDIR_ROOT/lib/scripts/bad_case.sh" <<'PROBE'
#!/bin/bash
lower="${val,,}"
PROBE

exit_code=0
bash "$TMPDIR_ROOT/tools/lint_bash_compat.sh" >/dev/null 2>&1 || exit_code=$?
assert_exit "\${var,,} detected" 1 "$exit_code"
rm "$TMPDIR_ROOT/lib/scripts/bad_case.sh"

# ---------------------------------------------------------------------------
# Test 3: declare -A → caught
# ---------------------------------------------------------------------------
echo ""
echo "-- Bash 4+ construct: declare -A --"

cat > "$TMPDIR_ROOT/lib/scripts/bad_assoc.sh" <<'PROBE'
#!/bin/bash
declare -A mymap
PROBE

exit_code=0
bash "$TMPDIR_ROOT/tools/lint_bash_compat.sh" >/dev/null 2>&1 || exit_code=$?
assert_exit "declare -A detected" 1 "$exit_code"
rm "$TMPDIR_ROOT/lib/scripts/bad_assoc.sh"

# ---------------------------------------------------------------------------
# Test 4: mapfile → caught
# ---------------------------------------------------------------------------
echo ""
echo "-- Bash 4+ construct: mapfile --"

cat > "$TMPDIR_ROOT/lib/scripts/bad_mapfile.sh" <<'PROBE'
#!/bin/bash
mapfile -t lines < /dev/null
PROBE

exit_code=0
bash "$TMPDIR_ROOT/tools/lint_bash_compat.sh" >/dev/null 2>&1 || exit_code=$?
assert_exit "mapfile detected" 1 "$exit_code"
rm "$TMPDIR_ROOT/lib/scripts/bad_mapfile.sh"

# ---------------------------------------------------------------------------
# Test 5: mktemp with suffix after X's → caught
# ---------------------------------------------------------------------------
echo ""
echo "-- BSD mktemp: suffix after X's --"

cat > "$TMPDIR_ROOT/lib/scripts/bad_mktemp.sh" <<'PROBE'
#!/bin/bash
mktemp /tmp/lean4-session-XXXXXX.json
PROBE

exit_code=0
bash "$TMPDIR_ROOT/tools/lint_bash_compat.sh" >/dev/null 2>&1 || exit_code=$?
assert_exit "mktemp with .json suffix detected" 1 "$exit_code"
rm "$TMPDIR_ROOT/lib/scripts/bad_mktemp.sh"

# ---------------------------------------------------------------------------
# Test 6: declare -n → caught
# ---------------------------------------------------------------------------
echo ""
echo "-- Bash 4.3+ construct: declare -n --"

cat > "$TMPDIR_ROOT/lib/scripts/bad_nameref.sh" <<'PROBE'
#!/bin/bash
declare -n ref=var
PROBE

exit_code=0
bash "$TMPDIR_ROOT/tools/lint_bash_compat.sh" >/dev/null 2>&1 || exit_code=$?
assert_exit "declare -n detected" 1 "$exit_code"
rm "$TMPDIR_ROOT/lib/scripts/bad_nameref.sh"

# ---------------------------------------------------------------------------
# Test 7: coproc → caught
# ---------------------------------------------------------------------------
echo ""
echo "-- Bash 4+ construct: coproc --"

cat > "$TMPDIR_ROOT/lib/scripts/bad_coproc.sh" <<'PROBE'
#!/bin/bash
coproc mycoproc { cat; }
PROBE

exit_code=0
bash "$TMPDIR_ROOT/tools/lint_bash_compat.sh" >/dev/null 2>&1 || exit_code=$?
assert_exit "coproc detected" 1 "$exit_code"
rm "$TMPDIR_ROOT/lib/scripts/bad_coproc.sh"

# ---------------------------------------------------------------------------
# Test 8: ${var@Q} → caught
# ---------------------------------------------------------------------------
echo ""
echo '-- Bash 4.4+ construct: ${var@Q} --'

cat > "$TMPDIR_ROOT/lib/scripts/bad_at_op.sh" <<'PROBE'
#!/bin/bash
echo "${myvar@Q}"
PROBE

exit_code=0
bash "$TMPDIR_ROOT/tools/lint_bash_compat.sh" >/dev/null 2>&1 || exit_code=$?
assert_exit '${var@Q} detected' 1 "$exit_code"
rm "$TMPDIR_ROOT/lib/scripts/bad_at_op.sh"

# ---------------------------------------------------------------------------
# Test 9: All constructs in one file → all caught
# ---------------------------------------------------------------------------
echo ""
echo "-- Combined: all constructs in one file --"

cat > "$TMPDIR_ROOT/lib/scripts/bad_all.sh" <<'PROBE'
#!/bin/bash
lower="${val,,}"
declare -A mymap
mapfile -t lines < /dev/null
mktemp /tmp/lean4-session-XXXXXX.json
declare -n ref=var
coproc mycoproc { cat; }
echo "${myvar@Q}"
PROBE

exit_code=0
output=$(bash "$TMPDIR_ROOT/tools/lint_bash_compat.sh" 2>&1) || exit_code=$?
assert_exit "Combined file detected" 1 "$exit_code"

# Count that multiple checks fired
issue_count=$(echo "$output" | grep -c '⚠️' || true)
if [[ "$issue_count" -ge 6 ]]; then
  echo "  PASS: Multiple checks fired ($issue_count issues)"
  ((PASS++)) || true
else
  echo "  FAIL: Expected ≥6 issues, got $issue_count"
  ((FAIL++)) || true
fi
rm "$TMPDIR_ROOT/lib/scripts/bad_all.sh"

# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------
echo ""
echo "=== Results: $PASS passed, $FAIL failed ==="
[[ "$FAIL" -eq 0 ]]

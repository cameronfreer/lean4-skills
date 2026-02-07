#!/bin/bash
set -euo pipefail

# Regression tests for guardrails.sh
# Invokes the hook directly with crafted JSON and LEAN4_GUARDRAILS_FORCE=1.

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
HOOK="$SCRIPT_DIR/../hooks/guardrails.sh"

PASS=0
FAIL=0

# Run a test case.  $1=description  $2=command  $3=expected exit code (0 or 2)
run_test() {
  local desc="$1" cmd="$2" expected="$3" actual
  actual=0
  echo "{\"tool_input\":{\"command\":$(printf '%s' "$cmd" | jq -Rs .)}}" \
    | LEAN4_GUARDRAILS_FORCE=1 bash "$HOOK" >/dev/null 2>&1 || actual=$?
  if [[ "$actual" -eq "$expected" ]]; then
    echo "  PASS: $desc"
    (( ++PASS ))
  else
    echo "  FAIL: $desc (expected exit $expected, got $actual)"
    (( ++FAIL ))
  fi
}

echo "=== guardrails.sh regression tests ==="
echo ""

echo "-- Fix 1: --push false positive --"
run_test "git remote set-url --push (allow)"      "git remote set-url --push origin url"   0

echo ""
echo "-- Fix 2: wrapper prefix bypass --"
run_test "sudo -u root git push (block)"           "sudo -u root git push origin main"      2
run_test "env -i git push (block)"                 "env -i git push origin main"            2

echo ""
echo "-- Fix 3: quoted arguments false positive --"
run_test "git commit -m mentioning push (allow)"   'git commit -m "mention git push"'       0
run_test "git commit -m mentioning amend (allow)"   'git commit -m "avoid --amend"'          0
run_test "gh issue body mentioning pr create (allow)" 'gh issue create --body "later gh pr create"' 0

echo ""
echo "-- Fix 4: quoted operators not splitting --"
run_test "semicolon inside quotes (allow)"          'git commit -m "fix; git push"'          0
run_test "ampersand inside quotes (allow)"          'git commit -m "a && git push"'          0

echo ""
echo "-- Sanity: existing behavior --"
run_test "git push (block)"                        "git push origin main"                   2
run_test "sudo git push (block)"                   "sudo git push origin main"              2
run_test "git push --dry-run (allow)"              "git push --dry-run"                     0
run_test "git stash push -m msg (allow)"           "git stash push -m msg"                  0
run_test "echo git push (allow)"                   "echo git push"                          0
run_test "env FOO=bar git push (block)"            "env FOO=bar git push"                   2

echo ""
echo "=== Results: $PASS passed, $FAIL failed ==="
[[ "$FAIL" -eq 0 ]]

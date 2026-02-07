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
echo "-- Fix 5: absolute-path and command-prefix bypass --"
run_test "/usr/bin/git push (block)"                "/usr/bin/git push origin main"          2
run_test "command git push (block)"                 "command git push origin main"           2
run_test "command -p git push (block)"              "command -p git push origin main"        2
run_test "sudo /usr/bin/git push (block)"           "sudo /usr/bin/git push origin main"    2
run_test "/usr/bin/env -i git push (block)"         "/usr/bin/env -i git push origin main"  2

echo ""
echo "-- Fix 6: bash -c nested shell bypass --"
run_test "bash -c 'git push' (block)"              "bash -c 'git push origin main'"         2
run_test "bash -lc 'git push' (block)"             "bash -lc 'git push origin main'"        2
run_test "sh -c 'git push' (block)"                "sh -c 'git push origin main'"           2
run_test "/bin/bash -c 'git push' (block)"          "/bin/bash -c 'git push origin main'"   2
run_test "bash --norc -c 'git push' (block)"        "bash --norc -c 'git push origin main'" 2

echo ""
echo "-- Fix 7: quoted args/flags handled correctly --"
run_test "git commit -m \"push\" (allow)"           'git commit -m "push"'                   0
run_test "git commit -m \"--amend\" (allow)"        'git commit -m "--amend"'                0
run_test "git commit \"--amend\" -m x (block)"      'git commit "--amend" -m x'              2
run_test "git \"push\" origin main (block)"         'git "push" origin main'                 2
run_test "git push \"--dry-run\" (allow)"           'git push "--dry-run"'                   0
run_test "git reset \"--hard\" (block)"             'git reset "--hard"'                     2
run_test "git checkout \"--\" file (block)"         'git checkout "--" file.txt'              2
run_test "git clean \"-f\" (block)"                 'git clean "-f"'                         2

echo ""
echo "-- Sanity: existing behavior --"
run_test "git push (block)"                        "git push origin main"                   2
run_test "sudo git push (block)"                   "sudo git push origin main"              2
run_test "git push --dry-run (allow)"              "git push --dry-run"                     0
run_test "git stash push -m msg (allow)"           "git stash push -m msg"                  0
run_test "echo git push (allow)"                   "echo git push"                          0
run_test "env FOO=bar git push (block)"            "env FOO=bar git push"                   2

echo ""
echo "-- Fix 8: quoted env-assignment prefix bypass --"
run_test "FOO=\"a b\" git push (block)"              'FOO="a b" git push origin main'         2
run_test "FOO=\"a b\" git reset --hard (block)"      'FOO="a b" git reset --hard'             2
run_test "/usr/bin/env FOO=\"a b\" git push (block)" '/usr/bin/env FOO="a b" git push origin main' 2
run_test "FOO=\$(cmd) git push (block)"              'FOO=$(printf "a b") git push origin main'  2
run_test "FOO=\`cmd\` git push (block)"              'FOO=`printf "a b"` git push origin main'   2
run_test "FOO=a\\ b git push (block)"                'FOO=a\ b git push origin main'             2
run_test "FOO=\$(cmd;cmd) git push (block)"          'FOO=$(echo "a b"; echo c) git push origin main' 2
run_test "FOO=\${BAR:-x y} git push (block)"         'FOO=${BAR:-x y} git push origin main'     2
run_test "FOO=\$(echo \")b\";cmd) git push (block)"  'FOO=$(echo "a)b"; echo c) git push origin main' 2
run_test "FOO=\$(echo \")b\";cmd) reset (block)"     'FOO=$(echo "a)b"; echo c) git reset --hard'     2
run_test "FOO=\$(echo \")b\";cmd) clean (block)"     'FOO=$(echo "a)b"; echo c) git clean -fd'        2

echo ""
echo "-- Fix 9: mixed nested syntax in assignments --"
run_test "nested \${..\$(..;..)} git push (block)"    'FOO=${BAR:-$(echo x; echo y)} git push origin main'    2
run_test "backtick inside \$() git push (block)"      'FOO=$(echo `whoami`) git push origin main'             2
run_test "double-quote + \$() + ; git reset (block)"  'X="a b" Y=$(echo c; echo d) git reset --hard'         2
run_test "\$() in env prefix git push (block)"        '/usr/bin/env FOO=$(echo "a;b") git push origin main'   2

echo ""
echo "=== Results: $PASS passed, $FAIL failed ==="
[[ "$FAIL" -eq 0 ]]

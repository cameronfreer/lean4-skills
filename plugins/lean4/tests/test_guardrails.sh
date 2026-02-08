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

# Run a test with a specific collaboration policy.
# $1=desc  $2=policy value (ask|allow|block|"" for unset)  $3=command  $4=expected exit
run_test_policy() {
  local desc="$1" policy="$2" cmd="$3" expected="$4" actual
  actual=0
  local policy_env=()
  if [[ -n "$policy" ]]; then
    policy_env=(LEAN4_GUARDRAILS_COLLAB_POLICY="$policy")
  fi
  echo "{\"tool_input\":{\"command\":$(printf '%s' "$cmd" | jq -Rs .)}}" \
    | env LEAN4_GUARDRAILS_FORCE=1 "${policy_env[@]}" bash "$HOOK" >/dev/null 2>&1 || actual=$?
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
run_test "\$() + ; gh pr create (block)"              'FOO=$(echo "a)b"; echo c) gh pr create --title test'   2
run_test "echo with \$() assignment (allow)"          'echo FOO=$(echo "a)b"; echo c)'                       0

echo ""
echo "-- Collaboration policy: ask mode --"
run_test_policy "ask: git push (block)"                 ask "git push origin main"            2
run_test_policy "ask: git commit --amend (block)"       ask "git commit --amend"              2
run_test_policy "ask: gh pr create (block)"             ask "gh pr create --title test"       2
run_test_policy "ask: bypass git push (allow)"          ask "LEAN4_GUARDRAILS_BYPASS=1 git push origin main"   0
run_test_policy "ask: bypass git commit --amend (allow)" ask "LEAN4_GUARDRAILS_BYPASS=1 git commit --amend"    0
run_test_policy "ask: bypass gh pr create (allow)"      ask "LEAN4_GUARDRAILS_BYPASS=1 gh pr create --title t" 0

echo ""
echo "-- Collaboration policy: allow mode --"
run_test_policy "allow: git push (allow)"               allow "git push origin main"          0
run_test_policy "allow: git commit --amend (allow)"     allow "git commit --amend"            0
run_test_policy "allow: gh pr create (allow)"           allow "gh pr create --title test"     0
run_test_policy "allow: reset --hard (still block)"     allow "git reset --hard"              2
run_test_policy "allow: clean -f (still block)"         allow "git clean -f"                  2
run_test_policy "allow: checkout -- (still block)"      allow "git checkout -- file.txt"      2

echo ""
echo "-- Collaboration policy: block mode --"
run_test_policy "block: git push (block)"               block "git push origin main"          2
run_test_policy "block: git commit --amend (block)"     block "git commit --amend"            2
run_test_policy "block: gh pr create (block)"           block "gh pr create --title test"     2
run_test_policy "block: bypass git push (still block)"  block "LEAN4_GUARDRAILS_BYPASS=1 git push origin main"   2
run_test_policy "block: bypass amend (still block)"     block "LEAN4_GUARDRAILS_BYPASS=1 git commit --amend"     2
run_test_policy "block: bypass pr create (still block)" block "LEAN4_GUARDRAILS_BYPASS=1 gh pr create --title t" 2
run_test_policy "block: reset --hard (still block)"     block "git reset --hard"              2

echo ""
echo "-- Collaboration policy: invalid/default --"
run_test_policy "invalid: yolo push (block=ask)"        yolo "git push origin main"           2
run_test_policy "invalid: yolo bypass push (allow=ask)" yolo "LEAN4_GUARDRAILS_BYPASS=1 git push origin main"   0
run_test_policy "unset: plain push (block=ask)"         ""   "git push origin main"           2
run_test_policy "unset: bypass push (allow=ask)"        ""   "LEAN4_GUARDRAILS_BYPASS=1 git push origin main"   0

echo ""
echo "=== Results: $PASS passed, $FAIL failed ==="
[[ "$FAIL" -eq 0 ]]

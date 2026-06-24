#!/usr/bin/env bash
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

# Run a test with a specific destructive policy (path-scoped destructive ops).
# $1=desc  $2=policy value (ask|allow|block|"" for unset)  $3=command  $4=expected exit
run_test_destructive_policy() {
  local desc="$1" policy="$2" cmd="$3" expected="$4" actual
  actual=0
  local policy_env=()
  if [[ -n "$policy" ]]; then
    policy_env=(LEAN4_GUARDRAILS_DESTRUCTIVE_POLICY="$policy")
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
echo "-- Fix 10: bypass with quoted-value env prefix --"
run_test "FOO=\"a b\" BYPASS=1 git push (allow)"       'FOO="a b" LEAN4_GUARDRAILS_BYPASS=1 git push origin main'    0
run_test "FOO=\$(cmd) BYPASS=1 git push (allow)"       'FOO=$(echo "x y") LEAN4_GUARDRAILS_BYPASS=1 git push main'   0
run_test "FOO=\"BYPASS=1\" git push (block)"            'FOO="LEAN4_GUARDRAILS_BYPASS=1" git push origin main'        2

echo ""
echo "-- Destructive policy: path-scoped checkout -- <path…> --"
# Default (unset = ask): blocks without bypass, allows with bypass
run_test_destructive_policy "unset: checkout -- file (block=ask)"           "" "git checkout -- file.lean"                            2
run_test_destructive_policy "unset: bypass checkout -- file (allow=ask)"    "" "LEAN4_GUARDRAILS_BYPASS=1 git checkout -- file.lean"  0
# allow: passes without bypass; covers multi-file and directory pathsets too
run_test_destructive_policy "allow: checkout -- file"                       allow "git checkout -- file.lean"                       0
run_test_destructive_policy "allow: checkout -- multi-file"                 allow "git checkout -- a.lean b.lean"                    0
run_test_destructive_policy "allow: checkout -- directory"                  allow "git checkout -- src/"                             0
# block: blocks even with bypass token
run_test_destructive_policy "block: checkout -- file (still block)"         block "git checkout -- file.lean"                       2
run_test_destructive_policy "block: bypass checkout -- file (still block)"  block "LEAN4_GUARDRAILS_BYPASS=1 git checkout -- file.lean" 2

# git checkout <tree-ish> <path…>  (restore-from-tree-ish form, no `--`)
# Default (ask): blocks without bypass, allows with bypass.
run_test_destructive_policy "unset: checkout HEAD file (block=ask)"         "" "git checkout HEAD file.lean"                          2
run_test_destructive_policy "unset: bypass checkout HEAD file (allow=ask)"  "" "LEAN4_GUARDRAILS_BYPASS=1 git checkout HEAD file.lean" 0
# allow: any tree-ish + bounded path passes
run_test_destructive_policy "allow: checkout HEAD file"                     allow "git checkout HEAD file.lean"                      0
run_test_destructive_policy "allow: checkout main file"                     allow "git checkout main src/foo.lean"                   0
# Non-force flag prefix before tree-ish + path — same soft-gate.
run_test_destructive_policy "unset: checkout -q HEAD file (block=ask)"      "" "git checkout -q HEAD file.lean"                         2
run_test_destructive_policy "unset: checkout --quiet HEAD file (block=ask)" "" "git checkout --quiet HEAD file.lean"                    2
run_test_destructive_policy "allow: checkout -q HEAD file"                  allow "git checkout -q HEAD file.lean"                    0
run_test_destructive_policy "allow: checkout --quiet HEAD file"             allow "git checkout --quiet HEAD file.lean"               0
run_test_destructive_policy "bypass: checkout -q HEAD file"                 "" "LEAN4_GUARDRAILS_BYPASS=1 git checkout -q HEAD file.lean" 0
# Flag interleaving between tree-ish and path — pins the documented behavior.
run_test_destructive_policy "unset: checkout HEAD -q file (block=ask)"      "" "git checkout HEAD -q file.lean"                         2
# Pathspec-oriented flags: single positional with one of these is
# unambiguously path-restore (empirically confirmed to discard).
run_test_destructive_policy "unset: checkout --ignore-skip-worktree-bits file" "" "git checkout --ignore-skip-worktree-bits file.lean"  2
run_test_destructive_policy "unset: checkout --no-overlay file (block=ask)"  "" "git checkout --no-overlay file.lean"                    2
run_test_destructive_policy "unset: checkout --overlay file (block=ask)"     "" "git checkout --overlay file.lean"                       2
run_test_destructive_policy "unset: checkout --recurse-submodules file"      "" "git checkout --recurse-submodules file.lean"            2
run_test_destructive_policy "allow: checkout --no-overlay file"              allow "git checkout --no-overlay file.lean"                 0
run_test_destructive_policy "allow: checkout --ignore-skip-worktree-bits file" allow "git checkout --ignore-skip-worktree-bits file.lean" 0
run_test_destructive_policy "bypass: checkout --no-overlay file"             "" "LEAN4_GUARDRAILS_BYPASS=1 git checkout --no-overlay file.lean" 0
# -p / --patch is interactive but pipeable (yes y | git checkout -p file
# discards the file). Soft-gate regardless of TTY.
run_test_destructive_policy "unset: checkout -p file (block=ask)"            "" "git checkout -p file.lean"                              2
run_test_destructive_policy "unset: checkout --patch file (block=ask)"       "" "git checkout --patch file.lean"                         2
run_test_destructive_policy "allow: checkout -p file"                        allow "git checkout -p file.lean"                          0
run_test_destructive_policy "allow: checkout --patch file"                   allow "git checkout --patch file.lean"                     0
run_test_destructive_policy "bypass: checkout -p file"                       "" "LEAN4_GUARDRAILS_BYPASS=1 git checkout -p file.lean"   0
# Patch with no path positional — TIER-1 hard-block (whole-worktree
# interactive sweep; pipes like `yes y | …` bypass interactivity).
# Empirically verified: both forms wipe every dirty file in the worktree.
run_test_destructive_policy "git checkout -p              (always block, no path)" allow "git checkout -p"                                2
run_test_destructive_policy "git checkout --patch         (always block, no path)" allow "git checkout --patch"                           2
run_test_destructive_policy "git checkout -p HEAD         (always block, no pathspec)" allow "git checkout -p HEAD"                       2
run_test_destructive_policy "git checkout --patch HEAD    (always block, no pathspec)" allow "git checkout --patch HEAD"                  2
run_test_destructive_policy "bypass git checkout -p       (still block, no path)" allow "LEAN4_GUARDRAILS_BYPASS=1 git checkout -p"      2
run_test_destructive_policy "bypass git checkout --patch  (still block, no path)" allow "LEAN4_GUARDRAILS_BYPASS=1 git checkout --patch" 2
run_test_destructive_policy "bypass git checkout -p HEAD  (still block)"         allow "LEAN4_GUARDRAILS_BYPASS=1 git checkout -p HEAD"  2
# Negative control: -p WITH a path positional still soft-gates (path-scoped).
run_test_destructive_policy "allow: checkout -p HEAD file"                       allow "git checkout -p HEAD file.lean"                  0
# Non-force flag prefix before explicit-prefix path — same soft-gate.
run_test_destructive_policy "unset: checkout -q ./file (block=ask)"         "" "git checkout -q ./file.lean"                            2
run_test_destructive_policy "allow: checkout --quiet :/foo.lean"            allow "git checkout --quiet :/foo.lean"                   0
# Negative controls: branch creation/detach flags must not soft-gate
# (those forms aren't path-restore).
run_test_destructive_policy "allow: git checkout -b newbranch"              "" "git checkout -b newbranch"                              0
run_test_destructive_policy "allow: git checkout -b newbranch main"         "" "git checkout -b newbranch main"                         0
run_test_destructive_policy "allow: git checkout -B existing main"          "" "git checkout -B existing main"                          0
run_test_destructive_policy "allow: git checkout --orphan newroot"          "" "git checkout --orphan newroot"                          0
run_test_destructive_policy "allow: git checkout --detach main"             "" "git checkout --detach main"                             0
run_test_destructive_policy "allow: checkout HEAD~1 file"                   allow "git checkout HEAD~1 file.lean"                    0
# block: even bypass token doesn't help
run_test_destructive_policy "block: checkout HEAD file (still block)"       block "git checkout HEAD file.lean"                      2
# Branch switching with a single arg is still allowed (not the restore form)
run_test_destructive_policy "allow: switch to branch by name"               ""    "git checkout main"                                 0
run_test_destructive_policy "allow: switch to ref by name"                  ""    "git checkout origin/main"                          0
# -b/-B newbranch creates a branch; not restore, not gated
run_test_destructive_policy "allow: checkout -b newbranch"                  ""    "git checkout -b newbranch"                         0
run_test_destructive_policy "allow: checkout -b newbranch start-point"      ""    "git checkout -b newbranch main"                    0

# Option-prefixed checkout pathspec forms (merge-conflict resolution flags
# + force flag). These are restore-mode operations gated by the
# destructive policy.
run_test_destructive_policy "unset: checkout --ours file (block=ask)"       "" "git checkout --ours file.lean"                          2
run_test_destructive_policy "unset: checkout --theirs file (block=ask)"     "" "git checkout --theirs file.lean"                        2
# --merge is the long form of -m. Unlike short -m (which _strip_optvals
# removes pre-emptively to support `git commit -m "msg"`), the long
# form survives normalization and IS gated here.
run_test_destructive_policy "unset: checkout --merge file (block=ask)"      "" "git checkout --merge file.lean"                         2
run_test_destructive_policy "allow: checkout --merge file"                  allow "git checkout --merge file.lean"                     0
run_test_destructive_policy "bypass: checkout --merge file"                 "" "LEAN4_GUARDRAILS_BYPASS=1 git checkout --merge file.lean" 0
# --conflict=<style> takes a value; the regex must accept `--conflict=merge`,
# `--conflict=zdiff3`, etc., not just bare `--conflict`.
run_test_destructive_policy "unset: checkout --conflict=merge file (block=ask)" "" "git checkout --conflict=merge file.lean"            2
run_test_destructive_policy "unset: checkout --conflict=zdiff3 file (block=ask)" "" "git checkout --conflict=zdiff3 file.lean"          2
run_test_destructive_policy "allow: checkout --conflict=merge file"         allow "git checkout --conflict=merge file.lean"            0
run_test_destructive_policy "allow: checkout --conflict=zdiff3 file"        allow "git checkout --conflict=zdiff3 file.lean"           0
# -2 / -3 are short aliases for --ours / --theirs (same conflict-resolution semantics).
run_test_destructive_policy "unset: checkout -2 file (block=ask)"           "" "git checkout -2 file.lean"                              2
run_test_destructive_policy "unset: checkout -3 file (block=ask)"           "" "git checkout -3 file.lean"                              2
run_test_destructive_policy "allow: checkout -2 file"                       allow "git checkout -2 file.lean"                          0
run_test_destructive_policy "allow: checkout -3 file"                       allow "git checkout -3 file.lean"                          0
run_test_destructive_policy "bypass: checkout -2 file"                      "" "LEAN4_GUARDRAILS_BYPASS=1 git checkout -2 file.lean"   0
# Note: -m is not covered — see _strip_optvals limitation comment in guardrails.sh
run_test_destructive_policy "allow: checkout --ours file"                   allow "git checkout --ours file.lean"                      0
run_test_destructive_policy "allow: checkout --theirs src/foo.lean"         allow "git checkout --theirs src/foo.lean"                  0
run_test_destructive_policy "bypass: checkout --ours file"                  "" "LEAN4_GUARDRAILS_BYPASS=1 git checkout --ours file.lean" 0
run_test_destructive_policy "block: checkout --ours file (still block)"     block "git checkout --ours file.lean"                       2

# Single positional with explicit path prefix (./, :/, ../)
# Distinguishes obvious path arguments from branch names.
run_test_destructive_policy "unset: checkout ./file (block=ask)"            "" "git checkout ./file.lean"                                2
run_test_destructive_policy "unset: checkout :/file (block=ask)"            "" "git checkout :/file.lean"                                2
run_test_destructive_policy "unset: checkout ../file (block=ask)"           "" "git checkout ../file.lean"                               2
run_test_destructive_policy "allow: checkout ./file"                        allow "git checkout ./file.lean"                            0
run_test_destructive_policy "bypass: checkout ./file"                       "" "LEAN4_GUARDRAILS_BYPASS=1 git checkout ./file.lean"      0
run_test_destructive_policy "block: checkout ./file (still block)"          block "git checkout ./file.lean"                            2

# Dotfile path-prefix forms (e.g., ./.env, ./.github/...) — same gating
# as non-dotfile path-prefix forms.
run_test_destructive_policy "unset: checkout ./.env (block=ask)"            "" "git checkout ./.env"                                     2
run_test_destructive_policy "unset: checkout :/.env (block=ask)"            "" "git checkout :/.env"                                     2
run_test_destructive_policy "unset: checkout ../.env (block=ask)"           "" "git checkout ../.env"                                    2
run_test_destructive_policy "allow: checkout ./.env"                        allow "git checkout ./.env"                                  0
run_test_destructive_policy "allow: checkout ./.github path"                allow "git checkout ./.github/workflows/lint.yml"            0

# Force-mode checkout / switch — branch-like vs path-like.
# Branch-like (no path indicators) is hard-blocked because force branch
# checkout discards uncommitted edits across the whole worktree.
run_test_destructive_policy "git checkout -f main             (always block)" allow "git checkout -f main"                              2
run_test_destructive_policy "git checkout --force main        (always block)" allow "git checkout --force main"                        2
run_test_destructive_policy "git checkout -f feature_x        (always block)" allow "git checkout -f feature_x"                        2
run_test_destructive_policy "bypass git checkout -f main      (still block)" allow "LEAN4_GUARDRAILS_BYPASS=1 git checkout -f main"   2
# git switch in force/discard-changes mode — always hard-block.
run_test_destructive_policy "git switch -f main               (always block)" allow "git switch -f main"                               2
run_test_destructive_policy "git switch --force main          (always block)" allow "git switch --force main"                         2
run_test_destructive_policy "git switch --discard-changes main (always block)" allow "git switch --discard-changes main"               2
run_test_destructive_policy "bypass git switch -f main        (still block)" allow "LEAN4_GUARDRAILS_BYPASS=1 git switch -f main"     2
# Force checkout with options interleaved before/after -f: same hard-block.
run_test_destructive_policy "git checkout -q -f main          (always block)" allow "git checkout -q -f main"                           2
run_test_destructive_policy "git checkout --quiet --force main (always block)" allow "git checkout --quiet --force main"                 2
run_test_destructive_policy "git checkout -f --detach HEAD    (always block)" allow "git checkout -f --detach HEAD"                     2
run_test_destructive_policy "git checkout -f -B tmp main      (always block)" allow "git checkout -f -B tmp main"                       2
# Force checkout with git ref shorthand forms — branch/ref-switch hard-block.
run_test_destructive_policy 'git checkout -f @{-1}           (always block)' allow 'git checkout -f @{-1}'                              2
run_test_destructive_policy "git checkout --force @{-1}      (always block)" allow 'git checkout --force @{-1}'                         2
run_test_destructive_policy "git checkout -f -                (always block)" allow "git checkout -f -"                                 2
run_test_destructive_policy "git checkout --force -            (always block)" allow "git checkout --force -"                            2
run_test_destructive_policy "git checkout -f @                (always block)" allow "git checkout -f @"                                 2
run_test_destructive_policy "git checkout -f HEAD~3           (always block)" allow "git checkout -f HEAD~3"                            2
run_test_destructive_policy 'git checkout -f HEAD@{1}        (always block)' allow 'git checkout -f HEAD@{1}'                           2
# Bypass token does not override ref-shorthand force hard-blocks (Layer 1
# confirmed these discard the dirty worktree; tier-1 stays absolute).
run_test_destructive_policy 'bypass git checkout -f @{-1}    (still block)' allow 'LEAN4_GUARDRAILS_BYPASS=1 git checkout -f @{-1}'      2
run_test_destructive_policy "bypass git checkout -f -         (still block)" allow "LEAN4_GUARDRAILS_BYPASS=1 git checkout -f -"        2
# Force checkout with path-like and option interleaving: soft-gate.
run_test_destructive_policy "unset: checkout -q -f file (block=ask)"        "" "git checkout -q -f file.lean"                            2
run_test_destructive_policy "allow: checkout -q -f file"                    allow "git checkout -q -f file.lean"                       0
run_test_destructive_policy "allow: checkout --quiet --force file"          allow "git checkout --quiet --force file.lean"             0
# Force checkout with explicit `--` separator: defers to general -- soft-gate.
run_test_destructive_policy "allow: checkout -f -- file"                    allow "git checkout -f -- file.lean"                       0
run_test_destructive_policy "unset: checkout -f -- file (block=ask)"        "" "git checkout -f -- file.lean"                           2
# Force restore with explicit ./ path prefix — soft-gate (path-scoped).
run_test_destructive_policy "unset: checkout -f ./file (block=ask)"         "" "git checkout -f ./file.lean"                              2
run_test_destructive_policy "allow: checkout -f ./file"                     allow "git checkout -f ./file.lean"                        0
run_test_destructive_policy "bypass: checkout -f ./file"                    "" "LEAN4_GUARDRAILS_BYPASS=1 git checkout -f ./file.lean" 0
# Path-like -f forms — soft-gate (path-scoped).
run_test_destructive_policy "unset: checkout -f file (block=ask)"           "" "git checkout -f file.lean"                              2
run_test_destructive_policy "unset: checkout -f docs/ (block=ask)"          "" "git checkout -f docs/"                                  2
run_test_destructive_policy "allow: checkout -f file"                       allow "git checkout -f file.lean"                          0
run_test_destructive_policy "allow: checkout --force file"                  allow "git checkout --force file.lean"                     0
run_test_destructive_policy "bypass: checkout -f file"                      "" "LEAN4_GUARDRAILS_BYPASS=1 git checkout -f file.lean"   0
run_test_destructive_policy "block: checkout -f file (still block)"         block "git checkout -f file.lean"                          2
# Negative: git switch --force-create (creates branch over existing; doesn't touch worktree)
# should NOT match the switch-force hard-block.
run_test_destructive_policy "allow: git switch --force-create new" "" "git switch --force-create new-branch" 0
# Negative: regular branch switching stays allowed.
run_test_destructive_policy "allow: git switch main" "" "git switch main" 0
run_test_destructive_policy "allow: git checkout main" "" "git checkout main" 0
# `git checkout -` (bare dash, no force) is "switch to previous branch"; git
# itself refuses the operation if the worktree is dirty, so it never destroys
# data. Stays in the implicit-allow tier — Layer 1 confirmed PRESERVED.
run_test_destructive_policy "allow: git checkout -" "" "git checkout -" 0

echo ""
echo "-- Destructive policy: path-scoped git restore <path…> --"
# Default: same shape
run_test_destructive_policy "unset: restore file (block=ask)"               "" "git restore file.lean"                                  2
run_test_destructive_policy "unset: bypass restore file (allow=ask)"        "" "LEAN4_GUARDRAILS_BYPASS=1 git restore file.lean"        0
# Pure unstaging — always allowed regardless of policy (any pathspec,
# including the whole-index `--staged .` form — pure unstaging is
# index-only and recoverable).
run_test_destructive_policy "unset: restore --staged file (allow always)"   "" "git restore --staged file.lean"                         0
run_test_destructive_policy "block: restore --staged file (allow always)"   block "git restore --staged file.lean"                     0
run_test_destructive_policy "unset: restore --staged . (allow always)"      "" "git restore --staged ."                                 0
run_test_destructive_policy "block: restore --staged . (allow always)"      block "git restore --staged ."                             0
run_test_destructive_policy "unset: restore --staged ./ (allow always)"     "" "git restore --staged ./"                                0
# allow: any path-scoped restore
run_test_destructive_policy "allow: restore file"                           allow "git restore file.lean"                              0
run_test_destructive_policy "allow: restore directory"                      allow "git restore src/"                                   0
# block: even bypass token doesn't help
run_test_destructive_policy "block: restore file (still block)"             block "git restore file.lean"                              2
run_test_destructive_policy "block: bypass restore file (still block)"      block "LEAN4_GUARDRAILS_BYPASS=1 git restore file.lean"    2

# Short flag aliases: -S = --staged, -W = --worktree.
# Pure unstaging via -S (or any bundle containing S but not W) is allowed.
run_test_destructive_policy "unset: restore -S file (allow always)"         "" "git restore -S file.lean"                                0
run_test_destructive_policy "block: restore -S file (allow always)"         block "git restore -S file.lean"                            0
run_test_destructive_policy "block: restore -S . (allow always)"            block "git restore -S ."                                    0
# Combined index+worktree via -SW or mixed long/short → hard-block
run_test_destructive_policy "git restore -SW file (always block)"           allow "git restore -SW file.lean"                           2
run_test_destructive_policy "git restore -WS file (always block)"           allow "git restore -WS file.lean"                           2
run_test_destructive_policy "git restore --staged -W file (always block)"   allow "git restore --staged -W file.lean"                   2
run_test_destructive_policy "git restore -S --worktree file (always block)" allow "git restore -S --worktree file.lean"                 2
# Worktree-only via -W alone is path-scoped destructive → soft-gate
run_test_destructive_policy "allow: restore -W file"                        allow "git restore -W file.lean"                            0
run_test_destructive_policy "unset: restore -W file (block=ask)"            "" "git restore -W file.lean"                                2

echo ""
echo "-- Hard-block: whole-worktree variants stay non-bypassable --"
# These must block regardless of DESTRUCTIVE_POLICY value or bypass token.
# Coverage includes the broader pathspec variants: `.`, `./`, `:/`,
# `:(top)`, the `checkout HEAD -- .` form (ref before `--`), and
# combined `--staged --worktree` restores.
run_test_destructive_policy "git checkout .                   (always block)" allow "git checkout ."                                    2
run_test_destructive_policy "git checkout ./                  (always block)" allow "git checkout ./"                                   2
run_test_destructive_policy "git checkout -- .                (always block)" allow "git checkout -- ."                                 2
run_test_destructive_policy "git checkout -- ./               (always block)" allow "git checkout -- ./"                                2
run_test_destructive_policy "git checkout -- :/               (always block)" allow "git checkout -- :/"                                2
run_test_destructive_policy "git checkout -- :(top)           (always block)" allow "git checkout -- :(top)"                            2
run_test_destructive_policy "git checkout HEAD -- .           (always block)" allow "git checkout HEAD -- ."                            2
run_test_destructive_policy "git checkout HEAD -- ./          (always block)" allow "git checkout HEAD -- ./"                           2
run_test_destructive_policy "git checkout HEAD .              (always block)" allow "git checkout HEAD ."                               2
run_test_destructive_policy "git checkout HEAD ./             (always block)" allow "git checkout HEAD ./"                              2
run_test_destructive_policy "git checkout main :/             (always block)" allow "git checkout main :/"                              2
# Option-prefixed whole-worktree pathspec variants — all hard-block.
run_test_destructive_policy "git checkout -f .                (always block)" allow "git checkout -f ."                                 2
run_test_destructive_policy "git checkout --force ./          (always block)" allow "git checkout --force ./"                           2
run_test_destructive_policy "git checkout --ours .            (always block)" allow "git checkout --ours ."                             2
run_test_destructive_policy "git checkout --theirs :/         (always block)" allow "git checkout --theirs :/"                          2
# Note: -m is not covered — see _strip_optvals limitation comment in guardrails.sh
# --pathspec-from-file always hard-blocks (paths hidden in a file)
run_test_destructive_policy "git checkout --pathspec-from-file (always block)" allow "git checkout --pathspec-from-file=paths.txt"      2
run_test_destructive_policy "git checkout HEAD --pathspec-from-file (always block)" allow "git checkout HEAD --pathspec-from-file=paths.txt" 2
run_test_destructive_policy "git restore .                    (always block)" allow "git restore ."                                     2
run_test_destructive_policy "git restore ./                   (always block)" allow "git restore ./"                                    2
run_test_destructive_policy "git restore :/                   (always block)" allow "git restore :/"                                    2
run_test_destructive_policy "git restore --staged --worktree  (always block)" allow "git restore --staged --worktree file.lean"        2
run_test_destructive_policy "git restore --pathspec-from-file (always block)" allow "git restore --pathspec-from-file=paths.txt"        2
run_test_destructive_policy "git restore --worktree --pathspec-from-file (always block)" allow "git restore --worktree --pathspec-from-file=paths.txt" 2
# Pure-unstaging --staged --pathspec-from-file remains allowed (index-only).
run_test_destructive_policy "restore --staged --pathspec-from-file (allow always)" block "git restore --staged --pathspec-from-file=paths.txt" 0
run_test_destructive_policy "restore -S --pathspec-from-file (allow always)" block "git restore -S --pathspec-from-file=paths.txt" 0
run_test_destructive_policy "git reset --hard                 (always block)" allow "git reset --hard"                                  2
run_test_destructive_policy "git clean -fd                    (always block)" allow "git clean -fd"                                     2
run_test_destructive_policy "git clean --force                (always block)" allow "git clean --force"                                 2
# Even with bypass token, whole-worktree ops must stay blocked.
run_test_destructive_policy "bypass git checkout .            (still block)" allow "LEAN4_GUARDRAILS_BYPASS=1 git checkout ."          2
run_test_destructive_policy "bypass git checkout -- .         (still block)" allow "LEAN4_GUARDRAILS_BYPASS=1 git checkout -- ."       2
run_test_destructive_policy "bypass git checkout HEAD -- .    (still block)" allow "LEAN4_GUARDRAILS_BYPASS=1 git checkout HEAD -- ."  2
run_test_destructive_policy "bypass git checkout HEAD .       (still block)" allow "LEAN4_GUARDRAILS_BYPASS=1 git checkout HEAD ."     2
run_test_destructive_policy "bypass git checkout -f .         (still block)" allow "LEAN4_GUARDRAILS_BYPASS=1 git checkout -f ."       2
run_test_destructive_policy "bypass git checkout --ours .     (still block)" allow "LEAN4_GUARDRAILS_BYPASS=1 git checkout --ours ."   2
run_test_destructive_policy "bypass git checkout --pathspec-from-file (still block)" allow "LEAN4_GUARDRAILS_BYPASS=1 git checkout --pathspec-from-file=paths.txt" 2
run_test_destructive_policy "bypass git restore --pathspec-from-file (still block)" allow "LEAN4_GUARDRAILS_BYPASS=1 git restore --pathspec-from-file=paths.txt" 2
run_test_destructive_policy "bypass git restore ./            (still block)" allow "LEAN4_GUARDRAILS_BYPASS=1 git restore ./"           2
run_test_destructive_policy "bypass git reset --hard          (still block)" allow "LEAN4_GUARDRAILS_BYPASS=1 git reset --hard"        2
run_test_destructive_policy "bypass git clean -fd             (still block)" allow "LEAN4_GUARDRAILS_BYPASS=1 git clean -fd"           2

echo ""
echo "-- Policy independence: COLLAB and DESTRUCTIVE govern separately --"
# DESTRUCTIVE_POLICY=allow doesn't unblock collab ops; COLLAB_POLICY=allow doesn't unblock destructive ops.
run_test_destructive_policy "allow: git push (still block — collab governs)" allow "git push origin main"                              2
run_test_policy "allow: checkout -- file (still block — destructive governs)" allow "git checkout -- file.lean"                       2
run_test_policy "allow: restore file (still block — destructive governs)"    allow "git restore file.lean"                            2

echo ""
echo "-- Invalid destructive policy values fall back to ask --"
run_test_destructive_policy "invalid: yolo plain checkout -- (block=ask)"  yolo "git checkout -- file.lean"                            2
run_test_destructive_policy "invalid: yolo bypass checkout -- (allow=ask)" yolo "LEAN4_GUARDRAILS_BYPASS=1 git checkout -- file.lean" 0

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

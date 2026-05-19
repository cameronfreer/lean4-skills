#!/usr/bin/env bash
set -euo pipefail

# Self-test for lint_runtime_portability.sh — verifies it catches all advertised
# Bash 4+ / BSD-incompatible constructs (Checks 1–7), runtime shebang
# regressions for both shell and Python (Checks 8–9), and the
# guardrail-bypassing bin/ shortcut path (Check 10) — and does NOT
# false-positive on safe parameter-expansion forms that legitimately
# contain , or ^.
#
# Helpers invoke the copied lint with $BASH_FOR_COMPAT (default /bin/bash)
# so the self-test is end-to-end under the system default Bash, even when a
# newer Bash is earlier on PATH. CI invokes this with the default to match
# the macOS Bash-3.2 contract. On hosts without /bin/bash (e.g. NixOS) the
# test SKIPs gracefully; developers can also point BASH_FOR_COMPAT at
# /opt/homebrew/bin/bash etc. to exercise other interpreters.
#
# Scope note: Check 1 (case modifiers) is a heuristic. It targets common
# forms — ${var,,}, ${var,}, ${var^^}, ${var^}, patterned variants — and
# has one known false-negative on arithmetic-subscript case-mod like
# ${arr[i-1],,}. That form is intentionally out of scope.

BASH_FOR_COMPAT="${BASH_FOR_COMPAT:-/bin/bash}"
if [[ ! -x "$BASH_FOR_COMPAT" ]]; then
  echo "SKIP: $BASH_FOR_COMPAT not found — cannot run lint self-test"
  exit 0
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LINT="$SCRIPT_DIR/../tools/lint_runtime_portability.sh"

PASS=0
FAIL=0

TMPDIR_ROOT=$(mktemp -d)
trap 'rm -rf "$TMPDIR_ROOT"' EXIT

mkdir -p "$TMPDIR_ROOT/hooks" "$TMPDIR_ROOT/lib/scripts" "$TMPDIR_ROOT/tools"
cp "$LINT" "$TMPDIR_ROOT/tools/lint_runtime_portability.sh"

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

# On FAIL, helpers dump the captured lint output indented under the
# failure line so the actual diagnostic is visible in CI logs without
# rerunning anything. Lint stdout+stderr is captured to a local variable
# (not /dev/null) for exactly this reason.

# expect_lint_fail "description" "script body"
#   Writes script body to a probe file, runs the lint under
#   $BASH_FOR_COMPAT, asserts exit 1 (lint caught the issue).
expect_lint_fail() {
  local desc="$1" body="$2" output
  local probe="$TMPDIR_ROOT/lib/scripts/probe.sh"
  printf '#!/usr/bin/env bash\n%s\n' "$body" > "$probe"
  local exit_code=0
  output=$("$BASH_FOR_COMPAT" "$TMPDIR_ROOT/tools/lint_runtime_portability.sh" 2>&1) || exit_code=$?
  if [[ "$exit_code" -eq 1 ]]; then
    echo "  PASS: $desc"
    ((PASS++)) || true
  else
    echo "  FAIL: $desc (expected exit 1, got $exit_code)"
    echo "$output" | sed 's/^/      /'
    ((FAIL++)) || true
  fi
  rm -f "$probe"
}

# expect_lint_pass "description" "script body"
#   Writes script body to a probe file, runs the lint under
#   $BASH_FOR_COMPAT, asserts exit 0 (lint did not false-positive).
expect_lint_pass() {
  local desc="$1" body="$2" output
  local probe="$TMPDIR_ROOT/lib/scripts/probe.sh"
  printf '#!/usr/bin/env bash\n%s\n' "$body" > "$probe"
  local exit_code=0
  output=$("$BASH_FOR_COMPAT" "$TMPDIR_ROOT/tools/lint_runtime_portability.sh" 2>&1) || exit_code=$?
  if [[ "$exit_code" -eq 0 ]]; then
    echo "  PASS: $desc"
    ((PASS++)) || true
  else
    echo "  FAIL: $desc (expected exit 0, got $exit_code)"
    echo "$output" | sed 's/^/      /'
    ((FAIL++)) || true
  fi
  rm -f "$probe"
}

# ---------------------------------------------------------------------------
# Bad probes — each MUST be caught (exit 1)
# ---------------------------------------------------------------------------
echo "-- Bad probes (must be caught) --"

# Check 1: case modifiers (heuristic, common forms only)
expect_lint_fail '${val,,} — basic lowercase'            'x="${val,,}"'
expect_lint_fail '${val,} — single-char lowercase'       'x="${val,}"'
expect_lint_fail '${val^^} — basic uppercase'            'x="${val^^}"'
expect_lint_fail '${val^} — single-char uppercase'       'x="${val^}"'
expect_lint_fail '${val,,[A-Z]} — patterned case-mod'    'x="${val,,[A-Z]}"'

# Check 2: associative arrays (any declare|local|typeset with A in flags)
expect_lint_fail 'declare -A — basic assoc'              'declare -A mymap'
expect_lint_fail 'declare -Ag — bundled assoc (global)'  'declare -Ag mymap'
expect_lint_fail 'declare -rA — bundled assoc (readonly)' 'declare -rA mymap'
expect_lint_fail 'local -A — local assoc'                'local -A mymap'
expect_lint_fail 'typeset -A — typeset assoc'            'typeset -A mymap'

# Check 3: namerefs (any declare|local|typeset with n in flags)
expect_lint_fail 'declare -n — basic nameref'            'declare -n ref=var'
expect_lint_fail 'declare -gn — bundled nameref (global)' 'declare -gn ref=var'
expect_lint_fail 'declare -rn — bundled nameref (readonly)' 'declare -rn ref=var'
expect_lint_fail 'local -n — local nameref'              'local -n ref=var'
expect_lint_fail 'typeset -n — typeset nameref'          'typeset -n ref=var'

# Check 4: mapfile / readarray
expect_lint_fail 'mapfile — Bash 4+'                     'mapfile -t lines < /dev/null'
expect_lint_fail 'readarray — Bash 4+'                   'readarray -t lines < /dev/null'

# Check 5: coproc
expect_lint_fail 'coproc — Bash 4+'                      'coproc mycoproc { cat; }'

# Check 6: ${var@op} expansions
expect_lint_fail '${var@Q} — Bash 4.4+'                  'echo "${myvar@Q}"'

# Check 7: mktemp with suffix after X's (BSD portability)
expect_lint_fail 'mktemp ...XXXXXX.json — BSD incompat'  'mktemp /tmp/lean4-session-XXXXXX.json'

# ---------------------------------------------------------------------------
# Safe probes — each MUST pass (exit 0) — prevent Check 1 over-matching
# ---------------------------------------------------------------------------
echo ""
echo "-- Safe probes (must pass) --"

# Colon parameter-expansion forms with , or ^ in the replacement
expect_lint_pass '${v:-foo,bar} — colon-default with comma'      'x="${v:-foo,bar}"'
expect_lint_pass '${v:=foo^bar} — colon-assign with caret'        'x="${v:=foo^bar}"'
expect_lint_pass '${v:+foo,bar} — colon-alternate with comma'     'x="${v:+foo,bar}"'

# Non-colon parameter-expansion forms with , or ^ in the replacement
expect_lint_pass '${v-foo,bar} — non-colon default with comma'    'x="${v-foo,bar}"'
expect_lint_pass '${v=foo^bar} — non-colon assign with caret'     'x="${v=foo^bar}"'
expect_lint_pass '${v?foo,bar} — non-colon error with comma'      'x="${v?foo,bar}"'
expect_lint_pass '${v+foo^bar} — non-colon alternate with caret'  'x="${v+foo^bar}"'

# Other operators with , or ^ in their operand
expect_lint_pass '${v/foo,bar/baz} — substitution with comma'     'x="${v/foo,bar/baz}"'
expect_lint_pass '${v#foo,bar} — prefix removal with comma'       'x="${v#foo,bar}"'
expect_lint_pass '${v%foo^bar} — suffix removal with caret'       'x="${v%foo^bar}"'

# declare / local / typeset without the specific flags
expect_lint_pass 'declare -a arr — indexed array (Bash 2+)'       'declare -a arr'
expect_lint_pass 'local -r x=1 — readonly local'                  'local -r x=1 2>/dev/null || true'

# mktemp forms that are portable
expect_lint_pass 'mktemp -d — no suffix'                          'mktemp -d'
expect_lint_pass 'mktemp ending in XXXXXX — no post-X suffix'     'mktemp "${TMPDIR:-/tmp}/lean4.XXXXXX"'

# ---------------------------------------------------------------------------
# Combined probe — exactly 7 categories should fire (one per lint check)
# Using == not >= so overmatching regressions are caught.
# ---------------------------------------------------------------------------
echo ""
echo "-- Combined probe (exactly 7 categories fire) --"

cat > "$TMPDIR_ROOT/lib/scripts/bad_all.sh" <<'PROBE'
#!/usr/bin/env bash
lower="${val,,}"
declare -A mymap
mapfile -t lines < /dev/null
mktemp /tmp/lean4-session-XXXXXX.json
declare -n ref=var
coproc mycoproc { cat; }
echo "${myvar@Q}"
PROBE

combined_output=$("$BASH_FOR_COMPAT" "$TMPDIR_ROOT/tools/lint_runtime_portability.sh" 2>&1 || true)
# Count warn lines that report actual matches (filename:line:content),
# excluding the summary line ("⚠️  N issue(s) found...").
combined_issue_count=$(echo "$combined_output" | grep -c '^⚠️.*:[0-9]\+:' || true)
if [[ "$combined_issue_count" -eq 7 ]]; then
  echo "  PASS: Combined probe fires exactly 7 categories"
  ((PASS++)) || true
else
  echo "  FAIL: Expected exactly 7 issues, got $combined_issue_count"
  echo "$combined_output"
  ((FAIL++)) || true
fi
rm "$TMPDIR_ROOT/lib/scripts/bad_all.sh"

# ---------------------------------------------------------------------------
# Check 8 self-tests — runtime-path shebang regression
#
# Writes a probe with the given shebang line and a no-op body, asserts the
# linter exits non-zero (Check 8 flags the shebang). Kept separate from
# the "exactly 7 categories" combined probe above, which intentionally
# stays scoped to Bash-4/BSD construct categories.
# ---------------------------------------------------------------------------
echo ""
echo "-- Check 8 self-tests (shebang regression) --"

expect_shebang_lint_fail() {
  local desc="$1" shebang="$2" output
  local probe="$TMPDIR_ROOT/lib/scripts/probe.sh"
  printf '%s\n: # no-op\n' "$shebang" > "$probe"
  local exit_code=0
  output=$("$BASH_FOR_COMPAT" "$TMPDIR_ROOT/tools/lint_runtime_portability.sh" 2>&1) || exit_code=$?
  if [[ "$exit_code" -eq 1 ]]; then
    echo "  PASS: $desc"
    ((PASS++)) || true
  else
    echo "  FAIL: $desc (expected exit 1, got $exit_code)"
    echo "$output" | sed 's/^/      /'
    ((FAIL++)) || true
  fi
  rm -f "$probe"
}

# Positive cases — absolute Bash shebangs must be rejected in runtime path.
expect_shebang_lint_fail '#!/bin/bash — system path'                '#!/bin/bash'
expect_shebang_lint_fail '#!/usr/bin/bash — alt system path'        '#!/usr/bin/bash'
expect_shebang_lint_fail '#!/opt/homebrew/bin/bash — Homebrew path' '#!/opt/homebrew/bin/bash'
expect_shebang_lint_fail '#!/usr/local/bin/bash — alt prefix'       '#!/usr/local/bin/bash'

# env-bash with extra arguments must be rejected: on Linux, env treats
# 'bash -e' as one program name and the kernel exec fails (env -S would
# split it, but we want a single, mechanical rule). Set flags inside the
# script body via 'set -...' instead.
expect_shebang_lint_fail '#!/usr/bin/env bash -e — non-portable env args' '#!/usr/bin/env bash -e'

# Token-boundary regression — defends against a future "loosening" of the
# exact match back to a prefix/substring form. Trivially rejected today
# (bashfoo != bash), but the probe ensures it stays that way.
expect_shebang_lint_fail '#!/usr/bin/env bashfoo — not bash token' '#!/usr/bin/env bashfoo'

# Wrong interpreter — env-sh / env-zsh etc. must be rejected; runtime
# scripts assume bash 3.2+ features (arrays, [[ ]], etc.).
expect_shebang_lint_fail '#!/usr/bin/env sh — wrong interpreter' '#!/usr/bin/env sh'

# No shebang at all — first line is a regular comment. Runtime scripts
# must declare their interpreter explicitly; the probe-writing helper
# uses head -n1 to read the shebang, so a leading non-#! line trips the
# check.
expect_shebang_lint_fail 'no shebang — first line is a regular comment' '# just a comment'

# Negative case — exact '#!/usr/bin/env bash' with a clean body must
# pass cleanly. Re-uses the existing expect_lint_pass helper, which
# writes '#!/usr/bin/env bash' as the probe's shebang.
expect_lint_pass '#!/usr/bin/env bash — accepted by Check 8' ': # no-op'

# ---------------------------------------------------------------------------
# Check 9 self-tests — runtime-path Python shebang regression
#
# Writes a probe .py file with the given shebang and a trivial body,
# asserts the linter exits 1 (Check 9 flags the shebang). The acceptable
# form is exactly '#!/usr/bin/env python3'; the no-shebang case is also
# acceptable (library modules without a shebang are out of scope).
# ---------------------------------------------------------------------------
echo ""
echo "-- Check 9 self-tests (Python shebang regression) --"

expect_py_shebang_lint_fail() {
  local desc="$1" shebang="$2" output
  local probe="$TMPDIR_ROOT/lib/scripts/probe.py"
  printf '%s\npass\n' "$shebang" > "$probe"
  local exit_code=0
  output=$("$BASH_FOR_COMPAT" "$TMPDIR_ROOT/tools/lint_runtime_portability.sh" 2>&1) || exit_code=$?
  if [[ "$exit_code" -eq 1 ]]; then
    echo "  PASS: $desc"
    ((PASS++)) || true
  else
    echo "  FAIL: $desc (expected exit 1, got $exit_code)"
    echo "$output" | sed 's/^/      /'
    ((FAIL++)) || true
  fi
  rm -f "$probe"
}

expect_py_lint_pass() {
  local desc="$1" content="$2" output
  local probe="$TMPDIR_ROOT/lib/scripts/probe.py"
  printf '%s\n' "$content" > "$probe"
  local exit_code=0
  output=$("$BASH_FOR_COMPAT" "$TMPDIR_ROOT/tools/lint_runtime_portability.sh" 2>&1) || exit_code=$?
  if [[ "$exit_code" -eq 0 ]]; then
    echo "  PASS: $desc"
    ((PASS++)) || true
  else
    echo "  FAIL: $desc (expected exit 0, got $exit_code)"
    echo "$output" | sed 's/^/      /'
    ((FAIL++)) || true
  fi
  rm -f "$probe"
}

# Positive cases — must be rejected.
expect_py_shebang_lint_fail '#!/usr/bin/env sh — polyglot trampoline regression' '#!/usr/bin/env sh'
expect_py_shebang_lint_fail '#!/usr/bin/env python — missing version suffix'     '#!/usr/bin/env python'
expect_py_shebang_lint_fail '#!/usr/bin/python3 — absolute system path'          '#!/usr/bin/python3'
expect_py_shebang_lint_fail '#!/opt/homebrew/bin/python3 — Homebrew path'        '#!/opt/homebrew/bin/python3'
expect_py_shebang_lint_fail '#!/usr/bin/env python3.10 — pinned minor version'   '#!/usr/bin/env python3.10'
expect_py_shebang_lint_fail '#!/usr/bin/env pythonfoo — token-boundary'          '#!/usr/bin/env pythonfoo'

# Negative cases — must be accepted.
expect_py_lint_pass '#!/usr/bin/env python3 — exact, accepted' '#!/usr/bin/env python3
pass'
expect_py_lint_pass 'no shebang — library module is out of scope' '"""Library module."""
def f(): pass'

# ---------------------------------------------------------------------------
# Check 10 self-tests — no plugins/lean4/bin shortcut path
#
# Creates $TMPDIR_ROOT/bin as a symlink, file, or directory and asserts
# the linter exits 1. Cleans up after each. The no-bin negative case is
# implicitly verified by every other probe (none of them creates bin/),
# so all the prior "lint exits 0" expectations also cover Check 10.
# ---------------------------------------------------------------------------
echo ""
echo "-- Check 10 self-tests (no bin shortcut) --"

expect_bin_lint_fail() {
  local desc="$1" kind="$2" output  # kind: symlink|file|dir
  local bin="$TMPDIR_ROOT/bin"
  case "$kind" in
    symlink) ln -s lib/scripts "$bin" ;;
    file) touch "$bin" ;;
    dir) mkdir "$bin" ;;
    *) echo "  FAIL: $desc (internal: unknown kind '$kind')"; ((FAIL++)) || true; return ;;
  esac
  local exit_code=0
  output=$("$BASH_FOR_COMPAT" "$TMPDIR_ROOT/tools/lint_runtime_portability.sh" 2>&1) || exit_code=$?
  if [[ "$exit_code" -eq 1 ]]; then
    echo "  PASS: $desc"
    ((PASS++)) || true
  else
    echo "  FAIL: $desc (expected exit 1, got $exit_code)"
    echo "$output" | sed 's/^/      /'
    ((FAIL++)) || true
  fi
  rm -rf "$bin"
}

expect_bin_lint_fail 'bin/ as symlink to lib/scripts' symlink
expect_bin_lint_fail 'bin/ as plain directory'        dir
expect_bin_lint_fail 'bin/ as plain file'             file

# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------
echo ""
echo "=== Results: $PASS passed, $FAIL failed ==="
[[ "$FAIL" -eq 0 ]]

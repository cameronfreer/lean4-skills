#!/usr/bin/env bash
set -euo pipefail

# Self-test for lint_bash_compat.sh — verifies it catches all 7 advertised
# Bash 4+ / BSD-incompatible constructs and does NOT false-positive on safe
# parameter-expansion forms that legitimately contain , or ^.
#
# Helpers invoke the copied lint with /bin/bash explicitly so the self-test
# is end-to-end under the system default Bash, even when a newer Bash is
# earlier on PATH. Matches the CI workflow's /bin/bash invocation.
#
# Scope note: Check 1 (case modifiers) is a heuristic. It targets common
# forms — ${var,,}, ${var,}, ${var^^}, ${var^}, patterned variants — and
# has one known false-negative on arithmetic-subscript case-mod like
# ${arr[i-1],,}. That form is intentionally out of scope.

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LINT="$SCRIPT_DIR/../tools/lint_bash_compat.sh"

PASS=0
FAIL=0

TMPDIR_ROOT=$(mktemp -d)
trap 'rm -rf "$TMPDIR_ROOT"' EXIT

mkdir -p "$TMPDIR_ROOT/hooks" "$TMPDIR_ROOT/lib/scripts" "$TMPDIR_ROOT/tools"
cp "$LINT" "$TMPDIR_ROOT/tools/lint_bash_compat.sh"

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

# expect_lint_fail "description" "script body"
#   Writes script body to a probe file, runs the lint under /bin/bash,
#   asserts exit 1 (lint caught the issue).
expect_lint_fail() {
  local desc="$1" body="$2"
  local probe="$TMPDIR_ROOT/lib/scripts/probe.sh"
  printf '#!/usr/bin/env bash\n%s\n' "$body" > "$probe"
  local exit_code=0
  /bin/bash "$TMPDIR_ROOT/tools/lint_bash_compat.sh" >/dev/null 2>&1 || exit_code=$?
  if [[ "$exit_code" -eq 1 ]]; then
    echo "  PASS: $desc"
    ((PASS++)) || true
  else
    echo "  FAIL: $desc (expected exit 1, got $exit_code)"
    ((FAIL++)) || true
  fi
  rm -f "$probe"
}

# expect_lint_pass "description" "script body"
#   Writes script body to a probe file, runs the lint under /bin/bash,
#   asserts exit 0 (lint did not false-positive).
expect_lint_pass() {
  local desc="$1" body="$2"
  local probe="$TMPDIR_ROOT/lib/scripts/probe.sh"
  printf '#!/usr/bin/env bash\n%s\n' "$body" > "$probe"
  local exit_code=0
  /bin/bash "$TMPDIR_ROOT/tools/lint_bash_compat.sh" >/dev/null 2>&1 || exit_code=$?
  if [[ "$exit_code" -eq 0 ]]; then
    echo "  PASS: $desc"
    ((PASS++)) || true
  else
    echo "  FAIL: $desc (expected exit 0, got $exit_code)"
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

combined_output=$(/bin/bash "$TMPDIR_ROOT/tools/lint_bash_compat.sh" 2>&1 || true)
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
# Summary
# ---------------------------------------------------------------------------
echo ""
echo "=== Results: $PASS passed, $FAIL failed ==="
[[ "$FAIL" -eq 0 ]]

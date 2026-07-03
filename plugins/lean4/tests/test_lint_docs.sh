#!/usr/bin/env bash
set -euo pipefail

# Self-test for lint_docs.sh Check 8c (Python helper interpreter prefix,
# closes #135) and Check 8e (compilation-errors.md heading uniqueness).
# For each check, verify it fires on a planted violation and emits its
# clean-run OK line once the violation is removed.
#
# Pattern: plant a violation inside the real plugin tree, run
# lint_docs.sh once (assert WARN fires), restore, run again (assert OK
# line present, WARN absent). Check 8c uses a scratch .md file inside
# references/; Check 8e mutates compilation-errors.md itself and restores
# from a mktemp backup (not git checkout — checkout would clobber any
# uncommitted user edits). A trap on EXIT stays installed as a safety net.
#
# Unlike test_lint_runtime_portability.sh (which copies the lint into
# a synthetic isolated tree), lint_docs.sh runs many checks that
# require a fully-populated plugin tree (commands/, agents/, SKILL.md,
# etc.). Building a minimal substitute is high-overhead; we use the
# real tree and assert on output content. Critically the test does
# NOT depend on lint_docs.sh exiting 0 — the linter may already exit
# nonzero from inherited warnings on main (line-length flags, etc.)
# unrelated to this check.
#
# Helpers invoke lint_docs.sh under $BASH_FOR_COMPAT (default /bin/bash)
# so the self-test runs under macOS Bash 3.2 in CI. On hosts without
# /bin/bash (e.g. NixOS) the test SKIPs gracefully.

BASH_FOR_COMPAT="${BASH_FOR_COMPAT:-/bin/bash}"
if [[ ! -x "$BASH_FOR_COMPAT" ]]; then
  echo "SKIP: $BASH_FOR_COMPAT not found — cannot run lint self-test"
  exit 0
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PLUGIN_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
LINT="$PLUGIN_ROOT/tools/lint_docs.sh"

if [[ ! -x "$LINT" ]]; then
  echo "FAIL: lint_docs.sh not found at $LINT"
  exit 1
fi

# Unique fixture so the assertion regex can pinpoint it amid other warnings.
FIXTURE_NAME="__lint_docs_test_fixture"
SCRATCH="$PLUGIN_ROOT/skills/lean4/references/${FIXTURE_NAME}.md"

# Backup cleanup in case the test aborts mid-stream.
trap 'rm -f "$SCRATCH"' EXIT

PASS=0
FAIL=0

# ---------------------------------------------------------------------------
# Probe 1 — fixture present: Check 8c MUST fire for the planted line.
# ---------------------------------------------------------------------------
cat > "$SCRATCH" <<EOF
# Test fixture for lint_docs.sh Check 8c (#135 self-test)

\`\`\`bash
python3 "\$LEAN4_SCRIPTS/${FIXTURE_NAME}.py" --foo
\`\`\`
EOF

# || true — lint_docs.sh may legitimately exit nonzero from inherited
# warnings unrelated to Check 8c. We assert on output content, not exit.
output1=$("$BASH_FOR_COMPAT" "$LINT" 2>&1 || true)

if echo "$output1" | grep -qE "${FIXTURE_NAME}\.md:.*Python helper uses bare python3"; then
  echo "  PASS: Probe 1 — Check 8c fires on planted fixture"
  ((PASS++)) || true
else
  echo "  FAIL: Probe 1 — Check 8c did not flag the planted fixture"
  echo "         expected: '${FIXTURE_NAME}.md:<line>: Python helper uses bare python3 — ...'"
  echo "         relevant output:"
  echo "$output1" | grep -E "(${FIXTURE_NAME}|Python helper interpreter)" | sed 's/^/           /' || true
  ((FAIL++)) || true
fi

# ---------------------------------------------------------------------------
# Explicit cleanup before Probe 2. Traps fire on EXIT only — not between
# probes — so the fixture removal here must be explicit. The trap stays
# installed as a safety net for the post-Probe-2 path.
# ---------------------------------------------------------------------------
rm -f "$SCRATCH"

# ---------------------------------------------------------------------------
# Probe 2 — fixture absent: Check 8c emits its OK line and no WARN.
# Both conditions together prove Check 8c ran cleanly without depending
# on lint_docs.sh's overall exit code.
# ---------------------------------------------------------------------------
output2=$("$BASH_FOR_COMPAT" "$LINT" 2>&1 || true)

ok_line='✓ Python helper interpreter prefixes checked'
warn_preamble='Python helper uses bare python3'

probe2_ok=1
if ! echo "$output2" | grep -qF "$ok_line"; then
  echo "  FAIL: Probe 2 — expected OK line not found"
  echo "         expected: '$ok_line'"
  probe2_ok=0
fi
if echo "$output2" | grep -qF "$warn_preamble"; then
  echo "  FAIL: Probe 2 — warning preamble unexpectedly present after fixture removal"
  echo "         offending lines:"
  echo "$output2" | grep -F "$warn_preamble" | sed 's/^/           /' || true
  probe2_ok=0
fi
if [[ $probe2_ok -eq 1 ]]; then
  echo "  PASS: Probe 2 — Check 8c clean on post-cleanup tree (OK line present, no WARN)"
  ((PASS++)) || true
else
  ((FAIL++)) || true
fi

# ---------------------------------------------------------------------------
# Probe 3 — Check 8e: compilation-errors.md numbered ### N. headings must be
# unique. Plant two `### 99. Fixture` headings in the real file, run lint,
# assert the new warn fires. Then restore from a mktemp backup and re-run,
# assert the OK line. Backup pattern (not `git checkout`) is deliberate —
# checkout would clobber any uncommitted user edits if this test races with
# in-progress editing. Fixture number 99 is chosen far above any plausible
# real section count so a mid-test glance at the file makes it obvious.
# ---------------------------------------------------------------------------
CE_FILE="$PLUGIN_ROOT/skills/lean4/references/compilation-errors.md"
CE_BACKUP=$(mktemp)
cp "$CE_FILE" "$CE_BACKUP"
# Extend the EXIT trap: restore compilation-errors.md and remove backup, in
# addition to removing the Check 8c scratch fixture (Probe 1 leftover).
trap 'cp "$CE_BACKUP" "$CE_FILE"; rm -f "$CE_BACKUP" "$SCRATCH"' EXIT

printf '\n### 99. Fixture A\n\n### 99. Fixture B\n' >> "$CE_FILE"

output3=$("$BASH_FOR_COMPAT" "$LINT" 2>&1 || true)

if echo "$output3" | grep -qF "compilation-errors.md: duplicate '### 99.' heading"; then
  echo "  PASS: Probe 3 — Check 8e fires on planted duplicate '### 99.' heading"
  ((PASS++)) || true
else
  echo "  FAIL: Probe 3 — Check 8e did not flag the planted duplicate"
  echo "         expected: \"compilation-errors.md: duplicate '### 99.' heading\""
  echo "         relevant output:"
  echo "$output3" | grep -E "compilation-errors|numbered headings" | sed 's/^/           /' || true
  ((FAIL++)) || true
fi

# ---------------------------------------------------------------------------
# Explicit restore before Probe 4. Traps fire on EXIT only — not between
# probes — so the file restoration here must be explicit. The trap stays
# installed as a safety net.
# ---------------------------------------------------------------------------
cp "$CE_BACKUP" "$CE_FILE"

# ---------------------------------------------------------------------------
# Probe 4 — fixture absent: Check 8e emits its OK line and no duplicate WARN.
# ---------------------------------------------------------------------------
output4=$("$BASH_FOR_COMPAT" "$LINT" 2>&1 || true)

ok_line_8e='✓ compilation-errors.md: numbered headings are unique'
warn_preamble_8e="compilation-errors.md: duplicate '###"

probe4_ok=1
if ! echo "$output4" | grep -qF "$ok_line_8e"; then
  echo "  FAIL: Probe 4 — expected OK line not found"
  echo "         expected: '$ok_line_8e'"
  probe4_ok=0
fi
if echo "$output4" | grep -qF "$warn_preamble_8e"; then
  echo "  FAIL: Probe 4 — duplicate-heading warning unexpectedly present after restore"
  echo "         offending lines:"
  echo "$output4" | grep -F "$warn_preamble_8e" | sed 's/^/           /' || true
  probe4_ok=0
fi
if [[ $probe4_ok -eq 1 ]]; then
  echo "  PASS: Probe 4 — Check 8e clean on restored tree (OK line present, no WARN)"
  ((PASS++)) || true
else
  ((FAIL++)) || true
fi

# ---------------------------------------------------------------------------
echo ""
echo "=== test_lint_docs.sh: $PASS passed, $FAIL failed ==="
[[ "$FAIL" -eq 0 ]]

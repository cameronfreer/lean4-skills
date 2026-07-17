#!/usr/bin/env bash
set -euo pipefail

# Regression tests for lib/scripts/preflight_env.sh (#108).
# Exercises --runtime and --bootstrap modes, and guards that diagnose.md
# still carries the three canonical recovery lines byte-for-byte (the
# helper is the single source of that wording).
#
# Runs under $BASH_FOR_COMPAT (default /bin/bash) so it exercises macOS
# Bash 3.2 in CI. SKIPs gracefully if that shell is unavailable.

BASH_FOR_COMPAT="${BASH_FOR_COMPAT:-/bin/bash}"
if [[ ! -x "$BASH_FOR_COMPAT" ]]; then
    echo "SKIP: $BASH_FOR_COMPAT not found — cannot run preflight self-test"
    exit 0
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PLUGIN_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
PREFLIGHT="$PLUGIN_ROOT/lib/scripts/preflight_env.sh"
DIAGNOSE="$PLUGIN_ROOT/commands/diagnose.md"

PASS=0
FAIL=0

# Canonical recovery lines — MUST match preflight_env.sh's emit_recovery
# and diagnose.md's inline fallback exactly.
CANON1="1. Run /lean4:diagnose env for a full diagnosis."
CANON2="2. Restart the Claude Code session (re-runs the SessionStart bootstrap hook)."
CANON3="3. If it persists, check the plugin hook/bootstrap state (hooks.json, bootstrap.sh)."

pass() { echo "  PASS: $1"; (( ++PASS )) || true; }
fail() { echo "  FAIL: $1"; (( ++FAIL )) || true; }

# ---------------------------------------------------------------------------
# --runtime mode
# ---------------------------------------------------------------------------

# Valid session env → exit 0.
out=0
env LEAN4_PLUGIN_ROOT="$PLUGIN_ROOT" \
    LEAN4_SCRIPTS="$PLUGIN_ROOT/lib/scripts" \
    LEAN4_REFS="$PLUGIN_ROOT/skills/lean4/references" \
    PATH="$PLUGIN_ROOT/bin:$PATH" \
    "$BASH_FOR_COMPAT" "$PREFLIGHT" --runtime >/dev/null 2>&1 || out=$?
[[ "$out" -eq 0 ]] && pass "runtime: valid env → exit 0" || fail "runtime: valid env → exit 0 (got $out)"

# Missing LEAN4_* → canonical block + exit 2.
out=0
runtime_out=$(env -u LEAN4_PLUGIN_ROOT -u LEAN4_SCRIPTS -u LEAN4_REFS \
    "$BASH_FOR_COMPAT" "$PREFLIGHT" --runtime 2>&1) || out=$?
if [[ "$out" -eq 2 ]] && grep -qF "$CANON1" <<<"$runtime_out"; then
    pass "runtime: missing env → canonical block + exit 2"
else
    fail "runtime: missing env → canonical block + exit 2 (got exit $out)"
fi

# ---------------------------------------------------------------------------
# --bootstrap mode
# ---------------------------------------------------------------------------

# Valid tree + writable env-file parent (file absent) → exit 0.
tmp=$(mktemp -d)
out=0
CLAUDE_ENV_FILE="$tmp/env" "$BASH_FOR_COMPAT" "$PREFLIGHT" --bootstrap "$PLUGIN_ROOT" >/dev/null 2>&1 || out=$?
[[ "$out" -eq 0 ]] && pass "bootstrap: valid tree + writable parent (file absent) → exit 0" \
    || fail "bootstrap: valid tree → exit 0 (got $out)"

# CLAUDE_ENV_FILE unset → exit 2 naming it.
out=0
bs_out=$(env -u CLAUDE_ENV_FILE "$BASH_FOR_COMPAT" "$PREFLIGHT" --bootstrap "$PLUGIN_ROOT" 2>&1) || out=$?
if [[ "$out" -eq 2 ]] && grep -qF "CLAUDE_ENV_FILE is not set" <<<"$bs_out"; then
    pass "bootstrap: CLAUDE_ENV_FILE unset → exit 2 naming it"
else
    fail "bootstrap: CLAUDE_ENV_FILE unset → exit 2 (got $out)"
fi

# Empty plugin root → exit 2 naming CLAUDE_PLUGIN_ROOT.
out=0
bs_out=$(CLAUDE_ENV_FILE="$tmp/env" "$BASH_FOR_COMPAT" "$PREFLIGHT" --bootstrap "" 2>&1) || out=$?
if [[ "$out" -eq 2 ]] && grep -qF "CLAUDE_PLUGIN_ROOT is not set" <<<"$bs_out"; then
    pass "bootstrap: empty root → exit 2 naming CLAUDE_PLUGIN_ROOT"
else
    fail "bootstrap: empty root → exit 2 (got $out)"
fi

# Tree missing bin/ → exit 2.
baddir=$(mktemp -d)
mkdir -p "$baddir/lib/scripts" "$baddir/skills/lean4/references"
out=0
bs_out=$(CLAUDE_ENV_FILE="$tmp/env" "$BASH_FOR_COMPAT" "$PREFLIGHT" --bootstrap "$baddir" 2>&1) || out=$?
if [[ "$out" -eq 2 ]] && grep -qF "bin does not exist" <<<"$bs_out"; then
    pass "bootstrap: tree missing bin/ → exit 2"
else
    fail "bootstrap: tree missing bin/ → exit 2 (got $out)"
fi

rm -rf "$tmp" "$baddir"

# ---------------------------------------------------------------------------
# Wording agreement: diagnose.md must contain the three canonical lines.
# Substring (grep -F) not whole-block diff — diagnose wraps them in a code
# block; only the exact recovery lines need to match.
# ---------------------------------------------------------------------------
for canon in "$CANON1" "$CANON2" "$CANON3"; do
    if grep -qF "$canon" "$DIAGNOSE"; then
        pass "diagnose.md contains canonical line: ${canon%% *}…"
    else
        fail "diagnose.md MISSING canonical line: $canon"
    fi
done

# Same three lines are what preflight_env.sh actually emits.
emitted=$(env -u LEAN4_PLUGIN_ROOT -u LEAN4_SCRIPTS -u LEAN4_REFS \
    "$BASH_FOR_COMPAT" "$PREFLIGHT" --runtime 2>&1 || true)
for canon in "$CANON1" "$CANON2" "$CANON3"; do
    grep -qF "$canon" <<<"$emitted" || fail "preflight did not emit canonical line: $canon"
done
pass "preflight_env.sh emits all three canonical lines"

# ---------------------------------------------------------------------------
echo ""
echo "=== test_preflight_env.sh: $PASS passed, $FAIL failed ==="
[[ "$FAIL" -eq 0 ]]

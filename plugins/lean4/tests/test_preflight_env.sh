#!/usr/bin/env bash
set -euo pipefail

# Regression tests for lib/scripts/preflight_env.sh (#108).
# Exercises --runtime, --bootstrap, and --codex modes, and guards that
# doctor.md still carries both canonical recovery blocks.
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
DOCTOR="$PLUGIN_ROOT/commands/doctor.md"

PASS=0
FAIL=0

# Canonical recovery lines — MUST match preflight_env.sh's emit_recovery
# and doctor.md's inline fallback exactly.
CANON1="1. Run /lean4:doctor env for a full diagnosis."
CANON2="2. Restart the Claude Code session (re-runs the SessionStart bootstrap hook)."
CANON3="3. If it persists, check the plugin hook/bootstrap state (hooks.json, bootstrap.sh)."
CODEX_CANON1="1. Review and trust the lean4 plugin hooks in /hooks."
CODEX_CANON2="2. Start a new Codex task (re-runs the SessionStart hook)."
CODEX_CANON3="3. Run the absolute <plugin-root>/bin/lean4-skills-preflight --codex command; if it is missing, reinstall the plugin."

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

# ---------------------------------------------------------------------------
# --codex mode: absolute installed-tree checks, no env/PATH dependency.
# ---------------------------------------------------------------------------

out=0
env -u LEAN4_PLUGIN_ROOT -u LEAN4_SCRIPTS -u LEAN4_REFS \
    PATH="/usr/bin:/bin" \
    "$BASH_FOR_COMPAT" "$PREFLIGHT" --codex "$PLUGIN_ROOT" >/dev/null 2>&1 || out=$?
[[ "$out" -eq 0 ]] && pass "codex: valid absolute runtime with no LEAN4_* or plugin PATH → exit 0" \
    || fail "codex: valid absolute runtime → exit 0 (got $out)"

out=0
env -u LEAN4_PLUGIN_ROOT -u LEAN4_SCRIPTS -u LEAN4_REFS \
    PATH="/usr/bin:/bin" \
    "$PLUGIN_ROOT/bin/lean4-skills-preflight" --codex >/dev/null 2>&1 || out=$?
[[ "$out" -eq 0 ]] && pass "codex: self-locating absolute preflight wrapper → exit 0" \
    || fail "codex: absolute preflight wrapper → exit 0 (got $out)"

out=0
codex_out=$(env -u PLUGIN_ROOT -u CLAUDE_PLUGIN_ROOT \
    "$BASH_FOR_COMPAT" "$PREFLIGHT" --codex "" 2>&1) || out=$?
if [[ "$out" -eq 2 ]] && grep -qF "PLUGIN_ROOT is not set" <<<"$codex_out"; then
    pass "codex: empty root → canonical recovery + exit 2"
else
    fail "codex: empty root → canonical recovery + exit 2 (got $out)"
fi

badcodex=$(mktemp -d)
mkdir -p "$badcodex/.codex-plugin" "$badcodex/hooks" \
    "$badcodex/lib/scripts" "$badcodex/skills/lean4/references" "$badcodex/bin"
touch "$badcodex/.codex-plugin/plugin.json" "$badcodex/hooks/codex-hooks.json" \
    "$badcodex/skills/lean4/SKILL.md"
out=0
codex_out=$("$BASH_FOR_COMPAT" "$PREFLIGHT" --codex "$badcodex" 2>&1) || out=$?
if [[ "$out" -eq 2 ]] && grep -qF "lean4-skills-preflight is missing or not executable" <<<"$codex_out"; then
    pass "codex: missing absolute wrapper → canonical recovery + exit 2"
else
    fail "codex: missing wrapper → canonical recovery + exit 2 (got $out)"
fi

badcodex_scripts=$(mktemp -d)
mkdir -p "$badcodex_scripts/.codex-plugin" "$badcodex_scripts/hooks" \
    "$badcodex_scripts/skills/lean4/references" "$badcodex_scripts/bin"
touch "$badcodex_scripts/.codex-plugin/plugin.json" \
    "$badcodex_scripts/hooks/codex-hooks.json" \
    "$badcodex_scripts/skills/lean4/SKILL.md"
out=0
codex_out=$("$BASH_FOR_COMPAT" "$PREFLIGHT" --codex "$badcodex_scripts" 2>&1) || out=$?
if [[ "$out" -eq 2 ]] && grep -qF "lib/scripts does not exist" <<<"$codex_out"; then
    pass "codex: missing scripts directory → canonical recovery + exit 2"
else
    fail "codex: missing scripts directory → canonical recovery + exit 2 (got $out)"
fi

rm -rf "$tmp" "$baddir" "$badcodex" "$badcodex_scripts"

# ---------------------------------------------------------------------------
# Wording agreement: doctor.md must contain the three canonical lines.
# Substring (grep -F) not whole-block diff — doctor wraps them in a code
# block; only the exact recovery lines need to match.
# ---------------------------------------------------------------------------
for canon in "$CANON1" "$CANON2" "$CANON3"; do
    if grep -qF "$canon" "$DOCTOR"; then
        pass "doctor.md contains canonical line: ${canon%% *}…"
    else
        fail "doctor.md MISSING canonical line: $canon"
    fi
done

# Same three lines are what preflight_env.sh actually emits.
emitted=$(env -u LEAN4_PLUGIN_ROOT -u LEAN4_SCRIPTS -u LEAN4_REFS \
    "$BASH_FOR_COMPAT" "$PREFLIGHT" --runtime 2>&1 || true)
for canon in "$CANON1" "$CANON2" "$CANON3"; do
    grep -qF "$canon" <<<"$emitted" || fail "preflight did not emit canonical line: $canon"
done
pass "preflight_env.sh emits all three canonical lines"

# Codex recovery wording agreement and emitted behavior.
for canon in "$CODEX_CANON1" "$CODEX_CANON2" "$CODEX_CANON3"; do
    if grep -qF "$canon" "$DOCTOR"; then
        pass "doctor.md contains Codex canonical line: ${canon%% *}…"
    else
        fail "doctor.md MISSING Codex canonical line: $canon"
    fi
done

emitted=$(env -u PLUGIN_ROOT -u CLAUDE_PLUGIN_ROOT \
    "$BASH_FOR_COMPAT" "$PREFLIGHT" --codex "" 2>&1 || true)
for canon in "$CODEX_CANON1" "$CODEX_CANON2" "$CODEX_CANON3"; do
    grep -qF "$canon" <<<"$emitted" || fail "preflight did not emit Codex canonical line: $canon"
done
pass "preflight_env.sh emits all three Codex canonical lines"

# ---------------------------------------------------------------------------
echo ""
echo "=== test_preflight_env.sh: $PASS passed, $FAIL failed ==="
[[ "$FAIL" -eq 0 ]]

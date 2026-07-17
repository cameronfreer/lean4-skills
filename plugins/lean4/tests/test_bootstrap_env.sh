#!/usr/bin/env bash
set -euo pipefail

# Regression tests for hooks/bootstrap.sh (#108): honest reporting, PATH
# persistence, and PATH idempotency. Drives the hook with a fabricated
# CLAUDE_PLUGIN_ROOT (the real tree) and a CLAUDE_ENV_FILE in a tempdir.
#
# Runs under $BASH_FOR_COMPAT (default /bin/bash) so it exercises macOS
# Bash 3.2 in CI. SKIPs gracefully if that shell is unavailable.

BASH_FOR_COMPAT="${BASH_FOR_COMPAT:-/bin/bash}"
if [[ ! -x "$BASH_FOR_COMPAT" ]]; then
    echo "SKIP: $BASH_FOR_COMPAT not found — cannot run bootstrap self-test"
    exit 0
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PLUGIN_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
BOOTSTRAP="$PLUGIN_ROOT/hooks/bootstrap.sh"

PASS=0
FAIL=0
pass() { echo "  PASS: $1"; (( ++PASS )) || true; }
fail() { echo "  FAIL: $1"; (( ++FAIL )) || true; }

SCRATCH=$(mktemp -d)
trap 'rm -rf "$SCRATCH"' EXIT

# run_bootstrap: env-scoped invocation. Sets globals BS_OUT, BS_EXIT.
#   $1 = CLAUDE_PLUGIN_ROOT value ("" to leave unset)
#   $2 = CLAUDE_ENV_FILE value    ("" to leave unset)
run_bootstrap() {
    local root="$1" envfile="$2"
    # env(1) requires all -u options BEFORE any NAME=VALUE assignment —
    # once it sees an assignment the rest is the command. So collect unset
    # flags first, then assignments.
    local -a unset_flags=() assigns=()
    if [[ -n "$root" ]]; then assigns+=("CLAUDE_PLUGIN_ROOT=$root"); else unset_flags+=("-u" "CLAUDE_PLUGIN_ROOT"); fi
    if [[ -n "$envfile" ]]; then assigns+=("CLAUDE_ENV_FILE=$envfile"); else unset_flags+=("-u" "CLAUDE_ENV_FILE"); fi
    BS_EXIT=0
    BS_OUT=$(env "${unset_flags[@]+"${unset_flags[@]}"}" "${assigns[@]+"${assigns[@]}"}" \
        "$BASH_FOR_COMPAT" "$BOOTSTRAP" 2>&1) || BS_EXIT=$?
}

# ---------------------------------------------------------------------------
# Happy path: writable env-file parent, file absent (bootstrap creates it).
# ---------------------------------------------------------------------------
ef="$SCRATCH/happy_env"
run_bootstrap "$PLUGIN_ROOT" "$ef"
happy_ok=1
[[ "$BS_EXIT" -eq 0 ]] || { happy_ok=0; }
grep -qF "Lean4 v4 ready" <<<"$BS_OUT" || happy_ok=0
grep -q '^export LEAN4_PLUGIN_ROOT=' "$ef" 2>/dev/null || happy_ok=0
grep -q '^export LEAN4_SCRIPTS=' "$ef" 2>/dev/null || happy_ok=0
grep -q '^export LEAN4_REFS=' "$ef" 2>/dev/null || happy_ok=0
grep -q '^export PATH=' "$ef" 2>/dev/null || happy_ok=0
if [[ $happy_ok -eq 1 ]]; then
    pass "happy path: 'ready' + all LEAN4_* and PATH persisted, exit 0"
else
    fail "happy path (exit=$BS_EXIT); env file:"; sed 's/^/      /' "$ef" 2>/dev/null || true
fi

# The persisted PATH line keeps :$PATH literal (each shell prepends bin/).
if grep -qF "export PATH=\"$PLUGIN_ROOT/bin:\$PATH\"" "$ef" 2>/dev/null; then
    pass "PATH line keeps literal :\$PATH (bin/ prepended per-shell)"
else
    fail "PATH line not in expected literal form"
fi

# ---------------------------------------------------------------------------
# PATH idempotency: a second run must not stack a duplicate PATH line.
# ---------------------------------------------------------------------------
run_bootstrap "$PLUGIN_ROOT" "$ef"
n_path=$(grep -c '^export PATH=' "$ef" 2>/dev/null || echo 0)
if [[ "$n_path" -eq 1 ]]; then
    pass "PATH idempotency: exactly one export PATH= line after two runs"
else
    fail "PATH idempotency: expected 1 export PATH= line, got $n_path"
fi

# ---------------------------------------------------------------------------
# Degraded: CLAUDE_ENV_FILE unset → no 'ready', canonical block, exit 0.
# ---------------------------------------------------------------------------
run_bootstrap "$PLUGIN_ROOT" ""
if [[ "$BS_EXIT" -eq 0 ]] \
   && ! grep -qF "Lean4 v4 ready" <<<"$BS_OUT" \
   && grep -qF "Run /lean4:diagnose env for a full diagnosis." <<<"$BS_OUT"; then
    pass "degraded: CLAUDE_ENV_FILE unset → no 'ready', canonical block, exit 0"
else
    fail "degraded CLAUDE_ENV_FILE unset (exit=$BS_EXIT)"
fi

# ---------------------------------------------------------------------------
# Degraded: CLAUDE_PLUGIN_ROOT unset → no crash, canonical naming it, exit 0.
# (The removed `:?` hard-require used to abort nonzero here.)
# ---------------------------------------------------------------------------
run_bootstrap "" "$SCRATCH/root_unset_env"
if [[ "$BS_EXIT" -eq 0 ]] \
   && ! grep -qF "Lean4 v4 ready" <<<"$BS_OUT" \
   && grep -qF "CLAUDE_PLUGIN_ROOT is not set" <<<"$BS_OUT"; then
    pass "degraded: CLAUDE_PLUGIN_ROOT unset → canonical block naming it, exit 0"
else
    fail "degraded CLAUDE_PLUGIN_ROOT unset (exit=$BS_EXIT)"
fi
# ...and nothing was persisted off a guessed root.
[[ ! -e "$SCRATCH/root_unset_env" ]] && pass "root-unset: nothing persisted" \
    || fail "root-unset: env file unexpectedly written"

# ---------------------------------------------------------------------------
# Degraded: CLAUDE_ENV_FILE parent dir unwritable → no 'ready', warn, exit 0.
# (Skip if running as root, where write bits are ignored.)
# ---------------------------------------------------------------------------
if [[ "$(id -u)" -ne 0 ]]; then
    roDir="$SCRATCH/ro"; mkdir -p "$roDir"; chmod 555 "$roDir"
    run_bootstrap "$PLUGIN_ROOT" "$roDir/env"
    if [[ "$BS_EXIT" -eq 0 ]] && ! grep -qF "Lean4 v4 ready" <<<"$BS_OUT"; then
        pass "degraded: unwritable env-file parent → no 'ready', exit 0"
    else
        fail "degraded unwritable parent (exit=$BS_EXIT)"
    fi
    chmod 755 "$roDir"
else
    echo "  SKIP: unwritable-parent case (running as root)"
fi

# ---------------------------------------------------------------------------
# PATH coexistence: a foreign `export PATH=` line (another plugin's) and an
# unrelated var in the same env file must SURVIVE a bootstrap — persist_path
# dedups only our exact own-line, not every PATH line.
# ---------------------------------------------------------------------------
coex="$SCRATCH/coex_env"
printf 'export PATH="/opt/otherplugin/bin:$PATH"\nexport OTHER_VAR="keep me"\n' > "$coex"
run_bootstrap "$PLUGIN_ROOT" "$coex"
coex_ok=1
grep -qF 'export PATH="/opt/otherplugin/bin:$PATH"' "$coex" || coex_ok=0   # foreign PATH survived
grep -qF 'export OTHER_VAR="keep me"' "$coex" || coex_ok=0                 # unrelated var survived
grep -qF "$PLUGIN_ROOT/bin" "$coex" || coex_ok=0                           # our PATH added
run_bootstrap "$PLUGIN_ROOT" "$coex"                                       # second run
[[ "$(grep -c '^export PATH=' "$coex")" -eq 2 ]] || coex_ok=0             # still exactly 2 PATH lines
if [[ $coex_ok -eq 1 ]]; then
    pass "PATH coexistence: foreign PATH + unrelated var survive; ours deduped"
else
    fail "PATH coexistence"; sed 's/^/      /' "$coex"
fi

# ---------------------------------------------------------------------------
# Missing preflight helper → canonical block (not a raw "No such file"), exit 0.
# Point CLAUDE_PLUGIN_ROOT at a tree with an empty lib/scripts/ (no helper).
# ---------------------------------------------------------------------------
nohelper="$SCRATCH/nohelper"
mkdir -p "$nohelper/lib/scripts" "$nohelper/skills/lean4/references" "$nohelper/bin"
run_bootstrap "$nohelper" "$SCRATCH/nohelper_env"
if [[ "$BS_EXIT" -eq 0 ]] \
   && ! grep -qF "Lean4 v4 ready" <<<"$BS_OUT" \
   && grep -qF "Run /lean4:diagnose env for a full diagnosis." <<<"$BS_OUT"; then
    pass "missing preflight helper → canonical block, exit 0"
else
    fail "missing preflight helper (exit=$BS_EXIT): $BS_OUT"
fi

# ---------------------------------------------------------------------------
# Degraded: CLAUDE_ENV_FILE writable but NON-PERSISTENT (symlink to
# /dev/null, or an existing directory). Persistence there silently no-ops;
# the regular-file check in preflight --bootstrap must catch it at input
# validation so the bootstrap is loud, not silently degraded. exit 0.
# ---------------------------------------------------------------------------
ln -s /dev/null "$SCRATCH/devnull_link"
run_bootstrap "$PLUGIN_ROOT" "$SCRATCH/devnull_link"
if [[ "$BS_EXIT" -eq 0 ]] \
   && ! grep -qF "Lean4 v4 ready" <<<"$BS_OUT" \
   && grep -qF "Run /lean4:diagnose env for a full diagnosis." <<<"$BS_OUT"; then
    pass "degraded: CLAUDE_ENV_FILE → /dev/null symlink → canonical warning, exit 0"
else
    fail "degraded CLAUDE_ENV_FILE → /dev/null symlink (exit=$BS_EXIT): $BS_OUT"
fi

mkdir -p "$SCRATCH/envdir"
run_bootstrap "$PLUGIN_ROOT" "$SCRATCH/envdir"
if [[ "$BS_EXIT" -eq 0 ]] \
   && ! grep -qF "Lean4 v4 ready" <<<"$BS_OUT" \
   && grep -qF "not a regular file" <<<"$BS_OUT"; then
    pass "degraded: CLAUDE_ENV_FILE → directory → canonical warning, exit 0"
else
    fail "degraded CLAUDE_ENV_FILE → directory (exit=$BS_EXIT): $BS_OUT"
fi

# ---------------------------------------------------------------------------
echo ""
echo "=== test_bootstrap_env.sh: $PASS passed, $FAIL failed ==="
[[ "$FAIL" -eq 0 ]]

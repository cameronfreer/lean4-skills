#!/usr/bin/env bash
set -euo pipefail

# Regression tests for hooks/bootstrap.sh (#108, #157): honest Claude
# persistence plus truthful native-Codex absolute-path context.
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

# run_codex_bootstrap: native Codex invocation. Sets BS_OUT and BS_EXIT.
#   $1 = PLUGIN_ROOT value ("" to leave unset)
#   $2 = CLAUDE_PLUGIN_ROOT compatibility value ("" to leave unset)
#   $3 = CLAUDE_ENV_FILE sentinel (must never be written by Codex mode)
run_codex_bootstrap() {
    local root="$1" compat_root="$2" envfile="$3"
    local -a unset_flags=(
        "-u" "LEAN4_PLUGIN_ROOT" "-u" "LEAN4_SCRIPTS" "-u" "LEAN4_REFS"
        "-u" "PLUGIN_ROOT" "-u" "CLAUDE_PLUGIN_ROOT" "-u" "CLAUDE_ENV_FILE"
    )
    local -a assigns=()
    [[ -n "$root" ]] && assigns+=("PLUGIN_ROOT=$root")
    [[ -n "$compat_root" ]] && assigns+=("CLAUDE_PLUGIN_ROOT=$compat_root")
    [[ -n "$envfile" ]] && assigns+=("CLAUDE_ENV_FILE=$envfile")
    BS_EXIT=0
    BS_OUT=$(env "${unset_flags[@]}" "${assigns[@]+"${assigns[@]}"}" \
        "$BASH_FOR_COMPAT" "$BOOTSTRAP" --host codex 2>&1) || BS_EXIT=$?
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
   && grep -qF "Run /lean4:doctor env for a full diagnosis." <<<"$BS_OUT"; then
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
   && grep -qF "Run /lean4:doctor env for a full diagnosis." <<<"$BS_OUT"; then
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
   && grep -qF "Run /lean4:doctor env for a full diagnosis." <<<"$BS_OUT"; then
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
# Native Codex: absolute context, no persistent env/PATH claims or writes.
# ---------------------------------------------------------------------------
codex_env_sentinel="$SCRATCH/codex_must_not_write_env"
run_codex_bootstrap "$PLUGIN_ROOT" "" "$codex_env_sentinel"
codex_ok=1
[[ "$BS_EXIT" -eq 0 ]] || codex_ok=0
grep -qF "lean4_plugin_runtime=codex" <<<"$BS_OUT" || codex_ok=0
grep -qF "plugin_root=$PLUGIN_ROOT" <<<"$BS_OUT" || codex_ok=0
grep -qF "bin_dir=$PLUGIN_ROOT/bin" <<<"$BS_OUT" || codex_ok=0
grep -qF "preflight=$PLUGIN_ROOT/bin/lean4-skills-preflight" <<<"$BS_OUT" || codex_ok=0
grep -qF "wrapper_invocation=$PLUGIN_ROOT/bin/<wrapper-name>" <<<"$BS_OUT" || codex_ok=0
grep -qF "shell_env_persistent=false" <<<"$BS_OUT" || codex_ok=0
! grep -qF "Lean4 v4 ready" <<<"$BS_OUT" || codex_ok=0
[[ ! -e "$codex_env_sentinel" ]] || codex_ok=0
if [[ $codex_ok -eq 1 ]]; then
    pass "Codex: absolute runtime context, no env-file write or false PATH readiness"
else
    fail "Codex absolute runtime context (exit=$BS_EXIT): $BS_OUT"
fi

# The same trusted root produces byte-identical context on every lifecycle
# event; source matching belongs to codex-hooks.json and is tested separately.
codex_first="$BS_OUT"
run_codex_bootstrap "$PLUGIN_ROOT" "" "$codex_env_sentinel"
if [[ "$BS_OUT" == "$codex_first" ]]; then
    pass "Codex: SessionStart context is idempotent"
else
    fail "Codex: SessionStart context changed across identical runs"
fi

# Native PLUGIN_ROOT wins over the Claude compatibility variable.
run_codex_bootstrap "$PLUGIN_ROOT" "$SCRATCH/not-the-plugin" ""
if [[ "$BS_EXIT" -eq 0 ]] && grep -qF "plugin_root=$PLUGIN_ROOT" <<<"$BS_OUT"; then
    pass "Codex: PLUGIN_ROOT takes precedence over CLAUDE_PLUGIN_ROOT"
else
    fail "Codex root precedence (exit=$BS_EXIT): $BS_OUT"
fi

# A compatibility variable alone must not mask a missing native Codex root.
run_codex_bootstrap "" "$PLUGIN_ROOT" ""
if [[ "$BS_EXIT" -eq 0 ]] \
   && grep -qF "PLUGIN_ROOT is not set" <<<"$BS_OUT" \
   && ! grep -qF "lean4_plugin_runtime=codex" <<<"$BS_OUT"; then
    pass "Codex: CLAUDE_PLUGIN_ROOT does not replace native PLUGIN_ROOT"
else
    fail "Codex compatibility-only root handling (exit=$BS_EXIT): $BS_OUT"
fi

# Missing host root and corrupt roots degrade loudly without injecting a
# misleading runtime context or disrupting SessionStart.
run_codex_bootstrap "" "" ""
if [[ "$BS_EXIT" -eq 0 ]] \
   && grep -qF "PLUGIN_ROOT is not set" <<<"$BS_OUT" \
   && ! grep -qF "lean4_plugin_runtime=codex" <<<"$BS_OUT"; then
    pass "Codex: missing root emits canonical recovery without context"
else
    fail "Codex missing-root recovery (exit=$BS_EXIT): $BS_OUT"
fi

run_codex_bootstrap "$nohelper" "" ""
if [[ "$BS_EXIT" -eq 0 ]] \
   && grep -qF "preflight helper not found" <<<"$BS_OUT" \
   && ! grep -qF "lean4_plugin_runtime=codex" <<<"$BS_OUT"; then
    pass "Codex: corrupt plugin tree emits recovery without context"
else
    fail "Codex corrupt-root recovery (exit=$BS_EXIT): $BS_OUT"
fi

# ---------------------------------------------------------------------------
echo ""
echo "=== test_bootstrap_env.sh: $PASS passed, $FAIL failed ==="
[[ "$FAIL" -eq 0 ]]

#!/usr/bin/env bash
set -euo pipefail

# Resolve the plugin root. CLAUDE_PLUGIN_ROOT is set by Claude Code at hook
# time; if it's missing the hook was invoked abnormally. We do NOT hard-fail
# on that (a `:?` abort would bypass the honest degraded-warning path below);
# instead we self-locate a fallback root from BASH_SOURCE purely so we can
# still emit the canonical recovery message, and treat missing
# CLAUDE_PLUGIN_ROOT as a degraded state (no persistence, no "ready").
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
FALLBACK_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
PLUGIN_ROOT="${CLAUDE_PLUGIN_ROOT:-}"
PREFLIGHT="${PLUGIN_ROOT:-$FALLBACK_ROOT}/lib/scripts/preflight_env.sh"

ENV_OUT="${CLAUDE_ENV_FILE:-}"

# Persist env var: update if exists with different value, add if missing.
# Safe for singleton VAR=VALUE exports (LEAN4_*), where removing every
# `^export VAR=` line before re-adding is exactly the intended dedup.
persist_env() {
  local kv="$1"
  local var_name="${kv%%=*}"  # extract VAR_NAME from "export VAR_NAME=..."
  var_name="${var_name#export }"  # remove "export " prefix
  if [[ -n "${ENV_OUT}" ]]; then
    # Remove any existing line for this variable, then add the new one
    if [[ -f "${ENV_OUT}" ]]; then
      grep -v "^export ${var_name}=" "${ENV_OUT}" > "${ENV_OUT}.tmp" 2>/dev/null || true
      mv "${ENV_OUT}.tmp" "${ENV_OUT}"
    fi
    printf '%s\n' "$kv" >> "${ENV_OUT}"
  fi
}

# Persist PATH specifically. Unlike persist_env, PATH is NOT a singleton —
# other hooks/plugins may write their own `export PATH=...` lines into the
# same CLAUDE_ENV_FILE. Dedup on the EXACT own-line only (grep -vF), so a
# re-bootstrap replaces just our entry and leaves every other plugin's PATH
# export intact.
persist_path() {
  local own_line="$1"
  if [[ -n "${ENV_OUT}" ]]; then
    if [[ -f "${ENV_OUT}" ]]; then
      grep -vxF "$own_line" "${ENV_OUT}" > "${ENV_OUT}.tmp" 2>/dev/null || true
      mv "${ENV_OUT}.tmp" "${ENV_OUT}"
    fi
    printf '%s\n' "$own_line" >> "${ENV_OUT}"
  fi
}

# Emit the canonical recovery block and exit 0. We warn (not hard-fail)
# because a nonzero SessionStart exit risks disrupting session start and the
# self-locating lean4-skills-* wrappers may still function; a loud,
# actionable stderr warning is the right severity.
#
# ALWAYS emits the caller's concrete $problem inline — it does NOT re-run
# the preflight. A re-run could pass (e.g. a post-write validation failure
# where the INPUTS still look fine, such as CLAUDE_ENV_FILE being a symlink
# to /dev/null) and emit nothing, silently swallowing the warning. The
# canonical wording here is kept byte-identical to preflight_env.sh's
# emit_recovery (test_preflight_env.sh asserts the shared lines).
warn_degraded_and_exit() {
  local problem="$1"
  {
    echo "Lean4 bootstrap environment is not fully set up in this Claude Code session."
    echo "  Problem: ${problem}"
    echo "  Recovery:"
    echo "    1. Run /lean4:doctor env for a full diagnosis."
    echo "    2. Restart the Claude Code session (re-runs the SessionStart bootstrap hook)."
    echo "    3. If it persists, check the plugin hook/bootstrap state (hooks.json, bootstrap.sh)."
  } >&2
  exit 0
}

# Missing CLAUDE_PLUGIN_ROOT: degraded — warn via the canonical block and
# exit 0 without persisting off a guessed root.
if [[ -z "$PLUGIN_ROOT" ]]; then
  warn_degraded_and_exit "CLAUDE_PLUGIN_ROOT is not set (bootstrap hook invoked without it)"
fi

# Guard: if the preflight helper itself is missing, don't let a raw
# "No such file" error stand in for the diagnosis — emit the canonical
# block (warn_degraded_and_exit falls back to an inline copy).
if [[ ! -f "$PREFLIGHT" ]]; then
  warn_degraded_and_exit "preflight helper not found at $PREFLIGHT"
fi

# Step 1: validate INPUTS (tree layout + CLAUDE_ENV_FILE usability) before
# persisting anything. If they don't hold, nothing gets written — warn.
if ! bash "$PREFLIGHT" --bootstrap "$PLUGIN_ROOT"; then
  exit 0  # preflight already emitted the canonical block on stderr
fi

# Step 2: persist LEAN4_* and PATH. The PATH line keeps `:$PATH` literal
# (escaped) so each fresh shell prepends bin/ to its own PATH. PATH goes
# through persist_path (exact-own-line dedup) so re-bootstraps don't stack
# duplicates AND other plugins' PATH exports in the same env file survive.
# This is what makes the lean4-skills-* wrappers resolvable in later tool
# calls (and makes INSTALLATION.md's "bootstrap adds bin/ to PATH" true).
PYTHON_BIN="$(command -v python3 || command -v python || true)"

persist_env "export LEAN4_PLUGIN_ROOT=\"${PLUGIN_ROOT}\""
persist_env "export LEAN4_SCRIPTS=\"${PLUGIN_ROOT}/lib/scripts\""
persist_env "export LEAN4_REFS=\"${PLUGIN_ROOT}/skills/lean4/references\""
persist_path "export PATH=\"${PLUGIN_ROOT}/bin:\$PATH\""
[[ -n "${PYTHON_BIN}" ]] && persist_env "export LEAN4_PYTHON_BIN=\"${PYTHON_BIN}\""

# Step 3: re-validate that persistence actually happened — "ready" must mean
# the environment was written, not merely that inputs looked okay. Confirm
# the env file now carries the expected exports.
persisted_ok=true
for expected in \
  "export LEAN4_PLUGIN_ROOT=" \
  "export LEAN4_SCRIPTS=" \
  "export LEAN4_REFS=" \
  "export PATH="; do
  if ! grep -q "^${expected}" "${ENV_OUT}" 2>/dev/null; then
    persisted_ok=false
    break
  fi
done

if [[ "$persisted_ok" != true ]]; then
  warn_degraded_and_exit "env persistence to CLAUDE_ENV_FILE did not take effect"
fi

echo "Lean4 v4 ready: PLUGIN_ROOT=${PLUGIN_ROOT}"
exit 0

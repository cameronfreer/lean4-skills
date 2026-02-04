#!/bin/bash
set -euo pipefail
: "${CLAUDE_PLUGIN_ROOT:?missing CLAUDE_PLUGIN_ROOT}"
ENV_OUT="${CLAUDE_ENV_FILE:-}"

# Idempotent persist: only add if not already present
persist_if_missing() {
  local kv="$1"
  if [[ -n "${ENV_OUT}" ]]; then
    grep -qxF "$kv" "${ENV_OUT}" 2>/dev/null || printf '%s\n' "$kv" >> "${ENV_OUT}"
  fi
}

PYTHON_BIN="$(command -v python3 || command -v python || true)"

persist_if_missing "export LEAN4_PLUGIN_ROOT=\"${CLAUDE_PLUGIN_ROOT}\""
persist_if_missing "export LEAN4_SCRIPTS=\"${CLAUDE_PLUGIN_ROOT}/lib/scripts\""
persist_if_missing "export LEAN4_REFS=\"${CLAUDE_PLUGIN_ROOT}/skills/lean4/references\""
[[ -n "${PYTHON_BIN}" ]] && persist_if_missing "export LEAN4_PYTHON_BIN=\"${PYTHON_BIN}\""

echo "Lean4 v4 ready: PLUGIN_ROOT=${CLAUDE_PLUGIN_ROOT}"
exit 0

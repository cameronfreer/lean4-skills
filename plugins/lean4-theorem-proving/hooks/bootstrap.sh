#!/bin/bash
# Bootstrap env for the session so commands can reference plugin scripts reliably.

set -euo pipefail

# --- Sanity: hooks get this; commands do not. Fail fast if missing.
: "${CLAUDE_PLUGIN_ROOT:?missing CLAUDE_PLUGIN_ROOT in hook context}"

# Optional: where Claude tells us to persist env vars for the whole session.
ENV_OUT="${CLAUDE_ENV_FILE:-}"

# Resolve python (prefer python3, fall back to python).
PYTHON_BIN="$(command -v python3 || true)"
if [[ -z "${PYTHON_BIN}" ]]; then
  PYTHON_BIN="$(command -v python || true)"
fi
if [[ -z "${PYTHON_BIN}" ]]; then
  echo "WARN: No python interpreter found in PATH; commands that need Python will fail." >&2
fi

# Candidate locations for the analyzer (support both layouts):
#   (A) plugin-level:   plugins/lean4-theorem-proving/scripts/sorry_analyzer.py
#   (B) skill-scoped:   plugins/lean4-theorem-proving/skills/lean4-theorem-proving/scripts/sorry_analyzer.py
CANDIDATES=(
  "${CLAUDE_PLUGIN_ROOT}/scripts/sorry_analyzer.py"
  "${CLAUDE_PLUGIN_ROOT}/skills/lean4-theorem-proving/scripts/sorry_analyzer.py"
)

ANALYZER_PATH=""
for f in "${CANDIDATES[@]}"; do
  if [[ -f "$f" ]]; then
    ANALYZER_PATH="$f"
    break
  fi
done

# Tools dir = directory containing the analyzer if we found it; else default to plugin-level scripts/
TOOLS_DIR=""
if [[ -n "${ANALYZER_PATH}" ]]; then
  TOOLS_DIR="$(cd "$(dirname "$ANALYZER_PATH")" && pwd)"
else
  if [[ -d "${CLAUDE_PLUGIN_ROOT}/scripts" ]]; then
    TOOLS_DIR="$(cd "${CLAUDE_PLUGIN_ROOT}/scripts" && pwd)"
  fi
fi

# Make analyzer executable if present.
if [[ -n "${ANALYZER_PATH}" && -f "${ANALYZER_PATH}" ]]; then
  chmod +x "${ANALYZER_PATH}" || true
fi

# Copy scripts to workspace to avoid parameter substitution in commands.
# This makes commands immune to Claude Code's ${...} security filter.
WORKSPACE_TOOLS_DIR=".claude/tools/lean4"
mkdir -p "${WORKSPACE_TOOLS_DIR}"

# Stage sorry_analyzer (already found above)
if [[ -n "${ANALYZER_PATH}" && -f "${ANALYZER_PATH}" ]]; then
  cp -f "${ANALYZER_PATH}" "${WORKSPACE_TOOLS_DIR}/sorry_analyzer.py"
  chmod +x "${WORKSPACE_TOOLS_DIR}/sorry_analyzer.py" || true
  echo "Staged sorry_analyzer.py"
fi

# Stage other frequently-used scripts
STAGED_COUNT=0
if [[ -n "${TOOLS_DIR}" && -d "${TOOLS_DIR}" ]]; then
  for script in \
    search_mathlib.sh \
    smart_search.sh \
    check_axioms.sh \
    find_golfable.py \
    analyze_let_usage.py \
    count_tokens.py \
    suggest_tactics.sh
  do
    if [[ -f "${TOOLS_DIR}/${script}" ]]; then
      cp -f "${TOOLS_DIR}/${script}" "${WORKSPACE_TOOLS_DIR}/${script}"
      chmod +x "${WORKSPACE_TOOLS_DIR}/${script}" || true
      STAGED_COUNT=$((STAGED_COUNT + 1))
    fi
  done
  echo "Staged ${STAGED_COUNT} additional tool scripts to ${WORKSPACE_TOOLS_DIR}"
fi

# Stage reference documentation for subagents at predictable paths
DOC_STAGE=".claude/docs/lean4"
mkdir -p "${DOC_STAGE}"

DOC_STAGED_COUNT=0
# Find references directory (support both layouts)
REFS_DIR=""
for candidate in \
  "${CLAUDE_PLUGIN_ROOT}/skills/lean4-theorem-proving/references" \
  "${CLAUDE_PLUGIN_ROOT}/references"
do
  if [[ -d "$candidate" ]]; then
    REFS_DIR="$candidate"
    break
  fi
done

if [[ -n "${REFS_DIR}" && -d "${REFS_DIR}" ]]; then
  for doc in proof-golfing.md sorry-filling.md axiom-elimination.md compiler-guided-repair.md lean-lsp-tools-api.md; do
    if [[ -f "${REFS_DIR}/${doc}" ]]; then
      cp -f "${REFS_DIR}/${doc}" "${DOC_STAGE}/${doc}"
      DOC_STAGED_COUNT=$((DOC_STAGED_COUNT + 1))
    fi
  done
  echo "Staged ${DOC_STAGED_COUNT} reference docs to ${DOC_STAGE}"

  # Export doc stage location for reference
  if [[ -n "${ENV_OUT}" ]]; then
    printf 'export LEAN4_DOC_HOME="%s"\n' "${DOC_STAGE}" >> "${ENV_OUT}"
  fi
fi

# Persist variables for the rest of the session (so slash-commands can use them).
persist() {
  local kv="$1"
  if [[ -n "${ENV_OUT}" ]]; then
    printf '%s\n' "${kv}" >> "${ENV_OUT}"
  fi
}

# Always expose the plugin root (handy for other commands you may add)
persist "export LEAN4_PLUGIN_ROOT=\"${CLAUDE_PLUGIN_ROOT}\""

# Expose python if found
if [[ -n "${PYTHON_BIN}" ]]; then
  persist "export LEAN4_PYTHON_BIN=\"${PYTHON_BIN}\""
fi

# Expose tools directory and analyzer (if found)
if [[ -n "${TOOLS_DIR}" ]]; then
  persist "export LEAN4_TOOLS_DIR=\"${TOOLS_DIR}\""
fi
if [[ -n "${ANALYZER_PATH}" ]]; then
  persist "export LEAN4_SORRY_ANALYZER=\"${ANALYZER_PATH}\""
fi

# Optional: write a small status line (shows up in debug logs)
echo "Lean4 bootstrap: PLUGIN_ROOT=${CLAUDE_PLUGIN_ROOT} PYTHON=${PYTHON_BIN:-none} ANALYZER=${ANALYZER_PATH:-none}"
exit 0

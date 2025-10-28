#!/usr/bin/env bash
# Compiler-guided proof repair loop
# Usage: repairLoop.sh FILE.lean [maxAttempts] [--stage2-threshold=3]
#
# Inspired by APOLLO: Automatic Proof Optimizer with Lightweight Loop Optimization
# https://arxiv.org/abs/2505.05758
#
# Core loop: compile → parse error → route to fix → apply → verify

set -euo pipefail

FILE="${1:?Missing FILE.lean argument}"
MAX_ATTEMPTS="${2:-24}"
STAGE2_THRESHOLD="${3:-3}"
REPEAT_ERROR_LIMIT=3

REPAIR_DIR=".repair"
mkdir -p "${REPAIR_DIR}"

# Initialize attempt log
ATTEMPT_LOG="${REPAIR_DIR}/attempts.ndjson"
echo "" > "${ATTEMPT_LOG}"

previous_error_hash=""
same_error_count=0
stage=1

echo "🔧 Starting compiler-guided repair loop"
echo "   File: ${FILE}"
echo "   Max attempts: ${MAX_ATTEMPTS}"
echo "   Repeat error limit: ${REPEAT_ERROR_LIMIT}"
echo ""

for ((attempt=1; attempt<=MAX_ATTEMPTS; attempt++)); do
  start_time=$(date +%s)

  echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  echo "Attempt ${attempt}/${MAX_ATTEMPTS} (Stage ${stage})"
  echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

  # Compile and capture errors
  if lake build "${FILE}" 2> "${REPAIR_DIR}/errs.txt"; then
    elapsed=$(($(date +%s) - start_time))
    echo ""
    echo "✅ SUCCESS after ${attempt} attempts (${elapsed}s total)"

    # Log success
    if command -v jq >/dev/null 2>&1; then
      jq -n \
        --arg attempt "${attempt}" \
        --arg elapsed "${elapsed}" \
        --arg stage "${stage}" \
        '{attempt: $attempt|tonumber, success: true, elapsed: $elapsed|tonumber, stage: $stage|tonumber}' \
        >> "${ATTEMPT_LOG}"
    fi

    exit 0
  fi

  # Parse errors
  if ! python3 scripts/parseLeanErrors.py "${REPAIR_DIR}/errs.txt" > "${REPAIR_DIR}/context.json"; then
    echo "❌ Failed to parse Lean errors"
    exit 1
  fi

  # Extract error information
  if command -v jq >/dev/null 2>&1; then
    error_hash=$(jq -r '.errorHash' "${REPAIR_DIR}/context.json")
    error_msg=$(jq -r '.message' "${REPAIR_DIR}/context.json" | head -c 200)
  else
    # Fallback if jq not available
    error_hash=$(python3 -c "import json, sys; print(json.load(open('${REPAIR_DIR}/context.json'))['errorHash'])")
    error_msg=$(python3 -c "import json, sys; print(json.load(open('${REPAIR_DIR}/context.json'))['message'][:200])")
  fi

  echo "Error: ${error_msg}..."
  echo "Hash: ${error_hash}"

  # Check for repeated error
  if [[ "${error_hash}" == "${previous_error_hash}" ]]; then
    same_error_count=$((same_error_count + 1))
    echo "⚠️  Repeated error (${same_error_count}/${REPEAT_ERROR_LIMIT})"

    if [[ ${same_error_count} -ge ${REPEAT_ERROR_LIMIT} ]]; then
      if [[ ${stage} -eq 1 ]]; then
        echo "🔼 Escalating to Stage 2 (stronger model)"
        stage=2
        same_error_count=0
      else
        echo "❌ Same error repeated ${REPEAT_ERROR_LIMIT} times in Stage 2 - giving up"
        if command -v jq >/dev/null 2>&1; then
          jq -n \
            --arg attempt "${attempt}" \
            --arg error "${error_hash}" \
            --arg reason "repeat_error_limit" \
            '{attempt: $attempt|tonumber, success: false, error: $error, reason: $reason}' \
            >> "${ATTEMPT_LOG}"
        fi
        exit 1
      fi
    fi
  else
    same_error_count=0
  fi
  previous_error_hash="${error_hash}"

  # Try solver cascade first (fast path)
  echo "🤖 Trying automated solvers..."
  if python3 scripts/solverCascade.py "${REPAIR_DIR}/context.json" "${FILE}" > "${REPAIR_DIR}/solver.diff" 2>&1; then
    if git apply --check "${REPAIR_DIR}/solver.diff" 2>/dev/null; then
      git apply "${REPAIR_DIR}/solver.diff"
      echo "✓ Solver cascade applied patch"
      continue
    fi
  fi

  # Generate patch via agent
  echo "🧠 Generating repair patch (Stage ${stage})..."
  if ! python3 scripts/proposePatch.py "${REPAIR_DIR}/context.json" "${FILE}" --stage="${stage}" > "${REPAIR_DIR}/patch.diff" 2>&1; then
    echo "⚠️  Failed to generate patch (agent stub not implemented yet)"
    # For now, since proposePatch.py is a stub, we'll log and continue
    elapsed=$(($(date +%s) - start_time))
    if command -v jq >/dev/null 2>&1; then
      jq -n \
        --arg attempt "${attempt}" \
        --arg error "${error_hash}" \
        --arg elapsed "${elapsed}" \
        --arg reason "patch_generation_failed" \
        --arg stage "${stage}" \
        '{attempt: $attempt|tonumber, success: false, error: $error, elapsed: $elapsed|tonumber, reason: $reason, stage: $stage|tonumber}' \
        >> "${ATTEMPT_LOG}"
    fi
    continue
  fi

  # Apply patch
  if git apply --ignore-whitespace --reject "${REPAIR_DIR}/patch.diff" 2>/dev/null; then
    echo "✓ Patch applied"
  elif git apply --ignore-whitespace --3way "${REPAIR_DIR}/patch.diff" 2>/dev/null; then
    echo "✓ Patch applied (3-way merge)"
  else
    echo "⚠️  Patch failed to apply cleanly"
    # Log failed attempt
    elapsed=$(($(date +%s) - start_time))
    if command -v jq >/dev/null 2>&1; then
      jq -n \
        --arg attempt "${attempt}" \
        --arg error "${error_hash}" \
        --arg elapsed "${elapsed}" \
        --arg reason "patch_apply_failed" \
        --arg stage "${stage}" \
        '{attempt: $attempt|tonumber, success: false, error: $error, elapsed: $elapsed|tonumber, reason: $reason, stage: $stage|tonumber}' \
        >> "${ATTEMPT_LOG}"
    fi
    continue
  fi

  # Log attempt
  elapsed=$(($(date +%s) - start_time))
  if command -v jq >/dev/null 2>&1; then
    jq -n \
      --arg attempt "${attempt}" \
      --arg error "${error_hash}" \
      --arg elapsed "${elapsed}" \
      --arg stage "${stage}" \
      '{attempt: $attempt|tonumber, success: false, error: $error, elapsed: $elapsed|tonumber, stage: $stage|tonumber}' \
      >> "${ATTEMPT_LOG}"
  fi

done

echo ""
echo "❌ Repair failed after ${MAX_ATTEMPTS} attempts"
echo "   Attempt log: ${ATTEMPT_LOG}"
exit 1

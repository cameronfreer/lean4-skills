#!/bin/bash
set -euo pipefail

# Read JSON input from stdin
INPUT=$(cat)

# Parse command with jq, fall back to python3
if command -v jq >/dev/null 2>&1; then
  COMMAND=$(echo "$INPUT" | jq -r '.tool_input.command // empty')
else
  COMMAND=$(echo "$INPUT" | python3 <<'PY'
import json, sys
data = json.load(sys.stdin)
print((data.get("tool_input") or {}).get("command", ""))
PY
  )
fi

# If no command, allow
[ -z "$COMMAND" ] && exit 0

# Block git push (broad: catches git -C, sudo git, etc.)
# Allows: git push --dry-run
if echo "$COMMAND" | grep -qE '\bgit\b.*\bpush\b' && ! echo "$COMMAND" | grep -qE '\b--dry-run\b'; then
  echo "BLOCKED: git push - use /lean4:checkpoint, then push manually" >&2
  exit 2
fi

# Block git commit --amend (broad pattern)
if echo "$COMMAND" | grep -qE '\bgit\b.*\bcommit\b.*\b--amend\b'; then
  echo "BLOCKED: git commit --amend - autoprover creates new commits" >&2
  exit 2
fi

# Block gh pr create
if echo "$COMMAND" | grep -qE '\bgh\b.*\bpr\b.*\bcreate\b'; then
  echo "BLOCKED: gh pr create - review first, then create PR manually" >&2
  exit 2
fi

exit 0

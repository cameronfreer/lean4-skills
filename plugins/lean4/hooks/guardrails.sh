#!/bin/bash
set -euo pipefail
COMMAND="${TOOL_INPUT:-}"

# Block git push (broad: catches git -C, sudo git, etc.)
# Allows: git push --dry-run
echo "$COMMAND" | grep -qE '\bgit\b.*\bpush\b' && ! echo "$COMMAND" | grep -qE '\b--dry-run\b' && {
  echo "BLOCKED: git push - use /lean4:checkpoint, then push manually"; exit 1
}

# Block git commit --amend (broad pattern)
echo "$COMMAND" | grep -qE '\bgit\b.*\bcommit\b.*\b--amend\b' && {
  echo "BLOCKED: git commit --amend - autoprover creates new commits"; exit 1
}

# Block gh pr create
echo "$COMMAND" | grep -qE '\bgh\b.*\bpr\b.*\bcreate\b' && {
  echo "BLOCKED: gh pr create - review first, then create PR manually"; exit 1
}

exit 0

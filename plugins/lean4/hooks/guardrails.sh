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
# Allows: git push --dry-run, git stash push
if echo "$COMMAND" | grep -qE '\bgit\b.*\bpush\b' && \
   ! echo "$COMMAND" | grep -qE -- '--dry-run\b' && \
   ! echo "$COMMAND" | grep -qE '\bgit\b.*\bstash\b.*\bpush\b'; then
  echo "BLOCKED: git push - use /lean4:checkpoint, then push manually" >&2
  exit 2
fi

# Block git commit --amend (broad pattern)
if echo "$COMMAND" | grep -qE -- '\bgit\b.*\bcommit\b.*--amend\b'; then
  echo "BLOCKED: git commit --amend - autoprover creates new commits" >&2
  exit 2
fi

# Block gh pr create
if echo "$COMMAND" | grep -qE '\bgh\b.*\bpr\b.*\bcreate\b'; then
  echo "BLOCKED: gh pr create - review first, then create PR manually" >&2
  exit 2
fi

# Block destructive checkout (discards uncommitted changes)
# Allows: git checkout <branch>, git checkout -b <branch>, git checkout HEAD (detach)
# Blocks: git checkout -- <path>, git checkout . (anywhere after checkout)
if echo "$COMMAND" | grep -qE '\bgit\b.*\bcheckout\b.*\s--\s'; then
  echo "BLOCKED: destructive git checkout. Use git stash push -u or create a revert commit." >&2
  exit 2
fi
if echo "$COMMAND" | grep -qE '\bgit\b.*\bcheckout\b\s+\.(\s|$)'; then
  echo "BLOCKED: git checkout . discards changes. Use git stash push -u or create a revert commit." >&2
  exit 2
fi

# Block git restore (worktree changes only, allow pure unstaging)
# Blocks: git restore <path>, git restore --source=..., git restore --staged --worktree
# Allows: git restore --staged <path> (without --worktree)
if echo "$COMMAND" | grep -qE '\bgit\b.*\brestore\b'; then
  # Allow if --staged is present AND --worktree is NOT present
  if echo "$COMMAND" | grep -qE -- '--staged\b' && ! echo "$COMMAND" | grep -qE -- '--worktree\b'; then
    : # allowed - pure unstaging
  else
    echo "BLOCKED: git restore discards changes. Use git stash push -u or create a revert commit." >&2
    exit 2
  fi
fi

# Block git reset --hard (discards commits and changes)
if echo "$COMMAND" | grep -qE -- '\bgit\b.*\breset\b.*--hard\b'; then
  echo "BLOCKED: git reset --hard. Use git stash push -u or create a revert commit." >&2
  exit 2
fi

# Block git clean with -f/--force anywhere (deletes untracked files)
# Matches: -f, -fd, -fx, -nfd, --force, etc.
if echo "$COMMAND" | grep -qE '\bgit\b.*\bclean\b.*(-[a-zA-Z]*f|--force)'; then
  echo "BLOCKED: git clean deletes untracked files. Use git stash push -u instead." >&2
  exit 2
fi

exit 0

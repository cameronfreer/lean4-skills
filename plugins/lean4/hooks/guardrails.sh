#!/bin/bash
set -euo pipefail

# Override: skip all guardrails if explicitly disabled
[[ "${LEAN4_GUARDRAILS_DISABLE:-}" == "1" ]] && exit 0

# Lean project detection: walk ancestors for lakefile.lean, lean-toolchain, lakefile.toml
# No depth cap — deep monorepos are common. Terminates at filesystem root.
is_lean_project() {
  local dir="$1"
  [[ -d "$dir" ]] || return 1
  while true; do
    [[ -f "$dir/lakefile.lean" || -f "$dir/lean-toolchain" || -f "$dir/lakefile.toml" ]] && return 0
    [[ "$dir" == "/" ]] && break
    dir=$(dirname "$dir")
  done
  return 1
}

# Read JSON input from stdin
INPUT=$(cat)

# Parse command with jq, fall back to python3; default empty on parse failure
if command -v jq >/dev/null 2>&1; then
  COMMAND=$(echo "$INPUT" | jq -r '.tool_input.command // .command // empty' 2>/dev/null) || COMMAND=""
else
  COMMAND=$(echo "$INPUT" | python3 -c '
import json, sys
try:
    data = json.load(sys.stdin)
    ti = data.get("tool_input") or {}
    print(ti.get("command") or data.get("command") or "")
except Exception:
    print("")
' 2>/dev/null) || COMMAND=""
fi

# If no command, allow
[ -z "$COMMAND" ] && exit 0

# Determine working directory: .cwd → .tool_input.cwd → .tool_input.workdir → $PWD
# Fail-safe: parse failure → empty → falls through to $PWD default
if command -v jq >/dev/null 2>&1; then
  TOOL_CWD=$(echo "$INPUT" | jq -r '(.cwd // .tool_input.cwd // .tool_input.workdir) // empty' 2>/dev/null) || TOOL_CWD=""
else
  TOOL_CWD=$(echo "$INPUT" | python3 -c '
import json, sys
try:
    data = json.load(sys.stdin)
    ti = data.get("tool_input") or {}
    print(data.get("cwd") or ti.get("cwd") or ti.get("workdir") or "")
except Exception:
    print("")
' 2>/dev/null) || TOOL_CWD=""
fi
TOOL_CWD="${TOOL_CWD:-$PWD}"

# Normalize path (portable: realpath → cd+pwd -P → raw)
TOOL_CWD=$(realpath "$TOOL_CWD" 2>/dev/null || (cd "$TOOL_CWD" 2>/dev/null && pwd -P) || echo "$TOOL_CWD")

# Skip guardrails if not in a Lean project (unless forced)
if ! is_lean_project "$TOOL_CWD"; then
  [[ "${LEAN4_GUARDRAILS_FORCE:-}" == "1" ]] || exit 0
fi

# One-shot bypass: token in leading env-assignment prefix only (not arbitrary position)
# Accepts: LEAN4_GUARDRAILS_BYPASS=1 git push ...
#          env LEAN4_GUARDRAILS_BYPASS=1 git push ...
#          FOO=bar LEAN4_GUARDRAILS_BYPASS=1 git push ...
# Rejects: echo LEAN4_GUARDRAILS_BYPASS=1 && git push ... (token after a command word)
# Applies to collaboration ops only (push, amend, pr create), not destructive ops.
BYPASS=0
if [[ "$COMMAND" =~ ^(env[[:space:]]+)?([A-Za-z_][A-Za-z_0-9]*=[^[:space:]]*[[:space:]]+)*LEAN4_GUARDRAILS_BYPASS=1([[:space:]]|$) ]]; then
  BYPASS=1
fi

# Block git push (broad: catches git -C, sudo git, etc.)
# Allows: git push --dry-run, git stash push
if echo "$COMMAND" | grep -qE '\bgit\b.*\bpush\b' && \
   ! echo "$COMMAND" | grep -qE -- '--dry-run\b' && \
   ! echo "$COMMAND" | grep -qE '\bgit\b.*\bstash\b.*\bpush\b'; then
  [[ $BYPASS -eq 1 ]] && exit 0
  echo "BLOCKED (Lean guardrail): git push - use /lean4:checkpoint, then push manually" >&2
  echo "  To proceed once, prefix with: LEAN4_GUARDRAILS_BYPASS=1" >&2
  exit 2
fi

# Block git commit --amend (broad pattern)
if echo "$COMMAND" | grep -qE -- '\bgit\b.*\bcommit\b.*--amend\b'; then
  [[ $BYPASS -eq 1 ]] && exit 0
  echo "BLOCKED (Lean guardrail): git commit --amend - proving workflow creates new commits for safe rollback" >&2
  echo "  To proceed once, prefix with: LEAN4_GUARDRAILS_BYPASS=1" >&2
  exit 2
fi

# Block gh pr create
if echo "$COMMAND" | grep -qE '\bgh\b.*\bpr\b.*\bcreate\b'; then
  [[ $BYPASS -eq 1 ]] && exit 0
  echo "BLOCKED (Lean guardrail): gh pr create - review first, then create PR manually" >&2
  echo "  To proceed once, prefix with: LEAN4_GUARDRAILS_BYPASS=1" >&2
  exit 2
fi

# Block destructive checkout (discards uncommitted changes)
# Allows: git checkout <branch>, git checkout -b <branch>, git checkout HEAD (detach)
# Blocks: git checkout -- <path>, git checkout . (anywhere after checkout)
if echo "$COMMAND" | grep -qE '\bgit\b.*\bcheckout\b.*\s--\s'; then
  echo "BLOCKED (Lean guardrail): destructive git checkout. Use git stash push -u or create a revert commit." >&2
  exit 2
fi
if echo "$COMMAND" | grep -qE '\bgit\b.*\bcheckout\b\s+\.(\s|$)'; then
  echo "BLOCKED (Lean guardrail): git checkout . discards changes. Use git stash push -u or create a revert commit." >&2
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
    echo "BLOCKED (Lean guardrail): git restore discards changes. Use git stash push -u or create a revert commit." >&2
    exit 2
  fi
fi

# Block git reset --hard (discards commits and changes)
if echo "$COMMAND" | grep -qE -- '\bgit\b.*\breset\b.*--hard\b'; then
  echo "BLOCKED (Lean guardrail): git reset --hard. Use git stash push -u or create a revert commit." >&2
  exit 2
fi

# Block git clean with -f/--force anywhere (deletes untracked files)
# Matches: -f, -fd, -fx, -nfd, --force, etc.
if echo "$COMMAND" | grep -qE '\bgit\b.*\bclean\b.*(-[a-zA-Z]*f|--force)'; then
  echo "BLOCKED (Lean guardrail): git clean deletes untracked files. Use git stash push -u instead." >&2
  exit 2
fi

exit 0

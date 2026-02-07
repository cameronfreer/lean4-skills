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
# Never exits early — all destructive checks run first; bypass resolves at end.
BYPASS=0
if [[ "$COMMAND" =~ ^(env[[:space:]]+)?([A-Za-z_][A-Za-z_0-9]*=[^[:space:]]*[[:space:]]+)*LEAN4_GUARDRAILS_BYPASS=1([[:space:]]|$) ]]; then
  BYPASS=1
fi

# --- Segment-based command parsing ---
# Split command on unquoted shell operators (&&, ||, ;, |) into segments.
# Normalize each segment: strip wrappers (sudo, env, VAR=val), then strip
# quoted strings so patterns match only real command/flag tokens.

# Strip sudo (with options), env (with options), and VAR=val prefixes.
_strip_wrappers() {
  local s="$1" _next
  s="${s#"${s%%[![:space:]]*}"}"
  # Strip sudo with options
  if [[ "$s" =~ ^sudo[[:space:]] ]]; then
    s="${s#sudo}"; s="${s#"${s%%[![:space:]]*}"}"
    while [[ "$s" == -* ]]; do
      s="${s#${s%%[[:space:]]*}}"; s="${s#"${s%%[![:space:]]*}"}"
      _next="${s%%[[:space:]]*}"
      if [[ -n "$_next" && "$_next" != -* && ! "$_next" =~ ^[A-Za-z_][A-Za-z_0-9]*= ]]; then
        case "$_next" in git|gh|lake|env|sudo) break ;; esac
        s="${s#${_next}}"; s="${s#"${s%%[![:space:]]*}"}"
      fi
    done
  fi
  # Strip env with options
  if [[ "$s" =~ ^env[[:space:]] ]]; then
    s="${s#env}"; s="${s#"${s%%[![:space:]]*}"}"
    while [[ "$s" == -* ]]; do
      s="${s#${s%%[[:space:]]*}}"; s="${s#"${s%%[![:space:]]*}"}"
    done
  fi
  # Strip env-var assignments
  while [[ "$s" =~ ^[A-Za-z_][A-Za-z_0-9]*=[^[:space:]]*[[:space:]] ]]; do
    s="${s#${BASH_REMATCH[0]}}"
  done
  echo "$s"
}

# Quote-aware segment splitting: split on unquoted &&, ||, ;, |.
_split_segments() {
  local cmd="$1"
  local i=0 len=${#cmd} seg="" c="" nc="" in_sq=0 in_dq=0
  while [[ $i -lt $len ]]; do
    c="${cmd:i:1}"
    nc="${cmd:i+1:1}"
    if [[ $in_sq -eq 1 ]]; then
      seg+="$c"
      if [[ "$c" == "'" ]]; then in_sq=0; fi
    elif [[ $in_dq -eq 1 ]]; then
      if [[ "$c" == "\\" && -n "$nc" ]]; then
        seg+="$c$nc"; i=$((i + 2)); continue
      fi
      seg+="$c"
      if [[ "$c" == '"' ]]; then in_dq=0; fi
    elif [[ "$c" == "\\" && -n "$nc" ]]; then
      seg+="$c$nc"; i=$((i + 2)); continue
    elif [[ "$c" == "'" ]]; then
      in_sq=1; seg+="$c"
    elif [[ "$c" == '"' ]]; then
      in_dq=1; seg+="$c"
    elif [[ "$c" == "&" && "$nc" == "&" ]]; then
      echo "$seg"; seg=""; i=$((i + 2)); continue
    elif [[ "$c" == "|" && "$nc" == "|" ]]; then
      echo "$seg"; seg=""; i=$((i + 2)); continue
    elif [[ "$c" == ";" || "$c" == "|" ]]; then
      echo "$seg"; seg=""
    else
      seg+="$c"
    fi
    i=$((i + 1))
  done
  if [[ -n "$seg" ]]; then echo "$seg"; fi
}

# Strip quoted strings so patterns match only unquoted tokens.
_strip_quotes() {
  local s="$1"
  s=$(echo "$s" | sed -E 's/"([^"\\]|\\.)*"//g')
  s=$(echo "$s" | sed "s/'[^']*'//g")
  echo "$s"
}

SEGMENTS=()
while IFS= read -r _seg; do
  _seg="${_seg#"${_seg%%[![:space:]]*}"}"
  [[ -z "$_seg" ]] && continue
  _stripped=$(_strip_wrappers "$_seg")
  _stripped=$(_strip_quotes "$_stripped")
  SEGMENTS+=("$_stripped")
done < <(_split_segments "$COMMAND")

# Helper: true if any segment starts with $1 and matches $2.
# Optional $3: skip segments matching this pattern (scoped exemption).
seg_match() {
  local exe="$1" pattern="$2" exclude="${3:-}" _sm_seg
  for _sm_seg in "${SEGMENTS[@]}"; do
    echo "$_sm_seg" | grep -qE -- "^${exe}\b" || continue
    echo "$_sm_seg" | grep -qE -- "$pattern" || continue
    [[ -n "$exclude" ]] && echo "$_sm_seg" | grep -qE -- "$exclude" && continue
    return 0
  done
  return 1
}

# --- Collaboration ops (bypassable) ---

# Block git push (not --dry-run, not stash push — exemptions scoped per-segment)
if seg_match git '[[:space:]]push([[:space:]]|$)' '--dry-run\b|\bstash\b.*\bpush\b'; then
  if [[ $BYPASS -ne 1 ]]; then
    echo "BLOCKED (Lean guardrail): git push - use /lean4:checkpoint, then push manually" >&2
    echo "  To proceed once, prefix with: LEAN4_GUARDRAILS_BYPASS=1" >&2
    exit 2
  fi
fi

# Block git commit --amend
if seg_match git '\bcommit\b.*--amend\b'; then
  if [[ $BYPASS -ne 1 ]]; then
    echo "BLOCKED (Lean guardrail): git commit --amend - proving workflow creates new commits for safe rollback" >&2
    echo "  To proceed once, prefix with: LEAN4_GUARDRAILS_BYPASS=1" >&2
    exit 2
  fi
fi

# Block gh pr create
if seg_match gh '\bpr\b.*\bcreate\b'; then
  if [[ $BYPASS -ne 1 ]]; then
    echo "BLOCKED (Lean guardrail): gh pr create - review first, then create PR manually" >&2
    echo "  To proceed once, prefix with: LEAN4_GUARDRAILS_BYPASS=1" >&2
    exit 2
  fi
fi

# --- Destructive ops (never bypassable) ---

# Block destructive checkout (discards uncommitted changes)
# Allows: git checkout <branch>, git checkout -b <branch>
# Blocks: git checkout -- <path>, git checkout .
if seg_match git '\bcheckout\b.*\s--\s'; then
  echo "BLOCKED (Lean guardrail): destructive git checkout. Use git stash push -u or create a revert commit." >&2
  exit 2
fi
if seg_match git '\bcheckout\b\s+\.(\s|$)'; then
  echo "BLOCKED (Lean guardrail): git checkout . discards changes. Use git stash push -u or create a revert commit." >&2
  exit 2
fi

# Block git restore (worktree changes only, allow pure unstaging)
# Blocks: git restore <path>, git restore --source=..., git restore --staged --worktree
# Allows: git restore --staged <path> (without --worktree)
for _seg in "${SEGMENTS[@]}"; do
  echo "$_seg" | grep -qE '^git\b' || continue
  echo "$_seg" | grep -qE '\brestore\b' || continue
  if echo "$_seg" | grep -qE -- '--staged\b' && ! echo "$_seg" | grep -qE -- '--worktree\b'; then
    continue  # allowed - pure unstaging
  fi
  echo "BLOCKED (Lean guardrail): git restore discards changes. Use git stash push -u or create a revert commit." >&2
  exit 2
done

# Block git reset --hard (discards commits and changes)
if seg_match git '\breset\b.*--hard\b'; then
  echo "BLOCKED (Lean guardrail): git reset --hard. Use git stash push -u or create a revert commit." >&2
  exit 2
fi

# Block git clean with -f/--force anywhere (deletes untracked files)
# Matches: -f, -fd, -fx, -nfd, --force, etc.
if seg_match git '\bclean\b.*(-[a-zA-Z]*f|--force)'; then
  echo "BLOCKED (Lean guardrail): git clean deletes untracked files. Use git stash push -u instead." >&2
  exit 2
fi

# All checks passed — resolve deferred bypass or allow normally
exit 0

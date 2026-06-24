#!/usr/bin/env bash
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
# Detected per-segment during normalization using _strip_wrappers prefix diff.
# Accepts: LEAN4_GUARDRAILS_BYPASS=1 git push ...
#          env LEAN4_GUARDRAILS_BYPASS=1 git push ...
#          FOO="a b" LEAN4_GUARDRAILS_BYPASS=1 git push ...
# Rejects: echo LEAN4_GUARDRAILS_BYPASS=1 && git push ... (token after a command word)
#          FOO="LEAN4_GUARDRAILS_BYPASS=1" git push ...  (token inside quoted value)
# Applies to soft-gated ops (collaboration + path-scoped destructive);
# the whole-worktree destructive ops (reset --hard, clean -f,
# checkout ., restore .) remain non-bypassable regardless.
# Never exits early — all destructive checks run first; bypass resolves at end.
BYPASS=0

# Three-tier git operation policy:
#
#   1. ALLOW (implicit)         — status, diff, log, show, branch, add,
#                                 commit, stash push, switch <branch>,
#                                 restore --staged <path>, etc. No gate.
#
#   2. SOFT-GATE (this section) — policy-controlled, bypass-token-able.
#                                 Two independent vars cover the two
#                                 risk categories:
#                                   COLLAB_POLICY: push, amend, pr create
#                                     (affects shared state, reversible
#                                     via force-push / amend back / PR close)
#                                   DESTRUCTIVE_POLICY: checkout -- <path…>,
#                                     restore <path…>
#                                     (path-scoped local data loss — one
#                                     file, multiple files, a directory,
#                                     or any explicit pathset; smaller
#                                     blast radius than whole-worktree
#                                     wipes which use `.` / `./` / `:/`)
#
#   3. HARD-BLOCK (below)       — non-bypassable, no policy override.
#                                 reset --hard, clean -f/-fd/-fdx,
#                                 checkout ., restore ., checkout -- .
#                                 The blast radius is unbounded and
#                                 git reflog can't recover uncommitted
#                                 edits (and can't recover untracked
#                                 files via clean -f at all).
#
# Each soft-gate policy independently accepts ask | allow | block:
#   ask:   require human confirmation via one-shot bypass token (default)
#   allow: permit without bypass token (user explicitly opted in)
#   block: block even with bypass token (extra paranoia)

COLLAB_POLICY="${LEAN4_GUARDRAILS_COLLAB_POLICY:-ask}"
case "$COLLAB_POLICY" in
  ask|allow|block) ;;
  *) COLLAB_POLICY="ask" ;;
esac

DESTRUCTIVE_POLICY="${LEAN4_GUARDRAILS_DESTRUCTIVE_POLICY:-ask}"
case "$DESTRUCTIVE_POLICY" in
  ask|allow|block) ;;
  *) DESTRUCTIVE_POLICY="ask" ;;
esac

# --- Segment-based command parsing ---
# Split command on unquoted shell operators (&&, ||, ;, |) into segments.
# Normalize each segment: strip wrappers (sudo, env, VAR=val), then strip
# quoted strings so patterns match only real command/flag tokens.

# Strip sudo (with options), env (with options), and VAR=val prefixes.
_strip_wrappers() {
  local s="$1" _next _vi _vlen _vc _depth
  s="${s#"${s%%[![:space:]]*}"}"
  # Normalize /path/to/exe → exe for known commands and wrappers
  if [[ "${s%%[[:space:]]*}" == */* ]]; then
    _next="${s%%[[:space:]]*}"
    case "${_next##*/}" in
      git|gh|lake|sudo|env|bash|sh|zsh|command) s="${_next##*/}${s#"${_next}"}" ;;
    esac
  fi
  # Strip sudo with options
  if [[ "$s" =~ ^sudo[[:space:]] ]]; then
    s="${s#sudo}"; s="${s#"${s%%[![:space:]]*}"}"
    while [[ "$s" == -* ]]; do
      s="${s#"${s%%[[:space:]]*}"}"; s="${s#"${s%%[![:space:]]*}"}"
      _next="${s%%[[:space:]]*}"
      if [[ -n "$_next" && "$_next" != -* && ! "$_next" =~ ^[A-Za-z_][A-Za-z_0-9]*= ]]; then
        case "$_next" in git|gh|lake|env|sudo) break ;; esac
        s="${s#"${_next}"}"; s="${s#"${s%%[![:space:]]*}"}"
      fi
    done
  fi
  # Strip env with options
  if [[ "$s" =~ ^env[[:space:]] ]]; then
    s="${s#env}"; s="${s#"${s%%[![:space:]]*}"}"
    while [[ "$s" == -* ]]; do
      s="${s#"${s%%[[:space:]]*}"}"; s="${s#"${s%%[![:space:]]*}"}"
    done
  fi
  # Strip env-var assignments: NAME=VALUE where VALUE may contain quotes,
  # backslash escapes, $(...), ${...}, or backtick substitution.
  # Uses index-based scanning (not glob-based ${s#...}) to avoid infinite
  # loops when BASH_REMATCH contains backslashes interpreted as glob escapes.
  while [[ "$s" =~ ^[A-Za-z_][A-Za-z_0-9]*= ]]; do
    _vi=${#BASH_REMATCH[0]}
    _vlen=${#s}
    while [[ $_vi -lt $_vlen ]]; do
      _vc="${s:_vi:1}"
      if [[ "$_vc" == '"' ]]; then
        _vi=$((_vi + 1))
        while [[ $_vi -lt $_vlen && "${s:_vi:1}" != '"' ]]; do
          if [[ "${s:_vi:1}" == "\\" ]]; then _vi=$((_vi + 1)); fi
          _vi=$((_vi + 1))
        done
        _vi=$((_vi + 1))
      elif [[ "$_vc" == "'" ]]; then
        _vi=$((_vi + 1))
        while [[ $_vi -lt $_vlen && "${s:_vi:1}" != "'" ]]; do
          _vi=$((_vi + 1))
        done
        _vi=$((_vi + 1))
      elif [[ "$_vc" == '$' && "${s:_vi+1:1}" == '(' ]]; then
        _vi=$((_vi + 2)); _depth=1
        while [[ $_vi -lt $_vlen && $_depth -gt 0 ]]; do
          _vc="${s:_vi:1}"
          if [[ "$_vc" == '"' ]]; then
            _vi=$((_vi + 1))
            while [[ $_vi -lt $_vlen && "${s:_vi:1}" != '"' ]]; do
              if [[ "${s:_vi:1}" == "\\" ]]; then _vi=$((_vi + 1)); fi
              _vi=$((_vi + 1))
            done
          elif [[ "$_vc" == "'" ]]; then
            _vi=$((_vi + 1))
            while [[ $_vi -lt $_vlen && "${s:_vi:1}" != "'" ]]; do
              _vi=$((_vi + 1))
            done
          elif [[ "$_vc" == '(' ]]; then _depth=$((_depth + 1));
          elif [[ "$_vc" == ')' ]]; then _depth=$((_depth - 1));
          elif [[ "$_vc" == "\\" ]]; then _vi=$((_vi + 1)); fi
          _vi=$((_vi + 1))
        done
      elif [[ "$_vc" == '$' && "${s:_vi+1:1}" == '{' ]]; then
        _vi=$((_vi + 2)); _depth=1
        while [[ $_vi -lt $_vlen && $_depth -gt 0 ]]; do
          _vc="${s:_vi:1}"
          if [[ "$_vc" == '{' ]]; then _depth=$((_depth + 1));
          elif [[ "$_vc" == '}' ]]; then _depth=$((_depth - 1));
          elif [[ "$_vc" == "\\" ]]; then _vi=$((_vi + 1)); fi
          _vi=$((_vi + 1))
        done
      elif [[ "$_vc" == '`' ]]; then
        _vi=$((_vi + 1))
        while [[ $_vi -lt $_vlen && "${s:_vi:1}" != '`' ]]; do
          if [[ "${s:_vi:1}" == "\\" ]]; then _vi=$((_vi + 1)); fi
          _vi=$((_vi + 1))
        done
        _vi=$((_vi + 1))
      elif [[ "$_vc" == "\\" ]]; then
        _vi=$((_vi + 2))
      elif [[ "$_vc" == " " || "$_vc" == $'\t' ]]; then
        break
      else
        _vi=$((_vi + 1))
      fi
    done
    if [[ $_vi -ge $_vlen ]]; then s=""; break; fi
    while [[ $_vi -lt $_vlen && ("${s:_vi:1}" == " " || "${s:_vi:1}" == $'\t') ]]; do
      _vi=$((_vi + 1))
    done
    s="${s:_vi}"
  done
  # Strip 'command' prefix (with optional flags like -p)
  if [[ "$s" =~ ^command[[:space:]] ]]; then
    s="${s#command}"; s="${s#"${s%%[![:space:]]*}"}"
    while [[ "$s" == -* ]]; do
      s="${s#"${s%%[[:space:]]*}"}"; s="${s#"${s%%[![:space:]]*}"}"
    done
  fi
  # Strip shell -c invocation: bash -c 'cmd' / bash -lc 'cmd' → cmd
  if [[ "$s" =~ ^(bash|sh|zsh)([[:space:]]+-[a-zA-Z-]+)*[[:space:]]+-[a-zA-Z]*c[[:space:]] ]]; then
    s="${s#"${s%%[[:space:]]*}"}"; s="${s#"${s%%[![:space:]]*}"}"
    while [[ "$s" == -* ]]; do
      _next="${s%%[[:space:]]*}"
      s="${s#"${_next}"}"; s="${s#"${s%%[![:space:]]*}"}"
      if [[ "$_next" == *c && "$_next" != --* ]]; then break; fi
    done
    # Unquote the -c argument if quoted
    if [[ "$s" == \'*\' ]]; then s="${s#\'}"; s="${s%\'}";
    elif [[ "$s" == \"*\" ]]; then s="${s#\"}"; s="${s%\"}"; fi
  fi
  # Normalize again: wrappers may have exposed a path-qualified command
  if [[ "${s%%[[:space:]]*}" == */* ]]; then
    _next="${s%%[[:space:]]*}"
    case "${_next##*/}" in
      git|gh|lake|sudo|env|bash|sh|zsh|command) s="${_next##*/}${s#"${_next}"}" ;;
    esac
  fi
  echo "$s"
}

# Quote-aware segment splitting: split on unquoted &&, ||, ;, |.
# Tracks $() nesting and backticks so separators inside them don't split.
_split_segments() {
  local cmd="$1"
  local i=0 len=${#cmd} seg="" c="" nc="" in_sq=0 in_dq=0 paren_depth=0 in_bt=0
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
    elif [[ $in_bt -eq 1 ]]; then
      seg+="$c"
      if [[ "$c" == "\\" && -n "$nc" ]]; then
        seg+="$nc"; i=$((i + 2)); continue
      fi
      if [[ "$c" == '`' ]]; then in_bt=0; fi
    elif [[ $paren_depth -gt 0 ]]; then
      seg+="$c"
      if [[ "$c" == "\\" && -n "$nc" ]]; then
        seg+="$nc"; i=$((i + 2)); continue
      fi
      if [[ "$c" == "'" ]]; then in_sq=1;
      elif [[ "$c" == '"' ]]; then in_dq=1;
      elif [[ "$c" == '(' ]]; then paren_depth=$((paren_depth + 1));
      elif [[ "$c" == ')' ]]; then paren_depth=$((paren_depth - 1)); fi
    elif [[ "$c" == "\\" && -n "$nc" ]]; then
      seg+="$c$nc"; i=$((i + 2)); continue
    elif [[ "$c" == "'" ]]; then
      in_sq=1; seg+="$c"
    elif [[ "$c" == '"' ]]; then
      in_dq=1; seg+="$c"
    elif [[ "$c" == '$' && "$nc" == '(' ]]; then
      paren_depth=$((paren_depth + 1)); seg+="$c$nc"; i=$((i + 2)); continue
    elif [[ "$c" == '`' ]]; then
      in_bt=1; seg+="$c"
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

# Strip known text-value option pairs (-m "msg", --body "text", etc.) so
# argument content doesn't contribute to pattern matching.
# Anchored to token boundaries so patterns don't match inside quoted strings.
_strip_optvals() {
  local s="$1"
  # Short options with text values: -m "msg", -m'msg', -mmsg, -am "msg", -F file
  s=$(echo "$s" | sed -E "s/(^|[[:space:]])-[a-zA-Z]*[mF][[:space:]]*(\"[^\"]*\"|'[^']*'|[^[:space:]]+)/\1/g")
  # Long options with text values: --message/--file/--body/--title (= or space)
  s=$(echo "$s" | sed -E "s/(^|[[:space:]])--(message|file|body|title)(=(\"[^\"]*\"|'[^']*'|[^[:space:]]+)|[[:space:]]+(\"[^\"]*\"|'[^']*'|[^[:space:]]+))/\1/g")
  echo "$s"
}

# Unquote single-token quoted strings ("--hard" → --hard), remove
# multi-token ones ("mention git push" → removed).
_unquote_tokens() {
  local s="$1"
  s=$(echo "$s" | sed -E 's/"([^"[:space:]]*)"/ \1 /g; s/"([^"\\]|\\.)*"//g')
  s=$(echo "$s" | sed -E "s/'([^'[:space:]]*)'/ \1 /g; s/'[^']*'//g")
  echo "$s"
}

# Normalization pipeline: strip wrappers → strip option values → unquote tokens.
# Also detects bypass token: _strip_wrappers consumes env-var prefixes, so the
# prefix zone is raw minus stripped suffix.  A whitespace-bounded match there
# confirms a standalone assignment (not buried inside another var's quoted value).
SEGMENTS=()
RAW_SEGMENTS=()
while IFS= read -r _seg; do
  _seg="${_seg#"${_seg%%[![:space:]]*}"}"
  [[ -z "$_seg" ]] && continue
  RAW_SEGMENTS+=("$_seg")
  _stripped=$(_strip_wrappers "$_seg")
  if [[ $BYPASS -eq 0 ]]; then
    _prefix="${_seg%"$_stripped"}"
    if [[ "$_prefix" =~ (^|[[:space:]])LEAN4_GUARDRAILS_BYPASS=1([[:space:]]|$) ]]; then
      BYPASS=1
    fi
  fi
  _stripped=$(_strip_optvals "$_stripped")
  _stripped=$(_unquote_tokens "$_stripped")
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

# Lean script invocation + stderr suppression guard.
# Rationale: hidden stderr from analysis scripts causes silent failures.
# This guard is intentionally non-bypassable.
_has_lean_script_token() {
  local s="$1"
  echo "$s" | grep -qE -- '(\$LEAN4_SCRIPTS/|\$\{LEAN4_SCRIPTS\}/|plugins/lean4/(lib/scripts|scripts)/|(^|[[:space:]])(\./)?(lib/scripts|scripts)/[^[:space:]]+\.(py|sh)\b)'
}

_strip_quoted_literals() {
  local s="$1"
  # Ignore redirection-like text inside quoted arguments.
  s=$(echo "$s" | sed -E 's/"([^"\\]|\\.)*"//g')
  s=$(echo "$s" | sed -E "s/'[^']*'//g")
  echo "$s"
}

_has_stderr_null_redirect() {
  local s="$1"
  s=$(_strip_quoted_literals "$s")
  if echo "$s" | grep -qE -- '(^|[[:space:]])(2>>?|&>>?)[[:space:]]*/dev/null([^[:alnum:]_./-]|$)'; then
    return 0
  fi
  if echo "$s" | grep -qE -- '(^|[[:space:]])([0-9]*>>?)[[:space:]]*/dev/null([^[:alnum:]_./-]|$)' \
    && echo "$s" | grep -qE -- '(^|[[:space:]])2>&1([^[:alnum:]_./-]|$)'; then
    return 0
  fi
  return 1
}

for _seg in "${RAW_SEGMENTS[@]}"; do
  if _has_lean_script_token "$_seg" && _has_stderr_null_redirect "$_seg"; then
    echo "BLOCKED (Lean guardrail): suppressed stderr on Lean script invocation hides real errors. Remove '/dev/null' redirection and rerun." >&2
    exit 2
  fi
done

# Collaboration-op policy enforcement.
# $1 = short label (e.g. "git push")
# $2 = user-facing message suffix
_check_collab_op() {
  local label="$1" msg="$2"
  case "$COLLAB_POLICY" in
    allow) return 0 ;;
    block)
      echo "BLOCKED (Lean guardrail): $label - $msg [collab_policy=block]" >&2
      exit 2
      ;;
    *)  # ask (default): confirmation-gated; bypass is the one-time confirmed rerun path
      if [[ $BYPASS -ne 1 ]]; then
        echo "BLOCKED (Lean guardrail): $label - $msg [collab_policy=ask, confirm then rerun]" >&2
        echo "  To proceed once, prefix with: LEAN4_GUARDRAILS_BYPASS=1" >&2
        exit 2
      fi
      ;;
  esac
}

# Classify git restore flag presence (long + short forms) into two
# integers passed back via the global _restore_staged / _restore_worktree.
# Long forms: --staged / --worktree. Short forms: -S / -W, including
# bundled short flags like -SW, -WS, -qS (git docs document the short
# aliases and bundling). Detection runs over the raw segment text and
# uses a `(^|\s)` boundary so substrings like `--no-staged` don't
# false-match the staged check.
_classify_restore_flags() {
  local s="$1"
  _restore_staged=0
  _restore_worktree=0
  if echo "$s" | grep -qE -- '(^|[[:space:]])--staged([[:space:]]|=|$)'; then _restore_staged=1; fi
  if echo "$s" | grep -qE -- '(^|[[:space:]])--worktree([[:space:]]|=|$)'; then _restore_worktree=1; fi
  # Short flag bundles: `-` (not preceded by alphanumeric) + sequence of
  # letters that contains S or W. Excludes long-form `--…` by requiring
  # the char after `-` to be a letter (not `-`).
  if echo "$s" | grep -qE -- '(^|[[:space:]])-[A-Za-z]*S[A-Za-z]*([[:space:]]|$)'; then _restore_staged=1; fi
  if echo "$s" | grep -qE -- '(^|[[:space:]])-[A-Za-z]*W[A-Za-z]*([[:space:]]|$)'; then _restore_worktree=1; fi
}

# Destructive-op policy enforcement (path-scoped blast radius).
# Same shape as _check_collab_op but governed by DESTRUCTIVE_POLICY.
# Used by the soft-gated cases below — operations that name an
# explicit pathset (one file, several files, a directory, etc.) but
# don't target the whole worktree. Whole-worktree destructive ops
# (reset --hard, clean -f, checkout ., restore .) bypass this helper
# and exit 2 unconditionally — see the dedicated block further down.
# $1 = short label, $2 = user-facing message suffix
_check_destructive_op() {
  local label="$1" msg="$2"
  case "$DESTRUCTIVE_POLICY" in
    allow) return 0 ;;
    block)
      echo "BLOCKED (Lean guardrail): $label - $msg [destructive_policy=block]" >&2
      exit 2
      ;;
    *)  # ask (default): confirmation-gated; bypass token allows one-shot
      if [[ $BYPASS -ne 1 ]]; then
        echo "BLOCKED (Lean guardrail): $label - $msg [destructive_policy=ask, confirm then rerun]" >&2
        echo "  To proceed once, prefix with: LEAN4_GUARDRAILS_BYPASS=1" >&2
        exit 2
      fi
      ;;
  esac
}

# --- Collaboration ops (policy-controlled) ---

# Block git push (not --dry-run, not stash push — exemptions scoped per-segment)
if seg_match git '[[:space:]]push([[:space:]]|$)' '--dry-run\b|\bstash\b.*\bpush\b'; then
  _check_collab_op "git push" "use /lean4:checkpoint, then push manually"
fi

# Block git commit --amend
if seg_match git '\bcommit\b.*--amend\b'; then
  _check_collab_op "git commit --amend" "proving workflow creates new commits for safe rollback"
fi

# Block gh pr create
if seg_match gh '\bpr\b.*\bcreate\b'; then
  _check_collab_op "gh pr create" "review first, then create PR manually"
fi

# ---------------------------------------------------------------------------
# Destructive ops: whole-worktree (HARD-BLOCK — non-bypassable)
# ---------------------------------------------------------------------------
# These wipe state across the whole worktree (or untracked files); reflog
# can't recover uncommitted edits and `clean -f` can't recover untracked
# files at all. No policy override; bypass token does not apply. The
# whole-worktree variants run BEFORE the soft-gated path-scoped variants
# below so a broad-blast pattern can't accidentally fall through into
# ask/allow territory.

# Whole-worktree pathspec variants for checkout. Detection generalized to
# match ANY whole-worktree pathspec token (`.`, `./`, `:/`, `:(top)`)
# appearing anywhere in the checkout segment, regardless of what comes
# between `checkout` and the pathspec. That subsumes:
#
#   git checkout .              git checkout HEAD .         (tree-ish form)
#   git checkout ./             git checkout main :/
#   git checkout -- .           git checkout HEAD -- .      (with `--`)
#   git checkout -- ./          git checkout HEAD -- ./
#   git checkout -- :/          git checkout -- :(top)
#   git checkout -f .           git checkout --ours .       (with options)
#   git checkout --theirs .     git checkout -m .
#
# Single regex: `\bcheckout\b.*\s<wp>(\s|$)` where `<wp>` is the pathspec
# alternation. The `.*` swallows any combination of refs and options
# before the whitespace-bounded pathspec token. Must run BEFORE soft-gate
# checks so option-prefixed whole-worktree pathspecs short-circuit there.
if seg_match git '\bcheckout\b.*\s(\.|\./|:/|:\(top\))(\s|$)'; then
  echo "BLOCKED (Lean guardrail): whole-worktree git checkout discards all changes. Commit or checkpoint first." >&2
  exit 2
fi

# git checkout --pathspec-from-file=... reads pathspecs from a file the
# guardrail can't inspect. The file could contain `.` or `:/` which would
# be a whole-worktree wipe. Hard-block conservatively — operators with a
# trustworthy paths file can stage the operation as explicit arguments.
if seg_match git '\bcheckout\b.*\s--pathspec-from-file([=[:space:]])'; then
  echo "BLOCKED (Lean guardrail): git checkout --pathspec-from-file reads paths from a file the guardrail can't inspect; could contain whole-worktree pathspecs. Pass explicit paths on the command line." >&2
  exit 2
fi

# Whole-worktree restore variants:
#   git restore .                  (whole-worktree)
#   git restore ./                 (same)
#   git restore :/                 (top-of-repo pathspec)
#   git restore --staged --worktree …  (restores both index and worktree)
#   git restore -SW <path>         (short form of --staged --worktree)
#   git restore --staged -W <path> (mixed long/short combined restore)
# But: pure `--staged` (or `-S`) without `--worktree` (or `-W`) is
# unstaging only — index-bounded, recoverable, never touches worktree.
# ALWAYS allowed regardless of path, so the unstaging exemption MUST
# be checked first, otherwise commands like `git restore --staged .`
# (legitimate "unstage everything") would be hard-blocked incorrectly.
# Flag detection covers long and short forms via _classify_restore_flags.
for _seg in "${SEGMENTS[@]}"; do
  echo "$_seg" | grep -qE '^git\b' || continue
  echo "$_seg" | grep -qE '\brestore\b' || continue
  _classify_restore_flags "$_seg"
  # Pure unstaging — always allowed, must come first.
  if [[ $_restore_staged -eq 1 && $_restore_worktree -eq 0 ]]; then
    continue
  fi
  # --pathspec-from-file in worktree-touching restore: the paths file is
  # opaque to the guardrail and could contain `.` or `:/`, which would be
  # a whole-worktree wipe with no warning. Hard-block conservatively;
  # pure-unstaging `--staged --pathspec-from-file=…` was already allowed
  # by the exemption above.
  if echo "$_seg" | grep -qE -- '--pathspec-from-file([=[:space:]])'; then
    echo "BLOCKED (Lean guardrail): git restore --pathspec-from-file reads paths from a file the guardrail can't inspect; could contain whole-worktree pathspecs. Pass explicit paths on the command line." >&2
    exit 2
  fi
  # Combined staged+worktree (any flag combo) — restores worktree too.
  if [[ $_restore_staged -eq 1 && $_restore_worktree -eq 1 ]]; then
    echo "BLOCKED (Lean guardrail): git restore --staged --worktree (or -SW) resets both index and worktree. Commit or checkpoint first." >&2
    exit 2
  fi
  # Whole-worktree pathspec — `.`, `./`, `:/`, `:(top)`.
  if echo "$_seg" | grep -qE '\brestore\b.*\s(\.|\./|:/|:\(top\))(\s|$)'; then
    echo "BLOCKED (Lean guardrail): git restore on whole-worktree pathspec discards all worktree changes. Commit or checkpoint first." >&2
    exit 2
  fi
done

# git reset --hard
if seg_match git '\breset\b.*--hard\b'; then
  echo "BLOCKED (Lean guardrail): git reset --hard. Commit or checkpoint first." >&2
  exit 2
fi

# git clean with -f/--force anywhere (deletes untracked files; not recoverable)
# Matches: -f, -fd, -fx, -nfd, --force, etc.
if seg_match git '\bclean\b.*(-[a-zA-Z]*f|--force)'; then
  echo "BLOCKED (Lean guardrail): git clean deletes untracked files. Commit or checkpoint first." >&2
  exit 2
fi

# git switch with force/discard-changes — throws away local modifications
# during branch switching. Reflog can't recover uncommitted edits.
# Matches `-f`, `--force`, and `--discard-changes` as standalone tokens.
# `--force-create` is intentionally NOT matched: it forces branch CREATION
# over an existing branch name, which doesn't touch the worktree state.
# The `(\s|$)` suffix on `--force` is what distinguishes it from
# `--force-create` (the latter is followed by `-`, not whitespace/EOL).
if seg_match git '\bswitch\b.*\s(-f|--force|--discard-changes)(\s|$)'; then
  echo "BLOCKED (Lean guardrail): git switch with --force / --discard-changes / -f discards uncommitted edits during branch switching. Commit or checkpoint first." >&2
  exit 2
fi

# git checkout -p|--patch without a path positional — interactive
# whole-worktree sweep. Same blast radius as `git checkout .` /
# `git checkout HEAD --` (rewrites every modified file the user says
# `y` to). Empirically verified (separate temp-repo probe) that both
# `yes y | git checkout -p` AND `yes y | git checkout -p HEAD` wipe
# every dirty file in the worktree — the interactive prompt isn't
# protection against piped stdin. Tier-1 hard-block, no bypass.
#
# Heuristic for "no path positional": no token in the segment contains
# `/`, `.`, or `:` after the leading non-flag char. With a path-like
# positional (`-p file.lean`, `-p HEAD docs/foo.lean`), defers to the
# pathspec-oriented flag soft-gate below.
for _seg in "${SEGMENTS[@]}"; do
  echo "$_seg" | grep -qE '^git\b' || continue
  echo "$_seg" | grep -qE '\bcheckout\b' || continue
  echo "$_seg" | grep -qE '\s(-p|--patch)(\s|$)' || continue
  # Path-like positional present → defer to soft-gate.
  if echo "$_seg" | grep -qE '(^|\s)[^-\s]\S*[/.:]\S*(\s|$)'; then
    continue
  fi
  echo "BLOCKED (Lean guardrail): git checkout -p / --patch without a path is an interactive whole-worktree sweep that pipes (yes y | …) can bypass. Commit or checkpoint first, then narrow to specific paths." >&2
  exit 2
done

# git checkout -f|--force — force-mode checkout. Order-insensitive
# loop so `-f` may appear anywhere in the option run (e.g.
# `git checkout -q -f main`, `--quiet --force main`, `-f --detach HEAD`,
# `-f -B tmp main` all hit the same branches as `-f main`).
#
# Three outcomes based on which positionals appear in the segment:
#
#   (a) `--` separator present → explicit path-restore form; defer to
#       the general `--` soft-gate below.
#   (b) Path-like positional present (token contains `/`, `.`, or `:`,
#       and isn't a whole-worktree pathspec — those were hard-blocked
#       earlier) → soft-gate as a path-scoped force-restore.
#   (c) Branch/ref-like positional present (token in `[A-Za-z0-9_@]
#       [A-Za-z0-9_@~^{}-]*` or the standalone `-` "previous branch"
#       shorthand — covers `main`, `HEAD`, `HEAD~3`, `HEAD@{1}`,
#       `@{-1}`, `@`, `-`) → hard-block: force branch checkout
#       discards uncommitted edits across the whole worktree (same
#       blast radius as `reset --hard`).
#   (d) Neither path-like nor branch/ref-like (e.g. bare `-f` or
#       `-f --quiet` with no positional) → fall through; git would
#       likely error anyway.
#
# Heuristic note: branch names containing `/` or `.` (e.g.
# `release/v1.0`) are deliberately classified as path-like and
# soft-gated. The trade-off prefers fewer false-positive hard-blocks
# over ref-name exhaustiveness; operators can still opt in via
# DESTRUCTIVE_POLICY=allow or the bypass token.
for _seg in "${SEGMENTS[@]}"; do
  echo "$_seg" | grep -qE '^git\b' || continue
  echo "$_seg" | grep -qE '\bcheckout\b' || continue
  echo "$_seg" | grep -qE '\s(-f|--force)(\s|$)' || continue
  # (a) `--` separator: defer to general soft-gate.
  if echo "$_seg" | grep -qE '\s--(\s|$)'; then
    continue
  fi
  # (b) Path-like positional present: soft-gate as path-scoped restore.
  if echo "$_seg" | grep -qE '(^|\s)[^-\s]\S*[/.:]\S*(\s|$)'; then
    _check_destructive_op "git checkout -f <path>" "force-restores the named path, discarding uncommitted edits"
    continue
  fi
  # (c) Branch/ref-like positional present: hard-block.
  if echo "$_seg" | grep -qE '\s([A-Za-z0-9_@][A-Za-z0-9_@~^{}-]*|-)(\s|$)'; then
    echo "BLOCKED (Lean guardrail): git checkout -f / --force <branch-or-ref> discards uncommitted edits across the whole worktree during branch switching. Commit or checkpoint first." >&2
    exit 2
  fi
done

# ---------------------------------------------------------------------------
# Destructive ops: path-scoped (SOFT-GATE via DESTRUCTIVE_POLICY)
# ---------------------------------------------------------------------------
# Bounded blast radius — the named pathset only (one file, several files,
# a subdirectory, etc.; whole-worktree pathspecs `.` / `./` / `:/` are
# excluded by the hard-block block above). Still loses uncommitted edits
# — reflog won't help — so default mode is `ask` (block unless bypass
# token), but the operator can opt into `allow` or paranoia-mode `block`
# via LEAN4_GUARDRAILS_DESTRUCTIVE_POLICY.

# git checkout -- <path…>   (one or more explicit path arguments after `--`)
if seg_match git '\bcheckout\b.*\s--\s'; then
  _check_destructive_op "git checkout --" "discards uncommitted edits in the named path(s)"
fi

# git checkout <tree-ish> <path…>   (no `--` separator; restore from tree-ish)
# Matches forms like `git checkout HEAD file.lean`,
# `git checkout main src/foo.lean`, `git checkout -q HEAD file.lean`,
# `git checkout --quiet HEAD a.lean b.lean`. Per-segment loop so
# non-destructive flag prefixes (`-q`, `--quiet`, etc.) can interleave
# with the positionals without forcing the regex to anchor `\S` to
# `\s+` immediately after `checkout`.
#
# Explicit skip list for branch-creation / detach flags (`-b`, `-B`,
# `--orphan`, `--detach`): those forms take a branch name as their
# next argument, not a tree-ish + path, and they aren't path-restore.
# `-f` / `--force` is also skipped — the force-mode loop above already
# applies the (stricter) classification for that case.
#
# Whole-worktree pathspec variants were hard-blocked earlier, so this
# only catches bounded paths.
for _seg in "${SEGMENTS[@]}"; do
  echo "$_seg" | grep -qE '^git\b' || continue
  echo "$_seg" | grep -qE '\bcheckout\b' || continue
  # Branch-creation / detach forms — not path-restore.
  if echo "$_seg" | grep -qE '\s(-b|-B|--orphan|--detach)(\s|$)'; then
    continue
  fi
  # Force mode handled by the dedicated loop above (stricter classification).
  if echo "$_seg" | grep -qE '\s(-f|--force)(\s|$)'; then
    continue
  fi
  # Two non-flag positionals with optional flag interleaving.
  if echo "$_seg" | grep -qE '\bcheckout\b\s+(-\S+\s+)*[^-\s]\S*\s+(-\S+\s+)*[^-\s]\S*'; then
    _check_destructive_op "git checkout <tree-ish> <path>" "restores the named path(s) from the tree-ish, discarding uncommitted edits"
  fi
done

# git checkout {--ours|--theirs|--conflict=…} <path…>
# Merge-conflict resolution flags that take pathspecs. With a path
# argument, these restore that path's "ours"/"theirs" version or
# re-create the merge conflict, discarding uncommitted edits in that
# path. Whole-worktree variants (`--ours .`) already short-circuited
# via the hard-block above.
#
# Note: bare `git checkout --ours` (no path) would soft-gate spuriously
# but git would error on it anyway, so acceptable.
#
# Limitation: short-form `-m` is NOT included here. The shared
# _strip_optvals normalization (needed for `git commit -m "msg"`
# false-positive avoidance in the collab checks) strips `-m <value>`
# from segments before pattern matching, so `git checkout -m <path>`
# arrives at the checkout checks with `-m <path>` already removed.
# Catching `-m` in checkout context would require splitting the
# normalization pipeline per-command; deferred. The long form
# `--merge` IS covered (below) — _strip_optvals only handles
# `--(message|file|body|title)` long flags, not `--merge`.
if seg_match git '\bcheckout\b.*\s(--ours|--theirs|-2|-3|--merge|--conflict(=\S+)?)(\s|$)'; then
  _check_destructive_op "git checkout <restore-flag>" "restores the named path(s) from the merge-conflict side, discarding uncommitted edits"
fi

# Pathspec-oriented checkout flags. When any of these appears in a
# checkout segment, the operation is meaningfully a path restore even
# with a single positional — distinguishing it from the deliberately-
# deferred bare `git checkout file.lean` ambiguity. Empirically verified
# (separate temp-repo probe) that all of these discard a dirty worktree
# file when used with a path positional:
#
#   git checkout --ignore-skip-worktree-bits f   → DISCARDED
#   git checkout --no-overlay f                  → DISCARDED
#   git checkout --overlay f                     → DISCARDED
#   git checkout --recurse-submodules f          → DISCARDED
#   yes y | git checkout -p f                    → DISCARDED
#   yes y | git checkout --patch f               → DISCARDED
#
# `-p` / `--patch` is interactive (per-hunk y/n), but interactivity
# is not absolute protection — pipes like `yes y | …` bypass it.
# Soft-gate consistently regardless of whether stdin is a TTY.
#
# `--recurse-submodules` is also valid with branch switching; for the
# branch case (`git checkout --recurse-submodules main`), git itself
# refuses a dirty switch without `-f` (PRESERVED in the probe), so a
# soft-gate here is at worst an extra confirmation prompt before a
# no-op — the conservative trade-off is preferred over a silent
# destructive false-negative.
if seg_match git '\bcheckout\b.*\s(--ignore-skip-worktree-bits|--no-overlay|--overlay|--recurse-submodules|-p|--patch)(\s|$)'; then
  _check_destructive_op "git checkout <pathspec-flag> <path>" "restores the named path(s) from index, discarding uncommitted edits"
fi

# Path-scoped `git checkout -f <path>` was handled by the force-mode
# loop above (outcome (b)) so its policy gate fires before this point.
# Falling through here means the `--` form took outcome (a) and will be
# matched by the general `--` soft-gate (already above).

# git checkout ./file or git checkout :/file or git checkout ../path
# Single positional with an explicit path prefix. Distinguishes
# obviously-a-path arguments from branch names; matches `./file.lean`,
# `./.env`, `./.github/workflows/foo.yml`, `:/file.lean`,
# `../subdir/foo.lean`, etc. Whole-worktree-pathspec variants (`./` /
# `:/` standalone) already short-circuited via the hard-block, so the
# `[^\s]+` suffix only excludes the bare prefix without forbidding
# dotfile-style paths.
# Optional flag prefix (`\s+(-\S+\s+)*`) so `git checkout -q ./file.lean`,
# `git checkout --quiet :/foo.lean`, etc. soft-gate too.
if seg_match git '\bcheckout\b\s+(-\S+\s+)*(\.{1,2}/|:/?)[^\s]+'; then
  _check_destructive_op "git checkout <path>" "restores the named path from index, discarding uncommitted edits"
fi

# git restore <path…>       (worktree-only; pure --staged/-S unstaging is allowed)
for _seg in "${SEGMENTS[@]}"; do
  echo "$_seg" | grep -qE '^git\b' || continue
  echo "$_seg" | grep -qE '\brestore\b' || continue
  _classify_restore_flags "$_seg"
  if [[ $_restore_staged -eq 1 && $_restore_worktree -eq 0 ]]; then
    continue  # pure unstaging — always allowed
  fi
  _check_destructive_op "git restore" "discards uncommitted edits in the named path(s)"
done

# All checks passed — resolve deferred bypass or allow normally
exit 0

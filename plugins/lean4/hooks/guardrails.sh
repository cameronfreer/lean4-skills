#!/usr/bin/env bash
set -euo pipefail

# Override: skip all guardrails if explicitly disabled
[[ "${LEAN4_GUARDRAILS_DISABLE:-}" == "1" ]] && exit 0

# Lean project detection: walk ancestors for lakefile.lean, lean-toolchain, lakefile.toml
# No depth cap — deep monorepos are common. Terminates at the filesystem root by
# fixed point (dirname of any root returns itself): "$dir" == "/" alone never
# fires on a Windows/Git-Bash drive-letter path, which reaches a non-"/" fixed
# point such as "C:" (Git-Bash reduces "C:/" to "C:", then dirname "C:" == "C:")
# and wedged the walk in an infinite loop (issue #164).
is_lean_project() {
  local dir="$1" parent
  [[ -d "$dir" ]] || return 1
  while true; do
    [[ -f "$dir/lakefile.lean" || -f "$dir/lean-toolchain" || -f "$dir/lakefile.toml" ]] && return 0
    parent=$(dirname "$dir")
    [[ "$parent" == "$dir" ]] && break   # reached a fixed point (/, C:, //server, .)
    dir="$parent"
  done
  return 1
}

# Read JSON input from stdin under a hard ~1s bound (issue #164). Fail open on
# an interactive stdin — a hook invoked without a piped payload has nothing to
# guard, and reading a TTY wedged the whole Bash call (the upstream TTY bug adds
# ~5s to every command). For a pipe, a backgrounded `cat` streams whatever is
# available; a killer ends it after 1s if the writer never sends EOF. 1s keeps
# the read comfortably within Claude Code's 5s hook deadline, and a payload
# already in the pipe is captured and enforced.
# Notes: `read -t` is not used — Bash 3.2 does not save partial input on its
# timeout, so a held-open pipe would lose the payload there. `cat <&3` is
# required because an async command in a non-interactive shell otherwise gets
# stdin from /dev/null. No GNU `timeout` (Bash-3.2 portability).
[[ -t 0 ]] && exit 0
INPUT="$(
  exec 3<&0
  cat <&3 & _gr_cat=$!
  ( sleep 1; kill "$_gr_cat" 2>/dev/null ) >/dev/null 2>&1 & _gr_killer=$!
  wait "$_gr_cat" 2>/dev/null || true
  kill "$_gr_killer" 2>/dev/null || true
  wait "$_gr_killer" 2>/dev/null || true
)"

# Parse command with jq, fall back to python3; default empty on parse failure.
# Working directory: .cwd → .tool_input.cwd → .tool_input.workdir → $PWD
# (fails open: parse failure → empty → falls through to the $PWD default).
#
# jq path: two cheap jq calls (unchanged). No-jq path (common on Windows/
# Git-Bash): ONE python3 startup emits both fields so each guarded call pays
# interpreter startup once, not twice (#193). Framing is line-count prefixed
# so a cwd containing newlines (legal on Unix) round-trips exactly:
#   <N>\n<cwd, spanning N lines>\n<command, the rest>
# Both fields have trailing newlines stripped, matching what the old
# two-call path's command substitutions did. The frame is read and written
# as raw UTF-8 bytes (stdin.buffer / stdout.buffer): a native Windows
# CPython's text-mode stdout would otherwise turn the LF separators into
# CRLF and the shell would reject the framing (and fail open).
if command -v jq >/dev/null 2>&1; then
  COMMAND=$(echo "$INPUT" | jq -r '.tool_input.command // .command // empty' 2>/dev/null) || COMMAND=""
else
  _parsed=$(echo "$INPUT" | python3 -c '
import json, sys
try:
    data = json.loads(sys.stdin.buffer.read())
    ti = data.get("tool_input") or {}
    cwd = str(data.get("cwd") or ti.get("cwd") or ti.get("workdir") or "")
    cmd = str(ti.get("command") or data.get("command") or "")
except Exception:
    cwd, cmd = "", ""
cwd = cwd.rstrip("\n")
cmd = cmd.rstrip("\n")
frame = "%d\n%s\n%s" % (cwd.count("\n") + 1, cwd, cmd)
sys.stdout.buffer.write(frame.encode("utf-8"))
' 2>/dev/null) || _parsed=""
  TOOL_CWD=""
  COMMAND=""
  _n="${_parsed%%$'\n'*}"
  if [[ "$_parsed" == *$'\n'* && "$_n" =~ ^[0-9]+$ ]]; then
    _rest="${_parsed#*$'\n'}"
    # Peel N lines off as the cwd; whatever remains is the command. (An empty
    # command leaves no trailing separator — command substitution strips it —
    # so the last cwd line may be the whole remainder.)
    while [[ "$_n" -gt 0 ]]; do
      if [[ "$_rest" == *$'\n'* ]]; then
        _line="${_rest%%$'\n'*}"
        _rest="${_rest#*$'\n'}"
      else
        _line="$_rest"
        _rest=""
      fi
      if [[ "$_n" -eq 1 ]]; then
        TOOL_CWD="${TOOL_CWD}${_line}"
      else
        TOOL_CWD="${TOOL_CWD}${_line}"$'\n'
      fi
      _n=$((_n - 1))
    done
    COMMAND="$_rest"
  fi
fi

# If no command, allow
[ -z "$COMMAND" ] && exit 0

# Fast rejection of irrelevant input (issue #208). Every guarded operation
# below needs one of these spellings SOMEWHERE in the raw command text —
# `git`/`gh` as a word (also after `/usr/bin/`, inside `bash -c '…'`, after
# `sudo`/`env`/VAR= prefixes: normalization only removes text, never
# creates these words), or a Lean-script token (the stderr-suppression
# guard). A command with none of them cannot match any check, so it is
# allowed without parsing. This is a superset filter — a large document
# that merely mentions `git` still goes through the full, heredoc-aware
# parser below (which treats literal heredoc bodies as data).
_GUARDED_VOCAB='(^|[^[:alnum:]_])(git|gh)([^[:alnum:]_]|$)|LEAN4_SCRIPTS|plugins/lean4/|(^|[[:space:]/])(lib/scripts|scripts)/|lean4-skills-'
if ! [[ "$COMMAND" =~ $_GUARDED_VOCAB ]]; then
  exit 0
fi

if command -v jq >/dev/null 2>&1; then
  TOOL_CWD=$(echo "$INPUT" | jq -r '(.cwd // .tool_input.cwd // .tool_input.workdir) // empty' 2>/dev/null) || TOOL_CWD=""
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
#                                 Per-op collab policies (v4.5.2+):
#                                   PUSH_POLICY:       git push
#                                   AMEND_POLICY:      git commit --amend
#                                   PR_CREATE_POLICY:  gh pr create
#                                 plus DESTRUCTIVE_POLICY for path-scoped
#                                 local data loss (checkout -- <path>,
#                                 restore <path>; smaller blast radius
#                                 than whole-worktree wipes `.` / `:/`).
#
#                                 Back-compat: legacy
#                                 LEAN4_GUARDRAILS_COLLAB_POLICY is
#                                 honored as the fallback for any per-op
#                                 collab policy that isn't explicitly
#                                 set (so users who set
#                                 COLLAB_POLICY=allow / =block keep
#                                 their existing semantics).
#
#   3. HARD-BLOCK (below)       — non-bypassable, no policy override.
#                                 reset --hard, clean -f/-fd/-fdx,
#                                 checkout ., restore ., checkout -- .,
#                                 AND (v4.5.2+) push --force /
#                                 --force-with-lease / --mirror /
#                                 --delete / `<remote> :<ref>` ref-delete
#                                 syntax. Blast radius is unbounded; for
#                                 force-push it's shared-history rewrite
#                                 (not just local). Escape hatch:
#                                 LEAN4_GUARDRAILS_DISABLE=1 for that
#                                 specific command.
#
# Each soft-gate policy independently accepts host | ask | allow | block:
#   host:  exit 0 — defer to Claude Code's native Bash permission rule
#          (recommended default; lets Claude Code "ask once, remember").
#   ask:   require human confirmation via one-shot bypass token.
#   allow: permit without bypass token (user explicitly opted in).
#   block: block even with bypass token (extra paranoia).

## Per-op collab policies (v4.5.2+).
#
# Each soft-gated collaboration op (push, --amend, gh pr create) has its
# own policy var, accepting `host` | `ask` | `allow` | `block`. Defaults
# are `host`, which means the hook exits 0 and Claude Code's native
# `Bash(...)` permission rule handles the "ask once, remember" UX
# instead of the hook fighting it with exit-2 + bypass-token retries.
#
# Back-compat: LEAN4_GUARDRAILS_COLLAB_POLICY (the legacy bundled var)
# is honored as the fallback for any per-op policy that isn't explicitly
# set. So users who already configured COLLAB_POLICY=allow / =block keep
# their existing semantics on the soft-gate path; new users get the
# `host` default automatically.
COLLAB_POLICY="${LEAN4_GUARDRAILS_COLLAB_POLICY:-}"
PUSH_POLICY="${LEAN4_GUARDRAILS_PUSH_POLICY:-${COLLAB_POLICY:-host}}"
PR_CREATE_POLICY="${LEAN4_GUARDRAILS_PR_CREATE_POLICY:-${COLLAB_POLICY:-host}}"
AMEND_POLICY="${LEAN4_GUARDRAILS_AMEND_POLICY:-${COLLAB_POLICY:-host}}"
# Validate each. Two distinct fallbacks:
#   - UNSET vars already resolved to `host` (the friendly default) via the
#     parameter-expansion chain above, before validation runs.
#   - SET but invalid values (typos like `alow`, `bock`, `yolo`, or
#     legitimate values that get corrupted in env propagation) fall back
#     to `ask` — the safer choice. A typo shouldn't silently relax the
#     plugin-level guardrail; it should ask. This means
#     `LEAN4_GUARDRAILS_PUSH_POLICY=alow` blocks rather than allowing.
# ${!_p} indirect expansion works on Bash 3.2+. Writing back the
# validated value still uses eval since indirect *assignment* via the
# same name isn't supported by `${!_p}=...` on Bash 3.2.
for _p in PUSH_POLICY PR_CREATE_POLICY AMEND_POLICY; do
  case "${!_p}" in
    host|ask|allow|block) ;;
    *) eval "$_p=ask" ;;
  esac
done
unset _p

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

# Quote-aware segment splitting (issue #208): ONE awk pass over the whole
# command (no per-character Bash loop, no per-line subprocesses) that splits
# on unquoted &&, ||, ;, | and newlines, tracks '…', "…", $(…), `…`, and
# applies explicit heredoc semantics:
#   * `cmd <<'EOF' … EOF` / `<<"EOF"` / `<<E'OF'` / `<<\EOF` (any quoting in
#     the delimiter word): the body is literal data — skipped, unless the
#     RECEIVING PIPELINE (bounded by the real `;`/`&&`/`||`/newline
#     separators) has a shell as its normalized COMMAND WORD in some stage
#     (`bash <<'EOF'`, `bash<<'EOF'`, `'bash' <<'EOF'`, `/bin/bash <<'EOF'`,
#     `cat <<'EOF' | sudo bash`, `X='one two' bash <<'EOF'`, `env -u X bash
#     <<'EOF'`, `2>/dev/null bash <<'EOF'`, `env -S 'bash -x' <<'EOF'`; NOT
#     an argument named bash (`cat - bash <<'EOF'`) and NOT a separate command
#     (`cat <<'EOF'; bash -c true`)); a receiver that cannot be identified
#     (`"$SHELL" <<'EOF'`, `$(which bash) <<'EOF'`) is treated as executable —
#     failing to identify it is never proof that the body is data; then the
#     body is tokenized like any command; several heredocs
#     queued on one line each keep their own receiver (`cat <<'A'; bash <<'B'`
#     checks the B body and keeps the A body as data);
#   * a shell comment (`# …` at a word boundary) runs to the newline and
#     contains no operators — `echo hi # <<EOF` opens no heredoc;
#   * a double-quoted delimiter follows double-quote escape rules (`"E\OF"`
#     names `E\OF`); a backslash-newline inside an unquoted or double-quoted
#     delimiter is a line continuation (`<<EO\` + newline + `F` names `EOF`,
#     still unquoted); an ANSI-C-quoted delimiter (`<<$'EOF'`) names `EOF`
#     (quoted); a delimiter with an unsupported escape consumes NO body — the
#     following lines stay checkable rather than being taken as data;
#   * in an unquoted heredoc body a backslash-newline joins physical lines
#     before the terminator is compared (`EO\` + newline + `F` terminates an
#     unquoted `<<EOF`); a quoted heredoc is compared line by line;
#   * `exec` and the compound-command keywords a command may follow (`then`,
#     `do`, `else`, `elif`, `if`, `while`, `until`, `time`, `!`, `{`) are
#     transparent when finding the receiver (`exec bash <<'EOF'`, `if true;
#     then bash <<'EOF'`); other compound keywords make the receiver
#     unidentifiable, i.e. conservatively executable;
#   * `cmd <<EOF … EOF` (unquoted delimiter): the body undergoes expansion, so
#     its $(…) and `…` substitutions are executable — those are tokenized
#     (quote-aware: a quoted `)` does not end a substitution); the rest of the
#     body is data;
#   * `<<-` strips leading tabs from the terminator; `<<<` is a here-string,
#     not a heredoc; several heredocs on one line are consumed in order; an
#     unterminated body runs to the end of the input;
#   * the command after the terminator line is checked as usual.
# Segments are emitted separated by \036 (record separator); newlines inside
# a segment (quoted) become spaces so every pattern below sees one line.
# POSIX awk only (BSD awk on macOS, mawk, gawk); Bash 3.2 reads with `read -d`.
_GR_AWK='
function emit(seg) {
  gsub(/\n/, " ", seg)
  sub(/^[ \t]+/, "", seg)
  if (seg != "") printf "%s\036", seg
}
function skip_quoted(body, i, len,   c) {
  # body[i] is an opening quote; return the index just past its closing quote
  c = substr(body, i, 1); i++
  if (c == "\047") { while (i <= len && substr(body, i, 1) != "\047") i++ }
  else { while (i <= len && substr(body, i, 1) != "\"") { if (substr(body, i, 1) == "\\") i++; i++ } }
  return i + 1
}
function subst_scan(body,   i, len, c, depth, start) {
  # tokenize the $(…) and `…` substitutions of an unquoted heredoc body;
  # quote-aware inside $(…) so a quoted ")" does not end the substitution
  len = length(body); i = 1
  while (i <= len) {
    c = substr(body, i, 1)
    if (c == "\\") { i += 2; continue }
    if (c == "$" && substr(body, i + 1, 1) == "(") {
      depth = 1; start = i + 2; i += 2
      while (i <= len && depth > 0) {
        c = substr(body, i, 1)
        if (c == "\\") { i += 2; continue }
        if (c == "\047" || c == "\"") { i = skip_quoted(body, i, len); continue }
        if (c == "(") depth++
        else if (c == ")") depth--
        i++
      }
      tokenize(substr(body, start, i - 1 - start))
      continue
    }
    if (c == "`") {
      start = i + 1; i++
      while (i <= len && substr(body, i, 1) != "`") { if (substr(body, i, 1) == "\\") i++; i++ }
      tokenize(substr(body, start, i - start))
      i++
      continue
    }
    i++
  }
}
function is_shell_word(w) {
  sub(/.*\//, "", w)                       # /bin/bash -> bash
  return (w == "bash" || w == "sh" || w == "zsh" || w == "dash" || w == "ksh")
}
function wrapper_takes_operand(wrapper, flag) {
  # options of the supported wrappers that take a separate operand
  if (wrapper == "sudo") return flag ~ /^-(u|g|p|C|h|U|r|t|D|R|T)$/
  if (wrapper == "env") return flag ~ /^(-u|-C|--unset|--chdir)$/
  return 0
}
function next_word(stage, i,   len, c, w) {
  # one complete shell word starting at i (leading blanks skipped): quotes
  # and backslashes removed; stops at blanks and operators. Side channels:
  # _nw_i = index after the word, _nw_q = any quoting, _nw_qname = quoting
  # before the first "=" (so X=\047a b\047 is still an assignment), _nw_exp =
  # the word contains ACTIVE expansion ($ or backtick outside single quotes)
  # — never resolved, only recorded
  len = length(stage); _nw_q = 0; _nw_qname = 0; _nw_eq = 0; _nw_exp = 0; w = ""
  while (i <= len && substr(stage, i, 1) ~ /[ \t]/) i++
  while (i <= len) {
    c = substr(stage, i, 1)
    if (c ~ /[ \t|&;<>()]/) break
    if (c == "\047") { _nw_q = 1; if (!_nw_eq) _nw_qname = 1; i++; while (i <= len && substr(stage, i, 1) != "\047") { w = w substr(stage, i, 1); i++ }; i++; continue }
    if (c == "\"") {
      _nw_q = 1; if (!_nw_eq) _nw_qname = 1; i++
      while (i <= len && substr(stage, i, 1) != "\"") {
        c = substr(stage, i, 1)
        if (c == "\\") { if (substr(stage, i + 1, 1) == "\n") { i += 2; continue }; i++; w = w substr(stage, i, 1); i++; continue }
        if (c == "$" || c == "`") _nw_exp = 1        # active inside double quotes
        w = w c; i++
      }
      i++; continue
    }
    if (c == "\\") {
      if (substr(stage, i + 1, 1) == "\n") { i += 2; continue }   # line continuation: no characters
      _nw_q = 1; if (!_nw_eq) _nw_qname = 1; i++; w = w substr(stage, i, 1); i++; continue
    }
    if (c == "$" || c == "`") _nw_exp = 1            # active expansion (unquoted)
    if (c == "=" && !_nw_eq) _nw_eq = length(w) + 1
    w = w c; i++
  }
  _nw_i = i
  return w
}
function stage_cmd_word(stage,   len, i, c, w, bw, flag, op) {
  # the normalized command word of one pipeline stage: leading redirections
  # ([n]>file, [n]>>file, [n]<file, <<WORD, <<<word, [n]>&m, &>file) and
  # VAR=value assignments are skipped; the sudo/env/command wrappers are
  # skipped with their options and the options\047 operands (one complete
  # shell word each); env -S / --split-string SUPPLY the command through
  # their operand, which is parsed as the command text. Returns "" when no
  # command word can be identified (the caller treats that conservatively).
  len = length(stage); i = 1
  while (i <= len) {
    while (i <= len && substr(stage, i, 1) ~ /[ \t]/) i++
    if (i > len) return ""
    c = substr(stage, i, 1)
    if (c ~ /[0-9]/ && substr(stage, i) ~ /^[0-9]+[<>]/) { while (substr(stage, i, 1) ~ /[0-9]/) i++; c = substr(stage, i, 1) }
    if (c == "<" || c == ">" || (c == "&" && substr(stage, i + 1, 1) == ">")) {
      # a redirection: skip the operator, then its target (a dup target
      # &N / &- has no word; a file, or a heredoc/here-string word, has one)
      if (c == "&") i++
      while (i <= len && substr(stage, i, 1) ~ /[<>]/) i++
      if (substr(stage, i, 1) == "-" && substr(stage, i - 1, 2) == "<-") i++   # <<-
      if (substr(stage, i, 1) == "&") { i++; while (i <= len && substr(stage, i, 1) ~ /[0-9-]/) i++ }
      else { w = next_word(stage, i); i = _nw_i }
      continue
    }
    if (c ~ /[|&;()]/) return ""
    w = next_word(stage, i); i = _nw_i; _cw_exp = _nw_exp
    if (w == "") return ""
    if (!_nw_q && !_nw_exp) {
      # shell prefixes that are transparent to the command word: exec and
      # the compound-command keywords a command may directly follow
      if (w == "exec" || w == "then" || w == "do" || w == "else" || w == "elif" || w == "if" || w == "while" || w == "until" || w == "time" || w == "!" || w == "{") continue
      # other compound keywords: the receiver is not identifiable here — the
      # caller treats that conservatively (executable), never as data
      # (the last keyword is the bash-4 coprocess one, matched by regex so the
      # Bash-3.2 portability lint does not see the literal token — this is a
      # string compared against the COMMAND being checked, never executed)
      if (w == "case" || w == "for" || w == "select" || w == "function" || w ~ /^cop[r]oc$/) return ""
    }
    if (!_nw_qname && !_nw_exp && w ~ /^[A-Za-z_][A-Za-z0-9_]*=/) continue   # VAR=value prefix
    bw = w; sub(/.*\//, "", bw)                                  # /usr/bin/env -> env
    if (!_nw_exp && (bw == "sudo" || bw == "env" || bw == "command")) {
      # a literal wrapper name — quoted or not (\047env\047 names env) — but
      # never an expanded one
      while (i <= len) {
        while (i <= len && substr(stage, i, 1) ~ /[ \t]/) i++
        if (substr(stage, i, 1) != "-") break
        flag = next_word(stage, i); i = _nw_i
        if (bw == "env" && (flag == "-S" || flag == "--split-string")) { op = next_word(stage, i); if (_nw_exp) { _cw_exp = 1; return op }; return stage_cmd_word(op) }
        if (bw == "env" && flag ~ /^--split-string=/) { sub(/^--split-string=/, "", flag); return stage_cmd_word(flag) }
        if (wrapper_takes_operand(bw, flag)) { op = next_word(stage, i); i = _nw_i }
      }
      continue
    }
    return w
  }
  return ""
}
function pipeline_feeds_shell(text,   n, parts, k, i, len, c, stage, in_sq, in_dq) {
  # the pipeline that RECEIVES the heredoc (its real boundaries: from the
  # previous ; && || or line start to the next ; && || or newline): true iff
  # the command word of any stage is a shell — `bash<<EOF`, a quoted bash word,
  # `/bin/bash <<EOF`, `cat <<EOF | sudo bash`; not `cat - bash <<EOF` (an
  # argument) and not a separate command after `;`
  len = length(text); stage = ""; in_sq = 0; in_dq = 0
  for (i = 1; i <= len; i++) {
    c = substr(text, i, 1)
    if (in_sq) { stage = stage c; if (c == "\047") in_sq = 0; continue }
    if (in_dq) { if (c == "\\") { stage = stage c substr(text, i + 1, 1); i++; continue }; stage = stage c; if (c == "\"") in_dq = 0; continue }
    if (c == "\047") { in_sq = 1; stage = stage c; continue }
    if (c == "\"") { in_dq = 1; stage = stage c; continue }
    if (c == "\\") { stage = stage c substr(text, i + 1, 1); i++; continue }
    if (c == "|" && substr(text, i + 1, 1) != "|") { if (stage_is_receiver(stage)) return 1; stage = ""; continue }
    stage = stage c
  }
  return stage_is_receiver(stage)
}
function stage_is_receiver(stage,   cw) {
  # a stage receives executable input iff its command word is a shell — or
  # cannot be identified at all (an empty word in a non-blank stage, or a
  # word with active expansion ANYWHERE: "$SHELL", /bin/$SH, $(which bash),
  # `printf bash` — recorded by next_word, never resolved): failing
  # to identify the receiver is never taken as proof that the body is data
  if (stage !~ /[^ \t]/) return 0
  _cw_exp = 0
  cw = stage_cmd_word(stage)
  if (cw == "" || _cw_exp) return 1          # unidentified, or produced by expansion anywhere in the word
  return is_shell_word(cw)
}
function tokenize(cmd,   i, len, c, nc, pc, seg, in_sq, in_dq, in_bt, paren, hn, hw, hq, hdash, hunsup, hstart, hend, k, w, q, line_start, pipe_start, body, rest, term, t, nl, lstart, found, hd, hbad, joined) {
  len = length(cmd); i = 1; seg = ""; in_sq = 0; in_dq = 0; in_bt = 0; paren = 0; hn = 0; line_start = 1; pipe_start = 1
  while (i <= len) {
    c = substr(cmd, i, 1); nc = substr(cmd, i + 1, 1)
    if (c == "#" && !in_sq && !in_dq && !in_bt && paren == 0) {
      # a shell comment starts at a word boundary (line/segment start or after
      # whitespace/operators) and runs to the newline — nothing in it is an
      # operator; a # inside a word (a#b) or inside quotes is literal
      pc = (i > 1) ? substr(cmd, i - 1, 1) : ""
      if (pc == "" || pc ~ /[ \t\n;|&(]/) {
        while (i <= len && substr(cmd, i, 1) != "\n") i++
        continue
      }
    }
    if (in_sq) { seg = seg c; if (c == "\047") in_sq = 0; i++; continue }
    if (in_dq) {
      if (c == "\\" && nc != "") { seg = seg c nc; i += 2; continue }
      seg = seg c; if (c == "\"") in_dq = 0; i++; continue
    }
    if (in_bt) {
      if (c == "\\" && nc != "") { seg = seg c nc; i += 2; continue }
      seg = seg c; if (c == "`") in_bt = 0; i++; continue
    }
    if (paren > 0) {
      if (c == "\\" && nc != "") { seg = seg c nc; i += 2; continue }
      seg = seg c
      if (c == "\047") in_sq = 1; else if (c == "\"") in_dq = 1
      else if (c == "(") paren++; else if (c == ")") paren--
      i++; continue
    }
    if (c == "\\" && nc != "") { seg = seg c nc; i += 2; continue }
    if (c == "\047") { in_sq = 1; seg = seg c; i++; continue }
    if (c == "\"") { in_dq = 1; seg = seg c; i++; continue }
    if (c == "$" && nc == "(") { paren++; seg = seg c nc; i += 2; continue }
    if (c == "`") { in_bt = 1; seg = seg c; i++; continue }
    if (c == "<" && nc == "<" && substr(cmd, i + 2, 1) == "<") {
      seg = seg "<<<"; i += 3; continue   # here-string: a complete operator, not a heredoc
    }
    if (c == "<" && nc == "<") {
      # heredoc operator: parse the delimiter word with shell quote removal
      # (EOF, "EOF", E"OF", \EOF, E\OF … all name EOF; any quoting => literal body)
      seg = seg "<<"; i += 2
      hd = 0; if (substr(cmd, i, 1) == "-") { hd = 1; seg = seg "-"; i++ }
      while (substr(cmd, i, 1) == " " || substr(cmd, i, 1) == "\t") { seg = seg " "; i++ }
      q = 0; w = ""; hbad = 0
      while (i <= len) {
        c = substr(cmd, i, 1)
        if (c == "$" && substr(cmd, i + 1, 1) == "\047") {
          # ANSI-C quoting (dollar-single-quote): quoted delimiter; an escaped
          # backslash and an escaped quote are translated,
          # any other escape is unsupported -> the heredoc is handled
          # conservatively (no body is consumed: everything stays checkable)
          q = 1; i += 2
          while (i <= len && substr(cmd, i, 1) != "\047") {
            c = substr(cmd, i, 1)
            if (c == "\\") {
              nc = substr(cmd, i + 1, 1)
              if (nc == "\\" || nc == "\047") { w = w nc; i += 2; continue }
              hbad = 1
            }
            w = w c; i++
          }
          i++; continue
        }
        if (c == "$" && substr(cmd, i + 1, 1) == "\"") { i++; continue }   # $"…" (locale): as "…"
        if (c == "\047") { q = 1; i++; while (i <= len && substr(cmd, i, 1) != "\047") { w = w substr(cmd, i, 1); i++ }; i++; continue }
        if (c == "\"") {
          # double-quote escape rules: a backslash is removed only before
          # \\ " $ ` (and a newline); otherwise it is part of the delimiter
          q = 1; i++
          while (i <= len && substr(cmd, i, 1) != "\"") {
            if (substr(cmd, i, 1) == "\\" && substr(cmd, i + 1, 1) == "\n") { i += 2; continue }   # continuation
            if (substr(cmd, i, 1) == "\\" && substr(cmd, i + 1, 1) ~ /[\\"$`]/) i++
            w = w substr(cmd, i, 1); i++
          }
          i++; continue
        }
        if (c == "\\") {
          # backslash-newline is a line continuation: both characters vanish
          # and the delimiter stays UNQUOTED (body substitutions stay active)
          if (substr(cmd, i + 1, 1) == "\n") { i += 2; continue }
          q = 1; i++; w = w substr(cmd, i, 1); i++; continue
        }
        if (c ~ /[ \t\n;|&<>()]/) break
        w = w c; i++
      }
      hn++; hw[hn] = w; hq[hn] = q; hdash[hn] = hd; hunsup[hn] = hbad
      hstart[hn] = pipe_start; hend[hn] = 0      # each heredoc keeps ITS receiving pipeline
      seg = seg (q ? "\047" w "\047" : w)
      continue
    }
    if (c == "\n") {
      if (hn > 0) {
        emit(seg); seg = ""
        rest = substr(cmd, i + 1)
        for (k = 1; k <= hn; k++) {
          t = substr(cmd, hstart[k], (hend[k] ? hend[k] : i) - hstart[k])   # the receiving pipeline of THIS heredoc
          # consume body lines up to the terminator (or the end of input)
          body = ""; found = 0; lstart = 1
          if (hunsup[k]) { continue }   # unsupported delimiter syntax: consume nothing
          while (lstart <= length(rest)) {
            # one logical line: in an UNQUOTED heredoc a backslash-newline
            # joins physical lines before the terminator is compared (and
            # vanishes from the body, as bash does); a quoted heredoc is
            # compared line by line
            joined = ""
            while (1) {
              nl = index(substr(rest, lstart), "\n")
              if (nl == 0) { term = substr(rest, lstart); nl = length(rest) - lstart + 2 } else term = substr(rest, lstart, nl - 1)
              lstart += nl
              if (!hq[k] && term ~ /\\$/ && term !~ /\\\\$/ && lstart <= length(rest)) { joined = joined substr(term, 1, length(term) - 1); continue }
              joined = joined term
              break
            }
            w = joined; if (hdash[k]) sub(/^\t+/, "", w)
            if (w == hw[k]) { found = 1; break }
            body = body joined "\n"
          }
          if (pipeline_feeds_shell(t)) tokenize(body)
          else if (!hq[k]) subst_scan(body)
          rest = substr(rest, lstart)
        }
        hn = 0
        cmd = rest; len = length(cmd); i = 1; line_start = 1; pipe_start = 1
        continue
      }
      emit(seg); seg = ""; i++; line_start = i; pipe_start = i; continue
    }
    if (c == "&" && nc == "&") { for (k = 1; k <= hn; k++) if (!hend[k]) hend[k] = i; emit(seg); seg = ""; i += 2; pipe_start = i; continue }
    if (c == "|" && nc == "|") { for (k = 1; k <= hn; k++) if (!hend[k]) hend[k] = i; emit(seg); seg = ""; i += 2; pipe_start = i; continue }
    if (c == ";") { for (k = 1; k <= hn; k++) if (!hend[k]) hend[k] = i; emit(seg); seg = ""; i++; pipe_start = i; continue }
    if (c == "|") { emit(seg); seg = ""; i++; continue }   # same pipeline continues
    seg = seg c; i++
  }
  emit(seg)
}
{ _all = _all $0 "\n" }
END { tokenize(_all) }
'
_tokenize() {
  printf '%s' "$1" | awk "$_GR_AWK"
}

# Segment normalization in ONE sed process (issue #208; formerly the two
# functions _strip_optvals + _unquote_tokens, whose expressions are kept
# verbatim and in the same order):
#   1. strip known text-value option pairs (-m "msg", -m'msg', -mmsg,
#      -am "msg", -F file; --message/--file/--body/--title with = or space)
#      so argument content doesn't contribute to pattern matching — anchored
#      to token boundaries so patterns don't match inside quoted strings;
#   2. unquote single-token quoted strings ("--hard" → --hard) and remove
#      multi-token ones ("mention git push" → removed).
_normalize_tokens() {
  echo "$1" | sed -E \
    -e "s/(^|[[:space:]])-[a-zA-Z]*[mF][[:space:]]*(\"[^\"]*\"|'[^']*'|[^[:space:]]+)/\1/g" \
    -e "s/(^|[[:space:]])--(message|file|body|title)(=(\"[^\"]*\"|'[^']*'|[^[:space:]]+)|[[:space:]]+(\"[^\"]*\"|'[^']*'|[^[:space:]]+))/\1/g" \
    -e 's/"([^"[:space:]]*)"/ \1 /g' -e 's/"([^"\\]|\\.)*"//g' \
    -e "s/'([^'[:space:]]*)'/ \1 /g" -e "s/'[^']*'//g"
}

# Normalization pipeline: strip wrappers → strip option values → unquote tokens.
# Also detects bypass token: _strip_wrappers consumes env-var prefixes, so the
# prefix zone is raw minus stripped suffix.  A whitespace-bounded match there
# confirms a standalone assignment (not buried inside another var's quoted value).
# Only segments carrying guarded vocabulary can match a check (see the fast
# path above): the others are kept out of SEGMENTS/RAW_SEGMENTS entirely, so
# the per-segment normalization forks are paid only where they can matter.
SEGMENTS=()
RAW_SEGMENTS=()
GIT_SEGMENTS=()
GH_SEGMENTS=()
while IFS= read -r -d $'\036' _seg; do
  _seg="${_seg#"${_seg%%[![:space:]]*}"}"
  [[ -z "$_seg" ]] && continue
  [[ "$_seg" =~ $_GUARDED_VOCAB ]] || continue
  RAW_SEGMENTS+=("$_seg")
  _stripped=$(_strip_wrappers "$_seg")
  if [[ $BYPASS -eq 0 ]]; then
    _prefix="${_seg%"$_stripped"}"
    if [[ "$_prefix" =~ (^|[[:space:]])LEAN4_GUARDRAILS_BYPASS=1([[:space:]]|$) ]]; then
      BYPASS=1
    fi
  fi
  _stripped=$(_normalize_tokens "$_stripped")
  SEGMENTS+=("$_stripped")
  case "$_stripped" in
    git|git[[:space:]]*) GIT_SEGMENTS+=("$_stripped") ;;
    gh|gh[[:space:]]*) GH_SEGMENTS+=("$_stripped") ;;
  esac
done < <(_tokenize "$COMMAND")

# Helper: true if any segment starts with $1 and matches $2.
# Optional $3: skip segments matching this pattern (scoped exemption).
# Batched (issue #208): the segments whose command word is `exe` are matched
# in ONE grep per pattern (segments are single-line, so per-line == per-
# segment), then the exclusion is applied to the matching lines.
seg_match() {
  local exe="$1" pattern="$2" exclude="${3:-}" _sm_hits
  case "$exe" in
    git) [[ ${#GIT_SEGMENTS[@]} -gt 0 ]] || return 1
         _sm_hits=$(printf '%s\n' "${GIT_SEGMENTS[@]}" | grep -E -- "$pattern") || return 1 ;;
    gh)  [[ ${#GH_SEGMENTS[@]} -gt 0 ]] || return 1
         _sm_hits=$(printf '%s\n' "${GH_SEGMENTS[@]}" | grep -E -- "$pattern") || return 1 ;;
    *)   [[ ${#SEGMENTS[@]} -gt 0 ]] || return 1
         _sm_hits=$(printf '%s\n' "${SEGMENTS[@]}" | grep -E -- "^${exe}\b" | grep -E -- "$pattern") || return 1 ;;
  esac
  if [[ -n "$exclude" ]]; then
    printf '%s\n' "$_sm_hits" | grep -qvE -- "$exclude" || return 1
  fi
  return 0
}

# Lean script invocation + stderr suppression guard.
# Rationale: hidden stderr from analysis scripts causes silent failures.
# This guard is intentionally non-bypassable.
#
# The token alternation covers:
#   * `$LEAN4_SCRIPTS/foo.sh` / `${LEAN4_SCRIPTS}/foo.py` — env-var paths
#   * `plugins/lean4/lib/scripts/foo.sh` — repo-relative path
#   * `(./)?(lib/scripts|scripts)/foo.sh` — `cd`-relative invocations
#   * `lean4-skills-foo` — model-facing prefixed wrappers (issue #117),
#     matching bare names (PATH lookup), `bin/lean4-skills-foo`,
#     `./bin/lean4-skills-foo`, and `plugins/lean4/bin/lean4-skills-foo`.
#     The leading boundary `(^|[[:space:]]|/)` accepts any of those.
_has_lean_script_token() {
  local s="$1"
  echo "$s" | grep -qE -- '(\$LEAN4_SCRIPTS/|\$\{LEAN4_SCRIPTS\}/|plugins/lean4/(lib/scripts|scripts)/|(^|[[:space:]])(\./)?(lib/scripts|scripts)/[^[:space:]]+\.(py|sh)\b|(^|[[:space:]]|/)lean4-skills-[a-z][a-z0-9-]*\b)'
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

for _seg in "${RAW_SEGMENTS[@]+"${RAW_SEGMENTS[@]}"}"; do
  [[ "$_seg" == */dev/null* ]] || continue
  if _has_lean_script_token "$_seg" && _has_stderr_null_redirect "$_seg"; then
    echo "BLOCKED (Lean guardrail): suppressed stderr on Lean script invocation hides real errors. Remove '/dev/null' redirection and rerun." >&2
    exit 2
  fi
done

# Collaboration-op policy enforcement.
# $1 = short label (e.g. "git push")
# $2 = user-facing message suffix
_check_collab_op() {
  local label="$1" msg="$2" policy_value="$3"
  case "$policy_value" in
    host|allow) return 0 ;;          # exit 0 — host: let Claude Code decide; allow: just pass.
    block)
      echo "BLOCKED (Lean guardrail): $label - $msg [policy=block]" >&2
      exit 2
      ;;
    *)  # ask: bypass-token-gated. Same UX as v4.5.1: confirm then rerun with the bypass prefix.
      if [[ $BYPASS -ne 1 ]]; then
        echo "BLOCKED (Lean guardrail): $label - $msg [policy=ask, confirm then rerun]" >&2
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

# Tier-3 hard-blocks for push variants that aren't ordinary feature-branch
# upstream pushes. These rewrite shared history (force / force-with-lease),
# delete refs (--delete, -d, `<remote> :<ref>` legacy syntax), or wipe all
# refs (--mirror). Non-bypassable, no policy override — matching the
# `git reset --hard` / `git clean -f` posture. Escape hatch:
# LEAN4_GUARDRAILS_DISABLE=1 for the specific command.
#
# Ordering: these run BEFORE the soft-gate _check_collab_op call below
# so that PUSH_POLICY=allow cannot unlock them.
#
# Standard exemptions (--dry-run, stash push) apply to all of these
# via the seg_match exemption arg.
_push_exempt='\bstash\b.*\bpush\b|--dry-run\b'

# `--force` / `-f`, bundled `-...f...` (plain force-push; rewrites remote history).
# Bundle detection: a single-dash short-option run containing `f` anywhere
# (e.g. `-fu`, `-uf`, `-vfu`, `-fnq`). The `--force-with-lease` long form is
# handled separately below; the bundle regex won't match it because the
# single-dash class `[A-Za-z]*` excludes `-`.
#
# Bundled `-n` (short for --dry-run) is intentionally NOT exempted here:
# if you want a dry-run force-push, use the long forms (--force --dry-run)
# which the existing --dry-run exemption catches. The bundled-short form
# signals force intent the hook flags regardless.
if seg_match git '\bpush\b.*\s(--force|-[A-Za-z]*f[A-Za-z]*)(\s|$)' "$_push_exempt"; then
  echo "BLOCKED (Lean guardrail): git push --force / -f / bundled -f short-flag (e.g. -fu, -uf) rewrites shared history. Non-bypassable. Escape hatch: LEAN4_GUARDRAILS_DISABLE=1 for this command." >&2
  exit 2
fi

# `--force-with-lease[=ref]` (safer force-push, but still history-rewriting)
if seg_match git '\bpush\b.*\s--force-with-lease(=|\s|$)' "$_push_exempt"; then
  echo "BLOCKED (Lean guardrail): git push --force-with-lease rewrites shared history. Non-bypassable. Escape hatch: LEAN4_GUARDRAILS_DISABLE=1 for this command." >&2
  exit 2
fi

# `--mirror` (replicates all refs from local to remote — destructive on the remote)
if seg_match git '\bpush\b.*\s--mirror(\s|$)' "$_push_exempt"; then
  echo "BLOCKED (Lean guardrail): git push --mirror replicates all refs to the remote, deleting any not present locally. Non-bypassable. Escape hatch: LEAN4_GUARDRAILS_DISABLE=1 for this command." >&2
  exit 2
fi

# `--delete` / `-d`, bundled `-...d...` (delete remote ref). Same bundle
# detection shape as force above: a single-dash short-option run containing
# `d` anywhere (e.g. `-dn`, `-nd`, `-vd`). `--delete-this-extension` (some
# hypothetical future long flag) won't false-match because the bundle regex
# is single-dash.
if seg_match git '\bpush\b.*\s(--delete|-[A-Za-z]*d[A-Za-z]*)(\s|$)' "$_push_exempt"; then
  echo "BLOCKED (Lean guardrail): git push --delete / -d / bundled -d short-flag (e.g. -dn, -nd) removes a remote ref. Non-bypassable. Escape hatch: LEAN4_GUARDRAILS_DISABLE=1 for this command." >&2
  exit 2
fi

# Legacy delete-ref syntax: `git push <remote> :<ref>` (the leading `:` on a
# pathspec-shaped token, after `push`, means "delete the named ref").
# Requires a non-empty ref name after `:` to avoid matching `:` as a literal
# pathspec separator in other tokens.
if seg_match git '\bpush\b.*\s:[A-Za-z0-9_./-]+(\s|$)' "$_push_exempt"; then
  echo "BLOCKED (Lean guardrail): git push <remote> :<ref> (legacy ref-delete syntax) removes a remote ref. Non-bypassable. Use git push --delete to be explicit, or LEAN4_GUARDRAILS_DISABLE=1 for this command." >&2
  exit 2
fi

# Leading-`+` force-refspec: `git push origin +<ref>` or `git push origin +<src>:<dst>`.
# Per git-push(1): a refspec prefixed with `+` requests non-fast-forward
# (force) update for that ref, equivalent to `--force` scoped to the
# specific refspec. The `+` must lead the token; subsequent `+` characters
# inside a refspec are not the force prefix.
if seg_match git '\bpush\b.*\s\+[^\s+][^\s]*(\s|$)' "$_push_exempt"; then
  echo "BLOCKED (Lean guardrail): git push <remote> +<refspec> (leading-+ force-refspec) requests non-fast-forward update — rewrites shared history. Non-bypassable. Escape hatch: LEAN4_GUARDRAILS_DISABLE=1 for this command." >&2
  exit 2
fi

# Block git push (not --dry-run, not stash push — exemptions scoped per-segment)
if seg_match git '[[:space:]]push([[:space:]]|$)' '--dry-run\b|\bstash\b.*\bpush\b'; then
  _check_collab_op "git push" "use /lean4:checkpoint, then push manually" "$PUSH_POLICY"
fi

# Block git commit --amend
if seg_match git '\bcommit\b.*--amend\b'; then
  _check_collab_op "git commit --amend" "proving workflow creates new commits for safe rollback" "$AMEND_POLICY"
fi

# Block gh pr create
if seg_match gh '\bpr\b.*\bcreate\b'; then
  _check_collab_op "gh pr create" "review first, then create PR manually" "$PR_CREATE_POLICY"
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
for _seg in "${GIT_SEGMENTS[@]+"${GIT_SEGMENTS[@]}"}"; do
  [[ "$_seg" == *restore* ]] || continue
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
for _seg in "${GIT_SEGMENTS[@]+"${GIT_SEGMENTS[@]}"}"; do
  [[ "$_seg" == *checkout* ]] || continue
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
for _seg in "${GIT_SEGMENTS[@]+"${GIT_SEGMENTS[@]}"}"; do
  [[ "$_seg" == *checkout* ]] || continue
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
for _seg in "${GIT_SEGMENTS[@]+"${GIT_SEGMENTS[@]}"}"; do
  [[ "$_seg" == *checkout* ]] || continue
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
# _normalize_tokens option-value stripping (needed for `git commit -m "msg"`
# false-positive avoidance in the collab checks) strips `-m <value>`
# from segments before pattern matching, so `git checkout -m <path>`
# arrives at the checkout checks with `-m <path>` already removed.
# Catching `-m` in checkout context would require splitting the
# normalization pipeline per-command; deferred. The long form
# `--merge` IS covered (below) — the option-value stripping only handles
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
for _seg in "${GIT_SEGMENTS[@]+"${GIT_SEGMENTS[@]}"}"; do
  [[ "$_seg" == *restore* ]] || continue
  _classify_restore_flags "$_seg"
  if [[ $_restore_staged -eq 1 && $_restore_worktree -eq 0 ]]; then
    continue  # pure unstaging — always allowed
  fi
  _check_destructive_op "git restore" "discards uncommitted edits in the named path(s)"
done

# All checks passed — resolve deferred bypass or allow normally
exit 0

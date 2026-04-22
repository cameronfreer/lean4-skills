#!/usr/bin/env bash
set -euo pipefail

# Resolve TMPDIR once: honor caller's TMPDIR (macOS always sets it), fall back
# to /tmp on systems where it is unset (common on Linux). Export so child
# processes (jq, python3, mktemp) see the same value.
: "${TMPDIR:=/tmp}"
export TMPDIR

# Session cycle/time tracker for autonomous commands (autoprove, autoformalize).
# State is stored in a JSON file. The directory is resolved at each call as
# LEAN4_SESSION_DIR (persisted by init) falling back to $TMPDIR. LEAN4_SESSION_DIR
# wins so later invocations (tick, status, stop) find the state file init
# created even when the ambient TMPDIR differs between calls (e.g. Claude Code
# sets TMPDIR=/tmp/claude in sandbox mode; a plain shell does not). All
# mutations are atomic (write-to-temp, then mv). Single-writer assumption:
# only the main command thread writes; subagents never touch the state file.
#
# Env-file persistence: resolves LEAN4_ENV_FILE → CLAUDE_ENV_FILE → (none).
# CLAUDE_ENV_FILE is the Claude Code adapter input; LEAN4_ENV_FILE is the
# host-neutral override. When an env file resolves, init persists both
# LEAN4_SESSION_ID and LEAN4_SESSION_DIR to it; subsequent invocations that
# source the env file inherit both and work regardless of ambient TMPDIR.
#
# When NO env file is available, init prints the session ID to stdout and
# prints the session directory to stderr as a hint. For manual cross-TMPDIR
# reuse the caller MUST pass BOTH vars (or preserve TMPDIR from init):
#   SID=$(cycle_tracker.sh init ...)            # stdout: just the sid
#   # stderr hint shows: LEAN4_SESSION_DIR=<dir>
#   LEAN4_SESSION_ID=$SID LEAN4_SESSION_DIR=<dir> cycle_tracker.sh tick ...
#
# Subcommands:
#   init   --max-cycles=N --max-stuck=N [--max-runtime=Xm] [--max-deep-per-cycle=N] [--max-consecutive-deep=N]
#          Aliases (long user-facing forms): --max-stuck-cycles, --max-total-runtime, --max-consecutive-deep-cycles
#   tick   --stuck=yes|no
#   can-deep
#   deep
#   status
#   stop

# ---------------------------------------------------------------------------
# JSON backend: jq preferred, python3 fallback
# ---------------------------------------------------------------------------
_json_backend=""

_detect_backend() {
  if [[ -n "$_json_backend" ]]; then return; fi
  if command -v jq >/dev/null 2>&1; then
    _json_backend="jq"
  elif command -v python3 >/dev/null 2>&1; then
    _json_backend="python3"
  else
    echo "error=no JSON backend (need jq or python3)" >&2
    exit 2
  fi
}

_json_read() {
  # $1 = file, $2 = jq expression (e.g., '.cycles')
  local file="$1" expr="$2"
  _detect_backend
  if [[ "$_json_backend" == "jq" ]]; then
    jq -r "$expr" "$file" 2>/dev/null
  else
    python3 -c "
import json, sys
with open('$file') as f:
    d = json.load(f)
# Evaluate the jq-like expression
expr = '''$expr'''
# Simple .field access
parts = [p for p in expr.lstrip('.').split('.') if p]
val = d
for p in parts:
    val = val[p]
print(val)
" 2>/dev/null
  fi
}

_json_write() {
  # $1 = file, $2 = python dict literal OR jq filter to apply
  # For simplicity, always use python3 for writes (handles complex updates).
  # For jq backend, use jq for writes too.
  local file="$1" updates="$2"
  _detect_backend
  local tmp
  tmp=$(mktemp "${file}.tmp.XXXXXX")
  if [[ "$_json_backend" == "jq" ]]; then
    jq "$updates" "$file" > "$tmp" 2>/dev/null
  else
    python3 -c "
import json
with open('$file') as f:
    d = json.load(f)
updates = $updates
d.update(updates)
with open('$tmp', 'w') as f:
    json.dump(d, f)
" 2>/dev/null
  fi
  mv "$tmp" "$file"
}

_json_create() {
  # $1 = file, $2 = JSON string
  local file="$1" content="$2"
  _detect_backend
  if [[ "$_json_backend" == "jq" ]]; then
    printf '%s' "$content" | jq '.' > "$file" 2>/dev/null
  else
    python3 -c "
import json
with open('$file', 'w') as f:
    json.dump(json.loads('''$content'''), f)
" 2>/dev/null
  fi
}

# ---------------------------------------------------------------------------
# persist_env: host-neutral env-file persistence
# Resolves: LEAN4_ENV_FILE → CLAUDE_ENV_FILE → (none = stdout fallback)
# ---------------------------------------------------------------------------
_resolve_env_file() {
  local raw="${LEAN4_ENV_FILE:-${CLAUDE_ENV_FILE:-}}"
  if [[ -z "$raw" ]]; then echo ""; return; fi
  # Reject broken symlinks: the link exists but its target does not.
  # Return empty so callers fall back to stdout-only.
  if [[ -L "$raw" && ! -e "$raw" ]]; then echo ""; return; fi
  # Resolve symlinks so we operate on the real target, not the link itself.
  # If the path is a symlink and resolution tools are unavailable, reject it
  # rather than operating on the link path (which would clobber the symlink).
  local resolved
  resolved=$(realpath "$raw" 2>/dev/null) \
    || resolved=$(readlink -f "$raw" 2>/dev/null) \
    || resolved=""
  if [[ -z "$resolved" ]]; then
    # Resolution failed. Safe to use raw path only if it's not a symlink.
    if [[ -L "$raw" ]]; then echo ""; return; fi
    resolved="$raw"
  fi
  echo "$resolved"
}

_persist_env() {
  local kv="$1"
  local var_name="${kv%%=*}"
  var_name="${var_name#export }"
  local env_out
  env_out=$(_resolve_env_file)
  if [[ -z "$env_out" ]]; then return; fi
  # Guard: if something exists at the path, it must be a regular file that is
  # readable+writable. Directories, FIFOs, devices, etc. are rejected.
  if [[ -e "$env_out" ]]; then
    if [[ ! -f "$env_out" || ! -r "$env_out" || ! -w "$env_out" ]]; then return; fi
  else
    # File does not exist: parent directory must exist and be writable.
    local _pdir
    _pdir=$(dirname "$env_out")
    if [[ ! -d "$_pdir" || ! -w "$_pdir" ]]; then return; fi
  fi
  if [[ -f "$env_out" ]]; then
    grep -v "^export ${var_name}=" "$env_out" > "${env_out}.tmp" 2>/dev/null || true
    mv "${env_out}.tmp" "$env_out"
  fi
  printf '%s\n' "$kv" >> "$env_out" 2>/dev/null || true
}

# ---------------------------------------------------------------------------
# State file resolution
# ---------------------------------------------------------------------------
_state_file() {
  local sid="${LEAN4_SESSION_ID:-}"
  if [[ -z "$sid" ]]; then
    echo "error=LEAN4_SESSION_ID is not set" >&2
    exit 2
  fi
  # Resolution order:
  #   1. LEAN4_SESSION_DIR — persisted by init, survives TMPDIR changes
  #      between invocations (tick, status, stop may run under a different
  #      ambient TMPDIR than init).
  #   2. TMPDIR — always set by the preamble at the top of this script,
  #      matches init when LEAN4_SESSION_DIR is not persisted.
  # LEAN4_SESSION_DIR wins so the tracker can always find the state file
  # init created, even when Claude Code and a plain shell disagree on TMPDIR.
  local dir="${LEAN4_SESSION_DIR:-$TMPDIR}"
  local f="${dir}/${sid}.json"
  if [[ ! -f "$f" ]]; then
    echo "error=state file not found: $f" >&2
    exit 2
  fi
  echo "$f"
}

_validate_state() {
  # Verify state file contains valid JSON. Exit 2 with clear error if not.
  local file="$1"
  _detect_backend
  if [[ "$_json_backend" == "jq" ]]; then
    if ! jq empty "$file" 2>/dev/null; then
      echo "error=corrupted state file: $file" >&2
      exit 2
    fi
  else
    if ! python3 -c "import json; json.load(open('$file'))" 2>/dev/null; then
      echo "error=corrupted state file: $file" >&2
      exit 2
    fi
  fi
}

_read_state() {
  local file
  file=$(_state_file)
  _detect_backend
  if [[ "$_json_backend" == "jq" ]]; then
    cat "$file"
  else
    python3 -c "
import json
with open('$file') as f:
    print(json.dumps(json.load(f)))
"
  fi
}

# ---------------------------------------------------------------------------
# Validation helpers
# ---------------------------------------------------------------------------
_require_positive_int() {
  local name="$1" val="$2"
  if [[ -z "$val" ]]; then
    echo "error=missing required parameter $name" >&2
    exit 2
  fi
  if ! [[ "$val" =~ ^[0-9]+$ ]] || [[ "$val" -le 0 ]]; then
    echo "error=$name must be a positive integer, got '$val'" >&2
    exit 2
  fi
}

_parse_duration() {
  # Accepts: 120m, 30s, 2h, 120 (bare = minutes). Returns seconds.
  local val="$1"
  if [[ -z "$val" ]]; then
    echo "0"
    return
  fi
  if ! [[ "$val" =~ ^[0-9]+[mshMSH]?$ ]]; then
    echo "error=invalid duration format '$val' (expected e.g. 120m, 30s, 2h, or bare number for minutes)" >&2
    exit 2
  fi
  local num="${val%%[mshMSH]}"
  local suffix="${val##*[0-9]}"
  suffix="$(printf '%s' "$suffix" | tr '[:upper:]' '[:lower:]')"  # portable lowercase
  case "$suffix" in
    s) echo "$num" ;;
    h) echo $(( num * 3600 )) ;;
    m|"") echo $(( num * 60 )) ;;
  esac
}

# ---------------------------------------------------------------------------
# Subcommand: init
# ---------------------------------------------------------------------------
cmd_init() {
  local max_cycles="" max_stuck="" max_runtime="" max_deep_per_cycle="1" max_consecutive_deep="2"

  # Track the flag name the caller actually used, for error messages
  local name_stuck="--max-stuck" name_runtime="--max-runtime" name_consec_deep="--max-consecutive-deep"

  for arg in "$@"; do
    case "$arg" in
      --max-cycles=*) max_cycles="${arg#*=}" ;;
      --max-stuck=*) max_stuck="${arg#*=}" ;;
      --max-stuck-cycles=*) max_stuck="${arg#*=}"; name_stuck="--max-stuck-cycles" ;;
      --max-runtime=*) max_runtime="${arg#*=}" ;;
      --max-total-runtime=*) max_runtime="${arg#*=}"; name_runtime="--max-total-runtime" ;;
      --max-deep-per-cycle=*) max_deep_per_cycle="${arg#*=}" ;;
      --max-consecutive-deep=*) max_consecutive_deep="${arg#*=}" ;;
      --max-consecutive-deep-cycles=*) max_consecutive_deep="${arg#*=}"; name_consec_deep="--max-consecutive-deep-cycles" ;;
      *) echo "error=unknown argument: $arg" >&2; exit 2 ;;
    esac
  done

  # Validate required — use the flag name the caller passed
  _require_positive_int "--max-cycles" "$max_cycles"
  _require_positive_int "$name_stuck" "$max_stuck"
  _require_positive_int "--max-deep-per-cycle" "$max_deep_per_cycle"
  _require_positive_int "$name_consec_deep" "$max_consecutive_deep"

  # Parse duration (optional)
  local runtime_seconds
  runtime_seconds=$(_parse_duration "$max_runtime")

  # Clean stale sessions (>24h, owned by current user)
  find "$TMPDIR" -maxdepth 1 -name 'lean4-session-*.json' -user "$(id -u)" -mmin +1440 -delete 2>/dev/null || true

  # Create state file via mktemp (no race).
  # BSD mktemp (macOS) requires the template to END with X's — a .json
  # suffix after the X's is treated as a literal path, not a template.
  # So we create without .json, then rename.
  _detect_backend
  local state_file tmp_file
  tmp_file=$(mktemp "$TMPDIR/lean4-session-XXXXXX")
  state_file="${tmp_file}.json"
  mv "$tmp_file" "$state_file"
  local session_id
  session_id=$(basename "$state_file" .json)

  local now
  now=$(date +%s)

  # Resolve env file once at init and record it in state, so stop uses the
  # same file even if LEAN4_ENV_FILE/CLAUDE_ENV_FILE changes between calls.
  local resolved_env_file
  resolved_env_file=$(_resolve_env_file)
  # Only record if actually writable regular file (or creatable); otherwise
  # empty = stdout-only fallback. Directories, FIFOs, devices are rejected.
  if [[ -n "$resolved_env_file" ]]; then
    if [[ -e "$resolved_env_file" ]]; then
      # Must be a regular file that is readable+writable.
      if [[ ! -f "$resolved_env_file" || ! -r "$resolved_env_file" || ! -w "$resolved_env_file" ]]; then
        resolved_env_file=""
      fi
    else
      # File does not exist: parent directory must exist and be writable.
      local parent_dir
      parent_dir=$(dirname "$resolved_env_file")
      if [[ ! -d "$parent_dir" || ! -w "$parent_dir" ]]; then
        resolved_env_file=""
      fi
    fi
  fi

  local content
  content=$(cat <<ENDJSON
{
  "session_id": "$session_id",
  "start_epoch": $now,
  "env_file": "$resolved_env_file",
  "max_cycles": $max_cycles,
  "max_stuck": $max_stuck,
  "max_runtime_seconds": $runtime_seconds,
  "max_deep_per_cycle": $max_deep_per_cycle,
  "max_consecutive_deep": $max_consecutive_deep,
  "cycles": 0,
  "consecutive_stuck": 0,
  "deep_this_cycle": 0,
  "consecutive_deep_cycles": 0,
  "cycles_total": 0,
  "stuck_cycles_total": 0,
  "deep_total": 0,
  "claims_attempted": 0,
  "claim_active": false
}
ENDJSON
  )

  _json_create "$state_file" "$content"

  # Persist session ID and the chosen state directory to the resolved env file.
  # LEAN4_SESSION_DIR lets later invocations (tick/status/stop) find the same
  # state file even if the ambient TMPDIR differs from init's — which matters
  # for Claude Code (where init runs under TMPDIR=/tmp/claude) vs. a plain shell.
  _persist_env "export LEAN4_SESSION_ID=\"$session_id\""
  _persist_env "export LEAN4_SESSION_DIR=\"$(dirname "$state_file")\""

  # Stdout-only fallback: no env file resolved → _persist_env was a no-op,
  # so manual callers won't automatically inherit LEAN4_SESSION_DIR. Surface
  # it on stderr as a hint so they can preserve it across invocations when
  # their TMPDIR changes. Stdout remains just the session id for backward
  # compatibility with callers that do SID=$(cycle_tracker.sh init ...).
  if [[ -z "$resolved_env_file" ]]; then
    local state_dir
    state_dir=$(dirname "$state_file")
    echo "LEAN4_SESSION_DIR=$state_dir" >&2
  fi

  echo "$session_id"
}

# ---------------------------------------------------------------------------
# Subcommand: tick --stuck=yes|no
# ---------------------------------------------------------------------------
cmd_tick() {
  local stuck=""
  for arg in "$@"; do
    case "$arg" in
      --stuck=yes) stuck="yes" ;;
      --stuck=no) stuck="no" ;;
      --stuck=*) echo "error=--stuck must be yes or no, got '${arg#*=}'" >&2; exit 2 ;;
      *) echo "error=unknown argument: $arg" >&2; exit 2 ;;
    esac
  done
  if [[ -z "$stuck" ]]; then
    echo "error=--stuck=yes|no is required for tick" >&2
    exit 2
  fi

  local file
  file=$(_state_file)
  _validate_state "$file"
  _detect_backend

  local now
  now=$(date +%s)

  # Read current state and compute new state in one shot
  local output
  if [[ "$_json_backend" == "jq" ]]; then
    output=$(jq -r --argjson stuck_flag "$(if [[ "$stuck" == "yes" ]]; then echo 1; else echo 0; fi)" \
                    --argjson now "$now" '
      # Update cycles (per-claim + session total)
      .cycles += 1 |
      .cycles_total += 1 |

      # Update stuck (per-claim consecutive + session total)
      (if $stuck_flag == 1 then .consecutive_stuck + 1 else 0 end) as $new_stuck |
      .consecutive_stuck = $new_stuck |
      (if $stuck_flag == 1 then .stuck_cycles_total + 1 else .stuck_cycles_total end) as $new_stuck_total |
      .stuck_cycles_total = $new_stuck_total |

      # Update deep
      (if .deep_this_cycle > 0 then .consecutive_deep_cycles + 1 else 0 end) as $new_consec_deep |
      .consecutive_deep_cycles = $new_consec_deep |
      .deep_this_cycle = 0 |

      # Compute elapsed
      ($now - .start_epoch) as $elapsed |

      # Check violations
      (
        [
          (if .cycles >= .max_cycles then "max-cycles" else empty end),
          (if .consecutive_stuck >= .max_stuck then "max-stuck" else empty end),
          (if .max_runtime_seconds > 0 and $elapsed >= .max_runtime_seconds then "max-runtime" else empty end)
        ] | join(",")
      ) as $violations |

      # Format elapsed display — use seconds when max is not a whole number of minutes
      (if .max_runtime_seconds > 0 and (.max_runtime_seconds % 60) != 0 then
        ($elapsed | tostring) + "s/" + (.max_runtime_seconds | tostring) + "s"
       elif .max_runtime_seconds > 0 then
        (($elapsed / 60) | floor | tostring) + "m/" + ((.max_runtime_seconds / 60) | floor | tostring) + "m"
       else
        (($elapsed / 60) | floor | tostring) + "m/unlimited"
       end) as $elapsed_display |

      # Output key=value, then the object for saving
      {
        _output: (
          "result=" + (if ($violations | length) > 0 then "LIMIT_REACHED" else "ok" end) + "\n" +
          (if ($violations | length) > 0 then "violation=" + $violations + "\n" else "" end) +
          "cycles=" + (.cycles | tostring) + "/" + (.max_cycles | tostring) + "\n" +
          "consecutive_stuck=" + (.consecutive_stuck | tostring) + "/" + (.max_stuck | tostring) + "\n" +
          "elapsed_seconds=" + ($elapsed | tostring) + "\n" +
          "elapsed_display=" + $elapsed_display + "\n" +
          "deep_this_cycle=" + (.deep_this_cycle | tostring) + "/" + (.max_deep_per_cycle | tostring) + "\n" +
          "consecutive_deep_cycles=" + (.consecutive_deep_cycles | tostring) + "/" + (.max_consecutive_deep | tostring)
        ),
        _state: (del(._output))
      }
    ' "$file" 2>/dev/null)

    local display state_json
    display=$(printf '%s' "$output" | jq -r '._output' 2>/dev/null)
    state_json=$(printf '%s' "$output" | jq 'del(._output) | ._state' 2>/dev/null)

    # Write state atomically
    local tmp
    tmp=$(mktemp "${file}.tmp.XXXXXX")
    printf '%s' "$state_json" > "$tmp"
    mv "$tmp" "$file"

    # Print output
    printf '%b\n' "$display"

    # Exit code based on violations
    if printf '%s' "$output" | jq -e '._output | test("LIMIT_REACHED")' >/dev/null 2>&1; then
      exit 1
    fi
  else
    # Python3 fallback
    local stuck_flag
    if [[ "$stuck" == "yes" ]]; then stuck_flag=1; else stuck_flag=0; fi
    python3 -c "
import json, sys

with open('$file') as f:
    d = json.load(f)

now = $now
stuck = bool($stuck_flag)

# Update cycles (per-claim + session total)
d['cycles'] += 1
d['cycles_total'] += 1

# Update stuck (per-claim consecutive + session total)
d['consecutive_stuck'] = d['consecutive_stuck'] + 1 if stuck else 0
if stuck:
    d['stuck_cycles_total'] += 1

# Update deep
if d['deep_this_cycle'] > 0:
    d['consecutive_deep_cycles'] += 1
else:
    d['consecutive_deep_cycles'] = 0
d['deep_this_cycle'] = 0

# Check violations
elapsed = now - d['start_epoch']
violations = []
if d['cycles'] >= d['max_cycles']:
    violations.append('max-cycles')
if d['consecutive_stuck'] >= d['max_stuck']:
    violations.append('max-stuck')
if d['max_runtime_seconds'] > 0 and elapsed >= d['max_runtime_seconds']:
    violations.append('max-runtime')

# Format display — use seconds when max < 60s
mrs = d['max_runtime_seconds']
if mrs > 0 and mrs % 60 != 0:
    elapsed_display = f'{elapsed}s/{mrs}s'
elif mrs > 0:
    elapsed_display = f'{elapsed // 60}m/{mrs // 60}m'
else:
    elapsed_display = f'{elapsed // 60}m/unlimited'

result = 'LIMIT_REACHED' if violations else 'ok'
lines = ['result=' + result]
if violations:
    lines.append('violation=' + ','.join(violations))
lines.extend([
    f\"cycles={d['cycles']}/{d['max_cycles']}\",
    f\"consecutive_stuck={d['consecutive_stuck']}/{d['max_stuck']}\",
    f'elapsed_seconds={elapsed}',
    f'elapsed_display={elapsed_display}',
    f\"deep_this_cycle={d['deep_this_cycle']}/{d['max_deep_per_cycle']}\",
    f\"consecutive_deep_cycles={d['consecutive_deep_cycles']}/{d['max_consecutive_deep']}\",
])

# Write state atomically
import tempfile, os
fd, tmp = tempfile.mkstemp(prefix=os.path.basename('$file') + '.tmp.', dir=os.path.dirname('$file'))
with os.fdopen(fd, 'w') as f:
    json.dump(d, f)
os.rename(tmp, '$file')

print('\n'.join(lines))
sys.exit(1 if violations else 0)
" 2>/dev/null
  fi
}

# ---------------------------------------------------------------------------
# Subcommand: can-deep
# ---------------------------------------------------------------------------
cmd_can_deep() {
  local file
  file=$(_state_file)
  _validate_state "$file"
  _detect_backend

  local now
  now=$(date +%s)

  if [[ "$_json_backend" == "jq" ]]; then
    jq -r --argjson now "$now" '
      ($now - .start_epoch) as $elapsed |
      (
        if .deep_this_cycle >= .max_deep_per_cycle then "max-deep-per-cycle"
        elif .consecutive_deep_cycles >= .max_consecutive_deep then "max-consecutive-deep"
        elif .max_runtime_seconds > 0 and $elapsed >= .max_runtime_seconds then "max-runtime"
        else "" end
      ) as $reason |
      "result=" + (if $reason == "" then "ok" else "denied" end),
      (if $reason != "" then "reason=" + $reason else empty end),
      "deep_this_cycle=" + (.deep_this_cycle | tostring) + "/" + (.max_deep_per_cycle | tostring),
      "consecutive_deep_cycles=" + (.consecutive_deep_cycles | tostring) + "/" + (.max_consecutive_deep | tostring),
      "elapsed_seconds=" + ($elapsed | tostring)
    ' "$file" 2>/dev/null

    # Check if denied
    local reason
    reason=$(jq -r --argjson now "$now" '
      ($now - .start_epoch) as $elapsed |
      if .deep_this_cycle >= .max_deep_per_cycle then "max-deep-per-cycle"
      elif .consecutive_deep_cycles >= .max_consecutive_deep then "max-consecutive-deep"
      elif .max_runtime_seconds > 0 and $elapsed >= .max_runtime_seconds then "max-runtime"
      else "" end
    ' "$file" 2>/dev/null)
    if [[ -n "$reason" ]]; then exit 1; fi
  else
    python3 -c "
import json, sys

with open('$file') as f:
    d = json.load(f)

now = $now
elapsed = now - d['start_epoch']

reason = ''
if d['deep_this_cycle'] >= d['max_deep_per_cycle']:
    reason = 'max-deep-per-cycle'
elif d['consecutive_deep_cycles'] >= d['max_consecutive_deep']:
    reason = 'max-consecutive-deep'
elif d['max_runtime_seconds'] > 0 and elapsed >= d['max_runtime_seconds']:
    reason = 'max-runtime'

result = 'denied' if reason else 'ok'
lines = ['result=' + result]
if reason:
    lines.append('reason=' + reason)
lines.extend([
    f\"deep_this_cycle={d['deep_this_cycle']}/{d['max_deep_per_cycle']}\",
    f\"consecutive_deep_cycles={d['consecutive_deep_cycles']}/{d['max_consecutive_deep']}\",
    f'elapsed_seconds={elapsed}',
])
print('\n'.join(lines))
sys.exit(1 if reason else 0)
" 2>/dev/null
  fi
}

# ---------------------------------------------------------------------------
# Subcommand: deep
# ---------------------------------------------------------------------------
cmd_deep() {
  local file
  file=$(_state_file)
  _validate_state "$file"
  _detect_backend

  if [[ "$_json_backend" == "jq" ]]; then
    local tmp
    tmp=$(mktemp "${file}.tmp.XXXXXX")
    jq '.deep_this_cycle += 1 | .deep_total += 1' "$file" > "$tmp" 2>/dev/null
    mv "$tmp" "$file"
  else
    python3 -c "
import json, tempfile, os
with open('$file') as f:
    d = json.load(f)
d['deep_this_cycle'] += 1
d['deep_total'] += 1
fd, tmp = tempfile.mkstemp(prefix=os.path.basename('$file') + '.tmp.', dir=os.path.dirname('$file'))
with os.fdopen(fd, 'w') as f:
    json.dump(d, f)
os.rename(tmp, '$file')
" 2>/dev/null
  fi
}

# ---------------------------------------------------------------------------
# Subcommand: start-claim
# ---------------------------------------------------------------------------
cmd_start_claim() {
  local file
  file=$(_state_file)
  _validate_state "$file"
  _detect_backend

  # Guard: fail if a claim is already active
  local active
  if [[ "$_json_backend" == "jq" ]]; then
    active=$(jq -r '.claim_active' "$file" 2>/dev/null)
  else
    active=$(python3 -c "import json; print(str(json.load(open('$file'))['claim_active']).lower())" 2>/dev/null)
  fi
  if [[ "$active" == "true" ]]; then
    echo "error=start-claim called while claim_active is already true" >&2
    exit 2
  fi

  if [[ "$_json_backend" == "jq" ]]; then
    local tmp
    tmp=$(mktemp "${file}.tmp.XXXXXX")
    jq '.claim_active = true' "$file" > "$tmp" 2>/dev/null
    mv "$tmp" "$file"
  else
    python3 -c "
import json, tempfile, os
with open('$file') as f:
    d = json.load(f)
d['claim_active'] = True
fd, tmp = tempfile.mkstemp(prefix=os.path.basename('$file') + '.tmp.', dir=os.path.dirname('$file'))
with os.fdopen(fd, 'w') as f:
    json.dump(d, f)
os.rename(tmp, '$file')
" 2>/dev/null
  fi
}

# ---------------------------------------------------------------------------
# Subcommand: reset-claim
# ---------------------------------------------------------------------------
cmd_reset_claim() {
  local file
  file=$(_state_file)
  _validate_state "$file"
  _detect_backend

  # Guard: fail if no claim is active
  local active
  if [[ "$_json_backend" == "jq" ]]; then
    active=$(jq -r '.claim_active' "$file" 2>/dev/null)
  else
    active=$(python3 -c "import json; print(str(json.load(open('$file'))['claim_active']).lower())" 2>/dev/null)
  fi
  if [[ "$active" != "true" ]]; then
    echo "error=reset-claim called while claim_active is false" >&2
    exit 2
  fi

  if [[ "$_json_backend" == "jq" ]]; then
    local tmp
    tmp=$(mktemp "${file}.tmp.XXXXXX")
    jq '
      .claims_attempted += 1 |
      .claim_active = false |
      .cycles = 0 |
      .consecutive_stuck = 0 |
      .deep_this_cycle = 0 |
      .consecutive_deep_cycles = 0
    ' "$file" > "$tmp" 2>/dev/null
    mv "$tmp" "$file"
  else
    python3 -c "
import json, tempfile, os
with open('$file') as f:
    d = json.load(f)
d['claims_attempted'] += 1
d['claim_active'] = False
d['cycles'] = 0
d['consecutive_stuck'] = 0
d['deep_this_cycle'] = 0
d['consecutive_deep_cycles'] = 0
fd, tmp = tempfile.mkstemp(prefix=os.path.basename('$file') + '.tmp.', dir=os.path.dirname('$file'))
with os.fdopen(fd, 'w') as f:
    json.dump(d, f)
os.rename(tmp, '$file')
" 2>/dev/null
  fi
}

# ---------------------------------------------------------------------------
# Subcommand: status
# ---------------------------------------------------------------------------
cmd_status() {
  local file
  file=$(_state_file)
  _validate_state "$file"
  _detect_backend

  local now
  now=$(date +%s)

  if [[ "$_json_backend" == "jq" ]]; then
    jq -r --argjson now "$now" '
      ($now - .start_epoch) as $elapsed |
      (if .max_runtime_seconds > 0 and (.max_runtime_seconds % 60) != 0 then
        ($elapsed | tostring) + "s/" + (.max_runtime_seconds | tostring) + "s"
       elif .max_runtime_seconds > 0 then
        (($elapsed / 60) | floor | tostring) + "m/" + ((.max_runtime_seconds / 60) | floor | tostring) + "m"
       else
        (($elapsed / 60) | floor | tostring) + "m/unlimited"
       end) as $elapsed_display |
      # Session totals (live-accumulated, always current)
      (.claims_attempted + (if .claim_active then 1 else 0 end)) as $claims_display |
      "session_id=" + .session_id,
      "claim_active=" + (if .claim_active then "true" else "false" end),
      "cycles=" + (.cycles | tostring) + "/" + (.max_cycles | tostring),
      "consecutive_stuck=" + (.consecutive_stuck | tostring) + "/" + (.max_stuck | tostring),
      "elapsed_seconds=" + ($elapsed | tostring),
      "elapsed_display=" + $elapsed_display,
      "deep_this_cycle=" + (.deep_this_cycle | tostring) + "/" + (.max_deep_per_cycle | tostring),
      "consecutive_deep_cycles=" + (.consecutive_deep_cycles | tostring) + "/" + (.max_consecutive_deep | tostring),
      "cycles_total=" + (.cycles_total | tostring),
      "stuck_cycles_total=" + (.stuck_cycles_total | tostring),
      "deep_total=" + (.deep_total | tostring),
      "claims_attempted=" + ($claims_display | tostring)
    ' "$file" 2>/dev/null
  else
    python3 -c "
import json
with open('$file') as f:
    d = json.load(f)
now = $now
elapsed = now - d['start_epoch']
mrs = d['max_runtime_seconds']
if mrs > 0 and mrs % 60 != 0:
    elapsed_display = f'{elapsed}s/{mrs}s'
elif mrs > 0:
    elapsed_display = f'{elapsed // 60}m/{mrs // 60}m'
else:
    elapsed_display = f'{elapsed // 60}m/unlimited'
claims_display = d['claims_attempted'] + (1 if d.get('claim_active') else 0)
lines = [
    f\"session_id={d['session_id']}\",
    f\"claim_active={'true' if d.get('claim_active') else 'false'}\",
    f\"cycles={d['cycles']}/{d['max_cycles']}\",
    f\"consecutive_stuck={d['consecutive_stuck']}/{d['max_stuck']}\",
    f'elapsed_seconds={elapsed}',
    f'elapsed_display={elapsed_display}',
    f\"deep_this_cycle={d['deep_this_cycle']}/{d['max_deep_per_cycle']}\",
    f\"consecutive_deep_cycles={d['consecutive_deep_cycles']}/{d['max_consecutive_deep']}\",
    f\"cycles_total={d['cycles_total']}\",
    f\"stuck_cycles_total={d['stuck_cycles_total']}\",
    f\"deep_total={d['deep_total']}\",
    f'claims_attempted={claims_display}',
]
print('\n'.join(lines))
" 2>/dev/null
  fi
}

# ---------------------------------------------------------------------------
# Subcommand: stop
# ---------------------------------------------------------------------------
cmd_stop() {
  local sid="${LEAN4_SESSION_ID:-}"
  if [[ -z "$sid" ]]; then
    return 0
  fi
  # Mirror _state_file's resolution order: persisted LEAN4_SESSION_DIR wins
  # over ambient TMPDIR, so stop finds the same file init created.
  local dir="${LEAN4_SESSION_DIR:-$TMPDIR}"
  local f="${dir}/${sid}.json"
  # Read the env file path that init recorded, so we clean up the right file
  # even if LEAN4_ENV_FILE/CLAUDE_ENV_FILE changed since init.
  # Read the env file path that init recorded. If the state file is missing or
  # corrupted, fall back to the currently resolved env file for best-effort
  # cleanup so we don't leak stale LEAN4_SESSION_ID exports.
  local recorded_env=""
  if [[ -f "$f" ]]; then
    _detect_backend
    recorded_env=$(_json_read "$f" ".env_file" 2>/dev/null) || recorded_env=""
    if [[ "$recorded_env" == "null" ]]; then recorded_env=""; fi
  fi
  if [[ -z "$recorded_env" ]]; then
    recorded_env=$(_resolve_env_file)
  fi
  rm -f "$f"
  # Also clean up any orphaned tmp files from atomic writes
  rm -f "${f}".tmp.* 2>/dev/null || true
  # Unpersist this session's LEAN4_SESSION_ID and (conditionally)
  # LEAN4_SESSION_DIR. A later init under the same env file may have
  # overwritten both lines with a newer session's values. If two sessions
  # share the same TMPDIR, the newer session's DIR string is identical to
  # ours — removing it by value would clobber the newer session's
  # persistence (weakening cross-TMPDIR robustness) even though its ID stays.
  # So only remove the DIR line when the env file's current ID still matches
  # ours (or no ID line remains). Uses `grep -F -x` (fixed strings,
  # whole-line) so regex metacharacters in ${sid}/${dir} — e.g. '.' in a
  # BSD mktemp path — can't cause over- or under-matches.
  if [[ -n "$recorded_env" && -f "$recorded_env" && -r "$recorded_env" && -w "$recorded_env" ]]; then
    local current_id_line current_id
    # `|| true` because grep exits 1 when no match, which combined with
    # pipefail would abort stop before the empty-current_id branch runs —
    # the same env file may legitimately have no LEAN4_SESSION_ID line
    # (e.g. only a stale DIR line after an interrupted prior cleanup).
    current_id_line=$(grep '^export LEAN4_SESSION_ID=' "$recorded_env" 2>/dev/null | tail -n1 || true)
    current_id="${current_id_line#export LEAN4_SESSION_ID=\"}"
    current_id="${current_id%\"}"
    local id_line="export LEAN4_SESSION_ID=\"${sid}\""
    local dir_line="export LEAN4_SESSION_DIR=\"${dir}\""
    if [[ -z "$current_id" || "$current_id" == "$sid" ]]; then
      grep -v -F -x "$id_line" "$recorded_env" \
        | grep -v -F -x "$dir_line" \
        > "${recorded_env}.tmp" 2>/dev/null || true
    else
      # Newer session supersedes us; only remove any lingering stale ID line
      # that matches our sid. Leave LEAN4_SESSION_DIR alone — it belongs to
      # the active session now.
      grep -v -F -x "$id_line" "$recorded_env" \
        > "${recorded_env}.tmp" 2>/dev/null || true
    fi
    mv "${recorded_env}.tmp" "$recorded_env"
  fi
}

# ---------------------------------------------------------------------------
# Main dispatch
# ---------------------------------------------------------------------------
subcmd="${1:-}"
shift || true

case "$subcmd" in
  init)        cmd_init "$@" ;;
  tick)        cmd_tick "$@" ;;
  can-deep)    cmd_can_deep "$@" ;;
  deep)        cmd_deep "$@" ;;
  start-claim) cmd_start_claim "$@" ;;
  reset-claim) cmd_reset_claim "$@" ;;
  status)      cmd_status "$@" ;;
  stop)        cmd_stop "$@" ;;
  "")          echo "error=no subcommand specified (init|tick|can-deep|deep|start-claim|reset-claim|status|stop)" >&2; exit 2 ;;
  *)        echo "error=unknown subcommand: $subcmd" >&2; exit 2 ;;
esac

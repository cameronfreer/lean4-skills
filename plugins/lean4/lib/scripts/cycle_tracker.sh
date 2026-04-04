#!/bin/bash
set -euo pipefail

# Session cycle/time tracker for autonomous commands (autoprove, autoformalize).
# State is stored in a JSON file under /tmp. All mutations are atomic
# (write-to-temp, then mv). Single-writer assumption: only the main command
# thread writes; subagents never touch the state file.
#
# Env-file persistence: resolves LEAN4_ENV_FILE → CLAUDE_ENV_FILE → (none).
# CLAUDE_ENV_FILE is the Claude Code adapter input; LEAN4_ENV_FILE is the
# host-neutral override. When neither is available, session ID is printed
# to stdout for manual env-prefix passing.
#
# Subcommands:
#   init   --max-cycles=N --max-stuck=N [--max-runtime=Xm] [--max-deep-per-cycle=N] [--max-consecutive-deep=N]
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
  echo "${LEAN4_ENV_FILE:-${CLAUDE_ENV_FILE:-}}"
}

_persist_env() {
  local kv="$1"
  local var_name="${kv%%=*}"
  var_name="${var_name#export }"
  local env_out
  env_out=$(_resolve_env_file)
  if [[ -z "$env_out" ]]; then return; fi
  # Guard: if the file exists, it must be readable+writable.
  if [[ -e "$env_out" && ( ! -r "$env_out" || ! -w "$env_out" ) ]]; then return; fi
  # Guard: if the file does not exist, the parent directory must be writable.
  if [[ ! -e "$env_out" ]]; then
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

_unpersist_env() {
  local var_name="$1"
  local env_out
  env_out=$(_resolve_env_file)
  if [[ -z "$env_out" ]]; then return; fi
  if [[ -e "$env_out" && ( ! -r "$env_out" || ! -w "$env_out" ) ]]; then return; fi
  if [[ -f "$env_out" ]]; then
    grep -v "^export ${var_name}=" "$env_out" > "${env_out}.tmp" 2>/dev/null || true
    mv "${env_out}.tmp" "$env_out"
  fi
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
  local f="/tmp/${sid}.json"
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
  suffix="${suffix,,}"  # lowercase
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

  for arg in "$@"; do
    case "$arg" in
      --max-cycles=*) max_cycles="${arg#*=}" ;;
      --max-stuck=*) max_stuck="${arg#*=}" ;;
      --max-runtime=*) max_runtime="${arg#*=}" ;;
      --max-deep-per-cycle=*) max_deep_per_cycle="${arg#*=}" ;;
      --max-consecutive-deep=*) max_consecutive_deep="${arg#*=}" ;;
      *) echo "error=unknown argument: $arg" >&2; exit 2 ;;
    esac
  done

  # Validate required
  _require_positive_int "--max-cycles" "$max_cycles"
  _require_positive_int "--max-stuck" "$max_stuck"
  _require_positive_int "--max-deep-per-cycle" "$max_deep_per_cycle"
  _require_positive_int "--max-consecutive-deep" "$max_consecutive_deep"

  # Parse duration (optional)
  local runtime_seconds
  runtime_seconds=$(_parse_duration "$max_runtime")

  # Clean stale sessions (>24h, owned by current user)
  find /tmp -maxdepth 1 -name 'lean4-session-*.json' -user "$(id -u)" -mmin +1440 -delete 2>/dev/null || true

  # Create state file via mktemp (no race)
  _detect_backend
  local state_file
  state_file=$(mktemp /tmp/lean4-session-XXXXXX.json)
  local session_id
  session_id=$(basename "$state_file" .json)

  local now
  now=$(date +%s)

  # Resolve env file once at init and record it in state, so stop uses the
  # same file even if LEAN4_ENV_FILE/CLAUDE_ENV_FILE changes between calls.
  local resolved_env_file
  resolved_env_file=$(_resolve_env_file)
  # Only record if actually writable; otherwise empty = stdout-only fallback.
  if [[ -n "$resolved_env_file" ]]; then
    if [[ -e "$resolved_env_file" ]]; then
      # Existing file: must be both readable and writable.
      if [[ ! -r "$resolved_env_file" || ! -w "$resolved_env_file" ]]; then
        resolved_env_file=""
      fi
    else
      # File does not exist: parent directory must exist and be writable,
      # and we must be able to create the file.
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
  "consecutive_deep_cycles": 0
}
ENDJSON
  )

  _json_create "$state_file" "$content"

  # Persist session ID to the resolved env file
  _persist_env "export LEAN4_SESSION_ID=\"$session_id\""

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
      # Update cycles
      .cycles += 1 |

      # Update stuck
      (if $stuck_flag == 1 then .consecutive_stuck + 1 else 0 end) as $new_stuck |
      .consecutive_stuck = $new_stuck |

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

# Update cycles
d['cycles'] += 1

# Update stuck
d['consecutive_stuck'] = d['consecutive_stuck'] + 1 if stuck else 0

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
    jq '.deep_this_cycle += 1' "$file" > "$tmp" 2>/dev/null
    mv "$tmp" "$file"
  else
    python3 -c "
import json, tempfile, os
with open('$file') as f:
    d = json.load(f)
d['deep_this_cycle'] += 1
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
      "session_id=" + .session_id,
      "cycles=" + (.cycles | tostring) + "/" + (.max_cycles | tostring),
      "consecutive_stuck=" + (.consecutive_stuck | tostring) + "/" + (.max_stuck | tostring),
      "elapsed_seconds=" + ($elapsed | tostring),
      "elapsed_display=" + $elapsed_display,
      "deep_this_cycle=" + (.deep_this_cycle | tostring) + "/" + (.max_deep_per_cycle | tostring),
      "consecutive_deep_cycles=" + (.consecutive_deep_cycles | tostring) + "/" + (.max_consecutive_deep | tostring)
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
lines = [
    f\"session_id={d['session_id']}\",
    f\"cycles={d['cycles']}/{d['max_cycles']}\",
    f\"consecutive_stuck={d['consecutive_stuck']}/{d['max_stuck']}\",
    f'elapsed_seconds={elapsed}',
    f'elapsed_display={elapsed_display}',
    f\"deep_this_cycle={d['deep_this_cycle']}/{d['max_deep_per_cycle']}\",
    f\"consecutive_deep_cycles={d['consecutive_deep_cycles']}/{d['max_consecutive_deep']}\",
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
  local f="/tmp/${sid}.json"
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
  # Unpersist LEAN4_SESSION_ID from the env file
  if [[ -n "$recorded_env" && -f "$recorded_env" && -r "$recorded_env" && -w "$recorded_env" ]]; then
    grep -v "^export LEAN4_SESSION_ID=" "$recorded_env" > "${recorded_env}.tmp" 2>/dev/null || true
    mv "${recorded_env}.tmp" "$recorded_env"
  fi
}

# ---------------------------------------------------------------------------
# Main dispatch
# ---------------------------------------------------------------------------
subcmd="${1:-}"
shift || true

case "$subcmd" in
  init)     cmd_init "$@" ;;
  tick)     cmd_tick "$@" ;;
  can-deep) cmd_can_deep "$@" ;;
  deep)     cmd_deep "$@" ;;
  status)   cmd_status "$@" ;;
  stop)     cmd_stop "$@" ;;
  "")       echo "error=no subcommand specified (init|tick|can-deep|deep|status|stop)" >&2; exit 2 ;;
  *)        echo "error=unknown subcommand: $subcmd" >&2; exit 2 ;;
esac

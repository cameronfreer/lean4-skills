#!/usr/bin/env bash
#
# preflight_env.sh — single source of the Lean4 env validation checks AND
# the canonical "bootstrap environment not set up" recovery message.
#
# Three modes:
#   --bootstrap   Validate the INPUTS a SessionStart bootstrap needs, given
#                 CLAUDE_PLUGIN_ROOT (passed as $2, or read from env): the
#                 plugin tree layout exists and CLAUDE_ENV_FILE is usable.
#                 Called by hooks/bootstrap.sh before it persists anything.
#   --runtime     (default) Validate the SESSION state a later Bash tool call
#                 depends on: LEAN4_* vars point at real dirs, bin/ is on
#                 PATH, and the lean4-skills-* wrappers resolve. Used for
#                 on-demand diagnosis (e.g. /lean4:doctor env, or manual run
#                 via the lean4-skills-preflight wrapper).
#   --codex       Validate the installed native Codex plugin layout and its
#                 absolute wrapper contract. Does not require LEAN4_* shell
#                 variables, an environment file, or bin/ on PATH.
#
# Exit 0 when the checked mode passes; exit 2 with the canonical recovery
# block on stderr when it fails. Self-locating (BASH_SOURCE) so it never
# depends on $LEAN4_SCRIPTS being set.
#
# The three numbered recovery steps below are CANONICAL: doctor.md
# reproduces them byte-for-byte. If you change them here, update doctor.md
# (test_preflight_env.sh asserts doctor.md still contains each line).

set -euo pipefail

# emit_claude_recovery <problem-description>
# Prints the canonical recovery block to stderr. $1 is a mode-specific,
# one-line description of what was wrong (interpolated into "Problem:").
emit_claude_recovery() {
    local problem="$1"
    {
        echo "Lean4 bootstrap environment is not fully set up in this Claude Code session."
        echo "  Problem: ${problem}"
        echo "  Recovery:"
        echo "    1. Run /lean4:doctor env for a full diagnosis."
        echo "    2. Restart the Claude Code session (re-runs the SessionStart bootstrap hook)."
        echo "    3. If it persists, check the plugin hook/bootstrap state (hooks.json, bootstrap.sh)."
    } >&2
}

# emit_codex_recovery <problem-description>
# Canonical native-Codex recovery block. doctor.md carries these same three
# numbered lines and test_preflight_env.sh guards the agreement.
emit_codex_recovery() {
    local problem="$1"
    {
        echo "Lean4 native Codex helper runtime is not ready."
        echo "  Problem: ${problem}"
        echo "  Recovery:"
        echo "    1. Review and trust the lean4 plugin hooks in /hooks."
        echo "    2. Start a new Codex task (re-runs the SessionStart hook)."
        echo "    3. Run the absolute <plugin-root>/bin/lean4-skills-preflight --codex command; if it is missing, reinstall the plugin."
    } >&2
}

# check_bootstrap <plugin-root>
# Validates the tree layout + CLAUDE_ENV_FILE usability. Returns 0 on
# success; on failure emits the canonical block and returns 2.
check_bootstrap() {
    local root="$1"
    local problems=()

    if [[ -z "$root" ]]; then
        emit_claude_recovery "CLAUDE_PLUGIN_ROOT is not set (bootstrap hook invoked without it)"
        return 2
    fi
    [[ -d "$root/lib/scripts" ]] || problems+=("$root/lib/scripts does not exist")
    [[ -d "$root/skills/lean4/references" ]] || problems+=("$root/skills/lean4/references does not exist")
    [[ -d "$root/bin" ]] || problems+=("$root/bin does not exist")

    # CLAUDE_ENV_FILE usability: the var must be nonempty, its PARENT dir
    # must exist and be writable, and IF the file already exists it must be a
    # REGULAR writable file. We do not require the file to pre-exist —
    # first-run bootstrap creates it. The regular-file check rejects a
    # writable-but-non-persistent target (a directory, /dev/null, or a
    # symlink to a device): persistence there silently no-ops, which would
    # otherwise slip past input validation into a silent degraded bootstrap.
    local env_file="${CLAUDE_ENV_FILE:-}"
    if [[ -z "$env_file" ]]; then
        problems+=("CLAUDE_ENV_FILE is not set — env cannot be persisted for later tool calls")
    else
        local env_dir
        env_dir="$(dirname "$env_file")"
        if [[ ! -d "$env_dir" ]]; then
            problems+=("CLAUDE_ENV_FILE parent directory $env_dir does not exist")
        elif [[ ! -w "$env_dir" ]]; then
            problems+=("CLAUDE_ENV_FILE parent directory $env_dir is not writable")
        elif [[ -e "$env_file" && ! -f "$env_file" ]]; then
            problems+=("CLAUDE_ENV_FILE $env_file exists but is not a regular file (persistence would not stick)")
        elif [[ -f "$env_file" && ! -w "$env_file" ]]; then
            problems+=("CLAUDE_ENV_FILE $env_file exists but is not writable")
        fi
    fi

    if [[ ${#problems[@]} -gt 0 ]]; then
        local joined
        joined="$(printf '%s; ' "${problems[@]}")"
        emit_claude_recovery "${joined%; }"
        return 2
    fi
    return 0
}

# check_runtime
# Validates the session env a later Bash tool call depends on. Returns 0 on
# success; on failure emits the canonical block and returns 2.
check_runtime() {
    local problems=()
    local root="${LEAN4_PLUGIN_ROOT:-}"

    if [[ -z "$root" ]]; then
        problems+=("LEAN4_PLUGIN_ROOT is not set")
    elif [[ ! -d "$root" ]]; then
        problems+=("LEAN4_PLUGIN_ROOT ($root) is not a directory")
    fi

    if [[ -z "${LEAN4_SCRIPTS:-}" ]]; then
        problems+=("LEAN4_SCRIPTS is not set")
    elif [[ ! -d "${LEAN4_SCRIPTS}" ]]; then
        problems+=("LEAN4_SCRIPTS (${LEAN4_SCRIPTS}) is not a directory")
    fi

    if [[ -z "${LEAN4_REFS:-}" ]]; then
        problems+=("LEAN4_REFS is not set")
    elif [[ ! -d "${LEAN4_REFS}" ]]; then
        problems+=("LEAN4_REFS (${LEAN4_REFS}) is not a directory")
    fi

    # bin/ on PATH + a representative wrapper resolvable.
    if [[ -n "$root" ]] && [[ ":$PATH:" != *":$root/bin:"* ]]; then
        problems+=("$root/bin is not on PATH")
    fi
    if ! command -v lean4-skills-sorry-analyzer >/dev/null 2>&1; then
        problems+=("lean4-skills-* wrappers do not resolve on PATH")
    fi

    if [[ ${#problems[@]} -gt 0 ]]; then
        local joined
        joined="$(printf '%s; ' "${problems[@]}")"
        emit_claude_recovery "${joined%; }"
        return 2
    fi
    return 0
}

# check_codex <plugin-root>
# Validates the installed in-place Codex plugin and representative absolute
# wrappers. It intentionally makes no assertions about the caller's shell
# environment or PATH.
check_codex() {
    local root="$1"
    local problems=()

    if [[ -z "$root" ]]; then
        emit_codex_recovery "PLUGIN_ROOT is not set (Codex hook invoked without a plugin root)"
        return 2
    fi
    [[ -d "$root" ]] || problems+=("$root is not a directory")
    [[ -f "$root/.codex-plugin/plugin.json" ]] || problems+=("$root/.codex-plugin/plugin.json does not exist")
    [[ -f "$root/hooks/codex-hooks.json" ]] || problems+=("$root/hooks/codex-hooks.json does not exist")
    [[ -d "$root/lib/scripts" ]] || problems+=("$root/lib/scripts does not exist")
    [[ -f "$root/skills/lean4/SKILL.md" ]] || problems+=("$root/skills/lean4/SKILL.md does not exist")
    [[ -d "$root/skills/lean4/references" ]] || problems+=("$root/skills/lean4/references does not exist")
    [[ -d "$root/bin" ]] || problems+=("$root/bin does not exist")
    [[ -x "$root/bin/lean4-skills-preflight" ]] || problems+=("$root/bin/lean4-skills-preflight is missing or not executable")
    [[ -x "$root/bin/lean4-skills-sorry-analyzer" ]] || problems+=("$root/bin/lean4-skills-sorry-analyzer is missing or not executable")

    if [[ ${#problems[@]} -gt 0 ]]; then
        local joined
        joined="$(printf '%s; ' "${problems[@]}")"
        emit_codex_recovery "${joined%; }"
        return 2
    fi
    return 0
}

main() {
    local mode="${1:---runtime}"
    case "$mode" in
        --bootstrap)
            # Prefer the explicitly-passed root ($2); fall back to
            # CLAUDE_PLUGIN_ROOT from the environment.
            check_bootstrap "${2:-${CLAUDE_PLUGIN_ROOT:-}}"
            ;;
        --runtime)
            check_runtime
            ;;
        --codex)
            # Prefer an explicitly-passed root. PLUGIN_ROOT is Codex's native
            # hook variable; CLAUDE_PLUGIN_ROOT is its compatibility fallback.
            check_codex "${2:-${PLUGIN_ROOT:-${CLAUDE_PLUGIN_ROOT:-}}}"
            ;;
        *)
            echo "Usage: preflight_env.sh [--bootstrap [PLUGIN_ROOT] | --runtime | --codex [PLUGIN_ROOT]]" >&2
            exit 64
            ;;
    esac
}

main "$@"

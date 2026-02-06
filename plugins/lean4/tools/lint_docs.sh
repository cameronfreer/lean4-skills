#!/usr/bin/env bash
# Verify documentation consistency for the Lean4 plugin
# Usage: bash lint_docs.sh [--verbose]
#
# MAINTAINER-ONLY: This is a development tool for plugin maintainers,
# not a user-facing runtime script. It lives in tools/ rather than
# lib/scripts/ to keep it separate from the public LEAN4_SCRIPTS.

set -euo pipefail

VERBOSE="${1:-}"
PLUGIN_ROOT="${LEAN4_PLUGIN_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
ISSUES=0

log() {
    echo "$1"
}

warn() {
    echo "⚠️  $1"
    ((ISSUES++)) || true
}

ok() {
    echo "✓ $1"
}

# Check 1: Commands in doctor.md match actual command files
check_commands() {
    log ""
    log "Checking commands..."

    local cmd_dir="$PLUGIN_ROOT/commands"
    local actual_commands
    actual_commands=$(find "$cmd_dir" -name "*.md" -type f | xargs -I{} basename {} .md | sort)
    local count
    count=$(echo "$actual_commands" | wc -l | tr -d ' ')

    if [[ $count -eq 6 ]]; then
        ok "Found 6 command files"
    else
        warn "Expected 6 commands, found $count"
    fi

    # Check each command has required sections
    for cmd in $actual_commands; do
        local file="$cmd_dir/$cmd.md"
        local lines
        lines=$(wc -l < "$file")

        if [[ $lines -gt 120 ]]; then
            warn "$cmd.md: $lines lines (target: 80-120)"
        elif [[ $lines -lt 60 ]]; then
            warn "$cmd.md: $lines lines (too short, target: 80-120)"
        else
            [[ -n "$VERBOSE" ]] && ok "$cmd.md: $lines lines"
        fi

        # Check for required sections
        if ! grep -q "^## Usage" "$file"; then
            warn "$cmd.md: Missing '## Usage' section"
        fi
        if ! grep -q "^## Actions" "$file"; then
            warn "$cmd.md: Missing '## Actions' section"
        fi
        if ! grep -q "^## Safety" "$file"; then
            warn "$cmd.md: Missing '## Safety' section"
        fi
        if ! grep -q "^## See Also" "$file"; then
            warn "$cmd.md: Missing '## See Also' section"
        fi
    done
}

# Check 2: Agent files have required sections and match template
check_agents() {
    log ""
    log "Checking agents..."

    local agent_dir="$PLUGIN_ROOT/agents"
    local actual_agents
    actual_agents=$(find "$agent_dir" -name "*.md" -type f | xargs -I{} basename {} .md | sort)
    local count
    count=$(echo "$actual_agents" | wc -l | tr -d ' ')

    if [[ $count -eq 4 ]]; then
        ok "Found 4 agent files"
    else
        warn "Expected 4 agents, found $count"
    fi

    # Check each agent
    for agent in $actual_agents; do
        local file="$agent_dir/$agent.md"
        local lines
        lines=$(wc -l < "$file")

        if [[ $lines -gt 115 ]]; then
            warn "$agent.md: $lines lines (target: 80-110)"
        elif [[ $lines -lt 60 ]]; then
            warn "$agent.md: $lines lines (too short, target: 80-110)"
        else
            [[ -n "$VERBOSE" ]] && ok "$agent.md: $lines lines"
        fi

        # Check for required frontmatter
        if ! grep -q "^tools:" "$file"; then
            warn "$agent.md: Missing 'tools:' in frontmatter"
        fi
        if ! grep -q "^model:" "$file"; then
            warn "$agent.md: Missing 'model:' in frontmatter"
        fi
        if ! grep -q "^thinking:" "$file"; then
            warn "$agent.md: Missing 'thinking:' in frontmatter"
        fi

        # Check for required sections
        if ! grep -q "^## Inputs" "$file"; then
            warn "$agent.md: Missing '## Inputs' section"
        fi
        if ! grep -q "^## Actions" "$file"; then
            warn "$agent.md: Missing '## Actions' section"
        fi
        if ! grep -q "^## Output" "$file"; then
            warn "$agent.md: Missing '## Output' section"
        fi
        if ! grep -q "^## Constraints" "$file"; then
            warn "$agent.md: Missing '## Constraints' section"
        fi
        if ! grep -q "^## See Also" "$file"; then
            warn "$agent.md: Missing '## See Also' section"
        fi
    done
}

# Check 3: Reference files exist
check_references() {
    log ""
    log "Checking references..."

    local ref_dir="$PLUGIN_ROOT/skills/lean4/references"
    local ref_count
    ref_count=$(find "$ref_dir" -name "*.md" -type f | wc -l | tr -d ' ')

    # Check for required new reference files
    if [[ -f "$ref_dir/command-examples.md" ]]; then
        ok "command-examples.md exists"
    else
        warn "Missing command-examples.md"
    fi

    if [[ -f "$ref_dir/agent-workflows.md" ]]; then
        ok "agent-workflows.md exists"
    else
        warn "Missing agent-workflows.md"
    fi

    log "Total reference files: $ref_count"
}

# Check 4: Scripts are executable
check_scripts() {
    log ""
    log "Checking scripts..."

    local script_dir="$PLUGIN_ROOT/lib/scripts"
    local non_exec=0

    for script in "$script_dir"/*.sh "$script_dir"/*.py; do
        if [[ -f "$script" ]] && [[ ! -x "$script" ]]; then
            warn "$(basename "$script") is not executable"
            ((non_exec++)) || true
        fi
    done

    if [[ $non_exec -eq 0 ]]; then
        ok "All scripts are executable"
    fi
}

# Check 5: Cross-references are valid
check_cross_refs() {
    log ""
    log "Checking cross-references..."

    local all_files
    all_files=$(find "$PLUGIN_ROOT" -name "*.md" -type f)

    # Valid anchors for command-examples.md
    local cmd_anchors="prove autoprove checkpoint doctor golf review"

    # Valid anchors for agent-workflows.md
    local agent_anchors="lean4-sorry-filler-deep lean4-proof-repair lean4-proof-golfer lean4-axiom-eliminator"

    while IFS= read -r file; do
        # Check links to command-examples.md
        if grep -q "command-examples.md#" "$file" 2>/dev/null; then
            local anchors
            anchors=$(grep -oE "command-examples\.md#[a-z-]+" "$file" | sed 's/.*#//' | sort -u)
            for anchor in $anchors; do
                if ! echo "$cmd_anchors" | grep -qw "$anchor"; then
                    warn "$(basename "$file"): Invalid anchor #$anchor in command-examples.md link"
                fi
            done
        fi

        # Check links to agent-workflows.md
        if grep -q "agent-workflows.md#" "$file" 2>/dev/null; then
            local anchors
            anchors=$(grep -oE "agent-workflows\.md#[a-z0-9-]+" "$file" | sed 's/.*#//' | sort -u)
            for anchor in $anchors; do
                if ! echo "$agent_anchors" | grep -qw "$anchor"; then
                    warn "$(basename "$file"): Invalid anchor #$anchor in agent-workflows.md link"
                fi
            done
        fi
    done <<< "$all_files"

    ok "Cross-references checked"
}

# Main
log "Lean4 Plugin Documentation Lint"
log "================================"
log "(Maintainer tool - not a user-facing script)"

check_commands
check_agents
check_references
check_scripts
check_cross_refs

log ""
log "================================"
if [[ $ISSUES -eq 0 ]]; then
    log "✓ All checks passed"
    exit 0
else
    log "⚠️  $ISSUES issue(s) found"
    exit 1
fi

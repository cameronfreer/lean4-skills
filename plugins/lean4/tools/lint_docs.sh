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

        # Per-command line limits: prove/autoprove/doctor/review are inherently larger
        local max_lines=120
        case "$cmd" in
            prove|autoprove) max_lines=230 ;;
            doctor)          max_lines=220 ;;
            golf)            max_lines=150 ;;
            review)          max_lines=320 ;;
        esac

        if [[ $lines -gt $max_lines ]]; then
            warn "$cmd.md: $lines lines (target: 60-$max_lines)"
        elif [[ $lines -lt 60 ]]; then
            warn "$cmd.md: $lines lines (too short, target: 60-$max_lines)"
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

        local max_lines=115
        case "$agent" in
            lean4-proof-golfer) max_lines=135 ;;
        esac

        if [[ $lines -gt $max_lines ]]; then
            warn "$agent.md: $lines lines (target: 80-$max_lines)"
        elif [[ $lines -lt 60 ]]; then
            warn "$agent.md: $lines lines (too short, target: 80-$max_lines)"
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

        # Validate tool names against allowed set
        local allowed_tools="Read Grep Glob Edit Bash lean_goal lean_local_search lean_leanfinder lean_leansearch lean_loogle lean_multi_attempt lean_hover_info lean_diagnostic_messages"
        local tools_line
        tools_line=$(grep "^tools:" "$file" | sed 's/^tools: *//')
        if [[ -n "$tools_line" ]]; then
            IFS=',' read -ra tool_list <<< "$tools_line"
            for tool in "${tool_list[@]}"; do
                tool=$(echo "$tool" | xargs)  # trim whitespace
                if ! echo "$allowed_tools" | grep -qw "$tool"; then
                    warn "$agent.md: Unknown tool '$tool' in frontmatter"
                fi
            done
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

    if [[ -f "$ref_dir/cycle-engine.md" ]]; then
        ok "cycle-engine.md exists"
    else
        warn "Missing cycle-engine.md"
    fi

    if [[ -f "$ref_dir/lean4-custom-syntax.md" ]]; then
        ok "lean4-custom-syntax.md exists"
    else
        warn "Missing lean4-custom-syntax.md"
    fi

    if [[ -f "$ref_dir/scaffold-dsl.md" ]]; then
        ok "scaffold-dsl.md exists"
    else
        warn "Missing scaffold-dsl.md"
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

    # Valid anchors for cycle-engine.md
    local engine_anchors="six-phase-cycle lsp-first-protocol review-phase replan-phase stuck-definition deep-mode checkpoint-logic falsification-artifacts repair-mode safety"

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

        # Check links to cycle-engine.md
        if grep -q "cycle-engine.md#" "$file" 2>/dev/null; then
            local anchors
            anchors=$(grep -oE "cycle-engine\.md#[a-z-]+" "$file" | sed 's/.*#//' | sort -u)
            for anchor in $anchors; do
                if ! echo "$engine_anchors" | grep -qw "$anchor"; then
                    warn "$(basename "$file"): Invalid anchor #$anchor in cycle-engine.md link"
                fi
            done
        fi
    done <<< "$all_files"

    ok "Cross-references checked"
}

# Check 6: Reference file link validation
check_reference_links() {
    log ""
    log "Checking reference links..."

    local _rl_dir _rl_base _rl_targets _rl_target _rl_path _rl_anchor _rl_resolved _rl_found _rl_heading _rl_slug

    # Check all relative markdown links across plugin .md files
    while IFS= read -r file; do
        _rl_dir=$(dirname "$file")
        _rl_base=$(basename "$file")

        # Extract markdown links: [text](path.md) or [text](path.md#anchor)
        _rl_targets=$(grep -oE '\]\([a-zA-Z0-9_./-]+\.md(#[a-zA-Z0-9_-]+)?\)' "$file" 2>/dev/null | sed 's/\](\(.*\))/\1/' | sort -u || true)
        for _rl_target in $_rl_targets; do
            _rl_path="${_rl_target%%#*}"
            _rl_anchor="${_rl_target#*#}"
            [[ "$_rl_anchor" == "$_rl_target" ]] && _rl_anchor=""

            # Resolve relative to file's directory
            _rl_resolved=$(cd "$_rl_dir" && realpath "$_rl_path" 2>/dev/null || echo "")

            # Check target file exists
            if [[ -z "$_rl_resolved" || ! -f "$_rl_resolved" ]]; then
                warn "$_rl_base: Broken link to $_rl_path"
                continue
            fi

            # Check anchor exists as any heading level (if specified)
            if [[ -n "$_rl_anchor" ]]; then
                _rl_found=false
                while IFS= read -r _rl_heading; do
                    # Strip leading #s and space, lowercase, spaces→dashes, strip non-alnum-dash
                    _rl_slug=$(echo "$_rl_heading" | sed 's/^#\+ //' | tr '[:upper:]' '[:lower:]' | sed 's/ /-/g; s/[^a-z0-9-]//g')
                    if [[ "$_rl_slug" == "$_rl_anchor" ]]; then
                        _rl_found=true
                        break
                    fi
                done < <(grep -E "^#{1,6} " "$_rl_resolved")
                if [[ "$_rl_found" != "true" ]]; then
                    warn "$_rl_base: Broken anchor #$_rl_anchor in $_rl_path"
                fi
            fi
        done
    done < <(find "$PLUGIN_ROOT" -name "*.md" -type f)

    ok "Reference links checked"
}

# Check 7: Stale command names in runnable snippets
check_stale_commands() {
    log ""
    log "Checking for stale command names..."

    # Old names that should not appear outside MIGRATION.md
    local banned_commands="autoprover"
    local _sc_base _sc_line

    while IFS= read -r file; do
        # Skip MIGRATION.md (historical mentions OK)
        [[ "$(basename "$file")" == "MIGRATION.md" ]] && continue
        _sc_base=$(basename "$file")
        for cmd in $banned_commands; do
            if grep -qn "/lean4:$cmd" "$file" 2>/dev/null; then
                _sc_line=$(grep -n "/lean4:$cmd" "$file" | head -1 | cut -d: -f1)
                warn "$_sc_base:$_sc_line: Stale command /lean4:$cmd (renamed — see MIGRATION.md)"
            fi
        done
    done < <(find "$PLUGIN_ROOT" -name "*.md" -type f)

    ok "Stale command check done"
}

# Check 8: Bare script names in behavioral docs
check_bare_scripts() {
    log ""
    log "Checking for bare script invocations..."

    local _bs_base _bs_line _bs_match _bs_severity _bs_scripts _bs_pattern _bs_script

    # Build script list dynamically from lib/scripts/
    _bs_scripts=""
    for f in "$PLUGIN_ROOT"/lib/scripts/*.py "$PLUGIN_ROOT"/lib/scripts/*.sh; do
        [[ -f "$f" ]] && _bs_scripts="$_bs_scripts $(basename "$f")"
    done
    _bs_scripts=$(echo "$_bs_scripts" | xargs)  # trim

    if [[ -z "$_bs_scripts" ]]; then
        ok "No scripts found in lib/scripts/, skipping bare-script check"
        return
    fi

    # Build grep alternation: sorry_analyzer\.py|check_axioms_inline\.sh|...
    _bs_pattern=$(echo "$_bs_scripts" | tr ' ' '\n' | sed 's/\./\\./g' | paste -sd '|' -)

    while IFS= read -r file; do
        _bs_base=$(basename "$file")

        # Skip files where bare names are expected
        [[ "$_bs_base" == "MIGRATION.md" ]] && continue
        [[ "$_bs_base" == "SKILL.md" ]] && continue
        case "$file" in */lib/scripts/*) continue ;; esac

        # Severity: FAIL for commands/ and agents/, note for others
        _bs_severity="note"
        case "$file" in */commands/*|*/agents/*) _bs_severity="fail" ;; esac

        # Find lines containing any script name
        while IFS=: read -r _bs_line _bs_match; do
            [[ -z "$_bs_line" ]] && continue
            # Per-script check: for each known script, test if it appears bare on this line
            for _bs_script in $_bs_scripts; do
                # Skip if this script isn't on this line
                echo "$_bs_match" | grep -qF "$_bs_script" || continue
                # Portable: strip prefixed occurrences, check if bare name remains
                if echo "$_bs_match" | sed "s|LEAN4_SCRIPTS/$_bs_script||g" | grep -qF "$_bs_script"; then
                    if [[ "$_bs_severity" == "fail" ]]; then
                        warn "$_bs_base:$_bs_line: Bare script '$_bs_script' (use \$LEAN4_SCRIPTS/ prefix)"
                    else
                        [[ -n "$VERBOSE" ]] && log "  note: $_bs_base:$_bs_line: Bare '$_bs_script' in reference"
                    fi
                    break  # One warning per line is enough
                fi
            done
        done < <(grep -nE "($_bs_pattern)" "$file" 2>/dev/null || true)
    done < <(find "$PLUGIN_ROOT" -name "*.md" -type f)

    ok "Bare script check done"
}

# Check 9: Deep-safety invariants in prove/autoprove/cycle-engine
check_deep_safety() {
    log ""
    log "Checking deep-safety invariants..."

    local cmd_dir="$PLUGIN_ROOT/commands"
    local ref_dir="$PLUGIN_ROOT/skills/lean4/references"
    local _ds_file _ds_base

    # Required deep-safety flags as exact table rows in prove.md and autoprove.md
    local deep_flags="deep-snapshot deep-rollback deep-scope deep-max-files deep-max-lines deep-regression-gate"

    for cmd in prove autoprove; do
        _ds_file="$cmd_dir/$cmd.md"
        _ds_base="$cmd.md"
        for flag in $deep_flags; do
            if ! grep -q "| --$flag " "$_ds_file" 2>/dev/null; then
                warn "$_ds_base: Missing --$flag row in input table"
            fi
        done
    done

    # autoprove.md must have deep-safety coercion text
    _ds_file="$cmd_dir/autoprove.md"
    for coercion in "deep-rollback=never" "deep-regression-gate=off"; do
        if ! grep -q "$coercion" "$_ds_file" 2>/dev/null; then
            warn "autoprove.md: Missing coercion for $coercion"
        fi
    done

    # Both prove.md and autoprove.md must exclude rolled-back deep edits from checkpoint
    for cmd in prove autoprove; do
        _ds_file="$cmd_dir/$cmd.md"
        _ds_base="$cmd.md"
        if ! grep -q "rolled-back deep" "$_ds_file" 2>/dev/null; then
            warn "$_ds_base: Missing checkpoint exclusion for rolled-back deep edits"
        fi
    done

    # cycle-engine.md must have deep-safety sections
    _ds_file="$ref_dir/cycle-engine.md"
    _ds_base="cycle-engine.md"
    for heading in "Deep Safety Definitions" "Deep Snapshot and Rollback" "Deep Scope Fence" "Deep Regression Gate" "Deep Safety Coercions"; do
        if ! grep -q "$heading" "$_ds_file" 2>/dev/null; then
            warn "$_ds_base: Missing section: $heading"
        fi
    done

    # cycle-engine.md must document path-scoped snapshot and identical file set
    if ! grep -q "path-scoped" "$_ds_file" 2>/dev/null; then
        warn "$_ds_base: Missing path-scoped snapshot documentation"
    fi
    if ! grep -q "identical for baseline and comparison" "$_ds_file" 2>/dev/null; then
        warn "$_ds_base: Missing identical file set guarantee for regression gate"
    fi
    if ! grep -q "rollback.*fails.*skip checkpoint" "$_ds_file" 2>/dev/null; then
        warn "$_ds_base: Missing rollback-failure => skip checkpoint wording"
    fi

    ok "Deep-safety invariants checked"
}

# Check 10: Guardrail documentation completeness
check_guardrail_docs() {
    log ""
    log "Checking guardrail documentation..."

    local _gd_file _gd_base

    for doc in README.md MIGRATION.md; do
        _gd_file="$PLUGIN_ROOT/$doc"
        _gd_base="$doc"

        if [[ ! -f "$_gd_file" ]]; then
            warn "$_gd_base: File not found"
            continue
        fi

        if ! grep -qiE 'Lean project' "$_gd_file" 2>/dev/null; then
            warn "$_gd_base: Missing Lean project scope statement in guardrails section"
        fi
        if ! grep -q 'LEAN4_GUARDRAILS_DISABLE' "$_gd_file" 2>/dev/null; then
            warn "$_gd_base: Missing LEAN4_GUARDRAILS_DISABLE documentation"
        fi
        if ! grep -q 'LEAN4_GUARDRAILS_FORCE' "$_gd_file" 2>/dev/null; then
            warn "$_gd_base: Missing LEAN4_GUARDRAILS_FORCE documentation"
        fi
        if ! grep -q 'LEAN4_GUARDRAILS_BYPASS' "$_gd_file" 2>/dev/null; then
            warn "$_gd_base: Missing LEAN4_GUARDRAILS_BYPASS documentation"
        fi
        if ! grep -q 'LEAN4_GUARDRAILS_COLLAB_POLICY' "$_gd_file" 2>/dev/null; then
            warn "$_gd_base: Missing LEAN4_GUARDRAILS_COLLAB_POLICY documentation"
        fi
        # All three mode literals must appear together on one line (anchored to
        # avoid false-pass from unrelated uses of common words like "ask" or "block")
        if ! grep -qE 'ask.*allow.*block' "$_gd_file" 2>/dev/null; then
            warn "$_gd_base: Missing collaboration policy modes (ask, allow, block)"
        fi
        # Bypass must not be listed as bootstrap-set
        if grep -A2 'bootstrap' "$_gd_file" 2>/dev/null | grep -q 'LEAN4_GUARDRAILS_BYPASS'; then
            warn "$_gd_base: LEAN4_GUARDRAILS_BYPASS incorrectly listed as bootstrap-set"
        fi
    done

    ok "Guardrail documentation checked"
}

# Check 11: Guardrail implementation invariants
check_guardrail_impl() {
    log ""
    log "Checking guardrail implementation..."

    local _gi_file="$PLUGIN_ROOT/hooks/guardrails.sh"

    if [[ ! -f "$_gi_file" ]]; then
        warn "guardrails.sh: File not found"
        return
    fi

    if ! grep -q 'LEAN4_GUARDRAILS_DISABLE' "$_gi_file" 2>/dev/null; then
        warn "guardrails.sh: Missing LEAN4_GUARDRAILS_DISABLE support"
    fi
    if ! grep -q 'LEAN4_GUARDRAILS_FORCE' "$_gi_file" 2>/dev/null; then
        warn "guardrails.sh: Missing LEAN4_GUARDRAILS_FORCE support"
    fi
    if ! grep -q 'LEAN4_GUARDRAILS_BYPASS' "$_gi_file" 2>/dev/null; then
        warn "guardrails.sh: Missing LEAN4_GUARDRAILS_BYPASS support"
    fi
    # Bypass detection must use _strip_wrappers prefix diff (not raw regex)
    if ! grep -q '_strip_wrappers.*BYPASS\|_prefix.*BYPASS\|BYPASS.*_prefix' "$_gi_file" 2>/dev/null; then
        warn "guardrails.sh: Bypass detection should use _strip_wrappers prefix diff"
    fi
    if ! grep -q 'LEAN4_GUARDRAILS_COLLAB_POLICY' "$_gi_file" 2>/dev/null; then
        warn "guardrails.sh: Missing LEAN4_GUARDRAILS_COLLAB_POLICY support"
    fi
    # Invalid policy must fall back to ask (the *) default case)
    if ! grep -qE 'COLLAB_POLICY="ask"' "$_gi_file" 2>/dev/null; then
        warn "guardrails.sh: Missing invalid-policy fallback to ask"
    fi
    # At least 1 bypass hint in collaboration helper
    local _gi_hint_count
    _gi_hint_count=$(grep -c 'prefix with.*LEAN4_GUARDRAILS_BYPASS' "$_gi_file" 2>/dev/null) || _gi_hint_count=0
    if [[ $_gi_hint_count -lt 1 ]]; then
        warn "guardrails.sh: Missing bypass hint in collaboration policy helper"
    fi
    # Exactly 3 collaboration-op policy calls (push, amend, pr create)
    # Anchored to indented call sites, excludes function definition and comments
    local _gi_collab_count
    _gi_collab_count=$(grep -cE '^[[:space:]]+_check_collab_op[[:space:]]' "$_gi_file" 2>/dev/null) || _gi_collab_count=0
    if [[ $_gi_collab_count -ne 3 ]]; then
        warn "guardrails.sh: Expected 3 _check_collab_op calls (push, amend, pr create), found $_gi_collab_count"
    fi
    # Bypass hint must not appear in destructive blocks (reset, clean, checkout --, restore)
    # Check: no bypass hint line immediately after a destructive BLOCKED message
    if grep -A1 'BLOCKED.*reset --hard\|BLOCKED.*clean\|BLOCKED.*destructive git checkout\|BLOCKED.*checkout \. \|BLOCKED.*restore' "$_gi_file" 2>/dev/null | grep -q 'LEAN4_GUARDRAILS_BYPASS'; then
        warn "guardrails.sh: Bypass hint found in destructive block (must be collaboration-only)"
    fi
    # Bypass must never exit 0 directly — must defer through all destructive checks
    if grep -E 'BYPASS.*exit 0|exit 0.*BYPASS' "$_gi_file" 2>/dev/null | grep -vq '^\s*#'; then
        warn "guardrails.sh: Bypass must not exit 0 directly (must defer past destructive checks)"
    fi
    # Commands must be checked per-segment, not with raw whole-string matching
    if ! grep -q 'seg_match\|SEGMENTS' "$_gi_file" 2>/dev/null; then
        warn "guardrails.sh: Missing segment-based command parsing (raw-string matching is insufficient)"
    fi
    # Lean marker detection
    for marker in lakefile.lean lean-toolchain lakefile.toml; do
        if ! grep -q "$marker" "$_gi_file" 2>/dev/null; then
            warn "guardrails.sh: Missing Lean marker detection for $marker"
        fi
    done
    # Message prefix: must have qualified prefix, must not have bare "BLOCKED:" without qualifier
    if ! grep -q 'BLOCKED (Lean guardrail):' "$_gi_file" 2>/dev/null; then
        warn "guardrails.sh: Missing 'BLOCKED (Lean guardrail):' message prefix"
    fi
    # Reject any BLOCKED that isn't followed by " (Lean guardrail)" — catches quotes, format changes
    if grep -E 'BLOCKED[^(]' "$_gi_file" 2>/dev/null | grep -vq 'BLOCKED (Lean guardrail)' 2>/dev/null; then
        warn "guardrails.sh: Found bare BLOCKED without '(Lean guardrail)' qualifier"
    fi

    ok "Guardrail implementation checked"
}

# Check 12: Golf safety policy terms
check_golf_policy() {
    log ""
    log "Checking golf safety policy..."

    # golf.md: section headings anchor the policy blocks
    local file="$PLUGIN_ROOT/commands/golf.md"
    local missing=0
    for term in \
        "### Bulk Rewrite Safety" \
        "### Delegation Execution Policy" \
        "Auto-revert.*sorry count increases" \
        "Permission gate.*stop delegation immediately" \
        "never launch additional agents after first" \
        "\\| --max-delegates" \
        "never inside tactic blocks or calc blocks" \
        "context.*(uncertain|ambiguous).*skip|skip.*never force" \
        "nested tactic.mode boundary|nested.*by.*skip"; do
        if ! grep -qE "$term" "$file"; then
            warn "golf.md: Missing policy anchor: '$term'"
            missing=1
        fi
    done
    if [[ $missing -eq 0 ]]; then
        ok "golf.md: All safety policy anchors present"
    fi

    # lean4-proof-golfer.md: section heading + policy phrases
    local agent_file="$PLUGIN_ROOT/agents/lean4-proof-golfer.md"
    local agent_missing=0
    for term in \
        "## Delegation Awareness" \
        "Auto-revert batch if sorry count" \
        "permission denied.*stop immediately" \
        "do NOT retry or request again" \
        "max-delegates.*parent handles" \
        "nested tactic.mode|nested.*by.*skip" \
        "no broad replace-all|broad replace"; do
        if ! grep -qiE "$term" "$agent_file"; then
            warn "lean4-proof-golfer.md: Missing policy anchor: '$term'"
            agent_missing=1
        fi
    done
    if [[ $agent_missing -eq 0 ]]; then
        ok "lean4-proof-golfer.md: All agent policy anchors present"
    fi

    # proof-golfing.md: bulk trigger wording must match command+agent
    local ref_file="$PLUGIN_ROOT/skills/lean4/references/proof-golfing.md"
    local ref_missing=0
    for term in \
        "≥4 whitelisted.*candidates|>=4 whitelisted.*candidates" \
        "preview.*confirmation.*gate|user confirms.*preview"; do
        if ! grep -qE "$term" "$ref_file"; then
            warn "proof-golfing.md: Missing bulk-trigger anchor: '$term'"
            ref_missing=1
        fi
    done
    if [[ $ref_missing -eq 0 ]]; then
        ok "proof-golfing.md: Bulk-trigger anchors present"
    fi
}

# Check 13: Backward-compat scripts alias
check_compat_alias() {
    log ""
    log "Checking compat alias..."

    local _ca_link="$PLUGIN_ROOT/scripts"
    local _ca_target

    if [[ ! -L "$_ca_link" ]]; then
        warn "scripts: Missing compat symlink (expected scripts -> lib/scripts)"
        return
    fi

    _ca_target=$(readlink "$_ca_link")
    if [[ "$_ca_target" != "lib/scripts" ]]; then
        warn "scripts: Symlink points to '$_ca_target' (expected lib/scripts)"
    else
        [[ -n "$VERBOSE" ]] && ok "scripts -> lib/scripts symlink"
    fi

    ok "Compat alias checked"
}

# Check 14: Suspicious script path patterns in docs
check_path_patterns() {
    log ""
    log "Checking for suspicious script path patterns..."

    local _pp_base _pp_line _pp_match

    while IFS= read -r file; do
        _pp_base=$(basename "$file")

        # Skip files where raw paths are expected
        [[ "$_pp_base" == "MIGRATION.md" ]] && continue
        case "$file" in */lib/scripts/*|*/tools/*) continue ;; esac

        # Detect hardcoded cache paths: .claude/plugins/.../scripts/
        while IFS=: read -r _pp_line _pp_match; do
            [[ -z "$_pp_line" ]] && continue
            warn "$_pp_base:$_pp_line: Hardcoded cache path (use \$LEAN4_SCRIPTS/ instead)"
        done < <(grep -nE '\.claude/plugins/.*/scripts/' "$file" 2>/dev/null || true)

        # Detect bare /scripts/*.py|.sh that aren't lib/scripts or $LEAN4_SCRIPTS
        while IFS=: read -r _pp_line _pp_match; do
            [[ -z "$_pp_line" ]] && continue
            if echo "$_pp_match" | grep -qE '(lib/scripts|\$LEAN4_SCRIPTS|\$\{LEAN4_SCRIPTS)'; then
                continue
            fi
            warn "$_pp_base:$_pp_line: Suspicious path pattern (use lib/scripts/ or \$LEAN4_SCRIPTS/)"
        done < <(grep -nE '/scripts/[a-zA-Z_]+\.(py|sh)' "$file" 2>/dev/null || true)
    done < <(find "$PLUGIN_ROOT" \( -name "*.md" -o -name "*.sh" \) -type f)

    ok "Path pattern check done"
}

# Check 15: Custom syntax reference integrity
check_custom_syntax_refs() {
    log ""
    log "Checking custom syntax references..."

    local skill_md="$PLUGIN_ROOT/skills/lean4/SKILL.md"
    local syntax_ref="$PLUGIN_ROOT/skills/lean4/references/lean4-custom-syntax.md"

    # SKILL.md must have actual markdown link targets to both refs
    if grep -qE '\(references/lean4-custom-syntax\.md\)' "$skill_md" 2>/dev/null; then
        ok "SKILL.md links lean4-custom-syntax.md"
    else
        warn "SKILL.md missing link to references/lean4-custom-syntax.md"
    fi

    if grep -qE '\(references/scaffold-dsl\.md\)' "$skill_md" 2>/dev/null; then
        ok "SKILL.md links scaffold-dsl.md"
    else
        warn "SKILL.md missing link to references/scaffold-dsl.md"
    fi

    # lean4-custom-syntax.md must contain the scope guard
    if grep -q 'Not part of the prove/autoprove default loop' "$syntax_ref" 2>/dev/null; then
        ok "lean4-custom-syntax.md contains scope guard"
    else
        warn "lean4-custom-syntax.md missing scope guard ('Not part of the prove/autoprove default loop')"
    fi
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
check_reference_links
check_stale_commands
check_bare_scripts
check_deep_safety
check_guardrail_docs
check_guardrail_impl
check_golf_policy
check_compat_alias
check_path_patterns
check_custom_syntax_refs

log ""
log "================================"
if [[ $ISSUES -eq 0 ]]; then
    log "✓ All checks passed"
    exit 0
else
    log "⚠️  $ISSUES issue(s) found"
    exit 1
fi

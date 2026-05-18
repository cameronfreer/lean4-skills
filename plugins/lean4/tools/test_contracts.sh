#!/usr/bin/env bash
# Semantic contract tests for the formalize outer loop documentation.
# Verifies cross-document enum consistency, flag validation rules,
# state-machine traces, and negative guards.
#
# MAINTAINER-ONLY: Development tool for plugin maintainers.

set -euo pipefail

# Always resolve from script location — not LEAN4_PLUGIN_ROOT, which may
# point to a cached install with stale content.  These tests verify the
# working-copy docs, so dirname is the correct root.
PLUGIN_ROOT="$(cd "$(dirname "$0")/.." && pwd)"

# Key files
AUTOPROVE="$PLUGIN_ROOT/commands/autoprove.md"
CYCLE_ENGINE="$PLUGIN_ROOT/skills/lean4/references/cycle-engine.md"
REVIEW="$PLUGIN_ROOT/commands/review.md"
FORMALIZE="$PLUGIN_ROOT/commands/formalize.md"
EXAMPLES="$PLUGIN_ROOT/skills/lean4/references/command-examples.md"
DRAFT="$PLUGIN_ROOT/commands/draft.md"
AUTOFORMALIZE="$PLUGIN_ROOT/commands/autoformalize.md"

PASS=0
FAIL=0

ok() {
    echo "  PASS: $1"
    (( ++PASS ))
}

fail() {
    echo "  FAIL: $1"
    (( ++FAIL ))
}

# extract_section FILE HEADING
# Extracts lines from HEADING to the next heading of equal or higher level.
# Skips the heading line itself. Fence-aware: ignores headings inside ``` blocks.
extract_section() {
    local file="$1"
    local heading="$2"
    local prefix
    prefix="${heading%%[^#]*}"
    local level="${#prefix}"
    awk -v start="$heading" -v lvl="$level" '
        /^```/ { in_fence = !in_fence }
        $0 == start && !found { found=1; next }
        found && !in_fence && /^#+/ {
            match($0, /^#+/)
            if (RLENGTH <= lvl) exit
        }
        found { print }
    ' "$file"
}

# assert_ordered TEXT token1 token2 ...
# Fails if any token is missing or appears out of order (strictly increasing line numbers).
assert_ordered() {
    local text="$1"; shift
    local prev_line=0
    local token
    local line
    for token in "$@"; do
        line=$(echo "$text" | grep -n -m1 "$token" | cut -d: -f1)
        if [[ -z "$line" ]]; then
            return 1
        fi
        if [[ "$line" -le "$prev_line" ]]; then
            return 1
        fi
        prev_line="$line"
    done
    return 0
}

echo "=== Semantic contract tests ==="

# ─── Suite 1: Spec Matrix — Flag Validation Semantics ───

echo ""
echo "-- Suite 1: Flag Validation Semantics --"

validation_section=$(extract_section "$AUTOPROVE" "### Formalize Flag Validation")

# Check 1: auto + source (not claim-select/formalize-out) → error/requires
if echo "$validation_section" | grep -i 'auto' | grep -i 'source' | grep -iv 'claim-select' | grep -iv 'formalize-out' | grep -qiE 'error|requires'; then
    ok "Check 1: auto + source → error/requires"
else
    fail "Check 1: auto + source → error/requires"
fi

# Check 2: auto + claim-select → error/requires
if echo "$validation_section" | grep -i 'auto' | grep -i 'claim-select' | grep -qiE 'error|requires'; then
    ok "Check 2: auto + claim-select → error/requires"
else
    fail "Check 2: auto + claim-select → error/requires"
fi

# Check 3: auto + formalize-out (not source/claim-select) → error/requires
if echo "$validation_section" | grep -i 'auto' | grep -i 'formalize-out' | grep -iv 'claim-select' | grep -qiE 'error|requires'; then
    ok "Check 3: auto + formalize-out → error/requires"
else
    fail "Check 3: auto + formalize-out → error/requires"
fi

# Check 4: restage + source → ignored/warn/NOT require
if echo "$validation_section" | grep -i 'restage' | grep -i 'source' | grep -qiE 'ignored|warn|NOT require'; then
    ok "Check 4: restage + source → ignored/warn"
else
    fail "Check 4: restage + source → ignored/warn"
fi

# Check 5: never + source → ignores/warn
if echo "$validation_section" | grep -i 'never' | grep -i 'source' | grep -qiE 'ignores|warn'; then
    ok "Check 5: never + source → ignores/warn"
else
    fail "Check 5: never + source → ignores/warn"
fi

# Check 6: claim-select without source → ignored
if echo "$validation_section" | grep -i 'claim-select' | grep -i 'source' | grep -qi 'ignored'; then
    ok "Check 6: claim-select without source → ignored"
else
    fail "Check 6: claim-select without source → ignored"
fi

# Check 7: statement-policy coercion when formalize active
if echo "$validation_section" | grep -i 'formalize.*restage\|auto' | grep -qi 'rewrite-generated-only'; then
    ok "Check 7: formalize=restage|auto coerces statement-policy → rewrite-generated-only"
else
    fail "Check 7: missing statement-policy coercion rule for formalize modes"
fi

# Check 8: claim-select documented as queue-extraction filter
if echo "$validation_section" | grep -i 'claim-select' | grep -qi 'queue-extraction\|applied once'; then
    ok "Check 8: claim-select documented as one-time queue filter"
else
    fail "Check 8: claim-select missing queue-extraction semantics"
fi

# Check 9: --formalize mode enum match between inputs table and outer loop table
inputs_modes=$(grep -E '^\| --formalize ' "$AUTOPROVE" | grep -oE '`[a-z]+`' | sed 's/`//g' | sort -u)
loop_modes=$(extract_section "$AUTOPROVE" "## Formalize Outer Loop (Deprecated)" | grep '^| `' | grep -oE '`[a-z]+`' | sed 's/`//g' | sort -u)
if [[ "$inputs_modes" == "$loop_modes" ]]; then
    ok "Check 9: --formalize modes match (inputs ↔ outer loop table)"
else
    fail "Check 7: --formalize modes mismatch: inputs=[$inputs_modes] loop=[$loop_modes]"
fi

# ─── Suite 2: Enum Consistency ───

echo ""
echo "-- Suite 2: Enum Consistency --"

# Check 10: next_action enum — review.md classification ↔ cycle-engine Review Router
review_actions=$(grep 'next_action classification' "$REVIEW" | grep -oE '`[a-z-]+`' | sed 's/`//g' | sort -u)
router_section=$(extract_section "$CYCLE_ENGINE" "### Review Router")
router_actions=$(echo "$router_section" | grep '^| `' | grep -oE '`[a-z-]+`' | sed 's/`//g' | sort -u)
if [[ "$review_actions" == "$router_actions" ]]; then
    ok "Check 10: next_action enum match (review ↔ cycle-engine)"
else
    fail "Check 10: next_action mismatch: review=[$review_actions] router=[$router_actions]"
fi

# Check 9: --formalize modes — autoprove ↔ cycle-engine
ce_outer_section=$(extract_section "$CYCLE_ENGINE" "## Synthesis Outer Loop")
ce_modes=$(echo "$ce_outer_section" | grep -oE -- '--formalize=[a-z|]+' | tr '|' '\n' | sed 's/--formalize=//' | sort -u)
if [[ "$inputs_modes" == "$ce_modes" ]]; then
    ok "Check 11: --formalize modes match (autoprove ↔ cycle-engine)"
else
    fail "Check 9: --formalize modes mismatch: autoprove=[$inputs_modes] cycle-engine=[$ce_modes]"
fi

# Check 12: --claim-select policies — autoprove ↔ formalize
ap_claim=$(grep -E '^\| --claim-select ' "$AUTOPROVE" | grep -oE '`[a-z]+' | sed 's/`//' | sort -u)
fm_claim=$(grep -E '^\| --claim-select ' "$FORMALIZE" | grep -oE '`[a-z]+' | sed 's/`//' | sort -u)
if [[ "$ap_claim" == "$fm_claim" ]]; then
    ok "Check 12: --claim-select policies match (autoprove ↔ formalize)"
else
    fail "Check 12: --claim-select mismatch: autoprove=[$ap_claim] formalize=[$fm_claim]"
fi

# Check 12b: --claim-select policies — autoformalize ↔ draft
af_claim=$(grep -E '^\| --claim-select ' "$AUTOFORMALIZE" | grep -oE '`[a-z]+' | sed 's/`//' | sort -u)
dr_claim=$(grep -E '^\| --claim-select ' "$DRAFT" | grep -oE '`[a-z]+' | sed 's/`//' | sort -u)
if [[ "$af_claim" == "$dr_claim" ]]; then
    ok "Check 12b: --claim-select policies match (autoformalize ↔ draft)"
else
    fail "Check 12b: --claim-select mismatch: autoformalize=[$af_claim] draft=[$dr_claim]"
fi

# Check 13: --statement-policy — autoprove ↔ cycle-engine Statement Safety
ap_stmt=$(grep -E '^\| --statement-policy ' "$AUTOPROVE" | grep -oE '`[a-z][a-z-]*`' | sed 's/`//g' | sort -u)
stmt_section=$(extract_section "$CYCLE_ENGINE" "### Statement Safety")
ce_stmt=$(echo "$stmt_section" | grep -oE '`[a-z][a-z-]*`' | sed 's/`//g' | sort -u)
if [[ "$ap_stmt" == "$ce_stmt" ]]; then
    ok "Check 13: --statement-policy match (autoprove ↔ cycle-engine)"
else
    fail "Check 13: --statement-policy mismatch: autoprove=[$ap_stmt] cycle-engine=[$ce_stmt]"
fi

# Check 13b: --statement-policy — autoformalize ↔ cycle-engine
af_stmt=$(grep -E '^\| --statement-policy ' "$AUTOFORMALIZE" | grep -oE '`[a-z][a-z-]*`' | sed 's/`//g' | sort -u)
if [[ "$af_stmt" == "$ce_stmt" ]]; then
    ok "Check 13b: --statement-policy match (autoformalize ↔ cycle-engine)"
else
    fail "Check 13b: --statement-policy mismatch: autoformalize=[$af_stmt] cycle-engine=[$ce_stmt]"
fi

# Check 14: Stop reasons — bold labels slugified ↔ pipe-delimited tokens
slug_for_label() {
    case "$1" in
        Completion)         echo "completion" ;;
        "Max stuck cycles") echo "max-stuck" ;;
        "Max cycles")       echo "max-cycles" ;;
        "Max runtime")      echo "max-runtime" ;;
        "Manual user stop") echo "user-stop" ;;
        "Queue empty")      echo "queue-empty" ;;
        *)                  echo "UNMAPPED:$1" ;;
    esac
}

stop_section=$(extract_section "$AUTOPROVE" "## Stop Conditions")
stop_labels=$(echo "$stop_section" | grep -E '^[0-9]+\.' | grep -oE '\*\*[^*]+\*\*' | sed 's/\*\*//g')

stop_slugs=""
while IFS= read -r label; do
    stop_slugs+="$(slug_for_label "$label")"$'\n'
done <<< "$stop_labels"
stop_slugs=$(echo "$stop_slugs" | sed '/^$/d' | sort -u)

summary_section=$(extract_section "$AUTOPROVE" "## Structured Summary on Stop")
reason_tokens=$(echo "$summary_section" | grep 'Reason stopped' | grep -oE '\[[^]]+\]' | tr -d '[]' | tr '|' '\n' | sed 's/^ *//;s/ *$//' | sort -u)

if [[ "$stop_slugs" == "$reason_tokens" ]]; then
    ok "Check 14: Stop reason slugs match summary tokens"
else
    fail "Check 14: Stop reason mismatch: slugs=[$stop_slugs] tokens=[$reason_tokens]"
fi

# ─── Suite 3: State-Machine Traces ───

echo ""
echo "-- Suite 3: State-Machine Traces --"

# Check 13: Every Review Router row has non-empty response column
bad_router_rows=$(echo "$router_section" | awk -F'|' '
    /^\| `[a-z]/ {
        resp = $3
        gsub(/[ \t]/, "", resp)
        if (resp == "") print $2
    }
')
if [[ -z "$bad_router_rows" ]]; then
    ok "Check 15: All Review Router rows have non-empty response"
else
    fail "Check 15: Empty response for: $bad_router_rows"
fi

# Check 16: Algorithm references only valid --formalize modes
algo_section=$(extract_section "$CYCLE_ENGINE" "### Algorithm")
algo_modes=$(echo "$algo_section" | grep -oE -- '--formalize=[a-z-]+' | sed 's/--formalize=//' | sort -u)
valid_modes=$(printf '%s\n' auto never restage)
invalid_modes=$(comm -23 <(echo "$algo_modes") <(echo "$valid_modes"))
if [[ -z "$invalid_modes" ]]; then
    ok "Check 16: Algorithm references only valid --formalize modes"
else
    fail "Check 16: Invalid modes in Algorithm: $invalid_modes"
fi

# Check 17: Statement Safety has 3 policies with non-empty restage column
policy_rows=$(echo "$stmt_section" | awk -F'|' '/^\| `[a-z]/ { print }')
policy_count=$(echo "$policy_rows" | grep -c . || true)
empty_restage=$(echo "$policy_rows" | awk -F'|' '{ gsub(/[ \t]/, "", $5); if ($5 == "") print NR }')
if [[ "$policy_count" -eq 3 ]] && [[ -z "$empty_restage" ]]; then
    ok "Check 17: Statement Safety has 3 policies with non-empty restage"
else
    fail "Check 17: Statement Safety: count=$policy_count, empty_restage=[$empty_restage]"
fi

# Check 16: Scenario — auto happy path (token ordering in source-backed block)
source_block=$(echo "$algo_section" | awk '/Source-backed/,/Scope-backed/ { print }')
if assert_ordered "$source_block" "claim queue" "invoke draft" "Inner Cycle" "Advance"; then
    ok "Check 18: Auto happy path token order"
else
    fail "Check 18: Auto happy path tokens out of order or missing"
fi

# Check 17: Scenario — stuck → redraft (token ordering + re-draft co-occurrence)
if assert_ordered "$source_block" "stuck" "next_action" "redraft"; then
    # redraft and re-draft share a line; verify co-occurrence
    if echo "$source_block" | grep 'redraft' | grep -q 're-draft'; then
        ok "Check 19: Stuck → redraft token order + re-draft step"
    else
        fail "Check 19: redraft line missing re-draft step"
    fi
else
    fail "Check 19: Stuck → redraft tokens out of order or missing"
fi

# Check 20: preserve row restage column contains Error/manual
preserve_restage=$(echo "$stmt_section" | grep '`preserve`' | awk -F'|' '{ print $5 }')
if echo "$preserve_restage" | grep -qiE 'error|manual'; then
    ok "Check 20: preserve blocks restage (Error/manual)"
else
    fail "Check 20: preserve restage column: [$preserve_restage]"
fi

# ─── Suite 4: Negative Guards ───

echo ""
echo "-- Suite 4: Negative Guards --"

# Check 21: No stale 'bootstrap' in autoprove.md, cycle-engine.md, command-examples.md
stale_bootstrap=""
for f in "$AUTOPROVE" "$CYCLE_ENGINE" "$EXAMPLES"; do
    hits=$(grep -in 'bootstrap' "$f" | grep -iv 'bootstrap\.sh' | grep -iv 'bootstrap LSP' || true)
    if [[ -n "$hits" ]]; then
        stale_bootstrap+="$(basename "$f"): $hits"$'\n'
    fi
done
if [[ -z "$stale_bootstrap" ]]; then
    ok "Check 21: No stale bootstrap references"
else
    fail "Check 21: Stale bootstrap: $stale_bootstrap"
fi

# Check 22: No stale claim-batch-size in plugin
cbs_hits=$(grep -r 'claim-batch-size' "$PLUGIN_ROOT" --exclude='test_contracts.sh' || true)
if [[ -z "$cbs_hits" ]]; then
    ok "Check 22: No stale claim-batch-size references"
else
    fail "Check 22: Stale claim-batch-size: $cbs_hits"
fi

# Check 23: next_action in stuck-mode output example, absent from batch-mode output
# 21a: stuck-mode fenced block contains next_action
stuck_block=$(awk '
    /\*\*Stuck mode output format:\*\*/ { found=1; next }
    found && /^```/ && !in_block { in_block=1; next }
    found && in_block && /^```/ { exit }
    in_block { print }
' "$REVIEW")

if echo "$stuck_block" | grep -q 'next_action'; then
    pass_21a=1
else
    pass_21a=0
fi

# 21b: batch-mode ## Output section does NOT contain next_action
batch_output=$(extract_section "$REVIEW" "## Output")
if echo "$batch_output" | grep -q 'next_action'; then
    pass_21b=0
else
    pass_21b=1
fi

if [[ "$pass_21a" -eq 1 ]] && [[ "$pass_21b" -eq 1 ]]; then
    ok "Check 23: next_action in stuck output, absent from batch output"
else
    fail "Check 23: stuck_has_next_action=$pass_21a, batch_lacks_next_action=$pass_21b"
fi

###############################################################################
# Suite 5: Agent dispatch name resolution
###############################################################################
echo ""
echo "--- Suite 5: Agent dispatch name resolution ---"

# Build set of valid agent names from frontmatter
valid_agents=""
for agent_file in "$PLUGIN_ROOT"/agents/*.md; do
    aname=$(grep -m1 '^name:' "$agent_file" | sed 's/^name: *//')
    if [[ -n "$aname" ]]; then
        valid_agents="$valid_agents $aname"
    fi
done

# Search plugin docs for dispatch references to lean4 plugin agents.
# Match only known agent name patterns (not generic "Dispatch an Explore agent" etc.)
agent_pattern='sorry-filler-deep|proof-repair|proof-golfer|axiom-eliminator'
# Also check for old lean4- prefixed forms that should no longer exist
old_pattern='lean4-sorry-filler-deep|lean4-proof-repair|lean4-proof-golfer|lean4-axiom-eliminator'

dispatch_ok=1

# Check for stale old-form references
old_refs=$(grep -rn -E "$old_pattern" "$PLUGIN_ROOT"/skills/ "$PLUGIN_ROOT"/commands/ "$PLUGIN_ROOT"/agents/ 2>/dev/null \
    | grep -v '^Binary' || true)
if [[ -n "$old_refs" ]]; then
    fail "Check 24: Stale old-form agent names found:"
    echo "$old_refs" | head -10
    dispatch_ok=0
fi

# Check dispatch examples resolve to valid agent names
dispatch_refs=$(grep -rn -oE "Dispatch ($agent_pattern)" "$PLUGIN_ROOT"/skills/ "$PLUGIN_ROOT"/commands/ 2>/dev/null \
    | sed 's/.*Dispatch //' || true)
for ref in $dispatch_refs; do
    if ! echo "$valid_agents" | grep -qw "$ref"; then
        fail "Check 24: Dispatch reference '$ref' does not match any agent frontmatter name"
        dispatch_ok=0
    fi
done

if [[ "$dispatch_ok" -eq 1 ]]; then
    ok "Check 24: All agent dispatch names resolve to valid frontmatter names"
fi

# ── Check 25: Session tracking contract ──────────────────────────────────
# Autonomous commands must reference cycle_tracker.sh in their Invocation Contract.
# cycle-engine.md must have the Session Tracking section and Enforcement Levels table.

check25_ok=1

for cmd_file in "$AUTOPROVE" "$AUTOFORMALIZE"; do
    base=$(basename "$cmd_file")
    if ! grep -q 'cycle_tracker\.sh' "$cmd_file" 2>/dev/null; then
        fail "Check 25: $base missing cycle_tracker.sh reference in Invocation Contract"
        check25_ok=0
    fi
done

if ! grep -q '## Session Tracking' "$CYCLE_ENGINE" 2>/dev/null; then
    fail "Check 25: cycle-engine.md missing Session Tracking section"
    check25_ok=0
fi

if ! grep -q 'Enforcement Levels' "$CYCLE_ENGINE" 2>/dev/null; then
    fail "Check 25: cycle-engine.md missing Enforcement Levels table"
    check25_ok=0
fi

# No command file should describe --max-total-runtime as "Hard stop"
for cmd_file in "$AUTOPROVE" "$AUTOFORMALIZE"; do
    base=$(basename "$cmd_file")
    if grep -qE '^\| --max-total-runtime .*Hard stop' "$cmd_file" 2>/dev/null; then
        fail "Check 25: $base describes --max-total-runtime as Hard stop"
        check25_ok=0
    fi
done

# --deep-time-budget should include "advisory" (case-insensitive) in all 4 commands
for cmd_file in "$AUTOPROVE" "$AUTOFORMALIZE" \
                "$PLUGIN_ROOT/commands/prove.md" \
                "$FORMALIZE"; do
    base=$(basename "$cmd_file")
    if ! grep -i 'deep-time-budget.*advisory\|advisory.*deep-time-budget' "$cmd_file" 2>/dev/null; then
        # Check the table row specifically
        if ! grep 'deep-time-budget' "$cmd_file" 2>/dev/null | grep -qi 'advisory'; then
            fail "Check 25: $base --deep-time-budget not labeled as advisory"
            check25_ok=0
        fi
    fi
done

# Flag-name consistency: autoprove init contract block must reference long user-facing flags.
# The init contract spans multiple lines around "cycle_tracker.sh init", so extract a window.
if grep -q "cycle_tracker.sh.*init" "$AUTOPROVE" 2>/dev/null; then
    init_block=$(grep -A 3 "cycle_tracker.sh.*init" "$AUTOPROVE" 2>/dev/null)
    for flag in max-stuck-cycles max-total-runtime max-consecutive-deep-cycles; do
        if ! echo "$init_block" | grep -q "$flag"; then
            fail "Check 25: autoprove.md init contract missing --$flag"
            check25_ok=0
        fi
    done
fi

# autoformalize must NOT reference autoprove-only flag --max-consecutive-deep-cycles in init contract
if grep -q "cycle_tracker.sh.*init" "$AUTOFORMALIZE" 2>/dev/null; then
    af_init_block=$(grep -A 3 "cycle_tracker.sh.*init" "$AUTOFORMALIZE" 2>/dev/null)
    if echo "$af_init_block" | grep -q "max-consecutive-deep-cycles"; then
        fail "Check 25: autoformalize.md init contract references autoprove-only --max-consecutive-deep-cycles"
        check25_ok=0
    fi
fi

# cycle_tracker.sh must accept the long alias forms (grep the case statement)
TRACKER="$PLUGIN_ROOT/lib/scripts/cycle_tracker.sh"
if [[ -f "$TRACKER" ]]; then
    for alias in max-stuck-cycles max-total-runtime max-consecutive-deep-cycles; do
        if ! grep -q "\-\-${alias}=" "$TRACKER" 2>/dev/null; then
            fail "Check 25: cycle_tracker.sh init missing alias --$alias"
            check25_ok=0
        fi
    done
fi

if [[ "$check25_ok" -eq 1 ]]; then
    ok "Check 25: Session tracking contract verified across all files"
fi

echo ""
echo "=== Results: $PASS passed, $FAIL failed ==="
[[ "$FAIL" -eq 0 ]]

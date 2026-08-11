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
    if ! grep -q 'lean4-skills-cycle-tracker' "$cmd_file" 2>/dev/null; then
        fail "Check 25: $base missing lean4-skills-cycle-tracker reference in Invocation Contract"
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
if grep -q "lean4-skills-cycle-tracker.*init" "$AUTOPROVE" 2>/dev/null; then
    init_block=$(grep -A 3 "lean4-skills-cycle-tracker.*init" "$AUTOPROVE" 2>/dev/null)
    for flag in max-stuck-cycles max-total-runtime max-consecutive-deep-cycles; do
        if ! echo "$init_block" | grep -q "$flag"; then
            fail "Check 25: autoprove.md init contract missing --$flag"
            check25_ok=0
        fi
    done
fi

# autoformalize must NOT reference autoprove-only flag --max-consecutive-deep-cycles in init contract
if grep -q "lean4-skills-cycle-tracker.*init" "$AUTOFORMALIZE" 2>/dev/null; then
    af_init_block=$(grep -A 3 "lean4-skills-cycle-tracker.*init" "$AUTOFORMALIZE" 2>/dev/null)
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

# ---------------------------------------------------------------------------
# Check 26: every lean4-skills-* wrapper is referenced by at least one
# model-facing doc surface (commands/, agents/, or SKILL.md). The
# lint's Check 10 enforces *shape* only; this contract test enforces
# *coverage* — i.e. wrappers don't drift away from their documented
# call sites, and the curated set stays aligned with what the model
# actually invokes.
#
# Acceptance: the wrapper name appears either as a bare token
# (lean4-skills-foo …) or path-form (bin/lean4-skills-foo, etc.) in
# any of those doc surfaces. Adding a new wrapper file without adding
# at least one doc reference triggers this check.
# ---------------------------------------------------------------------------
check26_ok=1
BIN_DIR="$PLUGIN_ROOT/bin"
DOCS_DIRS=("$PLUGIN_ROOT/commands" "$PLUGIN_ROOT/agents" "$PLUGIN_ROOT/skills/lean4/SKILL.md")
if [[ -d "$BIN_DIR" ]]; then
    while IFS= read -r wrapper; do
        name=$(basename "$wrapper")
        # Search each docs dir/file for the wrapper name as a word token.
        # \b for word boundary catches both bare invocation and path-form.
        if ! grep -qrE -- "\\b${name}\\b" "${DOCS_DIRS[@]}" 2>/dev/null; then
            fail "Check 26: wrapper $name has no doc reference under commands/, agents/, or SKILL.md"
            check26_ok=0
        fi
    done < <(find "$BIN_DIR" -mindepth 1 -maxdepth 1 -name 'lean4-skills-*' -type f 2>/dev/null | sort)
fi
if [[ "$check26_ok" -eq 1 ]]; then
    ok "Check 26: bin/lean4-skills-* wrappers are all doc-referenced"
fi

# ---------------------------------------------------------------------------
# Check 27: no stale `$LEAN4_SCRIPTS/<wrapped-script>` invocations in
# model-facing docs. Catches doc drift after a wrapper is added — every
# wrapped script's env-var-form invocation should become the bare wrapper
# name in model-facing surfaces, unless the line is explicitly marked
# with the sentinel `guardrails: compatibility-fallback` (for intentional
# fallback documentation).
#
# Sentinel form is syntax-appropriate:
#   - Inside fenced code blocks: trailing `# guardrails: compatibility-fallback`
#   - In markdown prose:         trailing `<!-- guardrails: compatibility-fallback -->`
# The grep filter is the same in both cases (substring match on
# `guardrails: compatibility-fallback`).
#
# Wrapper-to-script mapping is derived from each wrapper's body
# (looking for the `lib/scripts/<basename>` delegation), not by
# inferring an extension from the wrapper name (some target .py,
# some .sh; not safe to guess).
# ---------------------------------------------------------------------------
check27_ok=1
DOC_SURFACES=(
    "$PLUGIN_ROOT/commands"
    "$PLUGIN_ROOT/agents"
    "$PLUGIN_ROOT/skills/lean4/SKILL.md"
    "$PLUGIN_ROOT/skills/lean4/references"
    "$PLUGIN_ROOT/README.md"
    "$PLUGIN_ROOT/../../INSTALLATION.md"
)
if [[ -d "$BIN_DIR" ]]; then
    while IFS= read -r wrapper; do
        # Derive underlying script basename from the wrapper's exec line
        # only — header comments also name lib/scripts/<basename>, and
        # parsing them could mask a malformed exec line. The extension
        # anchor avoids trailing docstring punctuation. `|| true` keeps
        # a no-match pipeline from tripping set -euo pipefail; the
        # unparseable-wrapper case is Check 28's explicit failure, so
        # Check 27 just skips it.
        script=$(grep -E '^exec ' "$wrapper" 2>/dev/null \
            | grep -oE 'lib/scripts/[a-zA-Z0-9_-]+\.(py|sh)' \
            | tail -1 \
            | sed 's|lib/scripts/||' || true)
        [[ -z "$script" ]] && continue
        # Escape for grep regex.
        sc_re=$(printf '%s' "$script" | sed 's/[][\/.^$*+?{}|()]/\\&/g')
        # Match both spellings: $LEAN4_SCRIPTS/<script> and ${LEAN4_SCRIPTS}/<script>.
        pat='\$\{?LEAN4_SCRIPTS\}?/'"$sc_re"
        # Search each doc surface; -I skips binaries; --include keeps it to .md.
        matches=$(grep -rnIE --include='*.md' -- "$pat" "${DOC_SURFACES[@]}" 2>/dev/null \
            | grep -v 'guardrails: compatibility-fallback' || true)
        if [[ -n "$matches" ]]; then
            fail "Check 27: stale \$LEAN4_SCRIPTS/$script invocation(s) in model-facing docs (use wrapper $(basename "$wrapper") or add a 'guardrails: compatibility-fallback' sentinel):"
            while IFS= read -r m; do
                echo "    $m" >&2
            done <<<"$matches"
            check27_ok=0
        fi
    done < <(find "$BIN_DIR" -mindepth 1 -maxdepth 1 -name 'lean4-skills-*' -type f 2>/dev/null | sort)
fi
if [[ "$check27_ok" -eq 1 ]]; then
    ok "Check 27: no stale \$LEAN4_SCRIPTS/<wrapped> invocations in model-facing docs"
fi

# ---------------------------------------------------------------------------
# Check 28: every wrapper's parsed delegation target exists and is
# executable. Check 27 parses the `lib/scripts/<basename>` delegation to
# build its doc-drift mapping but silently skips a wrapper whose body
# doesn't parse, and never verifies the target file — so a wrapper could
# ship pointing at a renamed or deleted script and only fail at runtime.
# This check makes the delegation itself a tested contract: parseable,
# present, executable.
# ---------------------------------------------------------------------------
check28_ok=1
if [[ -d "$BIN_DIR" ]]; then
    while IFS= read -r wrapper; do
        name=$(basename "$wrapper")
        # Same exec-line-only parse as Check 27 (comments could mask a
        # malformed exec line); `|| true` so a no-match reaches the
        # explicit failure below instead of tripping set -euo pipefail.
        script=$(grep -E '^exec ' "$wrapper" 2>/dev/null \
            | grep -oE 'lib/scripts/[a-zA-Z0-9_-]+\.(py|sh)' \
            | tail -1 \
            | sed 's|lib/scripts/||' || true)
        if [[ -z "$script" ]]; then
            fail "Check 28: wrapper $name has no parseable exec-line lib/scripts/<basename> delegation"
            check28_ok=0
            continue
        fi
        target="$PLUGIN_ROOT/lib/scripts/$script"
        if [[ ! -f "$target" ]]; then
            fail "Check 28: wrapper $name delegates to missing script lib/scripts/$script"
            check28_ok=0
        elif [[ ! -x "$target" ]]; then
            fail "Check 28: wrapper $name delegates to non-executable script lib/scripts/$script"
            check28_ok=0
        fi
    done < <(find "$BIN_DIR" -mindepth 1 -maxdepth 1 -name 'lean4-skills-*' -type f 2>/dev/null | sort)
fi
if [[ "$check28_ok" -eq 1 ]]; then
    ok "Check 28: every bin/ wrapper's delegation target exists and is executable"
fi

# ---------------------------------------------------------------------------
# Check 29: skills/lean4/agents/openai.yaml metadata contract. The file
# is generated once (skill-creator's generate_openai_yaml.py) and
# checked in; this check keeps later hand-edits from silently
# invalidating it. Contract: exactly one top-level `interface:` block
# with quoted display_name / short_description / default_prompt;
# short_description 25-64 chars (Codex UI budget); default_prompt names
# the `$lean4` invocation; no `policy:` block (allow_implicit_invocation
# defaults to true — restating defaults invites drift).
# ---------------------------------------------------------------------------
check29_ok=1
OPENAI_YAML="$PLUGIN_ROOT/skills/lean4/agents/openai.yaml"
if [[ ! -f "$OPENAI_YAML" ]]; then
    fail "Check 29: missing skills/lean4/agents/openai.yaml"
    check29_ok=0
else
    n_iface=$(grep -cE '^interface:[[:space:]]*$' "$OPENAI_YAML" || true)
    if [[ "$n_iface" -ne 1 ]]; then
        fail "Check 29: openai.yaml has $n_iface top-level 'interface:' blocks (want exactly 1)"
        check29_ok=0
    fi
    extra=$(grep -E '^[A-Za-z_]+:' "$OPENAI_YAML" | grep -vE '^interface:[[:space:]]*$' || true)
    if [[ -n "$extra" ]]; then
        fail "Check 29: openai.yaml has unexpected top-level key(s): $extra"
        check29_ok=0
    fi
    for key in display_name short_description default_prompt; do
        n_key=$(grep -cE "^  ${key}: \".+\"[[:space:]]*$" "$OPENAI_YAML" || true)
        if [[ "$n_key" -ne 1 ]]; then
            fail "Check 29: openai.yaml has $n_key quoted '$key' entries (want exactly 1)"
            check29_ok=0
        fi
    done
    sd=$(sed -n 's/^  short_description: "\(.*\)"[[:space:]]*$/\1/p' "$OPENAI_YAML")
    if [[ "${#sd}" -lt 25 || "${#sd}" -gt 64 ]]; then
        fail "Check 29: openai.yaml short_description length ${#sd} outside 25-64"
        check29_ok=0
    fi
    if ! grep -qE '^  default_prompt: ".*\$lean4.*"[[:space:]]*$' "$OPENAI_YAML"; then
        fail "Check 29: openai.yaml default_prompt does not name \$lean4"
        check29_ok=0
    fi
fi
if [[ "$check29_ok" -eq 1 ]]; then
    ok "Check 29: agents/openai.yaml metadata matches the generated contract"
fi

# Check 30: /lean4:doctor → /lean4:diagnose rename holds (v4.6.0 breaking
# change). The old name must not resurface in active surfaces: diagnose.md
# must exist with `name: diagnose` and "Lean4 Diagnostics" headings (no
# stale "Lean4 Doctor" output names), doctor.md must not exist, and no
# scanned file may reference `/lean4:doctor` or `doctor.md`. The scan
# covers the root README/INSTALLATION/manifests, .agents/ (Codex
# marketplace), .github/ (workflow step labels), and the whole plugin
# tree. Allowlisted: CHANGELOG.md (the v4.6.0 breaking entry and older
# historical entries are accurate for the releases they describe), and in
# MIGRATION.md only the two EXACT v4.6.0 rename/removal statements —
# which must both exist, and any other old-name/branding mention fails.
# Canonical recovery-wording
# agreement across diagnose.md / preflight / bootstrap is owned by
# test_preflight_env.sh and test_bootstrap_env.sh — not duplicated here.
# ---------------------------------------------------------------------------
check30_ok=1
# Repo root derived, not assumed: PLUGIN_ROOT is plugins/lean4, so two up.
_c30_repo_root="$(cd "$PLUGIN_ROOT/../.." && pwd)"
for _c30_must in "$_c30_repo_root/README.md" "$_c30_repo_root/INSTALLATION.md" "$_c30_repo_root/.claude-plugin"; do
    if [[ ! -e "$_c30_must" ]]; then
        fail "Check 30: expected repo-root path missing: $_c30_must (root derivation broken?)"
        check30_ok=0
    fi
done
if [[ ! -f "$PLUGIN_ROOT/commands/diagnose.md" ]]; then
    fail "Check 30: commands/diagnose.md missing"
    check30_ok=0
else
    if ! grep -q '^name: diagnose$' "$PLUGIN_ROOT/commands/diagnose.md"; then
        fail "Check 30: commands/diagnose.md frontmatter is not 'name: diagnose'"
        check30_ok=0
    fi
    if grep -q 'Lean4 Doctor' "$PLUGIN_ROOT/commands/diagnose.md"; then
        fail "Check 30: stale 'Lean4 Doctor' heading/output name in diagnose.md"
        check30_ok=0
    fi
    if ! grep -q '^# Lean4 Diagnostics$' "$PLUGIN_ROOT/commands/diagnose.md" \
        || ! grep -q '^## Lean4 Diagnostics Report$' "$PLUGIN_ROOT/commands/diagnose.md"; then
        fail "Check 30: diagnose.md missing 'Lean4 Diagnostics' title or 'Lean4 Diagnostics Report' heading"
        check30_ok=0
    fi
fi
# MIGRATION.md: the two exact v4.6.0 statements must exist, and they are
# the ONLY permitted old-name/branding mentions — exact-line matching, so
# neither a spoofed line containing 'renamed' nor deleting the statements
# can pass.
_c30_mig="$PLUGIN_ROOT/MIGRATION.md"
_c30_mig_head='## v4.6.0: `/lean4:doctor` renamed'
_c30_mig_body='`/lean4:doctor` was removed in v4.6.0. Use `/lean4:diagnose`; all modes and behavior are unchanged (`/lean4:diagnose`, `env`, `migrate`, `cleanup`).'
if ! grep -Fxq "$_c30_mig_head" "$_c30_mig" 2>/dev/null \
    || ! grep -Fxq "$_c30_mig_body" "$_c30_mig" 2>/dev/null; then
    fail "Check 30: MIGRATION.md missing the exact v4.6.0 rename heading or removal statement"
    check30_ok=0
fi
_c30_mig_bad=$(grep -n 'lean4:doctor\|doctor\.md\|Lean4 Doctor' "$_c30_mig" 2>/dev/null \
    | grep -Fv "$_c30_mig_head" | grep -Fv "$_c30_mig_body" || true)
if [[ -n "$_c30_mig_bad" ]]; then
    fail "Check 30: MIGRATION.md old-name mention outside the exact rename/removal statements: $_c30_mig_bad"
    check30_ok=0
fi
if [[ -e "$PLUGIN_ROOT/commands/doctor.md" ]]; then
    fail "Check 30: commands/doctor.md exists — the doctor command was removed in v4.6.0"
    check30_ok=0
fi
_c30_hits=$(grep -rln 'lean4:doctor\|doctor\.md\|Lean4 Doctor' \
    "$_c30_repo_root/README.md" "$_c30_repo_root/INSTALLATION.md" \
    "$PLUGIN_ROOT/README.md" "$PLUGIN_ROOT/commands" "$PLUGIN_ROOT/skills" \
    "$PLUGIN_ROOT/hooks" "$PLUGIN_ROOT/lib" "$PLUGIN_ROOT/tools" \
    "$PLUGIN_ROOT/tests" "$PLUGIN_ROOT/agents" "$PLUGIN_ROOT/bin" \
    "$PLUGIN_ROOT/.claude-plugin" "$PLUGIN_ROOT/.codex-plugin" \
    "$_c30_repo_root/.claude-plugin" "$_c30_repo_root/.agents" \
    "$_c30_repo_root/.github" 2>/dev/null \
    | grep -v 'tools/test_contracts.sh' \
    | grep -v "$PLUGIN_ROOT/MIGRATION.md" || true)
if [[ -n "$_c30_hits" ]]; then
    fail "Check 30: stale /lean4:doctor or doctor.md reference in active surfaces: $(echo "$_c30_hits" | tr '\n' ' ')"
    check30_ok=0
fi
if [[ "$check30_ok" -eq 1 ]]; then
    ok "Check 30: doctor→diagnose rename holds (no stale active references)"
fi

# ---------------------------------------------------------------------------
# Check 31: Mathlib template gate contract (#109). The gate's behavior lives
# in prompt documentation, so pin its load-bearing clauses: --output=file
# scope, helper invocation + exact schema/JSON field, flag precedence,
# unknown/helper-failure degradation + advisory, emitted-header ordering
# (module → public import → import → docstring), and mk_all non-execution
# (#111 owns checkpoint enforcement). draft.md is the canonical owner;
# formalize.md must carry the same summary and link back to it.
# ---------------------------------------------------------------------------
check31_ok=1
_c31_style="$PLUGIN_ROOT/skills/lean4/references/mathlib-style.md"
_c31_draft_gate=$(extract_section "$DRAFT" "### Mathlib Template Gate")
_c31_form_gate=$(extract_section "$FORMALIZE" "### Mathlib Template Gate")
for _c31_pair in "draft:$_c31_draft_gate" "formalize:$_c31_form_gate"; do
    _c31_name="${_c31_pair%%:*}"
    _c31_gate="${_c31_pair#*:}"
    if [[ -z "$_c31_gate" ]]; then
        fail "Check 31: $_c31_name.md has no '### Mathlib Template Gate' section"
        check31_ok=0
        continue
    fi
    # --output=file scope, other modes unchanged
    if ! echo "$_c31_gate" | grep -q -- '--output=file` whole-file writes only'; then
        fail "Check 31: $_c31_name gate does not scope to --output=file whole-file writes only"
        check31_ok=0
    fi
    # Helper invocation, schema pin, exact JSON field
    if ! echo "$_c31_gate" | grep -q 'lean4-skills-project-context --from' \
        || ! echo "$_c31_gate" | grep -q 'project-context/v1' \
        || ! echo "$_c31_gate" | grep -q 'intent\.contributing_upstream'; then
        fail "Check 31: $_c31_name gate missing helper invocation, schema pin, or intent.contributing_upstream field"
        check31_ok=0
    fi
    # Detection anchored at the nearest existing parent of --out (a new file
    # passed directly to --from would exit 4)
    if ! echo "$_c31_gate" | grep -q 'nearest existing parent'; then
        fail "Check 31: $_c31_name gate does not anchor detection at the nearest existing parent of --out"
        check31_ok=0
    fi
    # Flag precedence: explicit flag before helper consultation
    if ! assert_ordered "$_c31_gate" 'Explicit flag wins' 'lean4-skills-project-context'; then
        fail "Check 31: $_c31_name gate does not state explicit-flag precedence before helper consultation"
        check31_ok=0
    fi
    # unknown → advisory naming the opt-in flag; helper failure degrades, never blocks
    if ! echo "$_c31_gate" | grep 'unknown' | grep -q 'advisory' \
        || ! echo "$_c31_gate" | grep -q 'helper-failure' \
        || ! echo "$_c31_gate" | grep -q 'never blocks a write'; then
        fail "Check 31: $_c31_name gate missing unknown-advisory, helper-failure source, or never-blocks clause"
        check31_ok=0
    fi
    # mk_all non-execution + #111 ownership
    if ! echo "$_c31_gate" | grep 'does not run `lake exe mk_all`' >/dev/null \
        || ! echo "$_c31_gate" | grep -q '#111'; then
        fail "Check 31: $_c31_name gate missing mk_all non-execution statement or #111 ownership"
        check31_ok=0
    fi
done
# Emitted-header ordering pinned in the canonical owner (draft.md), one exact line
if ! echo "$_c31_draft_gate" | grep -Fq 'copyright block, then `module`, then the `public import` block, then the plain `import` block, then the `/-!` module docstring'; then
    fail "Check 31: draft.md gate missing the exact emitted-header ordering sentence"
    check31_ok=0
fi
# Explicit-false semantics: only true participates in precedence, in both commands
for _c31_pair in "draft:$_c31_draft_gate" "formalize:$_c31_form_gate"; do
    _c31_name="${_c31_pair%%:*}"
    _c31_gate="${_c31_pair#*:}"
    if ! echo "$_c31_gate" | grep -Fq 'Only a flag resolving to true participates in precedence; explicit false'; then
        fail "Check 31: $_c31_name gate missing the explicit-false-equals-omission sentence"
        check31_ok=0
    fi
done
# Import selection preserved — visibility split, not import rewriting
if ! echo "$_c31_draft_gate" | grep -q 'never import selection'; then
    fail "Check 31: draft.md gate missing the preserve-import-selection clause"
    check31_ok=0
fi
# formalize links back to the canonical owner
if ! echo "$_c31_form_gate" | grep -q 'draft.md#mathlib-template-gate'; then
    fail "Check 31: formalize.md gate does not link back to draft.md#mathlib-template-gate"
    check31_ok=0
fi
# Reference template ordering: mathlib-style.md canonical header shows
# module → public import → plain import → docstring, and retains YYYY Author Name
_c31_style_head=$(sed -n '1,60p' "$_c31_style")
if ! assert_ordered "$_c31_style_head" 'Copyright (c) YYYY Author Name' '^module$' '^public import ' '^import ' '^/-!$'; then
    fail "Check 31: mathlib-style.md canonical template not in module → public import → import → docstring order (or YYYY Author Name placeholder lost)"
    check31_ok=0
fi
# Blank-line separator between the public import and plain import groups
# (required by the mathlib style guide): no `public import` line may be
# immediately followed by a plain `import` line anywhere in the style doc,
# and the separated pattern (public import / blank / import) must appear.
if awk 'prev ~ /^public import / && /^import /{bad=1} {prev=$0} END{exit bad?0:1}' "$_c31_style"; then
    fail "Check 31: mathlib-style.md has a public import line directly followed by a plain import line (missing blank-line separator)"
    check31_ok=0
fi
if ! awk 'p2 ~ /^public import / && p1 == "" && /^import /{found=1} {p2=p1; p1=$0} END{exit found?0:1}' "$_c31_style"; then
    fail "Check 31: mathlib-style.md never shows the blank-line-separated public import / import groups"
    check31_ok=0
fi
if [[ "$check31_ok" -eq 1 ]]; then
    ok "Check 31: mathlib template gate contract pinned (draft canonical, formalize mirrored, style template ordered)"
fi

echo ""
echo "=== Results: $PASS passed, $FAIL failed ==="
[[ "$FAIL" -eq 0 ]]

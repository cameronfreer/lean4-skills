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
# Emitted-header ordering pinned in the canonical owner (draft.md), one exact
# line — including the public section, without which the generated
# declarations would remain private and the file would export nothing
if ! echo "$_c31_draft_gate" | grep -Fq 'copyright block, then `module`, then the `public import` block, then the plain `import` block, then the `/-!` module docstring, then a `public section` opening the exported scope before any declarations'; then
    fail "Check 31: draft.md gate missing the exact emitted-header ordering sentence (incl. public section)"
    check31_ok=0
fi
# Explicit-false semantics and the public-scope export rule, in both commands
for _c31_pair in "draft:$_c31_draft_gate" "formalize:$_c31_form_gate"; do
    _c31_name="${_c31_pair%%:*}"
    _c31_gate="${_c31_pair#*:}"
    if ! echo "$_c31_gate" | grep -Fq 'Only a flag resolving to true participates in precedence; explicit false'; then
        fail "Check 31: $_c31_name gate missing the explicit-false-equals-omission sentence"
        check31_ok=0
    fi
    if ! echo "$_c31_gate" | grep -q 'public section' \
        || ! echo "$_c31_gate" | grep -q 'private by default'; then
        fail "Check 31: $_c31_name gate missing the public-section / private-by-default export rule"
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
# Canonical template must CLOSE the module docstring and then open a public
# section (declarations in a module are private by default; a template
# without the public section would generate files that export nothing).
# Slice from the docstring opener so the copyright block's -/ can't satisfy
# the close-delimiter token.
_c31_style_doc=$(echo "$_c31_style_head" | sed -n '/^\/-!$/,$p')
if ! assert_ordered "$_c31_style_doc" '^-/$' '^public section$'; then
    fail "Check 31: mathlib-style.md canonical template does not close the /-! docstring and open a public section"
    check31_ok=0
fi
_c31_gfs=$(extract_section "$_c31_style" "### Good File Structure")
if ! echo "$_c31_gfs" | grep -q '^public section$'; then
    fail "Check 31: Good File Structure example missing the public section (declarations would stay private)"
    check31_ok=0
fi
if [[ "$check31_ok" -eq 1 ]]; then
    ok "Check 31: mathlib template gate contract pinned (draft canonical, formalize mirrored, style template ordered)"
fi

# ---------------------------------------------------------------------------
# Check 32: Module-system troubleshooting contract (#113). Error-triggered
# guidance lives in compilation-errors.md §16-§19 + diagnose.md; pin the
# exact Lean error strings (verified against the Lean source/reference so
# error-paste matching works), the direction split for meta-phase errors,
# the aggregator-vs-non-module distinction, scoped worked-example coverage,
# the diagnose triage contract, and the no-shake negative guard. Scoped to
# the new sections — whole-file token greps would prove little.
# ---------------------------------------------------------------------------
check32_ok=1
_c32_ce="$PLUGIN_ROOT/skills/lean4/references/compilation-errors.md"
_c32_diag="$PLUGIN_ROOT/commands/diagnose.md"
_c32_s16=$(extract_section "$_c32_ce" "### 16. Cannot Import Non-Module from Module")
_c32_s17=$(extract_section "$_c32_ce" "### 17. Module Visibility: Name Exists Upstream but Is Not Exported")
_c32_s18=$(extract_section "$_c32_ce" "### 18. Meta-Phase Errors (\`meta import\`, \`public meta import\`)")
_c32_s19=$(extract_section "$_c32_ce" "### 19. Old-Style Header in a Module-System Repo")
for _c32_pair in "16:$_c32_s16" "17:$_c32_s17" "18:$_c32_s18" "19:$_c32_s19"; do
    if [[ -z "${_c32_pair#*:}" ]]; then
        fail "Check 32: compilation-errors.md § ${_c32_pair%%:*} missing"
        check32_ok=0
    fi
done
# §16: full non-module error line + plain-preserves-style / --module-converts
# distinction + the staleness caveat + a real module-style aggregator snippet
if ! echo "$_c32_s16" | grep -Fq 'cannot import non-`module` Foo from `module`' \
    || ! echo "$_c32_s16" | grep -Fq 'preserves the existing style' \
    || ! echo "$_c32_s16" | grep -Fq 'create **or convert**' \
    || ! echo "$_c32_s16" | grep -Fq 'does not cause this specific non-module error' \
    || ! echo "$_c32_s16" | grep -Fq 'missing/unknown-module error' \
    || ! echo "$_c32_s16" | grep -Fq 'public import Mathlib.Tactic.Basic'; then
    fail "Check 32: §16 missing the full non-module error line, the plain-preserves/--module-converts distinction, the staleness caveat (incl. the rename/delete missing-module nuance), or the module-style aggregator snippet"
    check32_ok=0
fi
# §17: full visibility error lines, per-signature remedies, the same-package
# import-all worked example + downstream fence, and the concrete backward.*
# three-option fix. The backward.* option SUFFIX is deliberately NOT inside the
# emitted-diagnostic code block (Lean does not emit wildcards, and the suffix
# varies by toolchain) — pin only the stable "Private declaration `drop2`
# accessed publicly" prefix as the block's exact content, plus the remedies.
_c32_s17c=$(echo "$_c32_s17" | sed -n '/^Private declaration/p')
if ! echo "$_c32_s17" | grep -Fq 'Unknown identifier `greeting`' \
    || ! echo "$_c32_s17" | grep -Fq 'Invalid simp theorem `greeting`: Expected a definition with an exposed body' \
    || ! echo "$_c32_s17" | grep -Fq 'import all Tree.Basic' \
    || ! echo "$_c32_s17" | grep -Fq 'same Lake package' \
    || ! echo "$_c32_s17" | grep -Fq 'allowImportAll' \
    || ! echo "$_c32_s17" | grep -Fq 'never use `import all` on a downstream dependency' \
    || ! echo "$_c32_s17" | grep -Fq '@[expose]' \
    || [[ "$_c32_s17c" != 'Private declaration `drop2` accessed publicly' ]] \
    || ! echo "$_c32_s17" | grep -Fq 'rewrite the public signature'; then
    fail "Check 32: §17 missing an exact visibility error line, the same-Lake-package boundary / allowImportAll escape hatch, the import-all downstream fence, the stable-prefix backward warning (no wildcard in the block), or the concrete backward.* three-option fix"
    check32_ok=0
fi
# §18: full direction-B literal, direction-A fragments (identifiers vary), the
# direction-B negation, public meta import, and the both-phases worked example
# (a meta import line and a distinct runtime import line)
if ! echo "$_c32_s18" | grep -Fq 'Invalid definition `colors`, may not access declaration `toPalindrome` marked as `meta`' \
    || ! echo "$_c32_s18" | grep -Fq 'Invalid `meta` definition' \
    || ! echo "$_c32_s18" | grep -Fq 'not marked `meta`' \
    || ! echo "$_c32_s18" | grep -Fq '`meta import` is **not** the fix' \
    || ! echo "$_c32_s18" | grep -Eq '^public meta import ' \
    || ! echo "$_c32_s18" | grep -Fq 'meta import Phases.Pal' \
    || ! echo "$_c32_s18" | grep -Eq '^import Phases\.Pal'; then
    fail "Check 32: §18 missing the full direction-B error line, a direction-A fragment, the direction-B negation, a real public-meta-import code line, or the both-phases worked example"
    check32_ok=0
fi
# §19: public-section rule + canonical template link
if ! echo "$_c32_s19" | grep -Fq 'public section' \
    || ! echo "$_c32_s19" | grep -q 'mathlib-style.md#1-file-header'; then
    fail "Check 32: §19 missing the public-section rule or the mathlib-style.md template link"
    check32_ok=0
fi
# Worked-example token coverage scoped to the new sections (acceptance criteria)
_c32_new="$_c32_s16
$_c32_s17
$_c32_s18
$_c32_s19"
for _c32_tok in 'module' 'public import' 'import all' 'public meta import'; do
    if ! echo "$_c32_new" | grep -Fq "$_c32_tok"; then
        fail "Check 32: new sections lack a worked example mentioning '$_c32_tok'"
        check32_ok=0
    fi
done
# §15 see-also carries the module-system file-top order
_c32_s15=$(extract_section "$_c32_ce" "### 15. Invalid 'import' Command (Module Docstring Before Imports)")
if ! echo "$_c32_s15" | grep -Fq 'public section'; then
    fail "Check 32: §15 see-also not updated with the module-system file-top order"
    check32_ok=0
fi
# diagnose.md: triage input form, precedence over the generic build row,
# module-system section cross-linking the entries, #111 consistency note
_c32_diag_sec=$(extract_section "$_c32_diag" "### Module-System Troubleshooting")
if ! grep -Fq '/lean4:diagnose <pasted error>' "$_c32_diag"; then
    fail "Check 32: diagnose.md missing the pasted-error triage usage form"
    check32_ok=0
fi
# Dispatch is decided by the first positional token; mode flags stay flags
if ! grep -Fq 'first positional token' "$_c32_diag" \
    || ! grep -Fq 'never treated as error text' "$_c32_diag"; then
    fail "Check 32: diagnose.md missing the first-positional-token dispatch rule or the flags-not-error-text clause"
    check32_ok=0
fi
if [[ -z "$_c32_diag_sec" ]]; then
    fail "Check 32: diagnose.md missing the Module-System Troubleshooting section"
    check32_ok=0
else
    if ! echo "$_c32_diag_sec" | grep -q 'precedence over the generic' \
        || ! echo "$_c32_diag_sec" | grep -q 'compilation-errors.md' \
        || ! echo "$_c32_diag_sec" | grep -Fq '#111' \
        || ! echo "$_c32_diag_sec" | grep -Fq 'create **or convert**'; then
        fail "Check 32: diagnose Module-System section missing precedence rule, compilation-errors cross-link, #111 note, or the --module convert distinction"
        check32_ok=0
    fi
fi
# Negative guard: no shake recommendation (the executable command, not the word)
if grep -Fq 'lake exe shake' "$_c32_ce" || grep -Fq 'lake exe shake' "$_c32_diag"; then
    fail "Check 32: 'lake exe shake' recommendation present — shake was retired with the module system"
    check32_ok=0
fi
if [[ "$check32_ok" -eq 1 ]]; then
    ok "Check 32: module-system troubleshooting contract pinned (exact error strings, direction split, triage precedence, no shake)"
fi

# ---------------------------------------------------------------------------
# Check 33: checkpoint mk_all gate contract (#111). The gate is prompt-defined
# in checkpoint.md over a tested helper; pin the load-bearing clauses so they
# cannot silently regress: the versioned helper schema, before-build ordering,
# candidate-set-not-index definition, the project-context decision order, the
# explicit-opt-in-never-fails-open rule, stale-vs-operational distinction,
# check-only behaviour, verbatim mk_all remediation, and the global-check
# limitation note.
# ---------------------------------------------------------------------------
check33_ok=1
_c33_cp="$PLUGIN_ROOT/commands/checkpoint.md"
_c33_actions=$(extract_section "$_c33_cp" "## Actions")
_c33_gate=$(extract_section "$_c33_cp" "## Generated Root Files gate")
if [[ -z "$_c33_gate" ]]; then
    fail "Check 33: checkpoint.md missing the '## Generated Root Files gate' section"
    check33_ok=0
fi
# Ordering: the gate step runs before Verify Build in the Actions list
if ! assert_ordered "$_c33_actions" 'Generated Root Files gate' 'Verify Build'; then
    fail "Check 33: checkpoint.md Actions do not run the Generated Root Files gate before Verify Build"
    check33_ok=0
fi
# Versioned helper schema + wrapper invocation
if ! echo "$_c33_gate" | grep -Fq 'checkpoint-mathlib-roots/v1' \
    || ! echo "$_c33_gate" | grep -Fq 'lean4-skills-checkpoint-mathlib-roots'; then
    fail "Check 33: gate missing the versioned helper schema or the wrapper invocation"
    check33_ok=0
fi
# Candidate set defined independently of the git index (staging happens later)
if ! echo "$_c33_actions" | grep -Fq 'candidate set' \
    || ! echo "$_c33_actions" | grep -Fq 'independently of the current git index'; then
    fail "Check 33: checkpoint.md does not define the candidate set independently of the git index"
    check33_ok=0
fi
# project-context decision order + full-record validation + mk_all_declared unused
if ! echo "$_c33_gate" | grep -Fq 'lean4-skills-project-context --from "$PWD"' \
    || ! echo "$_c33_gate" | grep -Fq 'project-context/v1' \
    || ! echo "$_c33_gate" | grep -Fq 'intent.contributing_upstream' \
    || ! echo "$_c33_gate" | grep -Fq 'mk_all_declared` is **never** consulted'; then
    fail "Check 33: gate missing the project-context invocation, schema/field validation, or the mk_all_declared-never-consulted rule"
    check33_ok=0
fi
# Explicit opt-in overrides only the intent decision, not root discovery,
# and must not fail open when the root cannot be acquired.
if ! echo "$_c33_gate" | grep -Fq 'overrides only the *intent* decision' \
    || ! echo "$_c33_gate" | grep -Fq 'explicit opt-in must not fail open'; then
    fail "Check 33: gate does not require project-root acquisition under explicit opt-in / fail-closed"
    check33_ok=0
fi
# Fail closed on ANY unusable candidate-helper result, not just exit 4 —
# validate the versioned schema before trusting an empty changes list.
if ! echo "$_c33_gate" | grep -Fq 'Fail closed on any unusable result' \
    || ! echo "$_c33_gate" | grep -Fq 'do not treat an empty `changes` list as' \
    || ! echo "$_c33_gate" | grep -Fq 'schema` ≠ `checkpoint-mathlib-roots/v1'; then
    fail "Check 33: gate does not fail closed on every unusable candidate-helper result (schema/root/fields)"
    check33_ok=0
fi
# Stale output vs operational failure are distinguished; never invent filenames
if ! echo "$_c33_gate" | grep -Fq 'could not complete' \
    || ! echo "$_c33_gate" | grep -Fq 'do **not** invent stale filenames'; then
    fail "Check 33: gate does not distinguish stale output from operational failure"
    check33_ok=0
fi
# Check-only (no auto-rewrite) + verbatim remediation + preserve output
if ! echo "$_c33_gate" | grep -Fq 'Never** auto-rewrite' \
    || ! echo "$_c33_gate" | grep -Fq 'preserve its output verbatim' \
    || ! echo "$_c33_gate" | grep -Fq 'lake exe mk_all`'; then
    fail "Check 33: gate missing check-only/no-auto-rewrite, output-preservation, or the verbatim mk_all remediation"
    check33_ok=0
fi
# Global-check limitation honestly stated
if ! echo "$_c33_gate" | grep -Fq 'Global-check limitation'; then
    fail "Check 33: gate missing the global-check limitation note"
    check33_ok=0
fi
# The helper wrapper exists and is executable; its delegate too
_c33_wrap="$PLUGIN_ROOT/bin/lean4-skills-checkpoint-mathlib-roots"
_c33_py="$PLUGIN_ROOT/lib/scripts/checkpoint_mathlib_roots.py"
if [[ ! -x "$_c33_wrap" ]]; then
    fail "Check 33: bin/lean4-skills-checkpoint-mathlib-roots missing or not executable"
    check33_ok=0
fi
if [[ ! -x "$_c33_py" ]]; then
    fail "Check 33: lib/scripts/checkpoint_mathlib_roots.py missing or not executable"
    check33_ok=0
fi
if [[ "$check33_ok" -eq 1 ]]; then
    ok "Check 33: checkpoint mk_all gate contract pinned (schema, ordering, decision order, opt-in-never-fails-open, check-only)"
fi

# ---------------------------------------------------------------------------
# Check 34: workflow-scoped docstring policy (#54 + #116). The old blanket
# "docstrings are off-limits" prohibition is replaced by three mode-scoped
# rules; pin the load-bearing boundary of each in its owning file, the
# absence of the blanket rule, and #54's content, without duplicating prose.
# ---------------------------------------------------------------------------
check34_ok=1
_c34_skill="$PLUGIN_ROOT/skills/lean4/SKILL.md"
_c34_style="$PLUGIN_ROOT/skills/lean4/references/mathlib-style.md"
# The old blanket prohibition must be gone (it bundled docstrings with
# statements/signatures as globally off-limits).
if grep -Fq 'docstrings are off-limits' "$_c34_skill"; then
    fail "Check 34: SKILL.md still contains the old blanket 'docstrings are off-limits' prohibition"
    check34_ok=0
fi
# SKILL.md carries the three-rule permission matrix (Mode | May do | Boundary).
if ! grep -Fq '| Mode | May do | Boundary |' "$_c34_skill" \
    || ! grep -Fq 'Docstrings are scoped by workflow' "$_c34_skill"; then
    fail "Check 34: SKILL.md missing the workflow-scoped docstring permission matrix"
    check34_ok=0
fi
# Rule A is the default for ANY workflow mutating existing declarations, not
# only the named proof commands.
if ! grep -Fq 'any workflow that mutates existing declarations' "$_c34_skill"; then
    fail "Check 34: SKILL.md does not make Rule A the fallback for every existing-declaration edit"
    check34_ok=0
fi
# Each rule's boundary lives in its owning command doc.
_c34_prove=$(extract_section "$PLUGIN_ROOT/commands/prove.md" "## Safety")
if ! echo "$_c34_prove" | grep -Fq 'Rule A' \
    || ! echo "$_c34_prove" | grep -Fq 'never rewrite an existing docstring'; then
    fail "Check 34: prove.md Safety missing the Rule A existing-docstring protection"
    check34_ok=0
fi
_c34_review=$(extract_section "$PLUGIN_ROOT/commands/review.md" "## Safety")
if ! echo "$_c34_review" | grep -Fq 'Rule B' \
    || ! echo "$_c34_review" | grep -Fq 'propose replacement' \
    || ! echo "$_c34_review" | grep -Fq 'read-only'; then
    fail "Check 34: review.md Safety missing Rule B (flag + propose text, read-only)"
    check34_ok=0
fi
# Rule C in all three generation commands, each linked to the CANONICAL
# template section (durable), not to issue #109. Scope to the Safety section
# so the pin verifies Rule C's own link — draft/formalize already carry that
# same anchor in their #109 Mathlib Template Gate section, which must not
# satisfy this check on its own.
for _c34_cmd in draft formalize autoformalize; do
    _c34_safety=$(extract_section "$PLUGIN_ROOT/commands/$_c34_cmd.md" "## Safety")
    # Rule C must (a) name Rule C, (b) link the canonical template, and (c)
    # keep pre-existing declarations under Rule A — without (c) the commands
    # could regress to "generation may rewrite existing docstrings".
    if ! echo "$_c34_safety" | grep -Fq 'Rule C' \
        || ! echo "$_c34_safety" | grep -Fq 'mathlib-style.md#1-file-header' \
        || ! echo "$_c34_safety" | grep -Fq 'Rule A'; then
        fail "Check 34: $_c34_cmd.md Safety missing Rule C, its canonical-template link, or the pre-existing→Rule A boundary"
        check34_ok=0
    fi
done
# #54 content: sorry-free anti-pattern, section-header treatment, the inline
# patterns framed as review triggers (not deletion rules), and the blueprint
# surfaces (@[blueprint] fields + blueprint/src/content.tex) under Rule B —
# #54's fifth documented gap, required for `Closes #54` to be accurate.
_c34_devhist=$(extract_section "$_c34_style" "### Avoid Development History References")
if ! echo "$_c34_devhist" | grep -Fq 'sorry-free' \
    || ! echo "$_c34_devhist" | grep -Fq 'Section headers' \
    || ! echo "$_c34_devhist" | grep -Fq 'review triggers, not automatic-deletion rules' \
    || ! echo "$_c34_devhist" | grep -Fq '@[blueprint]' \
    || ! echo "$_c34_devhist" | grep -Fq 'blueprint/src/content.tex' \
    || ! echo "$_c34_devhist" | grep -Fq 'result-level API contract' \
    || ! echo "$_c34_devhist" | grep -Fq 'routine'; then
    fail "Check 34: mathlib-style.md dev-history section missing sorry-free, section-header, review-trigger framing, blueprint surfaces, or the result-vs-proof-method rule"
    check34_ok=0
fi
if [[ "$check34_ok" -eq 1 ]]; then
    ok "Check 34: workflow-scoped docstring policy pinned (matrix, per-command boundaries, #54 content, no blanket rule)"
fi

# ---------------------------------------------------------------------------
# Check 35: mathlib review taxonomy (#114 + #60). A reference file, not
# runtime behavior; pin the nine-bucket structure, naming/namespace as its
# own bucket, #60's semantically-scoped vacuous-api rule (the settled
# category/rule_id/severity), bucket 8's durable shipped-reference links (not
# closed issue numbers, and /lean4:diagnose never /lean4:doctor), the
# schema-not-frozen note, and the three navigational pointers.
# ---------------------------------------------------------------------------
check35_ok=1
_c35_tax="$PLUGIN_ROOT/skills/lean4/references/mathlib-review-taxonomy.md"
if [[ ! -f "$_c35_tax" ]]; then
    fail "Check 35: mathlib-review-taxonomy.md is missing"
    check35_ok=0
else
    # Nine buckets (## 1. … ## 9.)
    _c35_buckets=$(grep -cE '^## [1-9]\. ' "$_c35_tax")
    if [[ "$_c35_buckets" -ne 9 ]]; then
        fail "Check 35: expected 9 review buckets, found $_c35_buckets"
        check35_ok=0
    fi
    # Naming & namespace is its own bucket, not folded into surface style.
    if ! grep -qE '^## 2\. Naming & namespace' "$_c35_tax"; then
        fail "Check 35: 'Naming & namespace' is not its own bucket"
        check35_ok=0
    fi
    # Every bucket must actually carry the promised four-field shape. Extract
    # each '## N.' section by number and require all four markers — the intro,
    # issue, and changelog all promise this shape, so a missing field is a
    # broken structural promise, not cosmetics.
    for _c35_n in 1 2 3 4 5 6 7 8 9; do
        _c35_sec=$(awk -v n="^## ${_c35_n}\\\\. " '
            $0 ~ n {f=1; print; next}
            f && /^## [0-9]+\. / {exit}
            f {print}
        ' "$_c35_tax")
        for _c35_field in '**Reviewers mean:**' '**Cheap:**' '**Annoying:**' '**Example:**'; do
            if ! echo "$_c35_sec" | grep -Fq "$_c35_field"; then
                fail "Check 35: bucket $_c35_n missing '$_c35_field'"
                check35_ok=0
            fi
        done
    done
    # Load-bearing companion links live in their buckets, not only See Also.
    _c35_b4=$(extract_section "$_c35_tax" "## 4. File placement / import hygiene")
    _c35_b6=$(extract_section "$_c35_tax" "## 6. Attributes / \`simp\`")
    _c35_b7=$(extract_section "$_c35_tax" "## 7. Instances")
    if ! echo "$_c35_b4" | grep -Fq 'mathlib-guide.md'; then
        fail "Check 35: bucket 4 does not link mathlib-guide.md (the duplicate-result / search axis)"
        check35_ok=0
    fi
    if ! echo "$_c35_b6" | grep -Fq 'simp-reference.md'; then
        fail "Check 35: bucket 6 does not link simp-reference.md"
        check35_ok=0
    fi
    if ! echo "$_c35_b7" | grep -Fq 'instance-pollution.md'; then
        fail "Check 35: bucket 7 does not link instance-pollution.md"
        check35_ok=0
    fi
    # Bucket 4 carries the duplicate-existing-result axis (#110 Library
    # Integration), not just file placement.
    if ! echo "$_c35_b4" | grep -Fq 'already'; then
        fail "Check 35: bucket 4 missing the 'does an equivalent/more-general result already exist' axis"
        check35_ok=0
    fi
    # #60 vacuous-api: settled triple + semantic (not lexical) scope + advisory
    _c35_b5=$(extract_section "$_c35_tax" "## 5. API / generalization")
    if ! echo "$_c35_b5" | grep -Fq 'vacuous-api' \
        || ! echo "$_c35_b5" | grep -Fq 'category: api' \
        || ! echo "$_c35_b5" | grep -Fq 'severity: advisory' \
        || ! echo "$_c35_b5" | grep -Fq 'semantically, not lexically' \
        || ! echo "$_c35_b5" | grep -Fq 'does **not** cover `sorry`-scaffolding' \
        || ! echo "$_c35_b5" | grep -Fq 'never an automatic edit'; then
        fail "Check 35: bucket 5 missing the semantically-scoped vacuous-api rule / settled mapping / advisory framing"
        check35_ok=0
    fi
    # Bucket 8: durable shipped-reference links + /lean4:diagnose, never doctor.
    _c35_b8=$(extract_section "$_c35_tax" "## 8. Generated-file / module-system chores")
    if ! echo "$_c35_b8" | grep -Fq 'mathlib-style.md#1-file-header' \
        || ! echo "$_c35_b8" | grep -Fq 'checkpoint.md#generated-root-files-gate' \
        || ! echo "$_c35_b8" | grep -Fq 'compilation-errors.md#16' \
        || ! echo "$_c35_b8" | grep -Fq '/lean4:diagnose'; then
        fail "Check 35: bucket 8 missing a durable shipped-reference link or the /lean4:diagnose pointer"
        check35_ok=0
    fi
    if grep -Fq 'lean4:doctor' "$_c35_tax"; then
        fail "Check 35: taxonomy references the retired /lean4:doctor"
        check35_ok=0
    fi
    # Schema not frozen — #115 owns the enums; other tags are illustrative.
    if ! grep -Fq 'illustrative candidate mappings' "$_c35_tax" \
        || ! grep -Fq 'Issue #115 owns the final enums' "$_c35_tax"; then
        fail "Check 35: taxonomy does not mark non-settled category tags as illustrative / defer enums to #115"
        check35_ok=0
    fi
fi
# Three navigational pointers; review.md's must disclaim activation.
if ! grep -Fq 'mathlib-review-taxonomy' "$PLUGIN_ROOT/skills/lean4/SKILL.md"; then
    fail "Check 35: SKILL.md missing the taxonomy pointer"
    check35_ok=0
fi
if ! grep -Fq 'mathlib-review-taxonomy' "$PLUGIN_ROOT/skills/lean4/references/mathlib-guide.md"; then
    fail "Check 35: mathlib-guide.md missing the taxonomy pointer"
    check35_ok=0
fi
_c35_rev_seealso=$(extract_section "$PLUGIN_ROOT/commands/review.md" "## See Also")
# Since #110 the taxonomy is no longer background-only: review.md's See Also
# pointer must tie it to the Mathlib Review Layer that emits it (the old
# "does not change behavior" disclaimer would now contradict the command).
if ! echo "$_c35_rev_seealso" | grep -Fq 'mathlib-review-taxonomy' \
    || ! echo "$_c35_rev_seealso" | grep -Fq 'Mathlib Review Layer'; then
    fail "Check 35: review.md See Also missing the taxonomy pointer or its Mathlib Review Layer (Layer 2) link"
    check35_ok=0
fi
if [[ "$check35_ok" -eq 1 ]]; then
    ok "Check 35: mathlib review taxonomy pinned (nine buckets, naming bucket, vacuous-api #60, durable links, schema-deferred, pointers)"
fi

# ---------------------------------------------------------------------------
# Check 36: review schema files (#115). Pin the load-bearing decisions that
# test_review_schema.py's structural checks don't cover at the doc level: the
# two shipped JSON files exist; the input reuses project-context/v1's
# repository_kind (not a new repo_kind); review.md points --output-schema at
# the installed $LEAN4_REFS path (not a bare filename) and no longer inlines a
# full duplicate schema; and the version bumped to 2.0.
# ---------------------------------------------------------------------------
check36_ok=1
_c36_refs="$PLUGIN_ROOT/skills/lean4/references"
_c36_out="$_c36_refs/lean4-review-schema.json"
_c36_in="$_c36_refs/lean4-review-input-schema.json"
for _c36_f in "$_c36_out" "$_c36_in"; do
    if [[ ! -f "$_c36_f" ]]; then
        fail "Check 36: missing schema file $(basename "$_c36_f")"
        check36_ok=0
    fi
done
# Input reuses project-context/v1's repository_kind, not an invented repo_kind.
if [[ -f "$_c36_in" ]]; then
    if grep -Fq '"repo_kind"' "$_c36_in"; then
        fail "Check 36: input schema introduces repo_kind; reuse project-context/v1 repository_kind"
        check36_ok=0
    fi
    if ! grep -Fq '"repository_kind"' "$_c36_in" \
        || ! grep -Fq '"contributing_upstream"' "$_c36_in"; then
        fail "Check 36: input schema missing repository_kind / contributing_upstream (project-context/v1 reuse)"
        check36_ok=0
    fi
fi
# Output schema is Structured-Outputs-shaped + versioned.
if [[ -f "$_c36_out" ]]; then
    if ! grep -Fq '"const": "2.0"' "$_c36_out" \
        || ! grep -Fq '"additionalProperties": false' "$_c36_out"; then
        fail "Check 36: output schema missing version const 2.0 or additionalProperties:false"
        check36_ok=0
    fi
fi
# review.md: installed-path --output-schema, and no re-inlined full schema.
_c36_rev="$PLUGIN_ROOT/commands/review.md"
if ! grep -Fq -- '--output-schema "$LEAN4_REFS/lean4-review-schema.json"' "$_c36_rev"; then
    fail "Check 36: review.md does not point --output-schema at the installed \$LEAN4_REFS path"
    check36_ok=0
fi
if grep -Fq '"$schema": "https://json-schema.org/draft/2020-12/schema"' "$_c36_rev"; then
    fail "Check 36: review.md still inlines a full JSON Schema block (should link the shipped file)"
    check36_ok=0
fi
if [[ "$check36_ok" -eq 1 ]]; then
    ok "Check 36: review schema files pinned (two files, repository_kind reuse, structured-outputs shape, installed path, no duplication)"
fi

# ---------------------------------------------------------------------------
# Check 37: /lean4:review broadened to the mathlib-review bar (#110). Pin the
# load-bearing decisions the unit tests don't assert at the doc/wiring level:
# review adopted its first command_args spec (registered + hook-covered); the
# two mathlib-review gate flags + conflict rule + Invocation Contract are
# documented; the runtime output validator wrapper exists, delegates to the
# production module, and is wired into review.md; the input schema carries the
# scope-dependent if/then conditionals; and review.md states the Layer-2
# activation truth table (project-context gating, helper-failure → advisory)
# with normative advisory labelling.
# ---------------------------------------------------------------------------
check37_ok=1
_c37_rev="$PLUGIN_ROOT/commands/review.md"
_c37_spec="$PLUGIN_ROOT/lib/command_args/specs/review.py"
_c37_in="$PLUGIN_ROOT/skills/lean4/references/lean4-review-input-schema.json"
_c37_wrapper="$PLUGIN_ROOT/bin/lean4-skills-validate-review-output"
_c37_module="$PLUGIN_ROOT/lib/scripts/review_validate.py"

# Parser adoption: spec module + registration + hook coverage.
if [[ ! -f "$_c37_spec" ]]; then
    fail "Check 37: missing command_args spec lib/command_args/specs/review.py"
    check37_ok=0
fi
if ! grep -Fq 'from .review import SPEC' "$PLUGIN_ROOT/lib/command_args/specs/__init__.py"; then
    fail "Check 37: review SPEC not registered in command_args specs/__init__.py"
    check37_ok=0
fi
if ! grep -Fq '"review"' "$PLUGIN_ROOT/hooks/validate_user_prompt.py"; then
    fail "Check 37: 'review' not added to _COVERED_COMMANDS in validate_user_prompt.py"
    check37_ok=0
fi

# review.md: Invocation Contract, both gate flags, conflict rule.
if ! grep -Fq '## Invocation Contract' "$_c37_rev" \
    || ! grep -Fq '**Primary path (hook-validated):**' "$_c37_rev"; then
    fail "Check 37: review.md missing Invocation Contract / Primary-path marker"
    check37_ok=0
fi
for _c37_flag in -- '--mathlib-review' '--no-mathlib-review'; do
    [[ "$_c37_flag" == "--" ]] && continue
    if ! grep -Fq -- "$_c37_flag" "$_c37_rev"; then
        fail "Check 37: review.md does not document $_c37_flag"
        check37_ok=0
    fi
done
if ! grep -Fq 'startup validation error' "$_c37_rev"; then
    fail "Check 37: review.md missing the mathlib-review conflict → startup validation error rule"
    check37_ok=0
fi

# Runtime output validator: wrapper + production module + doc wiring.
if [[ ! -f "$_c37_wrapper" ]]; then
    fail "Check 37: missing validator wrapper bin/lean4-skills-validate-review-output"
    check37_ok=0
fi
if [[ ! -f "$_c37_module" ]]; then
    fail "Check 37: missing production validator lib/scripts/review_validate.py"
    check37_ok=0
fi
if ! grep -Fq 'lean4-skills-validate-review-output' "$_c37_rev"; then
    fail "Check 37: review.md does not wire the output validator into the merge path"
    check37_ok=0
fi

# Input schema: scope-dependent conditionals present.
if [[ -f "$_c37_in" ]] && ! grep -Fq '"allOf"' "$_c37_in"; then
    fail "Check 37: input schema missing the scope-dependent if/then (allOf) conditionals"
    check37_ok=0
fi

# review.md: Layer-2 activation truth table with helper-failure → advisory.
if ! grep -Fq 'Mathlib Review Layer (Layer 2)' "$_c37_rev" \
    || ! grep -Fq 'helper-failure' "$_c37_rev"; then
    fail "Check 37: review.md missing Layer-2 activation table / helper-failure fail-safe"
    check37_ok=0
fi
# review.md: Layer-2 detection is executable — the actual project-context
# invocation and the exact validated nested fields, not just the table.
if ! grep -Fq 'lean4-skills-project-context --from' "$_c37_rev"; then
    fail "Check 37: review.md Layer-2 activation never runs lean4-skills-project-context --from"
    check37_ok=0
fi
for _c37_field in 'project-context/v1' 'facts.repository_kind' 'intent.contributing_upstream' 'intent.source'; do
    if ! grep -Fq "$_c37_field" "$_c37_rev"; then
        fail "Check 37: review.md Layer-2 activation does not validate $_c37_field"
        check37_ok=0
    fi
done
# intent.source must be pinned to its actual project-context/v1 domain, not
# merely required to be a non-empty string (else "flag"/"anything" would pass).
if ! grep -Fq 'env-override | invalid-env-override | remote-heuristic | default' "$_c37_rev"; then
    fail "Check 37: review.md does not pin the intent.source domain (env-override|invalid-env-override|remote-heuristic|default)"
    check37_ok=0
fi
# The Resolved-Inputs source enumeration in the Invocation Contract must itself
# list intent.source — a global grep passes even when the enumeration omits it
# (intent.source also appears later in the activation section).
_c37_invcontract=$(extract_section "$_c37_rev" "## Invocation Contract")
if ! echo "$_c37_invcontract" | grep -Fq 'intent.source'; then
    fail "Check 37: Invocation Contract's Layer-2 source enumeration omits intent.source"
    check37_ok=0
fi
# review.md: the documented scope preconditions the parser now enforces.
if ! grep -Fq 'requires target file + --line' "$_c37_rev"; then
    fail "Check 37: review.md missing the sorry/deps 'requires target file + --line' precondition"
    check37_ok=0
fi

if [[ "$check37_ok" -eq 1 ]]; then
    ok "Check 37: /lean4:review mathlib-review bar pinned (parser adoption, gate flags + conflict, output validator wiring, input conditionals, Layer-2 activation)"
fi

# ---------------------------------------------------------------------------
# Check 38: Track 3 run-contract/v1 (#190, unifies #73/#69). Pin the canonical
# handoff-contract.md (both records, reused stuck vocabulary, files_owned vs
# files_changed, the rerun predicate, and persistence deferred to #82), the
# cycle-engine.md Run Contract section + no-subagent fallback + shared
# delegation policy, and that the consuming docs reference it.
# ---------------------------------------------------------------------------
check38_ok=1
_c38_hc="$PLUGIN_ROOT/skills/lean4/references/handoff-contract.md"
_c38_ce="$PLUGIN_ROOT/skills/lean4/references/cycle-engine.md"
_c38_rev="$PLUGIN_ROOT/commands/review.md"

if [[ ! -f "$_c38_hc" ]]; then
    fail "Check 38: missing references/handoff-contract.md"
    check38_ok=0
else
    # Versioned protocol + both records.
    for _c38_s in 'run-contract/v1' '"dispatch"' '"handoff"'; do
        if ! grep -Fq "$_c38_s" "$_c38_hc"; then
            fail "Check 38: handoff-contract.md missing $_c38_s"
            check38_ok=0
        fi
    done
    # Persistence explicitly deferred to #82; contract-only.
    if ! grep -Fq '#82' "$_c38_hc"; then
        fail "Check 38: handoff-contract.md must defer filesystem persistence to #82"
        check38_ok=0
    fi

    # -- Dispatch record: EVERY required field + the typed context envelope --
    _c38_disp=$(extract_section "$_c38_hc" "## Dispatch record (parent → worker)")
    for _c38_f in 'schema' 'record' 'target' 'scope' 'mode' 'worker' 'parameters' \
        'capabilities' 'owned_files' 'file_baseline' 'prior_blocker' 'evidence_delta' \
        'budget' 'context' 'prior_failure' 'goal_state' 'diagnostics' 'search_results' \
        'candidates_tested' 'code_actions' 'scratch_location'; do
        if ! echo "$_c38_disp" | grep -Fq "$_c38_f"; then
            fail "Check 38: dispatch record missing required field/member $_c38_f"
            check38_ok=0
        fi
    done
    # Negative: the baseline is ONE file-baseline/v1 object, never per-file
    # "custody entries" (the primitive emits one object with a files array).
    if grep -Fq 'custody entries' "$_c38_hc"; then
        fail "Check 38: handoff-contract.md still types owned_files as 'custody entries' (no such per-file record exists)"
        check38_ok=0
    fi

    # -- Handoff record: EVERY required field, incl. operational stops + deltas --
    _c38_hand=$(extract_section "$_c38_hc" "## Handoff record (worker → parent/human)")
    for _c38_f in 'schema' 'record' 'target' 'scope' 'mode' 'status' 'stop_reason' \
        'stop_detail' 'blocker_kind' 'blocker_class' 'blocker_signature' \
        'attempted_tools' 'best_candidates' 'failed_avenues' 'evidence' 'files_owned' \
        'files_changed' 'file_baseline' 'artifacts' 'next_action' \
        'new_evidence_required_for_rerun' \
        'blocker-driven' 'queue-empty' 'protocol-error' 'operational-error' \
        'safety-guard' 'goal_delta' 'diagnostic_delta' 'unified-diff'; do
        if ! echo "$_c38_hand" | grep -Fq "$_c38_f"; then
            fail "Check 38: handoff record missing required field/value $_c38_f"
            check38_ok=0
        fi
    done
    # The handoff must echo the task triple so the rerun guard is self-contained.
    if ! echo "$_c38_hand" | grep -Fq 'self-identifying'; then
        fail "Check 38: handoff record does not echo target/scope/mode (not self-identifying)"
        check38_ok=0
    fi

    # -- Rerun guard: predicate evaluable from the two records, with the
    #    load-bearing non-null precondition (else null==null forbids normal
    #    queue-empty/budget/user reruns). --
    _c38_rerun=$(extract_section "$_c38_hc" "## Rerun guard")
    if ! echo "$_c38_rerun" | grep -Fq 'prior_blocker == prior_handoff.blocker_signature' \
        || ! echo "$_c38_rerun" | grep -Fq 'evidence_delta' \
        || ! echo "$_c38_rerun" | grep -Fq 'from the two records' \
        || ! echo "$_c38_rerun" | grep -Fq 'same_task'; then
        fail "Check 38: rerun guard predicate not evaluable (needs same_task + prior_blocker + evidence_delta)"
        check38_ok=0
    fi
    if ! echo "$_c38_rerun" | grep -Fq 'is **non-null**'; then
        fail "Check 38: rerun guard missing the non-null blocker_signature precondition (null==null must not forbid a rerun)"
        check38_ok=0
    fi
    # Operational/protocol stops need their own rerun branch, else the null
    # blocker fields let a malformed dispatch/unavailable checker repeat forever.
    if ! echo "$_c38_rerun" | grep -Fq 'operational-error' \
        || ! echo "$_c38_rerun" | grep -Fq 'stop_detail'; then
        fail "Check 38: rerun guard missing the operational/protocol-error branch (relaunch only with evidence_delta resolving stop_detail)"
        check38_ok=0
    fi

    # -- Blocker-class human-phrase → enum mapping --
    if ! grep -Fq 'missing library lemma' "$_c38_hc" \
        || ! grep -Fq 'missing-library-lemma' "$_c38_hc"; then
        fail "Check 38: handoff-contract.md missing the review-phrase → blocker_class enum mapping"
        check38_ok=0
    fi
    # -- 'typed parameters' is actually typed: per-worker shapes defined --
    if ! grep -Fq '### Worker parameters' "$_c38_hc" \
        || ! grep -Fq 'sorry-filler-deep' "$_c38_hc" \
        || ! grep -Fq 'search_mode' "$_c38_hc"; then
        fail "Check 38: handoff-contract.md does not define per-worker parameters shapes"
        check38_ok=0
    fi
    # -- malformed dispatch still yields a valid handoff (nullable task/baseline) --
    if ! grep -Fq 'Malformed dispatch' "$_c38_hc"; then
        fail "Check 38: handoff-contract.md does not cover the malformed-dispatch handoff (nullable task echo/baseline)"
        check38_ok=0
    fi
fi

# cycle-engine.md: Run Contract section + no-subagent fallback + shared policy.
if ! grep -Fq '## Run Contract (`run-contract/v1`)' "$_c38_ce" \
    || ! grep -Fq 'No-subagent fallback' "$_c38_ce" \
    || ! grep -Fq '### Delegation Execution Policy' "$_c38_ce"; then
    fail "Check 38: cycle-engine.md missing Run Contract / no-subagent fallback / shared Delegation Execution Policy"
    check38_ok=0
fi
# The pre-flight block must be the COMPLETE dispatch envelope (all required
# fields present), not a "relevant subset" / "omit sections" prompt fragment.
if grep -Fq 'relevant subset' "$_c38_ce" || grep -Fq 'Omit sections with no data' "$_c38_ce"; then
    fail "Check 38: cycle-engine.md pre-flight block still uses subset/omit wording (must be the complete dispatch record)"
    check38_ok=0
fi
_c38_env=$(extract_section "$_c38_ce" "## Pre-flight Context for Subagent Dispatch")
for _c38_f in '"schema": "run-contract/v1"' '"record": "dispatch"' '"context"' \
    '"scope": "sorry"' '"schema": "file-baseline/v1"' '"prior_blocker": null' \
    '"evidence_delta": []'; do
    if ! echo "$_c38_env" | grep -Fq "$_c38_f"; then
        fail "Check 38: cycle-engine.md pre-flight envelope missing valid-instance field $_c38_f"
        check38_ok=0
    fi
done
# Negative: the concrete record must be a VALID instance, not pipe-delimited
# pseudo-values (which violate the contract's own enums/null types).
if echo "$_c38_env" | grep -Fq 'sorry | deps'; then
    fail "Check 38: pre-flight dispatch example uses pipe-delimited pseudo-values (must be one valid instance)"
    check38_ok=0
fi
# The embedded file-baseline/v1 entry must satisfy the shipped primitive:
# absolute path + realpath, and a 64-lowercase-hex sha256 for an existing file.
# (file_baseline.py rejects a relative path or a non-64-hex digest as malformed.)
if ! echo "$_c38_env" | grep -Eq '"owned_files": \["/' \
    || ! echo "$_c38_env" | grep -Eq '"path": "/[^"]+", "realpath": "/' \
    || ! echo "$_c38_env" | grep -Eq '"sha256": "[0-9a-f]{64}"'; then
    fail "Check 38: pre-flight baseline example is not a valid file-baseline/v1 (needs absolute path/realpath + 64-hex sha256)"
    check38_ok=0
fi

# review.md: reconciled — supplies vocab, is NOT itself a complete record.
if ! grep -Fq 'handoff-contract.md' "$_c38_rev"; then
    fail "Check 38: review.md does not reference the handoff contract"
    check38_ok=0
fi
if grep -Fq 'valid handoff record on its own' "$_c38_rev"; then
    fail "Check 38: review.md still claims its stuck block is a complete handoff record"
    check38_ok=0
fi

# Consuming docs reference the contract.
for _c38_doc in commands/prove.md commands/autoprove.md commands/golf.md \
    skills/lean4/SKILL.md skills/lean4/references/subagent-workflows.md \
    skills/lean4/references/agent-workflows.md; do
    if ! grep -Fq 'run-contract/v1' "$PLUGIN_ROOT/$_c38_doc"; then
        fail "Check 38: $_c38_doc does not reference run-contract/v1"
        check38_ok=0
    fi
done

# prove/autoprove emit the COMPLETE handoff record (not a partial field list)
# and reference the rerun guard.
for _c38_doc in commands/prove.md commands/autoprove.md; do
    if ! grep -Fq 'handoff-contract.md#rerun-guard' "$PLUGIN_ROOT/$_c38_doc" \
        || ! grep -Fq 'complete** `run-contract/v1`' "$PLUGIN_ROOT/$_c38_doc"; then
        fail "Check 38: $_c38_doc must emit the COMPLETE run-contract/v1 handoff record and reference the rerun guard"
        check38_ok=0
    fi
done

# golf.md: generic delegation rules live in the shared policy, not duplicated.
_c38_golf=$(extract_section "$PLUGIN_ROOT/commands/golf.md" "### Delegation Execution Policy")
if echo "$_c38_golf" | grep -Fq 'Fallback contract'; then
    fail "Check 38: golf.md still duplicates the generic Fallback contract rule (use the shared policy)"
    check38_ok=0
fi

# The ACTUAL proof-editing agents must consume the JSON dispatch and emit the
# handoff — the safety linkage broke while CI passed because Check 38 only
# looked at commands/. Each agent: references run-contract/v1 + owned_files,
# emits a handoff record, and must NOT gate custody on the old `### Owned
# files` heading (a JSON dispatch has no such heading → custody check skipped).
for _c38_ag in sorry-filler-deep proof-repair proof-golfer axiom-eliminator; do
    _c38_af="$PLUGIN_ROOT/agents/$_c38_ag.md"
    # No agent may gate custody on the old heading — a JSON dispatch has no such
    # heading, so the fail-closed branch would silently not activate.
    if grep -Fq '### Owned files' "$_c38_af"; then
        fail "Check 38: agents/$_c38_ag.md still gates custody on the '### Owned files' heading (must key off owned_files JSON)"
        check38_ok=0
    fi
    # Every agent consumes the dispatch (envelope + typed parameters) and emits
    # a handoff record — its ## Inputs must describe the dispatch, not legacy.
    if ! grep -Fq 'run-contract/v1' "$_c38_af" \
        || ! grep -Fq 'handoff record' "$_c38_af" \
        || ! grep -Fq 'dispatch record' "$_c38_af" \
        || ! grep -Fq 'parameters' "$_c38_af"; then
        fail "Check 38: agents/$_c38_ag.md does not consume the dispatch envelope + parameters / emit a handoff"
        check38_ok=0
    fi
done
# The three EDITING agents additionally key custody off the owned_files field.
for _c38_ag in sorry-filler-deep proof-golfer axiom-eliminator; do
    if ! grep -Fq 'owned_files' "$PLUGIN_ROOT/agents/$_c38_ag.md"; then
        fail "Check 38: editing agent agents/$_c38_ag.md does not fail-closed on the owned_files field"
        check38_ok=0
    fi
done
# proof-repair returns its diff in the handoff artifacts, not a bare diff.
if ! grep -Fq 'unified-diff' "$PLUGIN_ROOT/agents/proof-repair.md"; then
    fail "Check 38: proof-repair.md must carry its diff in the handoff artifacts (kind unified-diff)"
    check38_ok=0
fi

# A real structural fixture validator exists (grep alone can't prove semantics).
if [[ ! -f "$PLUGIN_ROOT/tests/test_run_contract.py" ]]; then
    fail "Check 38: missing tests/test_run_contract.py (structural dispatch/handoff fixtures)"
    check38_ok=0
fi

if [[ "$check38_ok" -eq 1 ]]; then
    ok "Check 38: run-contract/v1 handoff contract pinned (both records, reused vocab, files_owned≠files_changed, rerun guard, #82 deferral, cycle-engine + consumer wiring)"
fi

# ---------------------------------------------------------------------------
# Check 39: file-gate scope (#166). `lake env lean File.lean` checks against
# the built .oleans of the file's imports and does not rebuild them, so it can
# false-pass (or false-fail) after an imported module changes. Pin the
# canonical cycle-engine.md section (both failure directions, both recovery
# paths, no universal "sound check" claim), the two originally misleading
# sites, and the highest-risk cross-file editors. Deliberately NOT every
# `lake env lean` mention — fast file-local checks stay legitimate.
# ---------------------------------------------------------------------------
check39_ok=1
_c39_ce="$PLUGIN_ROOT/skills/lean4/references/cycle-engine.md"
_c39_sf="$PLUGIN_ROOT/skills/lean4/references/sorry-filling.md"
_c39_lsp="$PLUGIN_ROOT/skills/lean4/references/lean-lsp-server.md"

# Canonical section, scoped to its heading.
_c39_sec=$(extract_section "$_c39_ce" "### File Gate Scope")
if [[ -z "$_c39_sec" ]]; then
    fail "Check 39: cycle-engine.md missing '### File Gate Scope' section"
    check39_ok=0
else
    for _c39_s in 'does not rebuild imported modules' 'false pass' 'false failure' \
                  'Rebuild every changed imported module' 'for the importing target directly' \
                  'dependency-aware' 'final verification may still require' \
                  'lake lean <path/to/File.lean>'; do
        if ! grep -qF -- "$_c39_s" <<<"$_c39_sec"; then
            fail "Check 39: File Gate Scope section missing '$_c39_s'"
            check39_ok=0
        fi
    done
    # Negative: no universal soundness claim for lake build.
    if grep -qiE 'lake build[^.]*\bis the sound check\b' <<<"$_c39_sec"; then
        fail "Check 39: File Gate Scope must not call lake build 'the sound check' universally"
        check39_ok=0
    fi
fi
# Target spellings (Build Target Policy): current Lake accepts source paths; the
# naive '/' -> '.' module-name derivation is wrong under a custom srcDir.
_c39_btp=$(extract_section "$_c39_ce" "## Build Target Policy")
if ! grep -qF 'never derive a module name by textually turning' <<<"$_c39_btp"; then
    fail "Check 39: Build Target Policy must forbid deriving module names by textual / -> . conversion"
    check39_ok=0
fi
if ! grep -qF 'lake lean <path/to/File.lean>' <<<"$_c39_btp"; then
    fail "Check 39: Build Target Policy must mention lake lean <path/to/File.lean> (builds imports first)"
    check39_ok=0
fi
for _c39_f in skills/lean4/references/cycle-engine.md skills/lean4/references/command-examples.md \
              skills/lean4/references/disprove-engine.md; do
    if grep -qiE 'lake build.{0,40}does not accept file path' "$PLUGIN_ROOT/$_c39_f"; then
        fail "Check 39: $_c39_f still claims lake build does not accept file-path targets (false on current Lake)"
        check39_ok=0
    fi
    if grep -qE '`/` (→|->) `\.`|replac(e|ing) `/` with `\.`|with `/` (→|->) `\.` and `\.lean` dropped' "$PLUGIN_ROOT/$_c39_f"; then
        fail "Check 39: $_c39_f prescribes the naive / -> . module-name derivation (breaks on custom srcDir)"
        check39_ok=0
    fi
done

# The two sites #166 cited must carry the caveat + link, and the old
# unqualified formulations must not return.
_c39_step3=$(extract_section "$_c39_sf" "## Todo-Based Workflow (For Multiple Sorries)" | sed -n '/^\*\*Step 3: Verify compilation\*\*/,/^\*\*Step 4/p')
if [[ -z "$_c39_step3" ]]; then
    fail "Check 39: sorry-filling.md Todo-Based Workflow has no 'Step 3: Verify compilation' block"
    check39_ok=0
fi
if ! grep -qF 'cycle-engine.md#file-gate-scope' <<<"$_c39_step3"; then
    fail "Check 39: sorry-filling.md Step 3 must link cycle-engine.md#file-gate-scope"
    check39_ok=0
fi
if ! grep -qF 'does not rebuild' <<<"$_c39_step3"; then
    fail "Check 39: sorry-filling.md Step 3 must say the gate does not rebuild imports"
    check39_ok=0
fi
if grep -qE '^lake env lean path/to/File\.lean +# run from project root$' "$_c39_sf"; then
    fail "Check 39: sorry-filling.md still presents a bare, unqualified 'lake env lean' verification step"
    check39_ok=0
fi
if grep -qE 'Reserve `lake env lean[^`]*` \(run from project root\) for file-level gates and' "$_c39_lsp"; then
    fail "Check 39: lean-lsp-server.md still presents lake env lean as an unqualified file-level gate"
    check39_ok=0
fi
if ! grep -qF 'cycle-engine.md#file-gate-scope' "$_c39_lsp"; then
    fail "Check 39: lean-lsp-server.md must link cycle-engine.md#file-gate-scope"
    check39_ok=0
fi

# Highest-risk cross-file editors must route to lake lean <path/to/File.lean> and link
# the canonical section. (Not every mention — see header comment.)
for _c39_f in agents/sorry-filler-deep.md agents/axiom-eliminator.md \
              skills/lean4/references/proof-refactoring.md skills/lean4/SKILL.md; do
    if ! grep -qF 'cycle-engine.md#file-gate-scope' "$PLUGIN_ROOT/$_c39_f"; then
        fail "Check 39: $_c39_f must link cycle-engine.md#file-gate-scope"
        check39_ok=0
    fi
done
for _c39_f in agents/sorry-filler-deep.md agents/axiom-eliminator.md; do
    if ! grep -qF 'lake lean <path/to/File.lean>' "$PLUGIN_ROOT/$_c39_f"; then
        fail "Check 39: $_c39_f must route post-cross-file-edit gating to lake lean <path/to/File.lean>"
        check39_ok=0
    fi
done
# Quick references must distinguish the dependency-aware file gate (lake lean) from the project build.
if ! grep -qE '^lake lean path/to/File\.lean +#' "$PLUGIN_ROOT/agents/sorry-filler-deep.md"; then
    fail "Check 39: sorry-filler-deep.md quick reference must list the dependency-aware 'lake lean path/to/File.lean' line beside plain 'lake build'"
    check39_ok=0
fi

# /disprove certification: the REFUTED license is lake lean on the resolved target file
# (dependency-aware; accepts non-module files; writes no target .olean), never lake env lean.
_c39_dcmd="$PLUGIN_ROOT/commands/disprove.md"
_c39_deng="$PLUGIN_ROOT/skills/lean4/references/disprove-engine.md"
_c39_dfix="$PLUGIN_ROOT/tests/pressure/disprove_prime_directive.md"
_c39_pd_cmd=$(extract_section "$_c39_dcmd" "## Prime Directive")
_c39_pd_eng=$(extract_section "$_c39_deng" "## Prime Directive — Epistemological Strictness")
for _c39_pair in "disprove.md Prime Directive|$_c39_pd_cmd" "disprove-engine.md Prime Directive|$_c39_pd_eng"; do
    _c39_name="${_c39_pair%%|*}"; _c39_text="${_c39_pair#*|}"
    if [[ -z "$_c39_text" ]]; then
        fail "Check 39: $_c39_name section not found"
        check39_ok=0
        continue
    fi
    if ! grep -qF 'lake lean <target-file>' <<<"$_c39_text"; then
        fail "Check 39: $_c39_name must license REFUTED via lake lean <target-file>"
        check39_ok=0
    fi
    if ! grep -qE 'lake env lean.*(pre-screen|never the license)' <<<"$_c39_text"; then
        fail "Check 39: $_c39_name must demote lake env lean to a pre-screen"
        check39_ok=0
    fi
done
_c39_p3=$(extract_section "$_c39_deng" "## Phase 3 — Checkpoint")
if [[ -z "$_c39_p3" ]]; then
    fail "Check 39: disprove-engine.md '## Phase 3 — Checkpoint' section not found"
    check39_ok=0
else
    if ! grep -qE 'Compile gate.*lake lean <target-file>' <<<"$_c39_p3" || ! grep -qF 'This is unconditional' <<<"$_c39_p3"; then
        fail "Check 39: disprove-engine.md Phase 3 compile gate must be an unconditional lake lean <target-file>"
        check39_ok=0
    fi
    if ! grep -qE 're-run[[:space:]]*$' <<<"$_c39_p3" || ! grep -qF '`lake lean <target-file>` on the gate-free file' <<<"$_c39_p3"; then
        fail "Check 39: disprove-engine.md Phase 3 must rerun lake lean on the gate-free file after dropping the gate blocks"
        check39_ok=0
    fi
fi
for _c39_f in "$_c39_dcmd" "$_c39_deng"; do
    if grep -qE 'REFUTED. requires (\*\*both\*\* )?`lake env lean' "$_c39_f"; then
        fail "Check 39: $(basename "$_c39_f") still says REFUTED requires lake env lean"
        check39_ok=0
    fi
done
# /disprove worked examples (command-examples.md): the compile gate shown before
# REFUTED must be the dependency-aware lake lean, never lake env lean (and never a targeted lake build, which writes the target .olean and cannot build a non-module file).
# Section-scoped to the two worked examples so unrelated future examples can
# neither satisfy nor trip these assertions.
_c39_cex="$PLUGIN_ROOT/skills/lean4/references/command-examples.md"
# The verification-ladder mirror must recommend the dependency-aware file gate,
# not the version-dependent, module-only targeted build, after a cross-file edit.
if ! grep -qF 'after editing an imported module, run `lake lean <path/to/File.lean>`' "$_c39_cex"; then
    fail "Check 39: command-examples.md ladder note must route post-import-edit gating to lake lean <path/to/File.lean>"
    check39_ok=0
fi
if grep -qE 'after editing an imported module, run `lake build <path' "$_c39_cex"; then
    fail "Check 39: command-examples.md ladder note recommends a targeted lake build after an import edit again"
    check39_ok=0
fi
for _c39_h in '### Cycle 1 — decide-cascade Win Example' \
              '### Cycle 1 mine miss → cycle 2 enumerate widen + certify'; do
    _c39_ex=$(extract_section "$_c39_cex" "$_c39_h")
    if [[ -z "$_c39_ex" ]]; then
        fail "Check 39: command-examples.md section '$_c39_h' not found"
        check39_ok=0
        continue
    fi
    if grep -qE 'Compile gate.*lake env lean' <<<"$_c39_ex"; then
        fail "Check 39: '$_c39_h' still shows lake env lean as the compile gate before REFUTED"
        check39_ok=0
    fi
    if ! grep -qE '^Compile gate \(lake lean [^)]*\): passed' <<<"$_c39_ex"; then
        fail "Check 39: '$_c39_h' must show an explicit 'Compile gate (lake lean <target-file> ...): passed'"
        check39_ok=0
    fi
    if ! grep -qE '^Axiom gate \(#print axioms [A-Za-z_]+, read from the same lake lean run\)' <<<"$_c39_ex"; then
        fail "Check 39: '$_c39_h' must show the axiom gate as #print axioms read from the same lake lean run"
        check39_ok=0
    fi
    if ! grep -qE 'Dropped gate-only.*re-checked with lake lean [^:]*: passed' <<<"$_c39_ex"; then
        fail "Check 39: '$_c39_h' must show the post-wrapper re-check as a lake lean"
        check39_ok=0
    fi
    if grep -qE '^Compile gate: passed' <<<"$_c39_ex"; then
        fail "Check 39: '$_c39_h' has a generic 'Compile gate: passed' line — name the lake lean gate"
        check39_ok=0
    fi
done
# The license must not drift back to a targeted `lake build <target-file>`:
# it is `unknown target` for an accepted non-module File.lean:LINE target, and
# it writes the target .olean, so a source rollback after a failed axiom gate
# would leave the rejected declarations in the artifact (#195 review round 5).
for _c39_pair in "disprove.md Prime Directive|$_c39_pd_cmd" "disprove-engine.md Prime Directive|$_c39_pd_eng"; do
    _c39_name="${_c39_pair%%|*}"; _c39_text="${_c39_pair#*|}"
    if grep -qF 'lake build <target-file>' <<<"$_c39_text" || grep -qE 'REFUTED.*requires.*`lake build' <<<"$_c39_text"; then
        fail "Check 39: $_c39_name licenses REFUTED via a targeted lake build again — the gate is lake lean <target-file>"
        check39_ok=0
    fi
done
if [[ -n "$_c39_p3" ]]; then
    for _c39_s in 'outside any `lean_lib`' 'does **not** write the target'; do
        if ! grep -qF -- "$_c39_s" <<<"$_c39_p3"; then
            fail "Check 39: disprove-engine.md Phase 3 must state why lake lean is the gate ($_c39_s)"
            check39_ok=0
        fi
    done
    if grep -qE 'Compile gate.*`lake build <target-file>`' <<<"$_c39_p3"; then
        fail "Check 39: disprove-engine.md Phase 3 compile gate is a targeted lake build again"
        check39_ok=0
    fi
fi
# Axiom gate freshness: the licensing #print axioms must be elaborated by the
# same lake lean run as the compile gate. lean_verify goes through the LSP's
# persistent scratch pool, whose import snapshot can lag the rebuilt imports.
if [[ -n "$_c39_p3" ]]; then
    for _c39_s in '`#print axioms T_counterexample`' '`#print axioms T_counterexample_negates_target`' 'deliberately **unqualified**' \
                  '--role=gate --decl=T_counterexample_axioms' \
                  'same `lake lean` run' 'advisory cross-check only'; do
        if ! grep -qF -- "$_c39_s" <<<"$_c39_p3"; then
            fail "Check 39: disprove-engine.md Phase 3 axiom gate must be the same-run #print axioms probe ($_c39_s)"
            check39_ok=0
        fi
    done
    if grep -qE 'via `lean_verify` \(or `#print axioms`\)|`lean_verify` / `#print axioms`' <<<"$_c39_p3"; then
        fail "Check 39: disprove-engine.md Phase 3 presents lean_verify and #print axioms as interchangeable licensing routes"
        check39_ok=0
    fi
    # The probe must be UNQUALIFIED: blocks land at end-of-file, where a
    # namespace left open makes the artifact N.T_counterexample; `_root_.`
    # would inspect an imported root declaration of the same name instead.
    if grep -qF '#print axioms _root_.' <<<"$_c39_p3"; then
        fail "Check 39: disprove-engine.md Phase 3 probe is root-qualified (_root_.) — it must be the unqualified name so it resolves to the just-appended declaration"
        check39_ok=0
    fi
fi
if grep -qF '#print axioms _root_.' "$_c39_dcmd" "$_c39_cex"; then
    fail "Check 39: a /disprove axiom probe is root-qualified (_root_.) — use the unqualified name"
    check39_ok=0
fi
if grep -qE 'via `lean_verify` / `#print axioms`|via `lean_verify` \(or `#print axioms`\)' "$_c39_dcmd"; then
    fail "Check 39: disprove.md presents lean_verify and #print axioms as interchangeable licensing routes"
    check39_ok=0
fi
if ! grep -qF "from that same run's" "$_c39_dcmd"; then
    fail "Check 39: disprove.md Phase 3 summary must read the axiom set from the same lake lean run"
    check39_ok=0
fi
if grep -qF 'Lake 5 accepts' "$_c39_ce" "$_c39_cex" "$_c39_deng"; then
    fail "Check 39: 'Lake 5 accepts source paths' is not a valid version boundary (Lean 4.19's Lake also reports 5.0.0 and did not)"
    check39_ok=0
fi
# Pressure fixture: must teach the corrected rule; the old sentence must not return.
if [[ ! -f "$_c39_dfix" ]]; then
    fail "Check 39: missing tests/pressure/disprove_prime_directive.md"
    check39_ok=0
else
    if grep -qF 'only `lake env lean <path>`' "$_c39_dfix"; then
        fail "Check 39: pressure fixture still teaches that only lake env lean licenses the disproved claim (#166 proved that unsound)"
        check39_ok=0
    fi
    if ! grep -qF 'lake lean <target-file>' "$_c39_dfix"; then
        fail "Check 39: pressure fixture must name lake lean <target-file> as the license"
        check39_ok=0
    fi
fi

if [[ "$check39_ok" -eq 1 ]]; then
    ok "Check 39: file-gate scope pinned (#166: canonical section w/ both failure directions + both recovery paths, cited sites corrected, cross-file editors routed, disprove REFUTED licensed by lake lean <target-file>, no naive module-name derivation)"
fi

echo ""
echo "=== Results: $PASS passed, $FAIL failed ==="
[[ "$FAIL" -eq 0 ]]

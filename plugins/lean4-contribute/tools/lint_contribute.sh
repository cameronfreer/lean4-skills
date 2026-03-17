#!/usr/bin/env bash
# Minimal surface validation for the lean4-contribute plugin.
# Run from repo root:
#   bash plugins/lean4-contribute/tools/lint_contribute.sh
set -euo pipefail

PASS=0
FAIL=0

ok()   { echo "  ✓ $1"; (( ++PASS )); }
fail() { echo "  ✗ $1"; (( ++FAIL )); }

PLUGIN_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
REPO_ROOT="$(cd "$PLUGIN_ROOT/../.." && pwd)"

echo "Validating lean4-contribute plugin..."
echo ""

# 1. Valid JSON — plugin.json
echo "Checking plugin.json..."
plugin_json="$PLUGIN_ROOT/.claude-plugin/plugin.json"
if [[ ! -f "$plugin_json" ]]; then
    fail "plugin.json not found"
else
    if python3 -c "import json; json.load(open('$plugin_json'))" 2>/dev/null; then
        ok "plugin.json is valid JSON"
    else
        fail "plugin.json is not valid JSON"
    fi

    # Consent warning in plugin.json description
    if grep -qi 'share.*snippet\|snippet.*share\|may share' "$plugin_json"; then
        ok "plugin.json description contains consent warning"
    else
        fail "plugin.json description missing consent/sharing warning"
    fi
fi

# 2. Marketplace entry
echo ""
echo "Checking marketplace.json..."
marketplace_json="$REPO_ROOT/.claude-plugin/marketplace.json"
if [[ ! -f "$marketplace_json" ]]; then
    fail "marketplace.json not found"
else
    if python3 -c "import json; json.load(open('$marketplace_json'))" 2>/dev/null; then
        ok "marketplace.json is valid JSON"
    else
        fail "marketplace.json is not valid JSON"
    fi

    # lean4-contribute entry exists
    if grep -q '"lean4-contribute"' "$marketplace_json"; then
        ok "marketplace.json has lean4-contribute entry"
    else
        fail "marketplace.json missing lean4-contribute entry"
    fi

    # Consent warning in marketplace lean4-contribute description
    if command -v jq &>/dev/null; then
        market_desc=$(jq -r '.plugins[] | select(.name == "lean4-contribute") | .description' "$marketplace_json")
    else
        # Rough fallback
        market_desc=$(grep -A1 '"lean4-contribute"' "$marketplace_json" | grep '"description"' | head -1)
    fi
    if echo "$market_desc" | grep -qi 'share.*snippet\|snippet.*share\|may share'; then
        ok "marketplace description contains consent warning"
    else
        fail "marketplace description missing consent/sharing warning"
    fi
fi

# 3. Command files exist with correct frontmatter
echo ""
echo "Checking command files..."
expected_cmds=("bug-report" "feature-request" "share-insight")
for cmd in "${expected_cmds[@]}"; do
    cmd_file="$PLUGIN_ROOT/commands/$cmd.md"
    if [[ ! -f "$cmd_file" ]]; then
        fail "$cmd.md not found"
        continue
    fi
    ok "$cmd.md exists"

    # Check frontmatter fields
    name=$(sed -n 's/^name: *//p' "$cmd_file")
    desc=$(sed -n 's/^description: *//p' "$cmd_file")
    dmi=$(sed -n 's/^disable-model-invocation: *//p' "$cmd_file")

    if [[ "$name" == "$cmd" ]]; then
        ok "$cmd.md name matches filename"
    else
        fail "$cmd.md name '$name' != '$cmd'"
    fi

    if [[ -n "$desc" ]]; then
        ok "$cmd.md has description"
    else
        fail "$cmd.md missing description"
    fi

    if [[ "$dmi" == "true" ]]; then
        ok "$cmd.md disable-model-invocation: true"
    else
        fail "$cmd.md disable-model-invocation is '$dmi', expected 'true'"
    fi

    # Trust-contract checks
    if grep -q "Display the.*complete.*issue draft" "$cmd_file"; then
        ok "$cmd.md requires showing complete draft"
    else
        fail "$cmd.md missing 'Display the complete issue draft' requirement"
    fi

    if grep -q "Do.*not.*proceed unless the user explicitly confirms" "$cmd_file"; then
        ok "$cmd.md requires explicit confirmation"
    else
        fail "$cmd.md missing explicit confirmation gate"
    fi

    has_gh=0; has_browser=0; has_email=0
    grep -q 'gh issue create' "$cmd_file" && has_gh=1
    grep -q 'github.com/cameronfreer/lean4-skills/issues/new' "$cmd_file" && has_browser=1
    grep -q 'lean4skills@gmail.com' "$cmd_file" && has_email=1
    if [[ "$has_gh" -eq 1 && "$has_browser" -eq 1 && "$has_email" -eq 1 ]]; then
        ok "$cmd.md has all three submit paths (gh, browser, email)"
    else
        fail "$cmd.md missing submit path(s): gh=$has_gh browser=$has_browser email=$has_email"
    fi
done

# Summary
echo ""
echo "================================"
if [[ "$FAIL" -eq 0 ]]; then
    echo "✓ All $PASS checks passed"
else
    echo "✗ $FAIL check(s) failed, $PASS passed"
    exit 1
fi

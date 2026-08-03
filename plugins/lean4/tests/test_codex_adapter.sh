#!/usr/bin/env bash
set -euo pipefail

# Deterministic native-Codex adapter contract tests (#157). Real Codex
# install/trust behavior is smoke-tested separately; this suite stays
# dependency-free and runs under macOS Bash 3.2 in CI.

BASH_FOR_COMPAT="${BASH_FOR_COMPAT:-/bin/bash}"
if [[ ! -x "$BASH_FOR_COMPAT" ]]; then
    echo "SKIP: $BASH_FOR_COMPAT not found — cannot run Codex adapter self-test"
    exit 0
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PLUGIN_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
REPO_ROOT="$(cd "$PLUGIN_ROOT/../.." && pwd)"

CODEX_MANIFEST="$PLUGIN_ROOT/.codex-plugin/plugin.json"
CLAUDE_MANIFEST="$PLUGIN_ROOT/.claude-plugin/plugin.json"
CODEX_HOOKS="$PLUGIN_ROOT/hooks/codex-hooks.json"
CODEX_MARKETPLACE="$REPO_ROOT/.agents/plugins/marketplace.json"
BOOTSTRAP="$PLUGIN_ROOT/hooks/bootstrap.sh"
PROMPT_HOOK="$PLUGIN_ROOT/hooks/validate_user_prompt.py"
GUARDRAILS="$PLUGIN_ROOT/hooks/guardrails.sh"

PASS=0
FAIL=0
pass() { echo "  PASS: $1"; (( ++PASS )) || true; }
fail() { echo "  FAIL: $1"; (( ++FAIL )) || true; }

SCRATCH=$(mktemp -d)
trap 'rm -rf "$SCRATCH"' EXIT

echo "=== native Codex adapter contract tests ==="
echo ""

# ---------------------------------------------------------------------------
# Metadata contracts: in-place plugin, thin marketplace, dedicated hooks.
# ---------------------------------------------------------------------------
if python3 - "$CODEX_MANIFEST" "$CLAUDE_MANIFEST" "$CODEX_MARKETPLACE" "$CODEX_HOOKS" <<'PY'
import json
import re
import sys
from pathlib import Path

codex_path, claude_path, market_path, hooks_path = map(Path, sys.argv[1:])
codex = json.loads(codex_path.read_text())
claude = json.loads(claude_path.read_text())
market = json.loads(market_path.read_text())
hooks = json.loads(hooks_path.read_text())

assert codex["name"] == "lean4"
assert codex["version"] == claude["version"]
assert re.fullmatch(r"[0-9]+\.[0-9]+\.[0-9]+", codex["version"])
assert codex["description"] == claude["description"]
assert codex["skills"] == "./skills"
assert codex["hooks"] == "./hooks/codex-hooks.json"
assert codex["license"] == "MIT"
interface = codex["interface"]
for key in (
    "displayName",
    "shortDescription",
    "longDescription",
    "developerName",
    "category",
    "capabilities",
    "websiteURL",
    "defaultPrompt",
):
    assert interface[key]
assert "privacyPolicyURL" not in interface
assert "termsOfServiceURL" not in interface

assert market["name"] == "lean4-skills"
assert market["interface"]["displayName"] == "Lean 4 Skills"
assert len(market["plugins"]) == 1
entry = market["plugins"][0]
assert entry["name"] == "lean4"
assert entry["source"] == {"source": "local", "path": "./plugins/lean4"}
assert entry["policy"] == {
    "installation": "AVAILABLE",
    "authentication": "ON_INSTALL",
}
assert entry["category"] == "Coding"

events = hooks["hooks"]
assert set(events) == {"SessionStart", "UserPromptSubmit", "PreToolUse"}
session = events["SessionStart"][0]
assert session["matcher"] == "startup|resume|clear|compact"
assert session["hooks"][0]["command"] == '"$PLUGIN_ROOT/hooks/bootstrap.sh" --host codex'
prompt = events["UserPromptSubmit"][0]
assert "matcher" not in prompt
assert prompt["hooks"][0]["command"] == '"$PLUGIN_ROOT/hooks/validate_user_prompt.py"'
pretool = events["PreToolUse"][0]
assert pretool["matcher"] == "Bash"
assert pretool["hooks"][0]["command"] == '"$PLUGIN_ROOT/hooks/guardrails.sh"'
for event in events.values():
    for group in event:
        for hook in group["hooks"]:
            assert "CLAUDE_PLUGIN_ROOT" not in hook["command"]
PY
then
    pass "manifest, marketplace, and Codex hook contracts are valid"
else
    fail "manifest, marketplace, or Codex hook contract"
fi

if [[ -f "$CODEX_MANIFEST" && ! -L "$CODEX_MANIFEST" \
   && -f "$CODEX_HOOKS" && ! -L "$CODEX_HOOKS" \
   && ! -e "$PLUGIN_ROOT/packages" \
   && ! -e "$PLUGIN_ROOT/codex-package" ]]; then
    pass "adapter is in place with no mirrored package tree"
else
    fail "adapter introduced a symlinked or mirrored package surface"
fi

# ---------------------------------------------------------------------------
# Codex-shaped hook invocations.
# ---------------------------------------------------------------------------
session_payload='{"session_id":"session-1","cwd":"/tmp","source":"startup","hook_event_name":"SessionStart"}'
bootstrap_exit=0
bootstrap_out=$(printf '%s' "$session_payload" | env \
    -u LEAN4_PLUGIN_ROOT -u LEAN4_SCRIPTS -u LEAN4_REFS \
    PLUGIN_ROOT="$PLUGIN_ROOT" CLAUDE_PLUGIN_ROOT="$SCRATCH/wrong-root" \
    CLAUDE_ENV_FILE="$SCRATCH/must-not-exist" PATH="/usr/bin:/bin" \
    "$BASH_FOR_COMPAT" "$BOOTSTRAP" --host codex 2>&1) || bootstrap_exit=$?
if [[ "$bootstrap_exit" -eq 0 ]] \
   && grep -qF "plugin_root=$PLUGIN_ROOT" <<<"$bootstrap_out" \
   && grep -qF "shell_env_persistent=false" <<<"$bootstrap_out" \
   && [[ ! -e "$SCRATCH/must-not-exist" ]]; then
    pass "SessionStart emits truthful absolute context and writes no env file"
else
    fail "SessionStart Codex context (exit=$bootstrap_exit): $bootstrap_out"
fi

prompt_payload='{"session_id":"session-1","turn_id":"turn-1","cwd":"/tmp","permission_mode":"default","hook_event_name":"UserPromptSubmit","prompt":"/lean4:prove Foo.lean"}'
prompt_exit=0
prompt_out=$(printf '%s' "$prompt_payload" | env PLUGIN_ROOT="$PLUGIN_ROOT" "$PROMPT_HOOK" 2>&1) || prompt_exit=$?
if [[ "$prompt_exit" -eq 0 ]] && printf '%s' "$prompt_out" | python3 -c '
import json, sys
data = json.load(sys.stdin)
assert data["hookSpecificOutput"]["hookEventName"] == "UserPromptSubmit"
assert data["hookSpecificOutput"]["additionalContext"]
'; then
    pass "UserPromptSubmit accepts Codex input and emits additionalContext"
else
    fail "UserPromptSubmit Codex round-trip (exit=$prompt_exit): $prompt_out"
fi

skill_prompt='{"cwd":"/tmp","hook_event_name":"UserPromptSubmit","prompt":"$lean4 prove Foo.lean"}'
skill_prompt_exit=0
skill_prompt_out=$(printf '%s' "$skill_prompt" | env PLUGIN_ROOT="$PLUGIN_ROOT" "$PROMPT_HOOK" 2>&1) || skill_prompt_exit=$?
if [[ "$skill_prompt_exit" -eq 0 && -z "$skill_prompt_out" ]]; then
    pass "UserPromptSubmit passes an ordinary Codex \$lean4 prompt unchanged"
else
    fail "UserPromptSubmit ordinary \$lean4 prompt (exit=$skill_prompt_exit): $skill_prompt_out"
fi

blocked_prompt='{"cwd":"/tmp","hook_event_name":"UserPromptSubmit","prompt":"/lean4:draft --mode=banana x"}'
blocked_prompt_out=$(printf '%s' "$blocked_prompt" | env PLUGIN_ROOT="$PLUGIN_ROOT" "$PROMPT_HOOK" 2>/dev/null)
if printf '%s' "$blocked_prompt_out" | python3 -c '
import json, sys
data = json.load(sys.stdin)
assert data["decision"] == "block"
assert data["reason"]
'; then
    pass "UserPromptSubmit preserves legacy decision:block semantics"
else
    fail "UserPromptSubmit block response: $blocked_prompt_out"
fi

lean_project="$SCRATCH/lean-project"
mkdir -p "$lean_project"
touch "$lean_project/lean-toolchain"

safe_payload=$(printf '{"session_id":"session-1","turn_id":"turn-1","cwd":"%s","tool_name":"Bash","hook_event_name":"PreToolUse","tool_input":{"command":"git status"}}' "$lean_project")
safe_exit=0
printf '%s' "$safe_payload" | "$GUARDRAILS" >/dev/null 2>&1 || safe_exit=$?
if [[ "$safe_exit" -eq 0 ]]; then
    pass "PreToolUse allows a safe Codex Bash payload"
else
    fail "PreToolUse safe payload returned $safe_exit"
fi

blocked_payload=$(printf '{"session_id":"session-1","turn_id":"turn-1","cwd":"%s","tool_name":"Bash","hook_event_name":"PreToolUse","tool_input":{"command":"git reset --hard"}}' "$lean_project")
blocked_exit=0
blocked_out=$(printf '%s' "$blocked_payload" | "$GUARDRAILS" 2>&1) || blocked_exit=$?
if [[ "$blocked_exit" -eq 2 ]] && grep -qF "BLOCKED" <<<"$blocked_out"; then
    pass "PreToolUse blocks a destructive Codex Bash payload with exit 2"
else
    fail "PreToolUse destructive payload (exit=$blocked_exit): $blocked_out"
fi

echo ""
echo "=== test_codex_adapter.sh: $PASS passed, $FAIL failed ==="
[[ "$FAIL" -eq 0 ]]

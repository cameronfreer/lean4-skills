#!/usr/bin/env bash
set -euo pipefail

# Layer 2 integration tests for validate_user_prompt.py
# Pipes JSON to the hook and asserts on exit codes and stdout JSON fields.
#
# NOTE: We invoke "$HOOK" directly (no `bash` or `python3` prefix) so that
# the shebang line and executable bit are exercised end-to-end.

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
HOOK="$(cd "$SCRIPT_DIR/.." && pwd)/hooks/validate_user_prompt.py"

PASS=0
FAIL=0

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

# run_test: pipe $input to the hook, assert exit code.
#   $1=description  $2=stdin input  $3=expected exit code
run_test() {
  local desc="$1" input="$2" expected_exit="$3"
  local actual_exit=0
  echo "$input" | "$HOOK" >/dev/null 2>&1 || actual_exit=$?
  if [[ "$actual_exit" -eq "$expected_exit" ]]; then
    echo "  PASS: $desc"
    (( ++PASS ))
  else
    echo "  FAIL: $desc (expected exit $expected_exit, got $actual_exit)"
    (( ++FAIL ))
  fi
}

# run_test_empty: pipe $input to the hook, assert exit 0 AND empty stdout.
#   $1=description  $2=stdin input
run_test_empty() {
  local desc="$1" input="$2"
  local actual_exit=0 output
  output=$(echo "$input" | "$HOOK" 2>/dev/null) || actual_exit=$?
  if [[ "$actual_exit" -ne 0 ]]; then
    echo "  FAIL: $desc (expected exit 0, got $actual_exit)"
    (( ++FAIL ))
    return
  fi
  if [[ -z "$output" ]]; then
    echo "  PASS: $desc"
    (( ++PASS ))
  else
    echo "  FAIL: $desc (expected empty stdout, got '$output')"
    (( ++FAIL ))
  fi
}

# run_test_empty_stdin: send no stdin to the hook, assert exit 0 AND empty stdout.
#   $1=description
run_test_empty_stdin() {
  local desc="$1"
  local actual_exit=0 output
  output=$("$HOOK" </dev/null 2>/dev/null) || actual_exit=$?
  if [[ "$actual_exit" -ne 0 ]]; then
    echo "  FAIL: $desc (expected exit 0, got $actual_exit)"
    (( ++FAIL ))
    return
  fi
  if [[ -z "$output" ]]; then
    echo "  PASS: $desc"
    (( ++PASS ))
  else
    echo "  FAIL: $desc (expected empty stdout, got '$output')"
    (( ++FAIL ))
  fi
}

# run_test_json: pipe $input to the hook, extract a jq expression, compare to expected.
#   $1=description  $2=stdin input  $3=jq expression  $4=expected value
run_test_json() {
  local desc="$1" input="$2" jq_expr="$3" expected="$4"
  local output actual
  output=$(echo "$input" | "$HOOK" 2>/dev/null)
  # Use jq if available, else python3 fallback
  if command -v jq &>/dev/null; then
    actual=$(echo "$output" | jq -r "$jq_expr" 2>/dev/null)
  else
    actual=$(echo "$output" | python3 -c "
import sys, json
d = json.load(sys.stdin)
# Walk the jq-like path: .a.b.c -> d['a']['b']['c']
path = sys.argv[1].lstrip('.').split('.')
cur = d
for p in path:
    cur = cur[p]
print(cur)
" "$jq_expr" 2>/dev/null)
  fi
  if [[ "$actual" == "$expected" ]]; then
    echo "  PASS: $desc"
    (( ++PASS ))
  else
    echo "  FAIL: $desc (expected '$expected', got '$actual')"
    (( ++FAIL ))
  fi
}

# run_test_json_contains: pipe $input, extract jq field, check substring match.
#   $1=description  $2=stdin input  $3=jq expression  $4=substring
run_test_json_contains() {
  local desc="$1" input="$2" jq_expr="$3" substring="$4"
  local output actual
  output=$(echo "$input" | "$HOOK" 2>/dev/null)
  if command -v jq &>/dev/null; then
    actual=$(echo "$output" | jq -r "$jq_expr" 2>/dev/null)
  else
    actual=$(echo "$output" | python3 -c "
import sys, json
d = json.load(sys.stdin)
path = sys.argv[1].lstrip('.').split('.')
cur = d
for p in path:
    cur = cur[p]
print(cur)
" "$jq_expr" 2>/dev/null)
  fi
  if [[ "$actual" == *"$substring"* ]]; then
    echo "  PASS: $desc"
    (( ++PASS ))
  else
    echo "  FAIL: $desc (expected '$substring' in '$actual')"
    (( ++FAIL ))
  fi
}

echo "=== validate_user_prompt.py integration tests ==="
echo ""

# ---------------------------------------------------------------------------
# Passthrough cases (no output, exit 0)
# ---------------------------------------------------------------------------

echo "-- Passthrough cases (exit 0, empty stdout) --"

run_test_empty \
  "1. Empty prompt" \
  '{"prompt":""}'

run_test_empty \
  "2. Non-/lean4: prompt" \
  '{"prompt":"hello world"}'

run_test_empty \
  "3. /codex: prefix (not /lean4:)" \
  '{"prompt":"/codex:foo bar"}'

run_test_empty \
  "4. Whitespace-only prompt" \
  '{"prompt":"   "}'

run_test_empty \
  "5. Malformed JSON on stdin" \
  "not json at all"

run_test_empty_stdin \
  "6. Empty stdin"

run_test_empty \
  "7. Unknown /lean4: command" \
  '{"prompt":"/lean4:nonexistent foo"}'

run_test_empty \
  "8. /lean4: with no command name" \
  '{"prompt":"/lean4: foo"}'

run_test_empty \
  "9. Uncovered command (doctor)" \
  '{"prompt":"/lean4:doctor"}'

run_test_empty \
  "10. Uncovered command (checkpoint)" \
  '{"prompt":"/lean4:checkpoint"}'

# ---------------------------------------------------------------------------
# Blocked cases (exit 0, stdout has decision:block)
# ---------------------------------------------------------------------------

echo ""
echo "-- Blocked cases (exit 0, decision=block) --"

run_test \
  "11. Missing topic+source for draft (exit 0)" \
  '{"prompt":"/lean4:draft --mode=skeleton","cwd":"/tmp"}' \
  0

run_test_json \
  "11b. Missing topic+source for draft (decision=block)" \
  '{"prompt":"/lean4:draft --mode=skeleton","cwd":"/tmp"}' \
  ".decision" \
  "block"

run_test \
  "12. Bad enum for draft --mode (exit 0)" \
  '{"prompt":"/lean4:draft --mode=banana \"x\"","cwd":"/tmp"}' \
  0

run_test_json \
  "12b. Bad enum for draft --mode (decision=block)" \
  '{"prompt":"/lean4:draft --mode=banana \"x\"","cwd":"/tmp"}' \
  ".decision" \
  "block"

run_test \
  "13. Missing required flags for autoformalize (exit 0)" \
  '{"prompt":"/lean4:autoformalize","cwd":"/tmp"}' \
  0

run_test_json \
  "13b. Missing required flags for autoformalize (decision=block)" \
  '{"prompt":"/lean4:autoformalize","cwd":"/tmp"}' \
  ".decision" \
  "block"

run_test \
  "14. Bad int for autoprove --max-cycles (exit 0)" \
  '{"prompt":"/lean4:autoprove --max-cycles=cat","cwd":"/tmp"}' \
  0

run_test_json \
  "14b. Bad int for autoprove --max-cycles (decision=block)" \
  '{"prompt":"/lean4:autoprove --max-cycles=cat","cwd":"/tmp"}' \
  ".decision" \
  "block"

# ---------------------------------------------------------------------------
# Success cases (exit 0, stdout has hookSpecificOutput.additionalContext)
# ---------------------------------------------------------------------------

echo ""
echo "-- Success cases (exit 0, hookEventName=UserPromptSubmit) --"

run_test \
  "15. Valid draft (exit 0)" \
  '{"prompt":"/lean4:draft \"Theorem 1\"","cwd":"/tmp"}' \
  0

run_test_json \
  "15b. Valid draft (hookEventName)" \
  '{"prompt":"/lean4:draft \"Theorem 1\"","cwd":"/tmp"}' \
  ".hookSpecificOutput.hookEventName" \
  "UserPromptSubmit"

run_test \
  "16. Valid autoprove with coercion (exit 0)" \
  '{"prompt":"/lean4:autoprove --commit=ask --max-cycles=5","cwd":"/tmp"}' \
  0

run_test_json \
  "16b. Valid autoprove with coercion (hookEventName)" \
  '{"prompt":"/lean4:autoprove --commit=ask --max-cycles=5","cwd":"/tmp"}' \
  ".hookSpecificOutput.hookEventName" \
  "UserPromptSubmit"

run_test \
  "17. Valid prove (exit 0)" \
  '{"prompt":"/lean4:prove Foo.lean","cwd":"/tmp"}' \
  0

run_test_json \
  "17b. Valid prove (hookEventName)" \
  '{"prompt":"/lean4:prove Foo.lean","cwd":"/tmp"}' \
  ".hookSpecificOutput.hookEventName" \
  "UserPromptSubmit"

run_test \
  "18. Valid learn (exit 0)" \
  '{"prompt":"/lean4:learn \"groups\"","cwd":"/tmp"}' \
  0

run_test_json \
  "18b. Valid learn (hookEventName)" \
  '{"prompt":"/lean4:learn \"groups\"","cwd":"/tmp"}' \
  ".hookSpecificOutput.hookEventName" \
  "UserPromptSubmit"

run_test \
  "19. Valid formalize (exit 0)" \
  '{"prompt":"/lean4:formalize \"Zorn\"","cwd":"/tmp"}' \
  0

run_test_json \
  "19b. Valid formalize (hookEventName)" \
  '{"prompt":"/lean4:formalize \"Zorn\"","cwd":"/tmp"}' \
  ".hookSpecificOutput.hookEventName" \
  "UserPromptSubmit"

# ---------------------------------------------------------------------------
# Artifact cases
# ---------------------------------------------------------------------------

echo ""
echo "-- Artifact cases --"

# 20. With session_id + CLAUDE_SESSION_DIR: verify artifact file is written
ARTIFACT_DIR=$(mktemp -d)

# Run the hook with CLAUDE_SESSION_DIR so the artifact lands in our temp dir.
# env sets the variable for the entire pipeline (the hook is the reader).
echo '{"prompt":"/lean4:draft \"Theorem 1\"","cwd":"/tmp","session_id":"test123"}' \
  | env CLAUDE_SESSION_DIR="$ARTIFACT_DIR" "$HOOK" >/dev/null 2>&1 || true

if [[ -f "$ARTIFACT_DIR/lean4_invocation_test123.json" ]]; then
  echo "  PASS: 20. Artifact file written to CLAUDE_SESSION_DIR"
  (( ++PASS ))
else
  echo "  FAIL: 20. Artifact file not found at $ARTIFACT_DIR/lean4_invocation_test123.json"
  (( ++FAIL ))
fi
rm -rf "$ARTIFACT_DIR"

# 21. Without session_id: verify no artifact file
NO_ARTIFACT_DIR=$(mktemp -d)

echo '{"prompt":"/lean4:draft \"Theorem 1\"","cwd":"/tmp"}' \
  | env CLAUDE_SESSION_DIR="$NO_ARTIFACT_DIR" "$HOOK" >/dev/null 2>&1 || true

# Count files -- there should be none starting with lean4_invocation_
ARTIFACT_COUNT=$(find "$NO_ARTIFACT_DIR" -name 'lean4_invocation_*' 2>/dev/null | wc -l)
if [[ "$ARTIFACT_COUNT" -eq 0 ]]; then
  echo "  PASS: 21. No artifact file without session_id"
  (( ++PASS ))
else
  echo "  FAIL: 21. Unexpected artifact files found in $NO_ARTIFACT_DIR"
  (( ++FAIL ))
fi
rm -rf "$NO_ARTIFACT_DIR"

# ---------------------------------------------------------------------------
# Coercion visibility
# ---------------------------------------------------------------------------

echo ""
echo "-- Coercion visibility --"

run_test_json_contains \
  "22. Autoprove --commit=ask: additionalContext contains 'coerced'" \
  '{"prompt":"/lean4:autoprove --commit=ask --max-cycles=5","cwd":"/tmp"}' \
  ".hookSpecificOutput.additionalContext" \
  "coerced"

# ---------------------------------------------------------------------------
# Whitespace separator regressions
# ---------------------------------------------------------------------------

echo ""
echo "-- Whitespace separator regressions --"

# Tab separator between command and tail
run_test_json \
  "23. Tab separator: /lean4:draft<TAB>\"x\"" \
  "{\"prompt\":\"/lean4:draft\t\\\"x\\\"\",\"cwd\":\"/tmp\"}" \
  ".hookSpecificOutput.hookEventName" \
  "UserPromptSubmit"

# Newline separator between command and tail
run_test_json \
  "24. Newline separator: /lean4:draft<NL>\"x\"" \
  "{\"prompt\":\"/lean4:draft\n\\\"x\\\"\",\"cwd\":\"/tmp\"}" \
  ".hookSpecificOutput.hookEventName" \
  "UserPromptSubmit"

# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------

echo ""
echo "=== Results: $PASS passed, $FAIL failed ==="
[[ "$FAIL" -eq 0 ]]

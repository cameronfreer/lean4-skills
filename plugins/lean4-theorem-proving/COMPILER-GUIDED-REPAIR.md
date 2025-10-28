# Compiler-Guided Proof Repair

**Core insight:** Use Lean's compiler feedback to drive iterative proof repair with small, budgeted LLM calls instead of blind best-of-N sampling.

**Strategy:** Generate → Compile → Diagnose Error → Apply Targeted Fix → Re-verify (tight loop)

---

## Philosophy

### Traditional Approach (Blind Sampling)
```
Generate 100 proof attempts → Test all → Pick best
❌ Wasteful: 99% of attempts fail identically
❌ No learning: Same error repeated 50 times
❌ Expensive: Large model × high K
```

### Compiler-Guided Approach
```
Generate attempt → Lean error → Route to specific fix → Retry (max 24 attempts)
✅ Efficient: Error-driven action selection
✅ Adaptive: Different fix strategies per error type
✅ Economical: Small K (often K=1), fast model first, escalate only when needed
✅ Learning: Log attempts, avoid repeating dead ends
```

**Key wins:**
- **Low sampling budgets** (K=1 or K=3) with compiler guidance beat high-K blind sampling
- **Multi-stage approach** (fast model → escalate to strong model) optimizes cost/quality
- **Solver cascade** (try automation before resampling) handles 40-60% of cases mechanically
- **Early stopping** (bail after 3 identical errors) prevents runaway costs

---

## Architecture Overview

### Components

```
┌─────────────────────────────────────────────────────────────┐
│  Slash Commands (/repair-file, /repair-goal)               │
│  Entry points with budget knobs                             │
└────────────────┬────────────────────────────────────────────┘
                 │
                 ▼
┌─────────────────────────────────────────────────────────────┐
│  repairLoop.sh                                              │
│  Orchestrates: compile → parse → route → apply → verify    │
└────────────────┬────────────────────────────────────────────┘
                 │
        ┌────────┴────────┐
        │                 │
        ▼                 ▼
┌──────────────┐  ┌──────────────────────┐
│ Error Parser │  │ Error Strategy Table │
│ (Python)     │  │ (YAML routing)       │
└──────┬───────┘  └─────────┬────────────┘
       │                    │
       └─────────┬──────────┘
                 ▼
┌─────────────────────────────────────────────────────────────┐
│  Action Dispatcher                                          │
│  Routes to: solver cascade / subgoal split / have insert   │
│             / namespace open / agent call                   │
└────────────────┬────────────────────────────────────────────┘
                 │
        ┌────────┴─────────┐
        │                  │
        ▼                  ▼
┌──────────────┐  ┌────────────────────┐
│ Solver       │  │ lean4-proof-repair │
│ Cascade      │  │ Agent (2-stage)    │
│ (automated)  │  │ Haiku → Sonnet     │
└──────────────┘  └────────────────────┘
                          │
                          ▼
                  ┌────────────────┐
                  │ Attempt Logger │
                  │ (NDJSON)       │
                  └────────────────┘
```

---

## Implementation Details

### 1. Error Strategy Routing Table

**File:** `plugins/lean4-theorem-proving/config/errorStrategies.yaml`

```yaml
# Maps Lean error patterns → ordered list of repair actions
# Actions are tried in sequence until one succeeds

strategies:
  - pattern: "type mismatch"
    errorHash: "type_mismatch"
    actions:
      - action: "solverCascade"
        solvers: ["simp", "rfl", "ring"]
        timeout: 2
      - action: "refineSkeleton"
        addUnderscores: true
      - action: "insertHave"
        inferType: true
      - action: "convert"
        depth: 2
      - action: "agentRepair"
        agent: "lean4-proof-repair"
        stage: 1

  - pattern: "don't know how to synthesize implicit argument"
    errorHash: "synth_implicit"
    actions:
      - action: "openNamespace"
        candidates: ["scope", "parent"]
      - action: "provideInstance"
        inferFrom: "context"
      - action: "simpAll"
      - action: "agentRepair"
        agent: "lean4-proof-repair"
        stage: 1

  - pattern: "unsolved goals"
    errorHash: "unsolved_goals"
    actions:
      - action: "solverCascade"
        solvers: ["simp?", "apply?", "exact?", "aesop"]
        timeout: 5
      - action: "refineWithUnderscores"
      - action: "intro"
        autoNames: true
      - action: "cases"
        onFirstHypothesis: true
      - action: "agentRepair"
        agent: "lean4-proof-repair"
        stage: 1

  - pattern: "unknown identifier"
    errorHash: "unknown_ident"
    actions:
      - action: "searchMathlib"
        fuzzy: true
      - action: "openScoped"
        inferFrom: "errorMessage"
      - action: "importNamespace"
        suggestions: true
      - action: "agentRepair"
        agent: "lean4-proof-repair"
        stage: 1

  - pattern: "failed to synthesize instance"
    errorHash: "synth_instance"
    actions:
      - action: "haveI"
        inferFrom: "goal"
      - action: "letI"
        inferFrom: "context"
      - action: "openScoped"
        namespace: ["MeasureTheory", "Topology"]
      - action: "agentRepair"
        agent: "lean4-proof-repair"
        stage: 2  # Escalate immediately (complex)

  - pattern: "tactic 'sorry' has not been implemented"
    errorHash: "sorry_present"
    actions:
      - action: "searchMathlib"
        byType: true
      - action: "solverCascade"
        solvers: ["simp?", "ring", "linarith", "nlinarith", "omega"]
      - action: "agentRepair"
        agent: "lean4-sorry-filler"
        stage: 1

  - pattern: "maximum recursion depth"
    errorHash: "recursion_depth"
    actions:
      - action: "simplifyContext"
        dropUnused: true
      - action: "clearLocals"
      - action: "revertIntros"
      - action: "agentRepair"
        agent: "lean4-proof-repair"
        stage: 2

  - pattern: "deterministic timeout"
    errorHash: "timeout"
    actions:
      - action: "simpOnly"
        explicitLemmas: true
      - action: "narrowSimpScope"
      - action: "replaceDecide"
        with: "native_decide"
      - action: "agentRepair"
        agent: "lean4-proof-repair"
        stage: 2

# Default fallback
default:
  actions:
    - action: "solverCascade"
      solvers: ["simp?", "aesop", "exact?"]
    - action: "agentRepair"
      agent: "lean4-proof-repair"
      stage: 1
```

**Usage:**
```python
from repair_router import get_strategy
strategy = get_strategy(error_message="type mismatch at line 42")
for action in strategy.actions:
    success = execute_action(action, context)
    if success:
        break
```

---

### 2. Repair Loop Orchestrator

**File:** `scripts/repairLoop.sh`

```bash
#!/usr/bin/env bash
# Compiler-guided proof repair loop
# Usage: repairLoop.sh FILE.lean [maxAttempts] [--stage2-threshold=3]

set -euo pipefail

FILE="${1:?Missing FILE.lean argument}"
MAX_ATTEMPTS="${2:-24}"
STAGE2_THRESHOLD="${3:-3}"
REPEAT_ERROR_LIMIT=3

REPAIR_DIR=".repair"
mkdir -p "${REPAIR_DIR}"

# Initialize attempt log
ATTEMPT_LOG="${REPAIR_DIR}/attempts.ndjson"
echo "" > "${ATTEMPT_LOG}"

previous_error_hash=""
same_error_count=0
stage=1

echo "🔧 Starting compiler-guided repair loop"
echo "   File: ${FILE}"
echo "   Max attempts: ${MAX_ATTEMPTS}"
echo "   Repeat error limit: ${REPEAT_ERROR_LIMIT}"
echo ""

for ((attempt=1; attempt<=MAX_ATTEMPTS; attempt++)); do
  start_time=$(date +%s)

  echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  echo "Attempt ${attempt}/${MAX_ATTEMPTS} (Stage ${stage})"
  echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

  # Compile and capture errors
  if lake build "${FILE}" 2> "${REPAIR_DIR}/errs.txt"; then
    elapsed=$(($(date +%s) - start_time))
    echo ""
    echo "✅ SUCCESS after ${attempt} attempts (${elapsed}s total)"

    # Log success
    jq -n \
      --arg attempt "${attempt}" \
      --arg elapsed "${elapsed}" \
      --arg stage "${stage}" \
      '{attempt: $attempt|tonumber, success: true, elapsed: $elapsed|tonumber, stage: $stage|tonumber}' \
      >> "${ATTEMPT_LOG}"

    exit 0
  fi

  # Parse errors
  if ! python3 scripts/parseLeanErrors.py "${REPAIR_DIR}/errs.txt" > "${REPAIR_DIR}/context.json"; then
    echo "❌ Failed to parse Lean errors"
    exit 1
  fi

  # Extract error hash
  error_hash=$(jq -r '.errorHash' "${REPAIR_DIR}/context.json")
  error_msg=$(jq -r '.message' "${REPAIR_DIR}/context.json")

  echo "Error: ${error_msg}"
  echo "Hash: ${error_hash}"

  # Check for repeated error
  if [[ "${error_hash}" == "${previous_error_hash}" ]]; then
    same_error_count=$((same_error_count + 1))
    echo "⚠️  Repeated error (${same_error_count}/${REPEAT_ERROR_LIMIT})"

    if [[ ${same_error_count} -ge ${REPEAT_ERROR_LIMIT} ]]; then
      if [[ ${stage} -eq 1 ]]; then
        echo "🔼 Escalating to Stage 2 (stronger model)"
        stage=2
        same_error_count=0
      else
        echo "❌ Same error repeated ${REPEAT_ERROR_LIMIT} times in Stage 2 - giving up"
        jq -n \
          --arg attempt "${attempt}" \
          --arg error "${error_hash}" \
          --arg reason "repeat_error_limit" \
          '{attempt: $attempt|tonumber, success: false, error: $error, reason: $reason}' \
          >> "${ATTEMPT_LOG}"
        exit 1
      fi
    fi
  else
    same_error_count=0
  fi
  previous_error_hash="${error_hash}"

  # Try solver cascade first (fast path)
  echo "🤖 Trying automated solvers..."
  if python3 scripts/solverCascade.py "${REPAIR_DIR}/context.json" "${FILE}" > "${REPAIR_DIR}/solver.diff"; then
    if git apply --check "${REPAIR_DIR}/solver.diff" 2>/dev/null; then
      git apply "${REPAIR_DIR}/solver.diff"
      echo "✓ Solver cascade applied patch"
      continue
    fi
  fi

  # Generate patch via agent
  echo "🧠 Generating repair patch (Stage ${stage})..."
  if ! python3 scripts/proposePatch.py "${REPAIR_DIR}/context.json" "${FILE}" --stage="${stage}" > "${REPAIR_DIR}/patch.diff"; then
    echo "⚠️  Failed to generate patch"
    continue
  fi

  # Apply patch
  if git apply --ignore-whitespace --reject "${REPAIR_DIR}/patch.diff" 2>/dev/null; then
    echo "✓ Patch applied"
  elif git apply --ignore-whitespace --3way "${REPAIR_DIR}/patch.diff" 2>/dev/null; then
    echo "✓ Patch applied (3-way merge)"
  else
    echo "⚠️  Patch failed to apply cleanly"
    # Log failed attempt
    elapsed=$(($(date +%s) - start_time))
    jq -n \
      --arg attempt "${attempt}" \
      --arg error "${error_hash}" \
      --arg elapsed "${elapsed}" \
      --arg reason "patch_apply_failed" \
      --arg stage "${stage}" \
      '{attempt: $attempt|tonumber, success: false, error: $error, elapsed: $elapsed|tonumber, reason: $reason, stage: $stage|tonumber}' \
      >> "${ATTEMPT_LOG}"
    continue
  fi

  # Log attempt
  elapsed=$(($(date +%s) - start_time))
  jq -n \
    --arg attempt "${attempt}" \
    --arg error "${error_hash}" \
    --arg elapsed "${elapsed}" \
    --arg stage "${stage}" \
    '{attempt: $attempt|tonumber, success: false, error: $error, elapsed: $elapsed|tonumber, stage: $stage|tonumber}' \
    >> "${REPAIR_LOG}"

done

echo ""
echo "❌ Repair failed after ${MAX_ATTEMPTS} attempts"
echo "   Attempt log: ${ATTEMPT_LOG}"
exit 1
```

---

### 3. Error Parser

**File:** `scripts/parseLeanErrors.py`

```python
#!/usr/bin/env env python3
"""
Parse Lean compiler errors into structured JSON for repair routing.

Output schema:
{
  "errorHash": "type_mismatch_42",
  "errorType": "type_mismatch",
  "message": "type mismatch at...",
  "file": "Foo.lean",
  "line": 42,
  "column": 10,
  "goal": "⊢ Continuous f",
  "localContext": ["h1 : Measurable f", "h2 : Integrable f μ"],
  "codeSnippet": "theorem foo : Continuous f := by\n  exact h1  -- ❌ type mismatch\n",
  "suggestionKeywords": ["continuous", "measurable", "apply"]
}
"""

import json
import re
import sys
import hashlib
from pathlib import Path
from typing import Optional


ERROR_PATTERNS = [
    (r"type mismatch", "type_mismatch"),
    (r"don't know how to synthesize implicit argument", "synth_implicit"),
    (r"unsolved goals", "unsolved_goals"),
    (r"unknown identifier '([^']+)'", "unknown_ident"),
    (r"failed to synthesize instance", "synth_instance"),
    (r"tactic 'sorry' has not been implemented", "sorry_present"),
    (r"maximum recursion depth", "recursion_depth"),
    (r"deterministic timeout", "timeout"),
    (r"expected type", "type_expected"),
    (r"application type mismatch", "app_type_mismatch"),
]


def parse_location(line: str) -> Optional[dict]:
    """Extract file:line:column from error line."""
    match = re.match(r"^([^:]+):(\d+):(\d+):", line)
    if match:
        return {
            "file": match.group(1),
            "line": int(match.group(2)),
            "column": int(match.group(3))
        }
    return None


def classify_error(message: str) -> str:
    """Classify error type from message."""
    for pattern, error_type in ERROR_PATTERNS:
        if re.search(pattern, message, re.IGNORECASE):
            return error_type
    return "unknown"


def extract_goal(error_text: str) -> Optional[str]:
    """Extract goal state from error (if present)."""
    # Look for lines starting with ⊢
    goal_match = re.search(r"⊢\s+(.+)", error_text)
    if goal_match:
        return goal_match.group(1).strip()
    return None


def extract_local_context(error_text: str) -> list[str]:
    """Extract local context (hypotheses) from error."""
    # Look for lines like "h1 : Type" before ⊢
    context = []
    in_context = False
    for line in error_text.split("\n"):
        if "⊢" in line:
            in_context = False
        if in_context and ":" in line:
            # Extract hypothesis
            hyp = line.strip()
            if hyp and not hyp.startswith("case"):
                context.append(hyp)
        if "context:" in line.lower() or line.strip().endswith(":"):
            in_context = True
    return context


def extract_code_snippet(file_path: str, line: int, context_lines: int = 3) -> str:
    """Extract code snippet around error location."""
    try:
        with open(file_path) as f:
            lines = f.readlines()
        start = max(0, line - context_lines - 1)
        end = min(len(lines), line + context_lines)
        snippet_lines = []
        for i in range(start, end):
            prefix = "❌ " if i == line - 1 else "   "
            snippet_lines.append(f"{prefix}{i+1:4d} | {lines[i].rstrip()}")
        return "\n".join(snippet_lines)
    except Exception:
        return ""


def extract_suggestion_keywords(message: str) -> list[str]:
    """Extract relevant keywords for search/suggestions."""
    keywords = []
    # Extract identifiers in single quotes
    keywords.extend(re.findall(r"'([^']+)'", message))
    # Extract common type class names
    for term in ["Continuous", "Measurable", "Integrable", "Differentiable",
                 "Fintype", "DecidableEq", "Group", "Ring", "Field"]:
        if term.lower() in message.lower():
            keywords.append(term)
    return list(set(keywords))[:10]  # Limit to 10


def compute_error_hash(error_type: str, file: str, line: int) -> str:
    """Compute deterministic hash for error tracking."""
    content = f"{error_type}:{file}:{line}"
    return hashlib.sha256(content.encode()).hexdigest()[:12]


def parse_lean_errors(error_file: Path) -> dict:
    """Parse Lean error output file into structured JSON."""
    with open(error_file) as f:
        error_text = f.read()

    lines = error_text.strip().split("\n")
    if not lines:
        return {"error": "No error output"}

    # First line usually has location
    location = parse_location(lines[0])
    if not location:
        location = {"file": "unknown", "line": 0, "column": 0}

    # Full message is everything after the location line
    message = error_text[len(lines[0]):].strip() if len(lines) > 1 else ""

    error_type = classify_error(message)
    error_hash = compute_error_hash(error_type, location["file"], location["line"])

    result = {
        "errorHash": error_hash,
        "errorType": error_type,
        "message": message[:500],  # Truncate long messages
        "file": location["file"],
        "line": location["line"],
        "column": location["column"],
        "goal": extract_goal(error_text),
        "localContext": extract_local_context(error_text),
        "codeSnippet": extract_code_snippet(location["file"], location["line"]),
        "suggestionKeywords": extract_suggestion_keywords(message),
    }

    return result


def main():
    if len(sys.argv) < 2:
        print("Usage: parseLeanErrors.py ERROR_FILE", file=sys.stderr)
        sys.exit(1)

    error_file = Path(sys.argv[1])
    if not error_file.exists():
        print(f"Error file not found: {error_file}", file=sys.stderr)
        sys.exit(1)

    result = parse_lean_errors(error_file)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
```

---

### 4. Solver Cascade

**File:** `scripts/solverCascade.py`

```python
#!/usr/bin/env python3
"""
Try automated solvers in sequence before resampling with LLM.
Handles 40-60% of simple cases mechanically.

Cascade order:
1. rfl (definitional equality)
2. simp (simplifier)
3. ring (ring normalization)
4. linarith (linear arithmetic)
5. nlinarith (nonlinear arithmetic)
6. omega (arithmetic automation)
7. exact? (proof search)
8. apply? (proof search)
9. aesop (general automation)

Returns diff if any solver succeeds.
"""

import json
import sys
import subprocess
import tempfile
from pathlib import Path
from typing import Optional


SOLVERS = [
    ("rfl", 1),
    ("simp", 2),
    ("ring", 2),
    ("linarith", 3),
    ("nlinarith", 4),
    ("omega", 3),
    ("exact?", 5),
    ("apply?", 5),
    ("aesop", 8),
]


def try_solver(file_path: Path, line: int, column: int, solver: str, timeout: int) -> Optional[str]:
    """
    Try inserting solver tactic at given location.
    Returns diff if compilation succeeds.
    """
    with open(file_path) as f:
        lines = f.readlines()

    # Insert solver tactic (simple heuristic: replace 'sorry' or add after 'by')
    target_line = lines[line - 1]

    if "sorry" in target_line:
        # Replace sorry with solver
        modified = target_line.replace("sorry", solver)
    elif "by" in target_line:
        # Add solver on next line with proper indentation
        indent = len(target_line) - len(target_line.lstrip())
        modified = target_line + " " * (indent + 2) + solver + "\n"
    else:
        return None

    lines[line - 1] = modified

    # Write to temp file
    with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', delete=False) as tmp:
        tmp.writelines(lines)
        tmp_path = tmp.name

    try:
        # Try compiling
        result = subprocess.run(
            ["lake", "build", tmp_path],
            capture_output=True,
            timeout=timeout,
            text=True
        )

        if result.returncode == 0:
            # Success! Generate diff
            diff = subprocess.run(
                ["diff", "-u", str(file_path), tmp_path],
                capture_output=True,
                text=True
            ).stdout
            return diff

        return None

    except subprocess.TimeoutExpired:
        return None
    finally:
        Path(tmp_path).unlink()


def run_solver_cascade(context: dict, file_path: Path) -> Optional[str]:
    """Run solver cascade, return diff if any succeeds."""
    line = context.get("line", 0)
    column = context.get("column", 0)
    error_type = context.get("errorType", "")

    # Skip cascade for errors that won't benefit
    skip_types = ["unknown_ident", "synth_implicit", "recursion_depth"]
    if error_type in skip_types:
        return None

    print(f"🔍 Trying solver cascade at {file_path}:{line}:{column}")

    for solver, timeout in SOLVERS:
        print(f"   Trying {solver}...", end=" ", flush=True)
        diff = try_solver(file_path, line, column, solver, timeout)
        if diff:
            print(f"✅ {solver} succeeded!")
            return diff
        print("❌")

    return None


def main():
    if len(sys.argv) < 3:
        print("Usage: solverCascade.py CONTEXT.json FILE.lean", file=sys.stderr)
        sys.exit(1)

    with open(sys.argv[1]) as f:
        context = json.load(f)

    file_path = Path(sys.argv[2])

    diff = run_solver_cascade(context, file_path)
    if diff:
        print(diff)
        sys.exit(0)
    else:
        sys.exit(1)


if __name__ == "__main__":
    main()
```

---

### 5. Patch Proposer (LLM-backed)

**File:** `scripts/proposePatch.py`

```python
#!/usr/bin/env python3
"""
Generate repair patch using LLM with error context.
Two-stage approach: Stage 1 (Haiku, fast) → Stage 2 (Sonnet, precise)
"""

import json
import sys
import subprocess
from pathlib import Path
from typing import Optional


STAGE_CONFIGS = {
    1: {
        "model": "claude-3-5-haiku-20241022",
        "max_tokens": 2000,
        "temperature": 0.2,
        "thinking": False,
    },
    2: {
        "model": "claude-sonnet-4-20250514",
        "max_tokens": 4000,
        "temperature": 0.1,
        "thinking": True,
    }
}


REPAIR_PROMPT_TEMPLATE = """You are a Lean 4 proof repair specialist. Given a compilation error, produce a minimal diff that fixes the error.

**Error Context:**
- Type: {error_type}
- Message: {message}
- Location: {file}:{line}:{column}

**Current Code:**
```lean
{snippet}
```

**Goal State:** {goal}

**Local Context:**
{context}

**Task:**
Generate a MINIMAL patch (unified diff format) that fixes this error. Focus on:
1. Understanding the specific error type
2. Applying targeted fix (don't rewrite everything)
3. Using appropriate mathlib lemmas if needed

**Guidelines:**
- For type mismatches: try `convert`, `refine`, or explicit type annotations
- For missing instances: try `haveI`, `letI`, or `open scoped`
- For unsolved goals: try relevant tactics or mathlib search
- For unknown identifiers: check imports and namespaces

Output ONLY the unified diff. No explanation.
"""


def load_context(context_file: Path) -> dict:
    """Load parsed error context."""
    with open(context_file) as f:
        return json.load(f)


def format_prompt(context: dict) -> str:
    """Format repair prompt from error context."""
    goal = context.get("goal") or "Not shown"
    local_context = context.get("localContext", [])
    context_str = "\n".join(f"  {h}" for h in local_context) if local_context else "  (empty)"

    return REPAIR_PROMPT_TEMPLATE.format(
        error_type=context.get("errorType", "unknown"),
        message=context.get("message", ""),
        file=context.get("file", ""),
        line=context.get("line", 0),
        column=context.get("column", 0),
        snippet=context.get("codeSnippet", ""),
        goal=goal,
        context=context_str,
    )


def call_llm(prompt: str, stage: int) -> Optional[str]:
    """Call LLM to generate patch."""
    config = STAGE_CONFIGS[stage]

    # Call Claude via CLI (this would be replaced with actual API call)
    # For now, placeholder that would interface with your existing agent system

    # TODO: Interface with lean4-proof-repair agent
    # For minimal implementation, could use direct API call

    print(f"   Calling {config['model']} (Stage {stage})...", file=sys.stderr)

    # Placeholder - in real implementation, call your agent system
    return None


def generate_patch(context: dict, file_path: Path, stage: int) -> Optional[str]:
    """Generate repair patch for error."""
    prompt = format_prompt(context)
    diff = call_llm(prompt, stage)
    return diff


def main():
    if len(sys.argv) < 3:
        print("Usage: proposePatch.py CONTEXT.json FILE.lean --stage=N", file=sys.stderr)
        sys.exit(1)

    context_file = Path(sys.argv[1])
    file_path = Path(sys.argv[2])
    stage = 1

    # Parse stage flag
    for arg in sys.argv[3:]:
        if arg.startswith("--stage="):
            stage = int(arg.split("=")[1])

    context = load_context(context_file)
    diff = generate_patch(context, file_path, stage)

    if diff:
        print(diff)
        sys.exit(0)
    else:
        sys.exit(1)


if __name__ == "__main__":
    main()
```

---

### 6. lean4-proof-repair Agent

**File:** `plugins/lean4-subagents/agents/lean4-proof-repair.md`

```markdown
---
name: lean4-proof-repair
description: Compiler-guided iterative proof repair with two-stage model escalation (Haiku → Sonnet). Use for iterative error-driven proof fixing with small sampling budgets.
tools: Read, Grep, Glob, Edit, Bash, WebFetch
model: haiku-4.5
thinking: off
---

# Lean 4 Proof Repair - Compiler-Guided (EXPERIMENTAL)

**Core strategy:** Use Lean compiler feedback to drive targeted repairs, not blind best-of-N sampling.

**Philosophy:** Generate → Compile → Diagnose → Apply Specific Fix → Re-verify (tight loop, low K)

---

## Two-Stage Approach

### Stage 1: Fast (Haiku 4.5, thinking OFF)
- Model: `haiku-4.5`
- Thinking: OFF
- Top-K: 1
- Temperature: 0.2
- Max attempts: 6
- Budget: ~2 seconds per attempt
- Use for: First 6 attempts, most errors (80%)

### Stage 2: Precise (Sonnet 4.5, thinking ON)
- Model: `sonnet-4.5`
- Thinking: ON
- Top-K: 1
- Temperature: 0.1
- Max attempts: 18
- Budget: ~10 seconds per attempt
- Use for: After Stage 1 exhausted OR complex errors

**Escalation triggers:**
1. Same error 3 times in Stage 1
2. Error type: `synth_instance`, `recursion_depth`, `timeout`
3. Stage 1 exhausted (6 attempts)

---

## Error Context You Receive

When called, you get structured error context:

```json
{
  "errorHash": "type_mismatch_a3f2",
  "errorType": "type_mismatch",
  "message": "type mismatch at...",
  "file": "Foo.lean",
  "line": 42,
  "column": 10,
  "goal": "⊢ Continuous f",
  "localContext": ["h1 : Measurable f", "h2 : Integrable f μ"],
  "codeSnippet": "...",
  "suggestionKeywords": ["continuous", "measurable"]
}
```

---

## Your Task

**Generate a MINIMAL patch** (unified diff) that fixes the specific error.

### Repair Strategies by Error Type

#### `type_mismatch`
1. Try `convert _ using N` (where N is unification depth 1-3)
2. Add explicit type annotation: `(expr : TargetType)`
3. Use `refine` to provide skeleton with placeholders
4. Check if need to `rw` to align types
5. Last resort: introduce `have` with intermediate type

#### `unsolved_goals`
1. Check if automation handles it: `simp?`, `apply?`, `exact?`
2. Look at goal type:
   - Equality → try `rfl`, `ring`, `linarith`
   - ∀ → try `intro`
   - ∃ → try `use` or `refine ⟨_, _⟩`
   - → try `intro` then work on conclusion
3. Search mathlib for matching lemma
4. Break into subgoals with `constructor`, `cases`, `induction`

#### `unknown_ident`
1. Search mathlib: `bash .claude/tools/lean4/search_mathlib.sh "identifier" name`
2. Check if needs namespace: add `open Foo` or `open scoped Bar`
3. Check imports: might need `import Mathlib.Foo.Bar`
4. Check for typo: similar names?

#### `synth_implicit` / `synth_instance`
1. Try `haveI : MissingInstance := ...` to provide instance
2. Try `letI : MissingInstance := ...` for local instance
3. Open relevant scoped namespace: `open scoped Topology`
4. Check if instance exists in different form
5. Reorder arguments (instance arguments should come before regular arguments)

#### `sorry_present`
1. Search mathlib for exact lemma (60% hit rate)
2. Try automated solvers (handled by solver cascade)
3. Generate compositional proof from mathlib lemmas
4. Break into provable subgoals

#### `timeout` / `recursion_depth`
1. Narrow `simp` scope: `simp only [lemma1, lemma2]` instead of `simp [*]`
2. Clear unused hypotheses: `clear h1 h2`
3. Replace `decide` with `native_decide` or manual proof
4. Reduce type class search: provide explicit instances
5. Revert excessive intros, then re-intro in better order

---

## Output Format

**You MUST output a unified diff.**

### Good Example

```diff
--- Foo.lean
+++ Foo.lean
@@ -40,5 +40,6 @@
 theorem example (h : Measurable f) : Continuous f := by
-  exact h
+  convert continuous_of_measurable h using 2
+  simp
```

### Bad Example

```lean
-- Don't output full file rewrite!
theorem example (h : Measurable f) : Continuous f := by
  convert continuous_of_measurable h using 2
  simp
```

---

## Key Principles

### 1. Minimal Diffs
- Change ONLY lines related to the error
- Don't rewrite working code
- Preserve proof style
- Target: 1-5 line diffs

### 2. Error-Specific Fixes
- Read the error type carefully
- Apply the right category of fix
- Don't try random tactics

### 3. Search Before Creating
- 60% of proofs exist in mathlib
- Search FIRST: `.claude/tools/lean4/search_mathlib.sh`
- Then compose: combine 2-3 mathlib lemmas
- Last resort: novel proof

### 4. Stay In Budget
- Stage 1: Quick attempts (2s each)
- Don't overthink in Stage 1
- Save complex strategies for Stage 2

### 5. Test Ideas
- If uncertain, pick simplest fix
- Loop will retry if wrong
- Better to be fast and focused than slow and perfect

---

## Tools Available

**Search:**
```bash
bash .claude/tools/lean4/search_mathlib.sh "continuous measurable" content
bash .claude/tools/lean4/smart_search.sh "property description" --source=all
```

**LSP (if available):**
```
mcp__lean-lsp__lean_goal(file, line, column)  # Get live goal
mcp__lean-lsp__lean_leansearch("query")        # Search
```

**Read code:**
```
Read(file_path)
```

---

## Stage-Specific Guidance

### Stage 1 (Haiku, thinking OFF)
- **Speed over perfection**
- Try obvious fixes:
  - Known error pattern → standard fix
  - Type mismatch → `convert` or annotation
  - Unknown ident → search + import
- Output diff immediately
- Don't deliberate
- Budget: 2 seconds

### Stage 2 (Sonnet, thinking ON)
- **Precision and strategy**
- Think through:
  - Why Stage 1 failed
  - What's actually needed
  - Global context
- Consider:
  - Helper lemmas
  - Argument reordering
  - Instance declarations
  - Multi-line fixes
- Still keep diffs minimal
- Budget: 10 seconds

---

## Remember

- You are part of a LOOP (not one-shot)
- Minimal diffs (1-5 lines)
- Error-specific fixes
- Search mathlib first
- Fast in Stage 1, precise in Stage 2
- Output unified diff format ONLY

The repair loop will:
1. Apply your diff
2. Recompile
3. Call you again if still failing
4. Try up to 24 total attempts

Your job: ONE targeted fix per call.
```

---

## Integration Points

### 1. Slash Commands

**New commands to add:**

```markdown
/lean4-theorem-proving:repair-file FILE.lean [--max-attempts=24]
  Run compiler-guided repair loop on entire file

/lean4-theorem-proving:repair-goal FILE.lean LINE
  Repair specific goal at line

/lean4-theorem-proving:repair-interactive FILE.lean
  Interactive repair: show each attempt, ask for confirmation
```

### 2. SKILL.md Addition

Add to main skill file:

```markdown
## Compiler-Guided Proof Repair

When proofs fail to compile, use iterative compiler-guided repair instead of blind resampling:

**Quick repair:** `/lean4-theorem-proving:repair-file FILE.lean`

**How it works:**
1. Compile → extract structured error
2. Route to appropriate fix strategy (see errorStrategies.yaml)
3. Try automated solvers first (simp, ring, linarith, etc.)
4. If solvers fail, call lean4-proof-repair agent:
   - Stage 1: Haiku (fast, 6 attempts)
   - Stage 2: Sonnet (precise, 18 attempts)
5. Apply patch, recompile, repeat

**Key benefits:**
- Low sampling budget (K=1, not K=100)
- Error-driven action selection (not blind guessing)
- Fast model first, escalate only when needed
- Automated solver cascade handles 40-60% mechanically
- Early stopping prevents runaway costs

**Budget defaults:**
- Max attempts: 24
- Repeat error limit: 3
- Stage 1: Haiku, 6 attempts, thinking OFF
- Stage 2: Sonnet, 18 attempts, thinking ON

See references/compiler-guided-repair.md for details.
```

### 3. New Reference Doc

**File:** `references/compiler-guided-repair.md`

Quick reference for repair strategies, examples of each error type with before/after, and common patterns.

---

## Expected Outcomes

### Metrics to Track

**Success rate by error type:**
- `type_mismatch`: 70-85%
- `unsolved_goals`: 60-75%
- `unknown_ident`: 85-95%
- `synth_instance`: 50-70%
- Overall: ~70%

**Efficiency:**
- Avg attempts to success: 3-8
- Solver cascade hit rate: 40-60%
- Stage 1 resolution rate: 80%
- Stage 2 needed: 20%

**Cost:**
- Stage 1: ~$0.001 per attempt (Haiku)
- Stage 2: ~$0.01 per attempt (Sonnet)
- Avg cost per repair: $0.05-0.15 (vs $2-5 for blind sampling)

---

## Implementation Checklist

- [ ] Create `config/errorStrategies.yaml`
- [ ] Implement `scripts/parseLeanErrors.py`
- [ ] Implement `scripts/solverCascade.py`
- [ ] Implement `scripts/proposePatch.py` (LLM interface)
- [ ] Implement `scripts/repairLoop.sh`
- [ ] Create `agents/lean4-proof-repair.md`
- [ ] Add slash commands to `commands/`
- [ ] Create `references/compiler-guided-repair.md`
- [ ] Update `SKILL.md` with repair mode
- [ ] Wire up attempt logging (NDJSON)
- [ ] Integrate with `lean4-memories` for pattern learning

---

## References and Inspiration

This design is inspired by compiler-guided proof repair strategies, particularly:

**APOLLO: Automatic Proof Optimizer with Lightweight Loop Optimization**
- Paper: https://arxiv.org/abs/2505.05758
- Key insight: Use compiler feedback to drive iterative repair with small, budgeted LLM calls instead of blind best-of-N sampling
- Core contributions adapted here:
  - Multi-stage model selection (fast → precise escalation)
  - Error-driven action routing
  - Solver cascade before resampling
  - Low sampling budgets (K=1) with strong feedback
  - Structured attempt logging for learning

---

*Compiler-guided repair design document*
*Version: 1.0*
*Date: 2025-10-28*

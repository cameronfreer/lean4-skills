#!/usr/bin/env python3
"""
Generate repair patch using LLM with error context.
Two-stage approach: Stage 1 (Haiku, fast) → Stage 2 (Sonnet, precise)

Inspired by APOLLO's multi-stage repair strategy
https://arxiv.org/abs/2505.05758

NOTE: This script is currently a stub that documents the interface.

In practice, the repair workflow is orchestrated by the slash commands
(/repair-file, /repair-goal, /repair-interactive), which:
1. Parse errors using parseLeanErrors.py
2. Try solverCascade.py first
3. If cascade fails, call lean4-proof-repair agent via Task tool
4. Apply returned diff

This standalone script would be used for:
- Command-line repair automation (future)
- Testing the agent interface
- Direct API integration (future)

For now, use the slash commands for actual repair work.
"""

import json
import sys
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
    """
    Call LLM to generate patch.

    TODO: This needs to interface with the lean4-proof-repair agent.

    Options for implementation:
    1. Call agent via Task tool API
    2. Direct Claude API call
    3. Use mcp__lean-lsp__* tools if available
    4. Shell out to claude-code CLI

    For now, this is a stub that returns None.
    """
    config = STAGE_CONFIGS[stage]

    print(f"   Would call {config['model']} (Stage {stage})...", file=sys.stderr)
    print(f"   TODO: Implement agent integration", file=sys.stderr)

    # TODO: Implement actual LLM call
    # This would dispatch to the lean4-proof-repair agent
    # The agent would:
    # 1. Read the error context
    # 2. Apply stage-specific repair strategies
    # 3. Generate a minimal unified diff
    # 4. Return the diff

    return None


def generate_patch(context: dict, file_path: Path, stage: int) -> Optional[str]:
    """Generate repair patch for error."""
    prompt = format_prompt(context)

    print(f"\n📝 Repair Prompt (Stage {stage}):", file=sys.stderr)
    print("=" * 60, file=sys.stderr)
    print(prompt[:500] + "..." if len(prompt) > 500 else prompt, file=sys.stderr)
    print("=" * 60, file=sys.stderr)

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

    if not context_file.exists():
        print(f"Error: Context file not found: {context_file}", file=sys.stderr)
        sys.exit(1)

    context = load_context(context_file)
    diff = generate_patch(context, file_path, stage)

    if diff:
        print(diff)
        sys.exit(0)
    else:
        print("\n⚠️  proposePatch.py is currently a stub", file=sys.stderr)
        print("   Agent integration needed for actual patch generation", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()

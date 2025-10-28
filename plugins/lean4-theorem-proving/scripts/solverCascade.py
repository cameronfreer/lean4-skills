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

Inspired by APOLLO's solver-first strategy
https://arxiv.org/abs/2505.05758
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

#!/usr/bin/env python3
"""
Try `exact?` at various points in Lean 4 proofs to find one-liner replacements.

For each candidate proof block, replaces the tactic body with `exact?`,
runs Lean on a temporary copy, and captures any suggestion from diagnostics.

Usage:
    python3 try_exact_at_step.py File.lean:42          # test one proof
    python3 try_exact_at_step.py --batch File.lean      # test all candidates in file
    python3 try_exact_at_step.py --batch src/ -r        # recursive batch
    python3 try_exact_at_step.py --dry-run File.lean:42 # show what would be tested

The script never modifies the original file — it works on a temporary copy.
"""

import re
import sys
import subprocess
import shutil
import tempfile
from pathlib import Path
from typing import Optional, Tuple, List


def find_project_root(start: Path) -> Path:
    """Walk up from start to find the Lean project root (contains lakefile.lean or lean-toolchain)."""
    current = start.resolve()
    if current.is_file():
        current = current.parent
    while current != current.parent:
        if (current / 'lakefile.lean').exists() or (current / 'lean-toolchain').exists():
            return current
        current = current.parent
    # Fallback: return the file's parent
    return start.resolve().parent


def find_proof_bounds(lines: List[str], target_line: int) -> Tuple[int, int, int]:
    """Find the start (by line), end, and base indent of the proof containing target_line.

    Returns (by_line_idx, end_idx, base_indent) — all 0-indexed.
    """
    target_idx = target_line - 1  # convert to 0-indexed

    # Search backwards from target for the `by` keyword
    by_idx = target_idx
    for i in range(target_idx, max(target_idx - 20, -1), -1):
        stripped = lines[i].strip()
        if re.search(r'\bby\s*$', stripped):
            by_idx = i
            break

    base_indent = len(lines[by_idx]) - len(lines[by_idx].lstrip())

    # Find proof end by tracking indentation
    end_idx = by_idx + 1
    i = by_idx + 1
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()
        if not stripped or stripped.startswith('--'):
            i += 1
            continue
        indent = len(line) - len(line.lstrip())
        if indent <= base_indent and stripped:
            break
        end_idx = i
        i += 1

    return by_idx, end_idx, base_indent


def replace_proof_with_exact_q(lines: List[str], by_line_idx: int, end_idx: int) -> str:
    """Replace proof body with exact? and return the modified content."""
    # Determine the indentation of the first tactic line
    tactic_indent = '  '
    for i in range(by_line_idx + 1, end_idx + 1):
        stripped = lines[i].strip()
        if stripped and not stripped.startswith('--'):
            tactic_indent = lines[i][:len(lines[i]) - len(lines[i].lstrip())]
            break

    # Replace: keep the `by` line, replace body with `exact?`
    new_lines = lines[:by_line_idx + 1]
    new_lines.append(f'{tactic_indent}exact?')
    new_lines.extend(lines[end_idx + 1:])

    return '\n'.join(new_lines) + '\n'


def run_lean_and_capture(tmp_file: Path, target_line: int, project_root: Path,
                         timeout: int = 120) -> Optional[str]:
    """Run Lean on a temporary file and capture exact? suggestions.

    Returns the suggestion string if found, None otherwise.
    """
    try:
        result = subprocess.run(
            ['lake', 'env', 'lean', str(tmp_file)],
            capture_output=True, text=True, timeout=timeout,
            cwd=str(project_root)
        )
        output = result.stdout + result.stderr

        # Look for exact? suggestions near our target line
        # Format: "file:line:col: Try this: exact ..."
        suggestions = []
        for line in output.splitlines():
            m = re.match(r'.*?:(\d+):\d+:\s*Try this:\s*(.*)', line)
            if m:
                suggestion_line = int(m.group(1))
                suggestion = m.group(2).strip()
                # Accept suggestions near our target
                if abs(suggestion_line - target_line) <= 3:
                    suggestions.append(suggestion)

        if suggestions:
            return suggestions[0]

        # Check for errors to report
        for line in output.splitlines():
            if 'error' in line.lower():
                for delta in range(-2, 3):
                    check_line = target_line + delta
                    if f':{check_line}:' in line:
                        return f'ERROR: {line.strip()[:200]}'

        return None

    except subprocess.TimeoutExpired:
        return 'TIMEOUT'
    except Exception as e:
        return f'EXCEPTION: {e}'


def test_exact_at(file_path: Path, target_line: int, dry_run: bool = False,
                  timeout: int = 120) -> dict:
    """Test exact? replacement at a specific proof location.

    Works on a temporary copy — never modifies the original file.
    Returns a dict with: success, suggestion, original_tactics, saved_lines
    """
    lines = file_path.read_text().splitlines()
    by_idx, end_idx, base_indent = find_proof_bounds(lines, target_line)

    # Extract original tactics for reporting
    original_tactics = []
    for i in range(by_idx + 1, end_idx + 1):
        stripped = lines[i].strip()
        if stripped and not stripped.startswith('--'):
            original_tactics.append(stripped)

    original_line_count = end_idx - by_idx  # tactic lines being replaced

    result = {
        'file': str(file_path),
        'line': target_line,
        'by_line': by_idx + 1,
        'end_line': end_idx + 1,
        'original_tactics': original_tactics,
        'original_line_count': original_line_count,
        'success': False,
        'suggestion': None,
        'saved_lines': 0,
    }

    if dry_run:
        print(f"DRY RUN: Would replace lines {by_idx + 2}-{end_idx + 1} with `exact?`")
        print(f"  Original ({len(original_tactics)} tactics):")
        for t in original_tactics:
            print(f"    {t}")
        return result

    project_root = find_project_root(file_path)

    # Work on a temporary copy to avoid mutating the original
    with tempfile.TemporaryDirectory() as tmp_dir:
        tmp_path = Path(tmp_dir) / file_path.name
        # Copy the modified content (not the original) to temp
        modified = replace_proof_with_exact_q(lines, by_idx, end_idx)
        tmp_path.write_text(modified)

        # Compute the repo-relative path so lake can resolve imports
        try:
            rel_path = file_path.resolve().relative_to(project_root)
            lean_target = project_root / rel_path
            # Temporarily swap file for the lean invocation
            backup = lean_target.read_text()
            lean_target.write_text(modified)
            try:
                exact_line = by_idx + 2  # 1-indexed line where `exact?` is
                suggestion = run_lean_and_capture(lean_target, exact_line, project_root, timeout)
            finally:
                lean_target.write_text(backup)
        except (ValueError, OSError):
            # file_path not under project_root; fall back to temp copy
            exact_line = by_idx + 2
            suggestion = run_lean_and_capture(tmp_path, exact_line, project_root, timeout)

    if suggestion and not suggestion.startswith(('ERROR', 'TIMEOUT', 'EXCEPTION')):
        result['success'] = True
        result['suggestion'] = suggestion
        result['saved_lines'] = original_line_count - 1  # replacing N lines with 1
    else:
        result['suggestion'] = suggestion  # error info

    return result


def main():
    import argparse
    parser = argparse.ArgumentParser(
        description='Try exact? at proof locations in Lean 4 files',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s MyFile.lean:42               # test one proof
  %(prog)s --batch MyFile.lean          # test all candidates in file
  %(prog)s --batch src/ -r --priority high  # high-priority only, recursive
  %(prog)s --dry-run MyFile.lean:42     # show what would be tested

Note: Each test invokes a full Lean typecheck. Batch mode can be slow
on large files. Consider using --priority high to limit scope.
        """
    )
    parser.add_argument('target', nargs='?', help='FILE:LINE to test, or FILE/DIR for batch mode')
    parser.add_argument('--batch', action='store_true', help='Test all candidates in file/directory')
    parser.add_argument('--recursive', '-r', action='store_true',
                        help='Recursively scan directory in batch mode')
    parser.add_argument('--priority', default='high', help='Priority filter for batch mode (default: high)')
    parser.add_argument('--dry-run', action='store_true', help='Show what would be tested')
    parser.add_argument('--timeout', type=int, default=120, help='Lean timeout per test in seconds (default: 120)')
    args = parser.parse_args()

    if args.target and ':' in args.target and not args.batch:
        # Single test mode
        file_str, line_str = args.target.rsplit(':', 1)
        file_path = Path(file_str)
        if not file_path.exists():
            print(f"Error: {file_path} does not exist", file=sys.stderr)
            return 1
        target_line = int(line_str)

        print(f"Testing exact? at {file_path}:{target_line}...")
        result = test_exact_at(file_path, target_line, args.dry_run, args.timeout)

        if result['success']:
            print(f"\n  SUCCESS! Suggestion: {result['suggestion']}")
            print(f"  Would save {result['saved_lines']} lines")
        else:
            print(f"\n  No luck. {result.get('suggestion', 'No suggestion')}")
        print(f"  Original ({len(result['original_tactics'])} tactics):")
        for t in result['original_tactics']:
            print(f"    {t}")

    elif args.batch:
        # Batch mode: use find_exact_candidates to get targets
        # Import from same directory
        sys.path.insert(0, str(Path(__file__).resolve().parent))
        from find_exact_candidates import find_candidates

        if not args.target:
            print("Error: batch mode requires a file or directory argument", file=sys.stderr)
            return 1

        path = Path(args.target)
        if not path.exists():
            print(f"Error: {path} does not exist", file=sys.stderr)
            return 1

        if path.is_file():
            files = [path]
        elif args.recursive:
            files = sorted(path.rglob('*.lean'))
        else:
            files = sorted(path.glob('*.lean'))

        if not files:
            print(f"No .lean files found in {path}", file=sys.stderr)
            return 1

        all_candidates = []
        for f in files:
            all_candidates.extend(find_candidates(f))

        # Filter by priority
        if args.priority != 'all':
            all_candidates = [c for c in all_candidates if c.priority == args.priority]

        print(f"Testing {len(all_candidates)} candidates...")
        successes = []
        failures = []

        for i, cand in enumerate(all_candidates):
            print(f"\n[{i+1}/{len(all_candidates)}] {cand.file_path}:{cand.line_start} ({cand.lemma_name})")
            result = test_exact_at(Path(cand.file_path), cand.line_start, args.dry_run, args.timeout)

            if result['success']:
                print(f"  \u2713 {result['suggestion']}")
                print(f"    Saves {result['saved_lines']} lines")
                successes.append((cand, result))
            else:
                suggestion_str = result.get('suggestion', 'no suggestion') or 'no suggestion'
                print(f"  \u2717 {suggestion_str[:100]}")
                failures.append((cand, result))

        # Summary
        print(f"\n{'='*60}")
        print(f"RESULTS: {len(successes)} successes / {len(all_candidates)} tested")
        if successes:
            total_saved = sum(r['saved_lines'] for _, r in successes)
            print(f"Total lines saveable: {total_saved}")
            print(f"\nSuccessful replacements:")
            for cand, result in successes:
                print(f"  {cand.file_path}:{cand.line_start} ({cand.lemma_name})")
                print(f"    {result['suggestion']}")
                print(f"    Saves {result['saved_lines']} lines")

    else:
        parser.print_help()
        return 1

    return 0


if __name__ == '__main__':
    sys.exit(main())

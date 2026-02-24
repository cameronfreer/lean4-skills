#!/usr/bin/env python3
"""
Try `exact?` at various points in Lean 4 proofs to find one-liner replacements.

For each candidate proof block, replaces the tactic body with `exact?`,
swaps the source file with the modified version (atomic backup/restore),
runs Lean, and captures any suggestion from diagnostics.

Usage:
    python3 try_exact_at_step.py File.lean:42          # test one proof
    python3 try_exact_at_step.py --batch File.lean      # test all candidates in file
    python3 try_exact_at_step.py --batch src/ -r        # recursive batch
    python3 try_exact_at_step.py --dry-run File.lean:42 # show what would be tested

The script swaps the source file with a modified copy during Lean invocation
(required for import resolution), using an atomic backup/restore via
os.replace. A persistent .bak file is written first and cleaned up only
after successful restore, so interruptions leave a recoverable backup.
"""

import re
import sys
import os
import subprocess
import shutil
from pathlib import Path
from typing import Optional, Tuple, List


def find_project_root(start: Path) -> Path:
    """Walk up from start to find the Lean project root."""
    current = start.resolve()
    if current.is_file():
        current = current.parent
    markers = ('lakefile.lean', 'lakefile.toml', 'lean-toolchain')
    while current != current.parent:
        if any((current / m).exists() for m in markers):
            return current
        current = current.parent
    # Fallback: return the file's parent
    return start.resolve().parent


def find_proof_bounds(lines: List[str], target_line: int) -> Optional[Tuple[int, int, int]]:
    """Find the start (by line), end, and base indent of the proof containing target_line.

    Returns (by_line_idx, end_idx, base_indent) — all 0-indexed.
    Returns None if no enclosing `by` block is found within 50 lines.
    """
    target_idx = target_line - 1  # convert to 0-indexed

    # Search backwards from target for the `by` keyword
    by_idx = None
    for i in range(target_idx, max(target_idx - 50, -1), -1):
        stripped = lines[i].strip()
        if re.search(r'\bby\s*$', stripped):
            by_idx = i
            break

    if by_idx is None:
        return None

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


def run_lean_and_capture(lean_file: Path, target_line: int, project_root: Path,
                         timeout: int = 120) -> Optional[str]:
    """Run Lean on a file and capture exact? suggestions.

    Only accepts diagnostics whose file path matches lean_file (resolved),
    preventing misattribution from other files in the build.
    Returns the suggestion string if found, None otherwise.
    """
    file_stem = lean_file.resolve().name  # e.g. "Core.lean"
    try:
        result = subprocess.run(
            ['lake', 'env', 'lean', str(lean_file)],
            capture_output=True, text=True, timeout=timeout,
            cwd=str(project_root)
        )
        output = result.stdout + result.stderr

        # Look for exact? suggestions scoped to our file and target line
        # Format: "path/to/File.lean:line:col: Try this: exact ..."
        suggestions = []
        for line in output.splitlines():
            m = re.match(r'(.+?):(\d+):\d+:\s*Try this:\s*(.*)', line)
            if m:
                diag_file = m.group(1)
                suggestion_line = int(m.group(2))
                suggestion = m.group(3).strip()
                # Only accept diagnostics from our file
                if not diag_file.endswith(file_stem):
                    continue
                if abs(suggestion_line - target_line) <= 3:
                    suggestions.append(suggestion)

        if suggestions:
            return suggestions[0]

        # Check for errors scoped to our file
        for line in output.splitlines():
            if 'error' in line.lower() and file_stem in line:
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

    Uses atomic backup/restore when swapping the source file for Lean invocation.
    Returns a dict with: success, suggestion, original_tactics, saved_lines
    """
    lines = file_path.read_text().splitlines()
    bounds = find_proof_bounds(lines, target_line)
    if bounds is None:
        return {
            'file': str(file_path), 'line': target_line,
            'by_line': None, 'end_line': None,
            'original_tactics': [], 'original_line_count': 0,
            'success': False,
            'suggestion': f'ERROR: no enclosing `by` block found near line {target_line}',
            'saved_lines': 0,
        }
    by_idx, end_idx, base_indent = bounds

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
    modified = replace_proof_with_exact_q(lines, by_idx, end_idx)
    exact_line = by_idx + 2  # 1-indexed line where `exact?` is

    # Lean needs the file at its real path for import resolution.
    # Use a persistent .bak so interruptions leave a recoverable backup.
    lean_target = file_path.resolve()
    backup_path = lean_target.with_suffix(lean_target.suffix + '.exact_bak')

    # Write backup atomically (copy first, then swap)
    shutil.copy2(lean_target, backup_path)
    try:
        lean_target.write_text(modified)
        suggestion = run_lean_and_capture(lean_target, exact_line, project_root, timeout)
    finally:
        # Restore: atomic rename from backup
        os.replace(str(backup_path), str(lean_target))

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
        if file_path.suffix != '.lean':
            print(f"Error: {file_path} is not a .lean file", file=sys.stderr)
            return 1
        try:
            target_line = int(line_str)
        except ValueError:
            print(f"Error: invalid line number '{line_str}' in {args.target}", file=sys.stderr)
            return 1
        if not file_path.exists():
            print(f"Error: {file_path} does not exist", file=sys.stderr)
            return 1

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
            if path.suffix != '.lean':
                print(f"Error: {path} is not a .lean file", file=sys.stderr)
                return 1
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

#!/usr/bin/env python3
"""
Find proof blocks that are good candidates for `exact?` replacement.

Scans Lean 4 files for short tactic proofs (2-8 lines) where replacing
the entire proof body with `exact?` might find a one-liner.

Usage:
    python3 find_exact_candidates.py File.lean
    python3 find_exact_candidates.py src/ --recursive
    python3 find_exact_candidates.py File.lean --min-lines 3 --max-lines 6
    python3 find_exact_candidates.py . --priority high
"""

import re
import sys
from pathlib import Path
from dataclasses import dataclass
from typing import List


@dataclass
class ProofBlock:
    """A tactic proof block that might be replaceable by exact?."""
    file_path: str
    lemma_name: str
    line_start: int       # line of `:= by` or `by` (1-indexed)
    line_end: int         # last tactic line (1-indexed)
    tactic_count: int     # number of tactic steps
    tactics: List[str]    # the tactic lines
    category: str         # classification
    priority: str         # high/medium/low
    reason: str           # why it's a candidate


def find_proof_end(lines: List[str], start_idx: int, base_indent: int) -> int:
    """Find the end of a tactic proof block by tracking indentation."""
    i = start_idx + 1
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()
        # Skip blank lines and comments
        if not stripped or stripped.startswith('--'):
            i += 1
            continue
        # Measure indentation
        indent = len(line) - len(line.lstrip())
        # If indent drops to base level or below, proof is over
        if indent <= base_indent and stripped and not stripped.startswith('·'):
            break
        i += 1
    return i - 1


def get_tactic_lines(lines: List[str], start: int, end: int) -> List[str]:
    """Extract non-empty, non-comment tactic lines from a range."""
    result = []
    for i in range(start, end + 1):
        stripped = lines[i].strip()
        if stripped and not stripped.startswith('--'):
            result.append(stripped)
    return result


def classify_proof(tactics: List[str]) -> tuple:
    """Classify a proof block and estimate exact? likelihood.

    Returns (category, priority, reason).
    """
    # Category A: rw + exact/rfl — high chance exact? finds direct lemma
    if len(tactics) <= 3 and any(t.startswith('rw') for t in tactics) and \
       any(t.startswith(('exact', 'rfl')) for t in tactics):
        return ('rw_exact', 'high', 'rw + exact pattern — exact? may find direct lemma')

    # Category B: rw + ring/norm_num — identity might be known
    if len(tactics) <= 3 and any(t.startswith('rw') for t in tactics) and \
       any(t in ('ring', 'norm_num') for t in tactics):
        return ('rw_ring', 'high', 'rw + ring — algebraic identity might be a known lemma')

    # Category C: simp + linarith — might be single lemma
    if len(tactics) <= 3 and any('simp' in t for t in tactics) and \
       any('linarith' in t for t in tactics):
        return ('simp_linarith', 'medium', 'simp + linarith — might be closeable by exact?')

    # Category D: constructor + exact — could be anonymous constructor
    if any(t == 'constructor' for t in tactics) and \
       all(t in ('constructor',) or t.startswith('exact') or t.startswith('·') for t in tactics):
        return ('constructor_exact', 'high', 'constructor + exact — can be ⟨..., ...⟩')

    # Category E: by_contra + short — contradiction lemma might exist
    if len(tactics) <= 4 and any(t.startswith('by_contra') for t in tactics):
        return ('by_contra', 'medium', 'by_contra + short — contradiction lemma might exist')

    # Category F: intro + exact only — eta reduction
    if len(tactics) == 2 and tactics[0].startswith('intro') and tactics[1].startswith('exact'):
        return ('intro_exact', 'high', 'intro + exact — can be term-mode fun or eta-reduced')

    # Category G: have + exact — inline the have
    if len(tactics) <= 4 and sum(1 for t in tactics if t.startswith('have')) == 1 and \
       any(t.startswith('exact') for t in tactics):
        return ('have_exact', 'medium', 'have + exact — might inline into single term')

    # Category H: unfold/show + exact — definitional
    if len(tactics) <= 3 and any(t.startswith(('unfold', 'show')) for t in tactics) and \
       any(t.startswith('exact') for t in tactics):
        return ('unfold_exact', 'medium', 'unfold + exact — definitional; exact? might see through')

    # Category I: convert + single closer
    if len(tactics) <= 3 and any(t.startswith('convert') for t in tactics):
        return ('convert', 'medium', 'convert pattern — exact? might find direct match')

    # Category J: pure calc-free, no sorry, short
    if len(tactics) <= 4 and not any('sorry' in t for t in tactics) and \
       not any('calc' in t for t in tactics):
        return ('short_generic', 'low', f'{len(tactics)}-step proof — worth trying exact?')

    return ('skip', 'skip', '')


def find_candidates(file_path: Path, min_lines: int = 2, max_lines: int = 8) -> List[ProofBlock]:
    """Find proof blocks that are candidates for exact? replacement."""
    lines = file_path.read_text().splitlines()
    candidates = []

    for i, line in enumerate(lines):
        stripped = line.strip()

        # Look for `:= by` or standalone `by` starting a tactic block
        by_match = re.search(r':=\s+by\s*$', stripped)
        if not by_match:
            by_match = re.search(r'\bby\s*$', stripped)
            if not by_match:
                continue

        # Determine the base indentation
        indent = len(line) - len(line.lstrip())

        # Find the lemma name (look backwards for lemma/theorem/def)
        lemma_name = '(anonymous)'
        for j in range(i, max(i - 10, -1), -1):
            m = re.match(r'\s*(?:private\s+)?(?:noncomputable\s+)?(?:lemma|theorem|def|instance)\s+(\w+)', lines[j])
            if m:
                lemma_name = m.group(1)
                break

        # Find proof end
        proof_end = find_proof_end(lines, i, indent)

        # Get tactic lines (start from line after `by`)
        tactics = get_tactic_lines(lines, i + 1, proof_end)

        if len(tactics) < min_lines or len(tactics) > max_lines:
            continue

        # Skip proofs with >2 bullet points (multi-goal) — harder for exact?
        bullet_count = sum(1 for t in tactics if t.startswith('·'))
        if bullet_count > 2:
            continue

        # Classify
        category, priority, reason = classify_proof(tactics)
        if priority == 'skip':
            continue

        candidates.append(ProofBlock(
            file_path=str(file_path),
            lemma_name=lemma_name,
            line_start=i + 1,  # 1-indexed
            line_end=proof_end + 1,
            tactic_count=len(tactics),
            tactics=tactics,
            category=category,
            priority=priority,
            reason=reason,
        ))

    return candidates


def main():
    import argparse
    parser = argparse.ArgumentParser(
        description='Find exact? replacement candidates in Lean 4 files',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Categories (by priority):
  HIGH:    rw_exact, rw_ring, constructor_exact, intro_exact
  MEDIUM:  simp_linarith, by_contra, have_exact, unfold_exact, convert
  LOW:     short_generic
        """
    )
    parser.add_argument('path', help='Lean file or directory to scan')
    parser.add_argument('--recursive', '-r', action='store_true',
                        help='Recursively scan directory')
    parser.add_argument('--min-lines', type=int, default=2, help='Min tactic lines (default: 2)')
    parser.add_argument('--max-lines', type=int, default=8, help='Max tactic lines (default: 8)')
    parser.add_argument('--priority', choices=['high', 'medium', 'low', 'all'], default='all',
                        help='Filter by priority')
    parser.add_argument('--category', help='Filter by category name')
    args = parser.parse_args()

    path = Path(args.path)
    if not path.exists():
        print(f"Error: Path {path} does not exist", file=sys.stderr)
        return 1

    if path.is_file():
        if path.suffix != '.lean':
            print(f"Error: {path} is not a .lean file", file=sys.stderr)
            return 1
        files = [path]
    else:
        if args.recursive:
            files = sorted(path.rglob('*.lean'))
        else:
            files = sorted(path.glob('*.lean'))

    if not files:
        print(f"No .lean files found in {path}", file=sys.stderr)
        return 1

    all_candidates = []
    for f in files:
        all_candidates.extend(find_candidates(f, args.min_lines, args.max_lines))

    # Filter
    if args.priority != 'all':
        all_candidates = [c for c in all_candidates if c.priority == args.priority]
    if args.category:
        all_candidates = [c for c in all_candidates if c.category == args.category]

    # Sort by priority then file
    priority_order = {'high': 0, 'medium': 1, 'low': 2}
    all_candidates.sort(key=lambda c: (priority_order.get(c.priority, 3), c.file_path, c.line_start))

    # Output
    for c in all_candidates:
        print(f"[{c.priority.upper()}] {c.file_path}:{c.line_start} ({c.lemma_name}, {c.tactic_count} tactics)")
        print(f"  Category: {c.category} — {c.reason}")
        for t in c.tactics[:5]:
            print(f"    {t}")
        if len(c.tactics) > 5:
            print(f"    ... (+{len(c.tactics) - 5} more)")
        print()

    # Summary
    by_cat = {}
    for c in all_candidates:
        by_cat.setdefault(c.category, []).append(c)
    print(f"=== SUMMARY: {len(all_candidates)} candidates ===")
    for cat, items in sorted(by_cat.items(), key=lambda x: -len(x[1])):
        print(f"  {cat}: {len(items)}")

    return 0


if __name__ == '__main__':
    sys.exit(main())

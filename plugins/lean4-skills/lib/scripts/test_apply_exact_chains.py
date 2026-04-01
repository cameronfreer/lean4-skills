#!/usr/bin/env python3
"""Fixture tests for find_apply_exact_chains() in find_golfable.py.

Run from the repo root:
    python3 plugins/lean4/lib/scripts/test_apply_exact_chains.py
"""

import sys
import tempfile
from pathlib import Path

# Allow import from same directory
sys.path.insert(0, str(Path(__file__).resolve().parent))
from find_golfable import find_apply_exact_chains

# ── Fixtures ──────────────────────────────────────────────────────────

FIXTURES = {
    # Positive: bulleted apply/exact
    "pos_bullet": (1, """\
theorem foo : bar := by
  apply mul_lt_mul_of_pos_right
  · exact h_bound
  · exact h_pos
"""),
    # Positive: same-indent apply then exact
    "pos_same_indent": (1, """\
theorem foo : bar := by
  apply h
  exact hp
"""),
    # Negative: inside calc block
    "neg_calc": (0, """\
theorem foo : bar := by
  calc x
    _ = y := by
      apply f
      exact h
    _ = z := rfl
"""),
    # Negative: semicolon-heavy (>3)
    "neg_semicolons": (0, """\
theorem foo : bar := by
  apply f; exact a; apply g; exact b; exact c; apply h; exact d
"""),
    # Negative: has have
    "neg_have": (0, """\
theorem foo : bar := by
  apply f
  have h := some_lemma
  exact h.property
"""),
    # Negative: inside cases block (pattern-match arm)
    "neg_cases": (0, """\
theorem foo : bar := by
  cases n with
  | zero =>
    apply f
    exact h
  | succ n =>
    rfl
"""),
    # Negative: bullet-style cases branch
    "neg_bullet_cases": (0, """\
theorem foo : bar := by
  · cases n with
    | zero =>
      apply f
      exact h
    | succ n =>
      rfl
"""),
}

# ── Runner ────────────────────────────────────────────────────────────

def main() -> int:
    fail = 0
    with tempfile.TemporaryDirectory() as tmp:
        for name, (expected, content) in FIXTURES.items():
            p = Path(tmp) / f"{name}.lean"
            p.write_text(content)
            got = len(find_apply_exact_chains(p, p.read_text().splitlines(keepends=True)))
            ok = "\u2713" if got == expected else "\u2717"
            if got != expected:
                fail += 1
            print(f"{ok} {name}: expected={expected} actual={got}")

    print()
    if fail == 0:
        print("All passed!")
    else:
        print(f"{fail} FAILED")
    return fail

if __name__ == "__main__":
    sys.exit(main())

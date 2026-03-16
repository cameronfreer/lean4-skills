#!/usr/bin/env python3
"""Deterministic test for benefit-based sort order in find_golfable.py.

Validates that analyze_file() returns patterns sorted by policy order:
  directness → structural → conditional
and that intra-phase ordering matches the documented phase position
(by-exact before apply-exact-chain within directness).

Run:
    python3 tests/test_ordering.py
    # or from repo root:
    python3 plugins/lean4/lib/scripts/tests/test_ordering.py
"""

import sys
import tempfile
import unittest
from pathlib import Path

# Allow import from parent directory
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from find_golfable import analyze_file


# Lean fixture with patterns from each benefit category.
# Deliberately places apply-exact-chain BEFORE by-exact in the file
# to verify that sorting overrides file order.
FIXTURE = """\
-- apply-exact-chain pattern (directness, appears first in file)
theorem quux : Nat := by
  apply Nat.succ
  exact 41

-- by-exact pattern (directness, appears second in file)
theorem foo : Nat := by
  exact 42

-- let+have+exact pattern (structural)
theorem bar : Nat := by
  let x := 1
  have h : Nat := x
  exact h

-- constructor pattern (conditional, needs >=6 branch lines)
theorem baz : Prop := by
  constructor
    exact True.intro
    exact True.intro
    exact True.intro
    exact True.intro
    exact True.intro
    exact True.intro
"""


class TestBenefitOrdering(unittest.TestCase):
    """Patterns are returned in policy order: directness, structural, conditional."""

    def setUp(self):
        f = tempfile.NamedTemporaryFile(suffix=".lean", mode="w", delete=False)
        f.write(FIXTURE)
        f.flush()
        f.close()
        self.path = Path(f.name)
        self.patterns = analyze_file(self.path)

    def tearDown(self):
        self.path.unlink()

    def test_benefit_groups_present(self):
        benefits = [p.benefit for p in self.patterns]
        self.assertIn("directness", benefits)
        self.assertIn("structural", benefits)

    def test_cross_phase_ordering(self):
        """Directness before structural before conditional."""
        benefits = [p.benefit for p in self.patterns]
        first_directness = next(i for i, b in enumerate(benefits) if b == "directness")
        first_structural = next(i for i, b in enumerate(benefits) if b == "structural")
        self.assertLess(first_directness, first_structural,
                        f"directness (idx {first_directness}) should precede structural (idx {first_structural})")
        if "conditional" in benefits:
            first_conditional = next(i for i, b in enumerate(benefits) if b == "conditional")
            self.assertLess(first_structural, first_conditional,
                            f"structural (idx {first_structural}) should precede conditional (idx {first_conditional})")

    def test_intra_phase_ordering(self):
        """Within directness: by-exact before apply-exact-chain."""
        directness = [p for p in self.patterns if p.benefit == "directness"]
        types = [p.pattern_type for p in directness]
        if "by exact wrapper" in types and "apply-exact-chain" in types:
            idx_by = types.index("by exact wrapper")
            idx_apply = types.index("apply-exact-chain")
            self.assertLess(idx_by, idx_apply,
                            f"by-exact (idx {idx_by}) should precede apply-exact-chain (idx {idx_apply}) within directness")

    def test_benefit_field_values(self):
        valid_benefits = {"directness", "performance", "structural", "conditional"}
        for p in self.patterns:
            self.assertIn(p.benefit, valid_benefits,
                          f"{p.pattern_type} has invalid benefit '{p.benefit}'")


if __name__ == "__main__":
    unittest.main()

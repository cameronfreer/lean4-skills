#!/usr/bin/env python3
"""Deterministic test for benefit-based sort order in find_golfable.py.

Validates that analyze_file() returns patterns sorted by policy order:
  directness → structural → conditional

Run:
    python3 -m pytest tests/test_ordering.py -v
    # or from repo root:
    python3 -m pytest plugins/lean4/lib/scripts/tests/test_ordering.py -v
"""

import sys
import tempfile
from pathlib import Path

# Allow import from parent directory
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from find_golfable import analyze_file


# Lean fixture with one pattern from each benefit category.
# The file is crafted so that all three detectors fire.
FIXTURE = """\
-- by-exact pattern (directness)
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


def test_benefit_ordering():
    """Patterns are returned in policy order: directness, structural, conditional."""
    with tempfile.NamedTemporaryFile(suffix=".lean", mode="w", delete=False) as f:
        f.write(FIXTURE)
        f.flush()
        path = Path(f.name)

    try:
        patterns = analyze_file(path)
        # We should get at least one from each category
        benefits = [p.benefit for p in patterns]
        assert "directness" in benefits, f"Expected directness pattern, got {benefits}"
        assert "structural" in benefits, f"Expected structural pattern, got {benefits}"

        # Directness patterns must come before structural, structural before conditional
        first_directness = next(i for i, b in enumerate(benefits) if b == "directness")
        first_structural = next(i for i, b in enumerate(benefits) if b == "structural")
        assert first_directness < first_structural, (
            f"directness (idx {first_directness}) should precede structural (idx {first_structural})"
        )

        if "conditional" in benefits:
            first_conditional = next(i for i, b in enumerate(benefits) if b == "conditional")
            assert first_structural < first_conditional, (
                f"structural (idx {first_structural}) should precede conditional (idx {first_conditional})"
            )
    finally:
        path.unlink()


def test_benefit_field_values():
    """Each pattern has a valid benefit field."""
    with tempfile.NamedTemporaryFile(suffix=".lean", mode="w", delete=False) as f:
        f.write(FIXTURE)
        f.flush()
        path = Path(f.name)

    try:
        patterns = analyze_file(path)
        valid_benefits = {"directness", "performance", "structural", "conditional"}
        for p in patterns:
            assert p.benefit in valid_benefits, (
                f"{p.pattern_type} has invalid benefit '{p.benefit}'"
            )
    finally:
        path.unlink()


if __name__ == "__main__":
    test_benefit_ordering()
    test_benefit_field_values()
    print("All ordering tests passed.")

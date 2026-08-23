"""CommandSpec for /lean4:review -- read-only proof review.

/lean4:review had no parser spec until #110. It is adopted here as one full
spec covering every currently-documented flag PLUS the two mathlib-review
gate flags, rather than validating only the new flags (which would deepen the
drift #110's track removes). Behaviour beyond parsing — the Layer 1 / Layer 2
split, project-context gating, advisory labelling, and output validation —
lives in review.md.

The two gate flags encode the conflict rule: only flags resolving to true
participate (explicit false == omission); both true -> one startup error,
before any Layer-2 precedence resolution.
"""

from __future__ import annotations

from ..coercions import REVIEW_MATHLIB_REVIEW_CONFLICT
from ..types import CommandSpec, FlagSpec, PositionalSpec

SPEC = CommandSpec(
    name="review",
    positionals=(
        PositionalSpec(
            name="target",
            required=False,
            notes="File or directory to review.",
        ),
    ),
    flags=(
        FlagSpec(
            name="--scope",
            type="enum",
            enum_values=("sorry", "deps", "file", "changed", "project"),
            notes="Review scope; defaults are resolved at runtime from target/--line.",
        ),
        FlagSpec(
            name="--line",
            type="int",
            int_min=1,
            notes="1-indexed line for single-sorry (sorry/deps) scope.",
        ),
        FlagSpec(
            name="--codex",
            type="bool",
            default=False,
            notes="External review via Codex (interactive handoff).",
        ),
        FlagSpec(
            name="--llm",
            type="freeform",
            notes="Use the llm CLI with the given model.",
        ),
        FlagSpec(
            name="--hook",
            type="path",
            notes="Path to a custom analysis hook script.",
        ),
        FlagSpec(
            name="--json",
            type="bool",
            default=False,
            notes="Emit the built-in lean4-review-report/v1 JSON dump.",
        ),
        FlagSpec(
            name="--mode",
            type="enum",
            enum_values=("batch", "stuck"),
            default="batch",
            notes="batch (default) or stuck (triage).",
        ),
        FlagSpec(
            name="--mathlib-review",
            type="bool",
            default=False,
            notes=(
                "Force the Layer-2 mathlib-review bar at full strictness, "
                "overriding project-context detection."
            ),
        ),
        FlagSpec(
            name="--no-mathlib-review",
            type="bool",
            default=False,
            notes=(
                "Force Layer-2 findings to advisory, overriding project-context "
                "detection."
            ),
        ),
    ),
    cross_validations=(
        # --mathlib-review + --no-mathlib-review -> single startup error,
        # evaluated before Layer-2 precedence.
        REVIEW_MATHLIB_REVIEW_CONFLICT,
    ),
)

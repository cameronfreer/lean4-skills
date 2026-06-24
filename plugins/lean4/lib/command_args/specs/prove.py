"""Spec for /lean4:prove — guided cycle-by-cycle theorem proving."""

from __future__ import annotations

from ..types import (
    CommandSpec,
    FlagSpec,
    PositionalSpec,
)

# ---------------------------------------------------------------------------
# Flag definitions
# ---------------------------------------------------------------------------

FLAG_REPAIR_ONLY = FlagSpec(
    name="--repair-only",
    type="bool",
    default=False,
    enforcement="startup-validated",
    notes="Fix build errors only, skip sorry-filling",
)

FLAG_PLANNING = FlagSpec(
    name="--planning",
    type="enum",
    enum_values=("ask", "on", "off"),
    default="ask",
    enforcement="startup-validated",
    notes="ask prompts at startup",
)

FLAG_REVIEW_SOURCE = FlagSpec(
    name="--review-source",
    type="enum",
    enum_values=("internal", "external", "both", "none"),
    default="internal",
    enforcement="startup-validated",
)

FLAG_REVIEW_EVERY = FlagSpec(
    name="--review-every",
    type="freeform",
    default="checkpoint",
    enforcement="startup-validated",
    notes="N (sorries), checkpoint, or never",
)

FLAG_CHECKPOINT = FlagSpec(
    name="--checkpoint",
    type="bool",
    default=True,
    enforcement="startup-validated",
)

FLAG_DEEP = FlagSpec(
    name="--deep",
    type="enum",
    enum_values=("never", "ask", "stuck", "always"),
    default="never",
    enforcement="startup-validated",
)

FLAG_DEEP_SORRY_BUDGET = FlagSpec(
    name="--deep-sorry-budget",
    type="int",
    default=1,
    int_min=1,
    enforcement="session-enforced",
)

FLAG_DEEP_TIME_BUDGET = FlagSpec(
    name="--deep-time-budget",
    type="duration",
    default="10m",
    enforcement="advisory",
    notes="Scopes deep-mode subagent work. Not tracked or enforced.",
)

FLAG_MAX_DEEP_PER_CYCLE = FlagSpec(
    name="--max-deep-per-cycle",
    type="int",
    default=1,
    int_min=0,
    enforcement="session-enforced",
)

FLAG_DEEP_SNAPSHOT = FlagSpec(
    name="--deep-snapshot",
    type="enum",
    enum_values=("stash",),
    default="stash",
    enforcement="startup-validated",
    notes="V1: stash only",
)

FLAG_DEEP_ROLLBACK = FlagSpec(
    name="--deep-rollback",
    type="enum",
    enum_values=("on-regression", "on-no-improvement", "always", "never"),
    default="on-regression",
    enforcement="startup-validated",
)

FLAG_DEEP_SCOPE = FlagSpec(
    name="--deep-scope",
    type="enum",
    enum_values=("target", "cross-file"),
    default="target",
    enforcement="startup-validated",
)

FLAG_DEEP_MAX_FILES = FlagSpec(
    name="--deep-max-files",
    type="int",
    default=1,
    int_min=1,
    enforcement="session-enforced",
)

FLAG_DEEP_MAX_LINES = FlagSpec(
    name="--deep-max-lines",
    type="int",
    default=120,
    int_min=1,
    enforcement="session-enforced",
)

FLAG_DEEP_REGRESSION_GATE = FlagSpec(
    name="--deep-regression-gate",
    type="enum",
    enum_values=("strict", "off"),
    default="strict",
    enforcement="startup-validated",
    notes="strict auto-aborts on regression",
)

FLAG_BATCH_SIZE = FlagSpec(
    name="--batch-size",
    type="int",
    default=1,
    int_min=1,
    enforcement="advisory",
)

FLAG_COMMIT = FlagSpec(
    name="--commit",
    type="enum",
    enum_values=("ask", "auto", "never"),
    default="ask",
    enforcement="startup-validated",
    notes="ask prompts before each commit",
)

FLAG_GOLF = FlagSpec(
    name="--golf",
    type="enum",
    enum_values=("prompt", "auto", "never"),
    default="prompt",
    enforcement="startup-validated",
)


# ---------------------------------------------------------------------------
# Spec
# ---------------------------------------------------------------------------

SPEC = CommandSpec(
    name="prove",
    positionals=(
        PositionalSpec(
            name="scope",
            required=False,
            notes="Specific file or theorem to focus on; defaults to all",
        ),
    ),
    flags=(
        FLAG_REPAIR_ONLY,
        FLAG_PLANNING,
        FLAG_REVIEW_SOURCE,
        FLAG_REVIEW_EVERY,
        FLAG_CHECKPOINT,
        FLAG_DEEP,
        FLAG_DEEP_SORRY_BUDGET,
        FLAG_DEEP_TIME_BUDGET,
        FLAG_MAX_DEEP_PER_CYCLE,
        FLAG_DEEP_SNAPSHOT,
        FLAG_DEEP_ROLLBACK,
        FLAG_DEEP_SCOPE,
        FLAG_DEEP_MAX_FILES,
        FLAG_DEEP_MAX_LINES,
        FLAG_DEEP_REGRESSION_GATE,
        FLAG_BATCH_SIZE,
        FLAG_COMMIT,
        FLAG_GOLF,
    ),
    cross_validations=(),
)

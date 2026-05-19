"""Spec for /lean4:disprove — counterexample search with certified refutation.

Always interactive. The 6-phase cycle (Plan → Work → Checkpoint → Review →
Accumulate → Continue/Stop) runs once per cycle; the user picks one method
per cycle from Step 1's dynamic menu and one config from Step 2's dynamic
menu (Step 0 — Knowledge Search Menu — runs once in Cycle 1 by default,
and re-enters when Step 1 picks `knowledge search`). Per-method parameters
are dynamic Step 2 candidates the cycling LLM proposes, not top-level flags.
"""
from __future__ import annotations

from typing import Mapping

from ..types import (
    CommandSpec,
    CrossValidation,
    FlagSpec,
    ParseContext,
    PositionalSpec,
)


# ---------------------------------------------------------------------------
# Target shape regexes (matched by cross-validation)
#
# Shared with `lib/scripts/disprove_target_resolve.py` via
# `command_args.target_patterns` so both call sites accept exactly the
# same set of target strings.
# ---------------------------------------------------------------------------

from ..target_patterns import FILE_LINE_RE as _FILE_LINE_RE
from ..target_patterns import QUALIFIED_NAME_RE as _QUALIFIED_NAME_RE


# ---------------------------------------------------------------------------
# Cross-validations
# ---------------------------------------------------------------------------

def _target_required(
    flags: Mapping[str, object],
    ctx: ParseContext,
) -> list[str]:
    """target positional is required."""
    if not flags.get("__positional_target"):
        return ["target positional is required (File.lean:LINE or Namespace.theoremName)"]
    return []


TARGET_REQUIRED = CrossValidation(
    rule_id="disprove-target-required",
    fn=_target_required,
    severity="error",
    doc_phrases=(
        "target positional is required (File.lean:LINE or Namespace.theoremName)",
    ),
    summary="Require target positional.",
)


def _target_shape_valid(
    flags: Mapping[str, object],
    ctx: ParseContext,
) -> list[str]:
    """target must match File.lean:LINE or Namespace.theoremName."""
    target = flags.get("__positional_target")
    if not target:
        return []  # handled by TARGET_REQUIRED
    s = str(target)
    if _FILE_LINE_RE.match(s):
        return []
    if s.endswith(".lean"):
        return [
            f"target {s!r}: file path is missing ':LINE'. "
            "Use 'File.lean:LINE' (e.g. 'Foo.lean:42')."
        ]
    if _QUALIFIED_NAME_RE.match(s):
        return []
    return [
        f"target {s!r}: expected 'File.lean:LINE' or 'Namespace.theoremName' "
        "(inline Props not supported in v1)"
    ]


TARGET_SHAPE_VALID = CrossValidation(
    rule_id="disprove-target-shape-valid",
    fn=_target_shape_valid,
    severity="error",
    doc_phrases=(
        "target must match 'File.lean:LINE' or 'Namespace.theoremName' "
        "(inline Props not supported in v1)",
    ),
    summary="Validate target positional shape.",
)


# ---------------------------------------------------------------------------
# Flags
# ---------------------------------------------------------------------------

FLAG_MAX_RUNTIME = FlagSpec(
    name="--max-runtime",
    type="duration",
    default="5m",
    enforcement="best-effort",
    notes="Best-effort wall-clock session budget across all cycles.",
)

FLAG_MAX_CYCLES = FlagSpec(
    name="--max-cycles",
    type="int",
    default=3,
    int_min=1,
    enforcement="session-enforced",
    notes=(
        "Max widening passes. Each cycle picks one method via the Step 1 "
        "menu and configures its parameters via Step 2 prompts."
    ),
)

FLAG_MAX_STUCK_CYCLES = FlagSpec(
    name="--max-stuck-cycles",
    type="int",
    default=2,
    int_min=1,
    enforcement="session-enforced",
    notes=(
        "Bail after this many consecutive cycles where the next cycle's "
        "Step 1 menu has no non-failed `(family, config)` pair to place in "
        "its top 3 (no remaining widening lever)."
    ),
)

FLAG_NEGATION_POLICY = FlagSpec(
    name="--negation-policy",
    type="enum",
    enum_values=("counterexample-only",),
    default="counterexample-only",
    enforcement="startup-validated",
    notes="Locked to counterexample-only in v1 (append-only artifact). Reserved enum members may be added in v2.",
)

FLAG_COMMIT = FlagSpec(
    name="--commit",
    type="enum",
    enum_values=("auto", "ask", "never"),
    default="ask",
    enforcement="startup-validated",
    notes=(
        "Per-cycle Checkpoint behavior. 'ask' (default) prompts before each "
        "commit. 'auto' commits without prompting. 'never' skips committing "
        "(leave staging to /lean4:checkpoint)."
    ),
)

FLAG_KNOWLEDGE_SEARCH_BUDGET = FlagSpec(
    name="--knowledge-search-budget",
    type="int",
    default=3,
    int_min=1,
    enforcement="session-enforced",
    notes=(
        "Max Step 0 (knowledge search) visits per cycle. Cycle 1 always runs "
        "Step 0 once; subsequent visits only happen if a later cycle's Step 1 "
        "menu surfaces 'knowledge search' and the user picks it. Enforced by "
        "cycle_tracker.sh as --max-knowledge-search-per-cycle."
    ),
)


# ---------------------------------------------------------------------------
# Spec
# ---------------------------------------------------------------------------

SPEC = CommandSpec(
    name="disprove",
    positionals=(
        PositionalSpec(
            name="target",
            required=True,
            notes="'File.lean:LINE' or 'Namespace.theoremName'",
        ),
    ),
    flags=(
        FLAG_MAX_RUNTIME,
        FLAG_MAX_CYCLES,
        FLAG_MAX_STUCK_CYCLES,
        FLAG_NEGATION_POLICY,
        FLAG_COMMIT,
        FLAG_KNOWLEDGE_SEARCH_BUDGET,
    ),
    cross_validations=(
        TARGET_REQUIRED,
        TARGET_SHAPE_VALID,
    ),
)

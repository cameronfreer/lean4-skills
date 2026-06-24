"""CommandSpec for /lean4:draft -- draft Lean declaration skeletons from informal claims."""

from __future__ import annotations

from ..coercions import (
    CLAIM_SELECT_REQUIRES_SOURCE,
    INTENT_AUTO_COLLAPSE,
    OUTPUT_FILE_OVERWRITE_CHECK,
    OUTPUT_FILE_REQUIRES_OUT,
    TOPIC_OR_SOURCE_REQUIRED,
)
from ..types import CommandSpec, FlagSpec, PositionalSpec
from ._common import (
    claim_select_flag,
    intent_flag,
    level_flag,
    out_flag,
    output_flag,
    overwrite_flag,
    presentation_flag,
    source_flag,
)

# ---------------------------------------------------------------------------
# Draft-specific flags
# ---------------------------------------------------------------------------

FLAG_MODE = FlagSpec(
    name="--mode",
    type="enum",
    enum_values=("skeleton", "attempt"),
    default="skeleton",
    enforcement="startup-validated",
    notes=(
        "skeleton: sorry-stubbed declarations only. "
        "attempt: adds a proof-attempt loop before finalizing."
    ),
)

FLAG_ELAB_CHECK = FlagSpec(
    name="--elab-check",
    type="enum",
    enum_values=("best-effort", "strict"),
    default="best-effort",
    enforcement="startup-validated",
    notes="Elaboration check strictness for drafted skeletons.",
)

# Intent for draft: only auto, usage, math (internals/authoring collapsed).
# The coercion on --intent handles auto -> usage and internals/authoring -> usage.
FLAG_INTENT = intent_flag(
    default="math",
    enum_values=("auto", "usage", "math"),
    coerce=INTENT_AUTO_COLLAPSE,
)

# Claim-select unconditionally requires --source in draft context.
FLAG_CLAIM_SELECT = claim_select_flag(requires=("--source",))


# ---------------------------------------------------------------------------
# Spec
# ---------------------------------------------------------------------------

SPEC = CommandSpec(
    name="draft",
    positionals=(
        PositionalSpec(
            name="topic",
            required=False,
            notes=(
                "Informal claim to draft. Optional when --source provides it. "
                "At least one of topic or --source must be given."
            ),
        ),
    ),
    flags=(
        FLAG_MODE,
        FLAG_ELAB_CHECK,
        level_flag(),
        output_flag(),
        out_flag(),
        overwrite_flag(),
        source_flag(),
        FLAG_INTENT,
        presentation_flag(),
        FLAG_CLAIM_SELECT,
    ),
    cross_validations=(
        # At least one of topic or --source must be given
        TOPIC_OR_SOURCE_REQUIRED,
        # --output=file without --out -> startup validation error
        OUTPUT_FILE_REQUIRES_OUT,
        # --output=file + existing target + no --overwrite -> startup validation error
        OUTPUT_FILE_OVERWRITE_CHECK,
        # --claim-select without --source -> startup validation error
        # (Also enforced via FlagSpec.requires for the unconditional case,
        #  but the CrossValidation gives a clearer error message.)
        CLAIM_SELECT_REQUIRES_SOURCE,
    ),
)

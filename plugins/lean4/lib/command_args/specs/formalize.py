"""Spec for /lean4:formalize — interactive formalization (draft + prove)."""

from __future__ import annotations

from collections.abc import Mapping

from ..coercions import intent_auto_collapse
from ..types import (
    Coercion,
    CommandSpec,
    CrossValidation,
    FlagSpec,
    ParseContext,
    PositionalSpec,
)
from . import _common

# ---------------------------------------------------------------------------
# Formalize-specific coercions
# ---------------------------------------------------------------------------

INTENT_AUTO_COLLAPSE = Coercion(
    rule_id="formalize-intent-auto-collapse",
    fn=intent_auto_collapse,
    doc_phrases=(
        "--intent=auto inference: coerce internals -> usage and authoring -> usage",
        "formalize does not define behavior for internals or authoring intents",
    ),
    summary=(
        "After auto-inference, collapse internals/authoring to usage "
        "(formalize only supports usage and math intents)."
    ),
)


# ---------------------------------------------------------------------------
# Formalize-specific cross-validations
# ---------------------------------------------------------------------------


def _topic_or_source_full_validate(
    flags: Mapping[str, object],
    ctx: ParseContext,
) -> list[str]:
    """Cross-validation for: at least one of topic or --source required.

    Convention: the parser injects positionals into the cross-validation
    mapping as ``__positional_<name>`` keys so that cross-validators can
    inspect them.  This validator expects ``__positional_topic`` to be set
    to the topic string (or absent/falsy when the user omitted the topic
    positional).  If the parser does not yet inject positionals this way,
    a small patch to ``parse_invocation`` is needed (add positionals into
    ``resolved_values`` before running cross-validations).
    """
    has_topic = bool(flags.get("__positional_topic"))
    has_source = bool(flags.get("--source"))
    if not has_topic and not has_source:
        return ["At least one of topic (positional) or --source must be given"]
    return []


TOPIC_OR_SOURCE = CrossValidation(
    rule_id="formalize-topic-or-source",
    fn=_topic_or_source_full_validate,
    severity="error",
    doc_phrases=(
        "At least one of topic or --source must be given; "
        "omitting both is a startup validation error.",
    ),
    summary="Require at least one of positional topic or --source.",
)


def _output_file_requires_out_validate(
    flags: Mapping[str, object],
    ctx: ParseContext,
) -> list[str]:
    """--output=file without --out -> startup validation error."""
    if flags.get("--output") == "file" and not flags.get("--out"):
        return ["--output=file requires --out to specify an output path"]
    return []


OUTPUT_FILE_REQUIRES_OUT = CrossValidation(
    rule_id="formalize-output-file-requires-out",
    fn=_output_file_requires_out_validate,
    severity="error",
    doc_phrases=("--output=file without --out -> startup validation error",),
    summary="Require --out when --output=file.",
)


def _overwrite_check_validate(
    flags: Mapping[str, object],
    ctx: ParseContext,
) -> list[str]:
    """--output=file with existing target and no --overwrite -> error."""
    import os

    if flags.get("--output") != "file":
        return []
    out = flags.get("--out")
    if not out:
        return []  # handled by output-file-requires-out
    overwrite = flags.get("--overwrite")
    target = os.path.join(ctx.cwd, str(out))
    if os.path.exists(target) and not overwrite:
        return [
            f"--output=file target {out!r} already exists; "
            "pass --overwrite to allow overwriting"
        ]
    return []


OVERWRITE_CHECK = CrossValidation(
    rule_id="formalize-overwrite-check",
    fn=_overwrite_check_validate,
    severity="error",
    doc_phrases=(
        "--output=file with existing target and no --overwrite -> startup validation error",
    ),
    summary="Block overwrite of existing output file unless --overwrite is set.",
)


def _claim_select_requires_source_validate(
    flags: Mapping[str, object],
    ctx: ParseContext,
) -> list[str]:
    """--claim-select without --source -> startup validation error."""
    claim_select = flags.get("--claim-select")
    source = flags.get("--source")
    if claim_select and not source:
        return ["--claim-select requires --source (nothing to select from)"]
    return []


CLAIM_SELECT_REQUIRES_SOURCE = CrossValidation(
    rule_id="formalize-claim-select-requires-source",
    fn=_claim_select_requires_source_validate,
    severity="error",
    doc_phrases=(
        "--claim-select without --source -> startup validation error (nothing to select from).",
    ),
    summary="--claim-select is meaningless without --source.",
)


# ---------------------------------------------------------------------------
# Formalize-specific flags
# ---------------------------------------------------------------------------

FLAG_RIGOR = FlagSpec(
    name="--rigor",
    type="enum",
    enum_values=("checked", "sketch", "axiomatic"),
    default="checked",
    enforcement="startup-validated",
)

FLAG_VERIFY = _common.FLAG_VERIFY

FLAG_LEVEL = _common.FLAG_LEVEL

FLAG_OUTPUT = _common.FLAG_OUTPUT
FLAG_OUT = _common.FLAG_OUT
FLAG_OVERWRITE = _common.FLAG_OVERWRITE

FLAG_SOURCE = _common.FLAG_SOURCE

FLAG_INTENT_FORMALIZE = FlagSpec(
    name="--intent",
    type="enum",
    enum_values=("auto", "usage", "math"),
    default="math",
    enforcement="startup-validated",
    coerce=INTENT_AUTO_COLLAPSE,
    notes=(
        "formalize only supports usage and math; "
        "internals/authoring are collapsed to usage via coercion"
    ),
)

FLAG_PRESENTATION = _common.FLAG_PRESENTATION

FLAG_CLAIM_SELECT = FlagSpec(
    name="--claim-select",
    type="freeform",
    default=None,
    enforcement="startup-validated",
    notes='first | named:"..." | regex:"...". Noninteractive claim selection from --source.',
)

FLAG_DRAFT_MODE = FlagSpec(
    name="--draft-mode",
    type="enum",
    enum_values=("skeleton", "attempt"),
    default="attempt",
    enforcement="startup-validated",
    notes="Mode for the draft phase (default is attempt in formalize context)",
)

FLAG_DRAFT_ELAB_CHECK = FlagSpec(
    name="--draft-elab-check",
    type="enum",
    enum_values=("best-effort", "strict"),
    default="best-effort",
    enforcement="startup-validated",
    notes="Elaboration check for the draft phase",
)

FLAG_DEEP = FlagSpec(
    name="--deep",
    type="enum",
    enum_values=("never", "ask", "stuck", "always"),
    default="never",
    enforcement="startup-validated",
    notes="Deep mode for prove phase",
)

FLAG_DEEP_SORRY_BUDGET = FlagSpec(
    name="--deep-sorry-budget",
    type="int",
    default=1,
    enforcement="session-enforced",
    int_min=0,
    notes="Max sorries per deep invocation",
)

FLAG_DEEP_TIME_BUDGET = FlagSpec(
    name="--deep-time-budget",
    type="duration",
    default="10m",
    enforcement="advisory",
    notes="Advisory: scopes deep-mode subagent work. Not tracked or enforced.",
)

FLAG_COMMIT = FlagSpec(
    name="--commit",
    type="enum",
    enum_values=("ask", "auto", "never"),
    default="ask",
    enforcement="startup-validated",
    notes="Commit policy (inert in standalone formalize — no staging or committing)",
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
    name="formalize",
    positionals=(
        PositionalSpec(
            name="topic",
            required=False,
            notes=(
                "Informal claim to formalize. Optional when --source provides it. "
                "At least one of topic or --source must be given."
            ),
        ),
    ),
    flags=(
        FLAG_RIGOR,
        FLAG_VERIFY,
        FLAG_LEVEL,
        FLAG_OUTPUT,
        FLAG_OUT,
        FLAG_OVERWRITE,
        FLAG_SOURCE,
        FLAG_INTENT_FORMALIZE,
        FLAG_PRESENTATION,
        FLAG_CLAIM_SELECT,
        FLAG_DRAFT_MODE,
        FLAG_DRAFT_ELAB_CHECK,
        FLAG_DEEP,
        FLAG_DEEP_SORRY_BUDGET,
        FLAG_DEEP_TIME_BUDGET,
        FLAG_COMMIT,
        FLAG_GOLF,
    ),
    cross_validations=(
        TOPIC_OR_SOURCE,
        OUTPUT_FILE_REQUIRES_OUT,
        OVERWRITE_CHECK,
        CLAIM_SELECT_REQUIRES_SOURCE,
    ),
)

"""Spec for /lean4:autoformalize — autonomous end-to-end formalization."""

from __future__ import annotations

from collections.abc import Mapping

from ..types import (
    Coercion,
    CommandSpec,
    CrossValidation,
    FlagSpec,
    ParseContext,
)

# ---------------------------------------------------------------------------
# Autoformalize-specific coercions
# ---------------------------------------------------------------------------


def _review_source_coerce(
    value: object,
    flags: Mapping[str, object],
    ctx: ParseContext,
) -> tuple[object, str | None]:
    """--review-source=external|both -> coerced to internal."""
    if value in ("external", "both"):
        return "internal", (
            "--review-source=external requires interactive handoff. "
            "Using internal review for unattended operation."
        )
    return value, None


REVIEW_SOURCE_COERCION = Coercion(
    rule_id="autoformalize-review-source-to-internal",
    fn=_review_source_coerce,
    doc_phrases=(
        "coerced from external/both -- see autoprove",
        "--review-source=external requires interactive handoff",
    ),
    summary="Coerce --review-source=external|both to internal for unattended operation.",
)


# ---------------------------------------------------------------------------
# Autoformalize-specific cross-validations
# ---------------------------------------------------------------------------


def _source_required(
    flags: Mapping[str, object],
    ctx: ParseContext,
) -> list[str]:
    """--source is required; error if missing."""
    if not flags.get("--source"):
        return ["--source is required; error if missing."]
    return []


SOURCE_REQUIRED = CrossValidation(
    rule_id="autoformalize-source-required",
    fn=_source_required,
    severity="error",
    doc_phrases=("--source is required; error if missing.",),
    summary="Require --source for autoformalize.",
)


def _claim_select_required(
    flags: Mapping[str, object],
    ctx: ParseContext,
) -> list[str]:
    """--claim-select is required; error if missing."""
    if not flags.get("--claim-select"):
        return [
            "--claim-select is required; error if missing (no unattended guessing)."
        ]
    return []


CLAIM_SELECT_REQUIRED = CrossValidation(
    rule_id="autoformalize-claim-select-required",
    fn=_claim_select_required,
    severity="error",
    doc_phrases=(
        "--claim-select is required; error if missing (no unattended guessing).",
    ),
    summary="Require --claim-select for autoformalize.",
)


def _out_required(
    flags: Mapping[str, object],
    ctx: ParseContext,
) -> list[str]:
    """--out is required; error if missing."""
    if not flags.get("--out"):
        return [
            "--out is required when no existing target file is in scope; error if missing."
        ]
    return []


OUT_REQUIRED = CrossValidation(
    rule_id="autoformalize-out-required",
    fn=_out_required,
    severity="error",
    doc_phrases=(
        "--out is required when no existing target file is in scope; error if missing.",
    ),
    summary="Require --out for autoformalize.",
)


def _statement_policy_preserve_warn(
    flags: Mapping[str, object],
    ctx: ParseContext,
) -> list[str]:
    """--statement-policy=preserve warns that stuck redraft becomes manual."""
    if flags.get("--statement-policy") == "preserve":
        return [
            "--statement-policy=preserve: "
            "stuck redraft path becomes manual intervention, not automatic rewrite."
        ]
    return []


STATEMENT_POLICY_PRESERVE_WARNING = CrossValidation(
    rule_id="autoformalize-statement-policy-preserve-warning",
    fn=_statement_policy_preserve_warn,
    severity="warning",
    doc_phrases=(
        "--statement-policy=preserve is respected but warns: "
        "stuck redraft path becomes manual intervention, not automatic rewrite.",
    ),
    summary="Warn when --statement-policy=preserve (stuck redraft becomes manual).",
)


# ---------------------------------------------------------------------------
# Flag definitions
# ---------------------------------------------------------------------------

FLAG_SOURCE = FlagSpec(
    name="--source",
    type="freeform",
    default=None,
    enforcement="startup-validated",
    notes="File path, URL, or PDF for claim extraction. Required.",
)

FLAG_CLAIM_SELECT = FlagSpec(
    name="--claim-select",
    type="freeform",
    default=None,
    enforcement="startup-validated",
    notes='first | named:"..." | regex:"...". Required.',
)

FLAG_OUT = FlagSpec(
    name="--out",
    type="path",
    default=None,
    enforcement="startup-validated",
    notes="Target file for formalized claims. Required.",
)

FLAG_STATEMENT_POLICY = FlagSpec(
    name="--statement-policy",
    type="enum",
    enum_values=("preserve", "rewrite-generated-only", "adjacent-drafts"),
    default="rewrite-generated-only",
    enforcement="startup-validated",
)

FLAG_RIGOR = FlagSpec(
    name="--rigor",
    type="enum",
    enum_values=("sketch", "checked"),
    default="sketch",
    enforcement="startup-validated",
)

FLAG_DRAFT_MODE = FlagSpec(
    name="--draft-mode",
    type="enum",
    enum_values=("skeleton", "attempt"),
    default="skeleton",
    enforcement="startup-validated",
    notes="Passed to draft phase",
)

FLAG_DRAFT_ELAB_CHECK = FlagSpec(
    name="--draft-elab-check",
    type="enum",
    enum_values=("best-effort", "strict"),
    default="best-effort",
    enforcement="startup-validated",
    notes="Passed to draft phase",
)

FLAG_MAX_CYCLES = FlagSpec(
    name="--max-cycles",
    type="int",
    default=20,
    int_min=1,
    enforcement="session-enforced",
    notes="Per claim",
)

FLAG_MAX_TOTAL_RUNTIME = FlagSpec(
    name="--max-total-runtime",
    type="duration",
    default="120m",
    enforcement="best-effort",
    notes="Best-effort wall-clock session budget (per session)",
)

FLAG_MAX_STUCK_CYCLES = FlagSpec(
    name="--max-stuck-cycles",
    type="int",
    default=3,
    int_min=1,
    enforcement="session-enforced",
    notes="Per claim",
)

FLAG_DEEP = FlagSpec(
    name="--deep",
    type="enum",
    enum_values=("never", "stuck", "always"),
    default="stuck",
    enforcement="startup-validated",
)

FLAG_DEEP_SORRY_BUDGET = FlagSpec(
    name="--deep-sorry-budget",
    type="int",
    default=2,
    int_min=1,
    enforcement="session-enforced",
)

FLAG_DEEP_TIME_BUDGET = FlagSpec(
    name="--deep-time-budget",
    type="duration",
    default="20m",
    enforcement="advisory",
    notes="Scopes deep-mode subagent work. Not tracked or enforced by session tracker.",
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
    default=2,
    int_min=1,
    enforcement="session-enforced",
)

FLAG_DEEP_MAX_LINES = FlagSpec(
    name="--deep-max-lines",
    type="int",
    default=200,
    int_min=1,
    enforcement="session-enforced",
)

FLAG_DEEP_REGRESSION_GATE = FlagSpec(
    name="--deep-regression-gate",
    type="enum",
    enum_values=("strict", "off"),
    default="strict",
    enforcement="startup-validated",
)

FLAG_COMMIT = FlagSpec(
    name="--commit",
    type="enum",
    enum_values=("auto", "never"),
    default="auto",
    enforcement="startup-validated",
)

FLAG_GOLF = FlagSpec(
    name="--golf",
    type="enum",
    enum_values=("prompt", "auto", "never"),
    default="never",
    enforcement="startup-validated",
)

FLAG_REVIEW_SOURCE = FlagSpec(
    name="--review-source",
    type="enum",
    enum_values=("internal", "external", "both", "none"),
    default="internal",
    enforcement="startup-validated",
    coerce=REVIEW_SOURCE_COERCION,
    notes="Coerced from external/both to internal (see autoprove docs)",
)

FLAG_REVIEW_EVERY = FlagSpec(
    name="--review-every",
    type="freeform",
    default="checkpoint",
    enforcement="startup-validated",
    notes="N (sorries), checkpoint, or never",
)


# ---------------------------------------------------------------------------
# Spec
# ---------------------------------------------------------------------------

SPEC = CommandSpec(
    name="autoformalize",
    positionals=(),
    flags=(
        FLAG_SOURCE,
        FLAG_CLAIM_SELECT,
        FLAG_OUT,
        FLAG_STATEMENT_POLICY,
        FLAG_RIGOR,
        FLAG_DRAFT_MODE,
        FLAG_DRAFT_ELAB_CHECK,
        FLAG_MAX_CYCLES,
        FLAG_MAX_TOTAL_RUNTIME,
        FLAG_MAX_STUCK_CYCLES,
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
        FLAG_COMMIT,
        FLAG_GOLF,
        FLAG_REVIEW_SOURCE,
        FLAG_REVIEW_EVERY,
    ),
    cross_validations=(
        SOURCE_REQUIRED,
        CLAIM_SELECT_REQUIRED,
        OUT_REQUIRED,
        STATEMENT_POLICY_PRESERVE_WARNING,
    ),
)

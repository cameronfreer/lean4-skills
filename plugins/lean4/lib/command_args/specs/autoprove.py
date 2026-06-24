"""Spec for /lean4:autoprove — autonomous multi-cycle theorem proving."""

from __future__ import annotations

from collections.abc import Mapping

from ..types import (
    Coercion,
    CommandSpec,
    CrossValidation,
    FlagSpec,
    ParseContext,
    PositionalSpec,
)

# ---------------------------------------------------------------------------
# Autoprove-specific coercions
# ---------------------------------------------------------------------------


def _commit_ask_coerce(
    value: object,
    flags: Mapping[str, object],
    ctx: ParseContext,
) -> tuple[object, str | None]:
    """--commit=ask -> coerced to auto (no interactive confirmation)."""
    if value == "ask":
        return "auto", (
            "--commit=ask requires interactive confirmation. "
            "Using auto for unattended operation."
        )
    return value, None


COMMIT_ASK_COERCION = Coercion(
    rule_id="autoprove-commit-ask-to-auto",
    fn=_commit_ask_coerce,
    doc_phrases=(
        "--commit=ask requires interactive confirmation. Using auto for unattended operation.",
        "--commit=ask is coerced to auto",
    ),
    summary="Coerce --commit=ask to auto for unattended autoprove.",
)


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
    rule_id="autoprove-review-source-to-internal",
    fn=_review_source_coerce,
    doc_phrases=(
        "--review-source=external requires interactive handoff. "
        "Using internal review for unattended operation.",
        "autoprove coerces to internal at startup",
    ),
    summary="Coerce --review-source=external|both to internal for unattended operation.",
)


def _deep_ask_coerce(
    value: object,
    flags: Mapping[str, object],
    ctx: ParseContext,
) -> tuple[object, str | None]:
    """--deep=ask -> coerced to stuck (no interactive prompting)."""
    if value == "ask":
        return "stuck", (
            "--deep=ask requires interactive prompting. "
            "Using stuck for unattended operation."
        )
    return value, None


DEEP_ASK_COERCION = Coercion(
    rule_id="autoprove-deep-ask-to-stuck",
    fn=_deep_ask_coerce,
    doc_phrases=(
        "ask is coerced to stuck (no interactive prompting in autoprove)",
        "`ask` coerced to `stuck`",
    ),
    summary="Coerce --deep=ask to stuck for unattended autoprove.",
)


def _deep_rollback_never_coerce(
    value: object,
    flags: Mapping[str, object],
    ctx: ParseContext,
) -> tuple[object, str | None]:
    """--deep-rollback=never -> coerced to on-regression (safety)."""
    if value == "never":
        return "on-regression", (
            "--deep-rollback=never is unsafe. Using on-regression for safety."
        )
    return value, None


DEEP_ROLLBACK_NEVER_COERCION = Coercion(
    rule_id="autoprove-deep-rollback-never-to-on-regression",
    fn=_deep_rollback_never_coerce,
    doc_phrases=(
        "--deep-rollback=never -> coerced to on-regression",
        "Deep safety coercions",
    ),
    summary="Coerce --deep-rollback=never to on-regression for safety.",
)


def _deep_regression_gate_off_coerce(
    value: object,
    flags: Mapping[str, object],
    ctx: ParseContext,
) -> tuple[object, str | None]:
    """--deep-regression-gate=off -> coerced to strict (safety)."""
    if value == "off":
        return "strict", (
            "--deep-regression-gate=off is unsafe. Using strict for safety."
        )
    return value, None


DEEP_REGRESSION_GATE_OFF_COERCION = Coercion(
    rule_id="autoprove-deep-regression-gate-off-to-strict",
    fn=_deep_regression_gate_off_coerce,
    doc_phrases=(
        "--deep-regression-gate=off -> coerced to strict",
        "Deep safety coercions",
    ),
    summary="Coerce --deep-regression-gate=off to strict for safety.",
)


# ---------------------------------------------------------------------------
# Autoprove-specific cross-validations
# ---------------------------------------------------------------------------


def _statement_policy_preserve_warn(
    flags: Mapping[str, object],
    ctx: ParseContext,
) -> list[str]:
    """--statement-policy=preserve warns that stuck restage becomes manual."""
    formalize = flags.get("--formalize")
    policy = flags.get("--statement-policy")
    if policy == "preserve" and formalize in ("restage", "auto"):
        return [
            "--statement-policy=preserve with --formalize: "
            "stuck restage becomes manual intervention, not automatic rewrite."
        ]
    return []


STATEMENT_POLICY_PRESERVE_WARNING = CrossValidation(
    rule_id="autoprove-statement-policy-preserve-warning",
    fn=_statement_policy_preserve_warn,
    severity="warning",
    doc_phrases=(
        "Explicit --statement-policy=preserve is respected but warns: "
        "stuck restage becomes manual intervention, not automatic rewrite.",
    ),
    summary="Warn when --statement-policy=preserve with active formalize mode.",
)


def _formalize_auto_requires_source(
    flags: Mapping[str, object],
    ctx: ParseContext,
) -> list[str]:
    """--formalize=auto requires --source."""
    if flags.get("--formalize") == "auto" and not flags.get("--source"):
        return ["--formalize=auto requires --source; error if missing."]
    return []


FORMALIZE_AUTO_REQUIRES_SOURCE = CrossValidation(
    rule_id="autoprove-formalize-auto-requires-source",
    fn=_formalize_auto_requires_source,
    severity="error",
    doc_phrases=("--formalize=auto requires --source; error if missing.",),
    summary="Require --source when --formalize=auto.",
)


def _formalize_auto_requires_claim_select(
    flags: Mapping[str, object],
    ctx: ParseContext,
) -> list[str]:
    """--formalize=auto with --source requires --claim-select."""
    formalize = flags.get("--formalize")
    source = flags.get("--source")
    claim_select = flags.get("--claim-select")
    if formalize == "auto" and source and not claim_select:
        return [
            "--formalize=auto with --source requires --claim-select; "
            "error if missing (no unattended guessing)."
        ]
    return []


FORMALIZE_AUTO_REQUIRES_CLAIM_SELECT = CrossValidation(
    rule_id="autoprove-formalize-auto-requires-claim-select",
    fn=_formalize_auto_requires_claim_select,
    severity="error",
    doc_phrases=(
        "--formalize=auto with --source requires --claim-select; "
        "error if missing (no unattended guessing).",
    ),
    summary="Require --claim-select when --formalize=auto with --source.",
)


def _formalize_auto_requires_formalize_out(
    flags: Mapping[str, object],
    ctx: ParseContext,
) -> list[str]:
    """--formalize=auto requires --formalize-out."""
    if flags.get("--formalize") == "auto" and not flags.get("--formalize-out"):
        return [
            "--formalize=auto requires --formalize-out when no existing "
            "target file is in scope; error if missing."
        ]
    return []


FORMALIZE_AUTO_REQUIRES_FORMALIZE_OUT = CrossValidation(
    rule_id="autoprove-formalize-auto-requires-formalize-out",
    fn=_formalize_auto_requires_formalize_out,
    severity="error",
    doc_phrases=(
        "--formalize=auto requires --formalize-out when no existing target file is in scope",
    ),
    summary="Require --formalize-out when --formalize=auto.",
)


def _formalize_restage_ignores_source(
    flags: Mapping[str, object],
    ctx: ParseContext,
) -> list[str]:
    """--formalize=restage ignores --source (warn if provided)."""
    if flags.get("--formalize") == "restage" and flags.get("--source"):
        return ["--formalize=restage ignores --source (operates on existing scope)."]
    return []


FORMALIZE_RESTAGE_IGNORES_SOURCE = CrossValidation(
    rule_id="autoprove-formalize-restage-ignores-source",
    fn=_formalize_restage_ignores_source,
    severity="warning",
    doc_phrases=(
        "--formalize=restage does NOT require --source",
        "--source is ignored if provided (warn)",
    ),
    summary="Warn that --formalize=restage ignores --source.",
)


def _formalize_never_ignores_source(
    flags: Mapping[str, object],
    ctx: ParseContext,
) -> list[str]:
    """--formalize=never ignores --source (warn if provided)."""
    if flags.get("--formalize") == "never" and flags.get("--source"):
        return ["--formalize=never ignores --source."]
    return []


FORMALIZE_NEVER_IGNORES_SOURCE = CrossValidation(
    rule_id="autoprove-formalize-never-ignores-source",
    fn=_formalize_never_ignores_source,
    severity="warning",
    doc_phrases=("--formalize=never ignores --source (warn if provided)",),
    summary="Warn that --formalize=never ignores --source.",
)


def _statement_policy_formalize_coerce(
    value: object,
    flags: Mapping[str, object],
    ctx: ParseContext,
) -> tuple[object, str | None]:
    """--formalize=restage|auto with preserve default -> rewrite-generated-only."""
    formalize = flags.get("--formalize")
    if value == "preserve" and formalize in ("restage", "auto"):
        return "rewrite-generated-only", (
            "--statement-policy defaulted to preserve but --formalize="
            f"{formalize} active; coercing to rewrite-generated-only."
        )
    return value, None


STATEMENT_POLICY_FORMALIZE_COERCION = Coercion(
    rule_id="autoprove-statement-policy-formalize-default-coerce",
    fn=_statement_policy_formalize_coerce,
    doc_phrases=(
        "--formalize=restage|auto with default --statement-policy coerces "
        "preserve -> rewrite-generated-only at startup (warn)",
    ),
    summary="Coerce --statement-policy default from preserve to rewrite-generated-only when formalize active.",
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
    enum_values=("on", "off"),
    default="on",
    enforcement="startup-validated",
)

FLAG_REVIEW_SOURCE = FlagSpec(
    name="--review-source",
    type="enum",
    enum_values=("internal", "external", "both", "none"),
    default="internal",
    enforcement="startup-validated",
    coerce=REVIEW_SOURCE_COERCION,
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
    default="stuck",
    enforcement="startup-validated",
    coerce=DEEP_ASK_COERCION,
    notes="ask coerced to stuck for unattended operation",
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

FLAG_MAX_CONSECUTIVE_DEEP_CYCLES = FlagSpec(
    name="--max-consecutive-deep-cycles",
    type="int",
    default=2,
    int_min=1,
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
    coerce=DEEP_ROLLBACK_NEVER_COERCION,
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
    coerce=DEEP_REGRESSION_GATE_OFF_COERCION,
)

FLAG_BATCH_SIZE = FlagSpec(
    name="--batch-size",
    type="int",
    default=2,
    int_min=1,
    enforcement="advisory",
    notes="Sorries to attempt per cycle (advisory)",
)

FLAG_COMMIT = FlagSpec(
    name="--commit",
    type="enum",
    enum_values=("auto", "ask", "never"),
    default="auto",
    enforcement="startup-validated",
    coerce=COMMIT_ASK_COERCION,
    notes="ask coerced to auto for unattended operation",
)

FLAG_GOLF = FlagSpec(
    name="--golf",
    type="enum",
    enum_values=("prompt", "auto", "never"),
    default="never",
    enforcement="startup-validated",
)

FLAG_MAX_CYCLES = FlagSpec(
    name="--max-cycles",
    type="int",
    default=20,
    int_min=1,
    enforcement="session-enforced",
)

FLAG_MAX_TOTAL_RUNTIME = FlagSpec(
    name="--max-total-runtime",
    type="duration",
    default="120m",
    enforcement="best-effort",
    notes="Best-effort wall-clock session budget",
)

FLAG_MAX_STUCK_CYCLES = FlagSpec(
    name="--max-stuck-cycles",
    type="int",
    default=3,
    int_min=1,
    enforcement="session-enforced",
)

FLAG_FORMALIZE = FlagSpec(
    name="--formalize",
    type="enum",
    enum_values=("never", "restage", "auto"),
    default="never",
    enforcement="startup-validated",
    notes="deprecated: use /lean4:autoformalize",
)

FLAG_SOURCE = FlagSpec(
    name="--source",
    type="freeform",
    default=None,
    enforcement="startup-validated",
    notes="File path, URL, or PDF for claim extraction. Required when --formalize=auto. (deprecated)",
)

FLAG_CLAIM_SELECT = FlagSpec(
    name="--claim-select",
    type="freeform",
    default=None,
    enforcement="startup-validated",
    notes='first | named:"..." | regex:"...". Required when --formalize=auto. (deprecated)',
)

FLAG_FORMALIZE_RIGOR = FlagSpec(
    name="--formalize-rigor",
    type="enum",
    enum_values=("sketch", "checked"),
    default="sketch",
    enforcement="startup-validated",
    notes="deprecated: use /lean4:autoformalize --rigor",
)

FLAG_STATEMENT_POLICY = FlagSpec(
    name="--statement-policy",
    type="enum",
    enum_values=("preserve", "rewrite-generated-only", "adjacent-drafts"),
    default="preserve",
    enforcement="startup-validated",
    coerce=STATEMENT_POLICY_FORMALIZE_COERCION,
    notes="Default becomes rewrite-generated-only when --formalize=restage|auto. (deprecated)",
)

FLAG_FORMALIZE_OUT = FlagSpec(
    name="--formalize-out",
    type="path",
    default=None,
    enforcement="startup-validated",
    notes="Target file for formalized claims. Required if no existing target in scope. (deprecated)",
)


# ---------------------------------------------------------------------------
# Spec
# ---------------------------------------------------------------------------

SPEC = CommandSpec(
    name="autoprove",
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
        FLAG_MAX_CONSECUTIVE_DEEP_CYCLES,
        FLAG_DEEP_SNAPSHOT,
        FLAG_DEEP_ROLLBACK,
        FLAG_DEEP_SCOPE,
        FLAG_DEEP_MAX_FILES,
        FLAG_DEEP_MAX_LINES,
        FLAG_DEEP_REGRESSION_GATE,
        FLAG_BATCH_SIZE,
        FLAG_COMMIT,
        FLAG_GOLF,
        FLAG_MAX_CYCLES,
        FLAG_MAX_TOTAL_RUNTIME,
        FLAG_MAX_STUCK_CYCLES,
        FLAG_FORMALIZE,
        FLAG_SOURCE,
        FLAG_CLAIM_SELECT,
        FLAG_FORMALIZE_RIGOR,
        FLAG_STATEMENT_POLICY,
        FLAG_FORMALIZE_OUT,
    ),
    cross_validations=(
        STATEMENT_POLICY_PRESERVE_WARNING,
        FORMALIZE_AUTO_REQUIRES_SOURCE,
        FORMALIZE_AUTO_REQUIRES_CLAIM_SELECT,
        FORMALIZE_AUTO_REQUIRES_FORMALIZE_OUT,
        FORMALIZE_RESTAGE_IGNORES_SOURCE,
        FORMALIZE_NEVER_IGNORES_SOURCE,
    ),
)

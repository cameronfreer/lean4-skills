"""Named coercion and cross-validation functions for all lean4 slash commands.

Every function here encodes a parser-decidable rule documented in the
command markdown files under ``plugins/lean4/commands/*.md``.

**Naming convention:**

* ``snake_case`` — bare callable (CoerceFn or ValidateFn).  These are what
  ``Coercion.fn`` / ``CrossValidation.fn`` fields expect.
* ``UPPER_CASE`` — the corresponding ``Coercion`` or ``CrossValidation``
  record, ready to attach to a ``FlagSpec`` or ``CommandSpec``.

Coercion functions have signature:
    (value, options, ctx) -> (new_value, optional_note)

Validation functions have signature:
    (options, ctx) -> list[str]
"""

from __future__ import annotations

import os
from collections.abc import Mapping

from .types import Coercion, CrossValidation, ParseContext

# ═══════════════════════════════════════════════════════════════════════════
# Coercion callables + records
# ═══════════════════════════════════════════════════════════════════════════


# -- commit_ask_to_auto ----------------------------------------------------


def commit_ask_to_auto(
    value: object,
    options: Mapping[str, object],
    ctx: ParseContext,
) -> tuple[object, str | None]:
    """autoprove: --commit=ask -> auto (no interactive prompting)."""
    if value == "ask":
        return (
            "auto",
            "\u26a0 --commit=ask requires interactive confirmation. "
            "Using auto for unattended operation.",
        )
    return value, None


COMMIT_ASK_TO_AUTO = Coercion(
    rule_id="commit_ask_to_auto",
    fn=commit_ask_to_auto,
    doc_phrases=(
        "--commit=ask requires interactive confirmation",
        "ask` coerced to `auto",
    ),
    summary="autoprove: coerce --commit=ask to auto for unattended operation",
)


# -- review_source_external_to_internal ------------------------------------


def review_source_external_to_internal(
    value: object,
    options: Mapping[str, object],
    ctx: ParseContext,
) -> tuple[object, str | None]:
    """autoprove/autoformalize: --review-source=external|both -> internal."""
    if value in ("external", "both"):
        return (
            "internal",
            f"\u26a0 --review-source={value} requires interactive handoff. "
            "Using internal review for unattended operation.",
        )
    return value, None


REVIEW_SOURCE_EXTERNAL_TO_INTERNAL = Coercion(
    rule_id="review_source_external_to_internal",
    fn=review_source_external_to_internal,
    doc_phrases=(
        "--review-source=external requires interactive handoff",
        "coerces to `internal`",
    ),
    summary="autoprove/autoformalize: coerce external/both review to internal",
)


# -- deep_ask_to_stuck -----------------------------------------------------


def deep_ask_to_stuck(
    value: object,
    options: Mapping[str, object],
    ctx: ParseContext,
) -> tuple[object, str | None]:
    """autoprove: --deep=ask -> stuck (no interactive prompting)."""
    if value == "ask":
        return (
            "stuck",
            "\u26a0 --deep=ask requires interactive prompting. "
            "Using stuck for unattended operation.",
        )
    return value, None


DEEP_ASK_TO_STUCK = Coercion(
    rule_id="deep_ask_to_stuck",
    fn=deep_ask_to_stuck,
    doc_phrases=(
        "`ask` coerced to `stuck`",
        "ask` is coerced to `stuck`",
    ),
    summary="autoprove: coerce --deep=ask to stuck for unattended operation",
)


# -- deep_rollback_safety --------------------------------------------------


def deep_rollback_safety(
    value: object,
    options: Mapping[str, object],
    ctx: ParseContext,
) -> tuple[object, str | None]:
    """autoprove: --deep-rollback=never -> on-regression (safety)."""
    if value == "never":
        return (
            "on-regression",
            "\u26a0 --deep-rollback=never is unsafe for autonomous operation. "
            "Coerced to on-regression.",
        )
    return value, None


DEEP_ROLLBACK_SAFETY = Coercion(
    rule_id="deep_rollback_safety",
    fn=deep_rollback_safety,
    doc_phrases=(
        "--deep-rollback=never",
        "coerced to `on-regression`",
    ),
    summary="autoprove: coerce --deep-rollback=never to on-regression",
)


# -- deep_regression_gate_safety -------------------------------------------


def deep_regression_gate_safety(
    value: object,
    options: Mapping[str, object],
    ctx: ParseContext,
) -> tuple[object, str | None]:
    """autoprove: --deep-regression-gate=off -> strict (safety)."""
    if value == "off":
        return (
            "strict",
            "\u26a0 --deep-regression-gate=off is unsafe for autonomous operation. "
            "Coerced to strict.",
        )
    return value, None


DEEP_REGRESSION_GATE_SAFETY = Coercion(
    rule_id="deep_regression_gate_safety",
    fn=deep_regression_gate_safety,
    doc_phrases=(
        "--deep-regression-gate=off",
        "coerced to `strict`",
    ),
    summary="autoprove: coerce --deep-regression-gate=off to strict",
)


# -- intent_auto_collapse --------------------------------------------------


def intent_auto_collapse(
    value: object,
    options: Mapping[str, object],
    ctx: ParseContext,
) -> tuple[object, str | None]:
    """draft/formalize: --intent=auto -> usage (collapse internals/authoring).

    After inference, draft/formalize coerce internals/authoring to usage.
    At the parser level, auto is coerced to usage since the inference step
    will happen at runtime; the parser pre-collapses to usage.
    """
    if value == "auto":
        return (
            "usage",
            "\u26a0 --intent=auto coerced to usage "
            "(internals/authoring not defined for this command).",
        )
    if value in ("internals", "authoring"):
        return (
            "usage",
            f"\u26a0 --intent={value} coerced to usage (not defined for this command).",
        )
    return value, None


INTENT_AUTO_COLLAPSE = Coercion(
    rule_id="intent_auto_collapse",
    fn=intent_auto_collapse,
    doc_phrases=(
        "coerce `internals` \u2192 `usage` and `authoring` \u2192 `usage`",
        "intent=auto` inference",
    ),
    summary="draft/formalize: collapse --intent=auto/internals/authoring to usage",
)


# -- track_without_game_ignore ---------------------------------------------


def track_without_game_ignore(
    value: object,
    options: Mapping[str, object],
    ctx: ParseContext,
) -> tuple[object, str | None]:
    """learn: --track without --style=game -> coerce to None (warn + ignore)."""
    style = options.get("--style")
    if value is not None and style != "game":
        return (
            None,
            "\u26a0 --track is only valid with --style=game. Ignored.",
        )
    return value, None


TRACK_WITHOUT_GAME_IGNORE = Coercion(
    rule_id="track_without_game_ignore",
    fn=track_without_game_ignore,
    doc_phrases=(
        "--track` without `--style=game` \u2192 warn + ignore",
        "--track` without `--style=game`",
    ),
    summary="learn: ignore --track when --style is not game",
)


# -- scope_mathlib_coerce --------------------------------------------------


def scope_mathlib_coerce(
    value: object,
    options: Mapping[str, object],
    ctx: ParseContext,
) -> tuple[object, str | None]:
    """learn: --mode=mathlib + --scope=file|changed|project -> coerce to topic."""
    mode = options.get("--mode")
    if mode == "mathlib" and value in ("file", "changed", "project"):
        return (
            "topic",
            f"\u26a0 --scope={value} is not compatible with --mode=mathlib. "
            "Coerced to topic.",
        )
    return value, None


SCOPE_MATHLIB_COERCE = Coercion(
    rule_id="scope_mathlib_coerce",
    fn=scope_mathlib_coerce,
    doc_phrases=(
        "--mode=mathlib` + `--scope=file|changed|project` \u2192 warn + coerce to `topic`",
    ),
    summary="learn: coerce scope to topic when mode is mathlib",
)


# -- interactive_without_socratic_ignore -----------------------------------


def interactive_without_socratic_ignore(
    value: object,
    options: Mapping[str, object],
    ctx: ParseContext,
) -> tuple[object, str | None]:
    """learn: --interactive without --style=socratic -> coerce to False."""
    style = options.get("--style")
    if value is True and style != "socratic":
        return (
            False,
            "\u26a0 --interactive is only valid with --style=socratic. Ignored.",
        )
    return value, None


INTERACTIVE_WITHOUT_SOCRATIC_IGNORE = Coercion(
    rule_id="interactive_without_socratic_ignore",
    fn=interactive_without_socratic_ignore,
    doc_phrases=("Valid only with `--style=socratic`; ignored with warning otherwise",),
    summary="learn: ignore --interactive when --style is not socratic",
)


# -- formalize_statement_policy_coerce -------------------------------------


def formalize_statement_policy_coerce(
    value: object,
    options: Mapping[str, object],
    ctx: ParseContext,
) -> tuple[object, str | None]:
    """autoprove: --formalize=restage|auto with --statement-policy=preserve
    -> coerce to rewrite-generated-only."""
    formalize = options.get("--formalize")
    if formalize in ("restage", "auto") and value == "preserve":
        return (
            "rewrite-generated-only",
            "\u26a0 --statement-policy=preserve with --formalize="
            f"{formalize} coerced to rewrite-generated-only.",
        )
    return value, None


FORMALIZE_STATEMENT_POLICY_COERCE = Coercion(
    rule_id="formalize_statement_policy_coerce",
    fn=formalize_statement_policy_coerce,
    doc_phrases=(
        "coerces `preserve` \u2192 `rewrite-generated-only`",
        "--formalize=restage|auto` with default `--statement-policy`",
    ),
    summary="autoprove: coerce statement-policy from preserve when formalize active",
)


# ═══════════════════════════════════════════════════════════════════════════
# Cross-validation callables + records
# ═══════════════════════════════════════════════════════════════════════════


# -- topic_or_source_required ----------------------------------------------


def topic_or_source_required(
    options: Mapping[str, object],
    ctx: ParseContext,
) -> list[str]:
    """draft/formalize: at least one of topic or --source must be given.

    The parser stores positionals separately from options.  The positional
    ``topic`` presence is conveyed via the ``__positional_topic`` sentinel
    that the parser injects into the flags mapping at cross-validation time.
    """
    source = options.get("--source")
    topic_present = bool(options.get("__positional_topic"))
    if not source and not topic_present:
        return ["At least one of topic or --source must be given."]
    return []


TOPIC_OR_SOURCE_REQUIRED = CrossValidation(
    rule_id="topic_or_source_required",
    fn=topic_or_source_required,
    severity="error",
    doc_phrases=(
        "At least one of `topic` or `--source` must be given",
        "omitting both is a startup validation error",
    ),
    summary="draft/formalize: require topic or --source",
)


# -- output_file_requires_out ----------------------------------------------


def output_file_requires_out(
    options: Mapping[str, object],
    ctx: ParseContext,
) -> list[str]:
    """draft/learn/formalize: --output=file without --out -> error."""
    output = options.get("--output")
    out = options.get("--out")
    if output == "file" and not out:
        return ["--output=file requires --out to specify the target path."]
    return []


OUTPUT_FILE_REQUIRES_OUT = CrossValidation(
    rule_id="output_file_requires_out",
    fn=output_file_requires_out,
    severity="error",
    doc_phrases=(
        "--output=file` without `--out` \u2192 startup validation error",
        "Required when `--output=file`",
    ),
    summary="--output=file requires --out path",
)


# -- output_file_overwrite_check -------------------------------------------


def output_file_overwrite_check(
    options: Mapping[str, object],
    ctx: ParseContext,
) -> list[str]:
    """--output=file + existing target + no --overwrite -> error."""
    output = options.get("--output")
    out = options.get("--out")
    overwrite = options.get("--overwrite")
    if output == "file" and out:
        target = os.path.join(ctx.cwd, str(out))
        if os.path.exists(target) and not overwrite:
            return [
                f"--output=file target {out!s} already exists. "
                "Use --overwrite to replace it."
            ]
    return []


OUTPUT_FILE_OVERWRITE_CHECK = CrossValidation(
    rule_id="output_file_overwrite_check",
    fn=output_file_overwrite_check,
    severity="error",
    doc_phrases=(
        "--output=file` with existing target and no `--overwrite` \u2192 startup validation error",
        "existing target \u2192 startup validation error",
    ),
    summary="block file overwrite without --overwrite flag",
)


# -- statement_policy_preserve_warning -------------------------------------


def statement_policy_preserve_warning(
    options: Mapping[str, object],
    ctx: ParseContext,
) -> list[str]:
    """autoformalize/autoprove: --statement-policy=preserve -> warn."""
    policy = options.get("--statement-policy")
    if policy == "preserve":
        return [
            "\u26a0 --statement-policy=preserve: stuck redraft path becomes "
            "manual intervention, not automatic rewrite."
        ]
    return []


STATEMENT_POLICY_PRESERVE_WARNING = CrossValidation(
    rule_id="statement_policy_preserve_warning",
    fn=statement_policy_preserve_warning,
    severity="warning",
    doc_phrases=(
        "--statement-policy=preserve` is respected but warns",
        "stuck redraft path becomes manual intervention",
    ),
    summary="warn that preserve policy limits autonomous redrafting",
)


# -- source_overrides_scope_warning ----------------------------------------


def source_overrides_scope_warning(
    options: Mapping[str, object],
    ctx: ParseContext,
) -> list[str]:
    """learn: --source + --scope=file|changed|project -> warn."""
    source = options.get("--source")
    scope = options.get("--scope")
    if source and scope in ("file", "changed", "project"):
        return ["\u26a0 --source overrides --scope for initial discovery."]
    return []


SOURCE_OVERRIDES_SCOPE_WARNING = CrossValidation(
    rule_id="source_overrides_scope_warning",
    fn=source_overrides_scope_warning,
    severity="warning",
    doc_phrases=(
        "--source` + `--scope=file|changed|project` \u2192 warn",
        "source overrides scope for initial discovery",
    ),
    summary="learn: warn that --source overrides --scope",
)


# -- claim_select_requires_source ------------------------------------------


def claim_select_requires_source(
    options: Mapping[str, object],
    ctx: ParseContext,
) -> list[str]:
    """draft/formalize: --claim-select without --source -> error."""
    claim_select = options.get("--claim-select")
    source = options.get("--source")
    if claim_select is not None and not source:
        return ["--claim-select requires --source (nothing to select from)."]
    return []


CLAIM_SELECT_REQUIRES_SOURCE = CrossValidation(
    rule_id="claim_select_requires_source",
    fn=claim_select_requires_source,
    severity="error",
    doc_phrases=(
        "--claim-select` without `--source` \u2192 startup validation error",
        "nothing to select from",
    ),
    summary="--claim-select requires --source",
)


# -- formalize_auto_requires_source ----------------------------------------


def formalize_auto_requires_source(
    options: Mapping[str, object],
    ctx: ParseContext,
) -> list[str]:
    """autoprove: --formalize=auto requires --source."""
    formalize = options.get("--formalize")
    source = options.get("--source")
    if formalize == "auto" and not source:
        return ["--formalize=auto requires --source."]
    return []


FORMALIZE_AUTO_REQUIRES_SOURCE = CrossValidation(
    rule_id="formalize_auto_requires_source",
    fn=formalize_auto_requires_source,
    severity="error",
    doc_phrases=("--formalize=auto` requires `--source`",),
    summary="autoprove: --formalize=auto requires --source",
)


# -- formalize_auto_requires_claim_select ----------------------------------


def formalize_auto_requires_claim_select(
    options: Mapping[str, object],
    ctx: ParseContext,
) -> list[str]:
    """autoprove: --formalize=auto with --source requires --claim-select."""
    formalize = options.get("--formalize")
    source = options.get("--source")
    claim_select = options.get("--claim-select")
    if formalize == "auto" and source and not claim_select:
        return ["--formalize=auto with --source requires --claim-select."]
    return []


FORMALIZE_AUTO_REQUIRES_CLAIM_SELECT = CrossValidation(
    rule_id="formalize_auto_requires_claim_select",
    fn=formalize_auto_requires_claim_select,
    severity="error",
    doc_phrases=(
        "--formalize=auto` with `--source` requires `--claim-select`",
        "no unattended guessing",
    ),
    summary="autoprove: --formalize=auto requires --claim-select",
)


# -- formalize_auto_requires_out -------------------------------------------


def formalize_auto_requires_out(
    options: Mapping[str, object],
    ctx: ParseContext,
) -> list[str]:
    """autoprove: --formalize=auto requires --formalize-out."""
    formalize = options.get("--formalize")
    out = options.get("--formalize-out")
    if formalize == "auto" and not out:
        return [
            "--formalize=auto requires --formalize-out when no existing "
            "target file is in scope."
        ]
    return []


FORMALIZE_AUTO_REQUIRES_OUT = CrossValidation(
    rule_id="formalize_auto_requires_out",
    fn=formalize_auto_requires_out,
    severity="error",
    doc_phrases=("--formalize=auto` requires `--formalize-out`",),
    summary="autoprove: --formalize=auto requires --formalize-out",
)


# -- formalize_restage_source_warning --------------------------------------


def formalize_restage_source_warning(
    options: Mapping[str, object],
    ctx: ParseContext,
) -> list[str]:
    """autoprove: --formalize=restage + --source -> warn (source ignored)."""
    formalize = options.get("--formalize")
    source = options.get("--source")
    if formalize == "restage" and source:
        return ["\u26a0 --source is ignored with --formalize=restage."]
    return []


FORMALIZE_RESTAGE_SOURCE_WARNING = CrossValidation(
    rule_id="formalize_restage_source_warning",
    fn=formalize_restage_source_warning,
    severity="warning",
    doc_phrases=(
        "--formalize=restage` does NOT require `--source`",
        "`--source` is ignored if provided (warn)",
    ),
    summary="autoprove: warn that --source is ignored with --formalize=restage",
)


# -- formalize_never_source_warning ----------------------------------------


def formalize_never_source_warning(
    options: Mapping[str, object],
    ctx: ParseContext,
) -> list[str]:
    """autoprove: --formalize=never + --source -> warn (source ignored)."""
    formalize = options.get("--formalize")
    source = options.get("--source")
    if formalize == "never" and source:
        return ["\u26a0 --source is ignored without --formalize."]
    return []


FORMALIZE_NEVER_SOURCE_WARNING = CrossValidation(
    rule_id="formalize_never_source_warning",
    fn=formalize_never_source_warning,
    severity="warning",
    doc_phrases=("--formalize=never` ignores `--source` (warn if provided)",),
    summary="autoprove: warn that --source is ignored without --formalize",
)


# -- autoformalize_source_required -----------------------------------------


def autoformalize_source_required(
    options: Mapping[str, object],
    ctx: ParseContext,
) -> list[str]:
    """autoformalize: --source is required."""
    source = options.get("--source")
    if not source:
        return ["--source is required for autoformalize."]
    return []


AUTOFORMALIZE_SOURCE_REQUIRED = CrossValidation(
    rule_id="autoformalize_source_required",
    fn=autoformalize_source_required,
    severity="error",
    doc_phrases=("--source` is required",),
    summary="autoformalize: require --source",
)


# -- autoformalize_claim_select_required -----------------------------------


def autoformalize_claim_select_required(
    options: Mapping[str, object],
    ctx: ParseContext,
) -> list[str]:
    """autoformalize: --claim-select is required."""
    claim_select = options.get("--claim-select")
    if not claim_select:
        return ["--claim-select is required for autoformalize."]
    return []


AUTOFORMALIZE_CLAIM_SELECT_REQUIRED = CrossValidation(
    rule_id="autoformalize_claim_select_required",
    fn=autoformalize_claim_select_required,
    severity="error",
    doc_phrases=(
        "--claim-select` is required",
        "no unattended guessing",
    ),
    summary="autoformalize: require --claim-select",
)


# -- autoformalize_out_required --------------------------------------------


def autoformalize_out_required(
    options: Mapping[str, object],
    ctx: ParseContext,
) -> list[str]:
    """autoformalize: --out is required."""
    out = options.get("--out")
    if not out:
        return ["--out is required for autoformalize."]
    return []


AUTOFORMALIZE_OUT_REQUIRED = CrossValidation(
    rule_id="autoformalize_out_required",
    fn=autoformalize_out_required,
    severity="error",
    doc_phrases=("--out` is required",),
    summary="autoformalize: require --out",
)

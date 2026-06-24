"""Spec for /lean4:learn — interactive teaching and mathlib exploration."""

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
from . import _common

# ---------------------------------------------------------------------------
# Learn-specific coercions
# ---------------------------------------------------------------------------


def _track_without_game_coerce(
    value: object,
    flags: Mapping[str, object],
    ctx: ParseContext,
) -> tuple[object, str | None]:
    """--track without --style=game -> warn + reset to default (None)."""
    if flags.get("--style") != "game":
        return None, "--track ignored: only valid with --style=game"
    return value, None


TRACK_WITHOUT_GAME = Coercion(
    rule_id="learn-track-without-game-ignore",
    fn=_track_without_game_coerce,
    doc_phrases=(
        "--track without --style=game -> warn + ignore",
        "Valid only with --style=game; ignored with warning otherwise.",
    ),
    summary="Reset --track to default when --style is not game.",
)


def _interactive_without_socratic_coerce(
    value: object,
    flags: Mapping[str, object],
    ctx: ParseContext,
) -> tuple[object, str | None]:
    """--interactive without --style=socratic -> warn + reset to default (False)."""
    if flags.get("--style") != "socratic":
        return False, "--interactive ignored: only valid with --style=socratic"
    return value, None


INTERACTIVE_WITHOUT_SOCRATIC = Coercion(
    rule_id="learn-interactive-without-socratic-ignore",
    fn=_interactive_without_socratic_coerce,
    doc_phrases=(
        "--interactive without --style=socratic -> warn + ignore",
        "Valid only with --style=socratic; ignored with warning otherwise.",
    ),
    summary="Reset --interactive to False when --style is not socratic.",
)


# ---------------------------------------------------------------------------
# Learn-specific cross-validations
# ---------------------------------------------------------------------------


def _source_overrides_scope_validate(
    flags: Mapping[str, object],
    ctx: ParseContext,
) -> list[str]:
    """--source + --scope=file|changed|project -> warning."""
    source = flags.get("--source")
    scope = flags.get("--scope")
    if source and scope in ("file", "changed", "project"):
        return ["--source overrides --scope for initial discovery"]
    return []


SOURCE_OVERRIDES_SCOPE = CrossValidation(
    rule_id="learn-source-overrides-scope",
    fn=_source_overrides_scope_validate,
    severity="warning",
    doc_phrases=(
        '--source + --scope=file|changed|project -> warn "source overrides scope for initial discovery"',
    ),
    summary="Warn that --source takes priority over file/changed/project scope.",
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
    rule_id="learn-output-file-requires-out",
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
    rule_id="learn-overwrite-check",
    fn=_overwrite_check_validate,
    severity="error",
    doc_phrases=(
        "--output=file with existing target and no --overwrite -> startup validation error",
    ),
    summary="Block overwrite of existing output file unless --overwrite is set.",
)


# ---------------------------------------------------------------------------
# Learn-specific flags
# ---------------------------------------------------------------------------

FLAG_MODE = FlagSpec(
    name="--mode",
    type="enum",
    enum_values=("auto", "repo", "mathlib"),
    default="auto",
    enforcement="startup-validated",
    notes="auto resolves from topic after mode-resolution step",
)

FLAG_LEVEL = _common.FLAG_LEVEL

FLAG_SCOPE = FlagSpec(
    name="--scope",
    type="enum",
    enum_values=("auto", "file", "changed", "project", "topic"),
    default="auto",
    enforcement="startup-validated",
    notes="Defaults depend on resolved --mode; see scope-defaults-by-mode table",
)

FLAG_STYLE = FlagSpec(
    name="--style",
    type="enum",
    enum_values=("tour", "socratic", "exercise", "game"),
    default="tour",
    enforcement="startup-validated",
)

FLAG_OUTPUT = _common.FLAG_OUTPUT
FLAG_OUT = _common.FLAG_OUT
FLAG_OVERWRITE = _common.FLAG_OVERWRITE

FLAG_INTERACTIVE = FlagSpec(
    name="--interactive",
    type="bool",
    default=False,
    enforcement="startup-validated",
    coerce=INTERACTIVE_WITHOUT_SOCRATIC,
    notes="True Socratic method; valid only with --style=socratic",
)

FLAG_INTENT = _common.FLAG_INTENT_LEARN

FLAG_PRESENTATION = _common.FLAG_PRESENTATION

FLAG_VERIFY = _common.FLAG_VERIFY

FLAG_TRACK = FlagSpec(
    name="--track",
    type="enum",
    enum_values=("nng-like", "set-theory-like", "analysis-like", "proofs-reintro"),
    default=None,
    enforcement="startup-validated",
    coerce=TRACK_WITHOUT_GAME,
    notes="Exercise ladder; valid only with --style=game",
)

FLAG_SOURCE = _common.FLAG_SOURCE

FLAG_ADAPTIVE = FlagSpec(
    name="--adaptive",
    type="enum",
    enum_values=("on", "off"),
    default="on",
    enforcement="startup-validated",
    notes="Controls whether the debate can change style/level mid-session",
)


# ---------------------------------------------------------------------------
# Spec
# ---------------------------------------------------------------------------

SPEC = CommandSpec(
    name="learn",
    positionals=(
        PositionalSpec(
            name="topic",
            required=False,
            notes=(
                "Free-text topic, theorem name, file path, or natural-language claim. "
                "If omitted, start conversational discovery."
            ),
        ),
    ),
    flags=(
        FLAG_MODE,
        FLAG_LEVEL,
        FLAG_SCOPE,
        FLAG_STYLE,
        FLAG_OUTPUT,
        FLAG_OUT,
        FLAG_OVERWRITE,
        FLAG_INTERACTIVE,
        FLAG_INTENT,
        FLAG_PRESENTATION,
        FLAG_VERIFY,
        FLAG_TRACK,
        FLAG_SOURCE,
        FLAG_ADAPTIVE,
    ),
    cross_validations=(
        SOURCE_OVERRIDES_SCOPE,
        OUTPUT_FILE_REQUIRES_OUT,
        OVERWRITE_CHECK,
    ),
)

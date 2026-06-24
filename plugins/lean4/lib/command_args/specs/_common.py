"""Shared FlagSpec fragments reused across multiple command specs.

Each function returns a FlagSpec (or list of FlagSpecs) so per-command
overrides can customize defaults, coercions, or enforcement classes.
"""

from __future__ import annotations

from ..types import Coercion, FlagSpec

# ---------------------------------------------------------------------------
# Output flags: --output, --out, --overwrite
# ---------------------------------------------------------------------------


def output_flag(
    *,
    default: str = "chat",
    enum_values: tuple[str, ...] = ("chat", "scratch", "file"),
) -> FlagSpec:
    """--output flag shared by draft, learn, formalize."""
    return FlagSpec(
        name="--output",
        type="enum",
        enum_values=enum_values,
        default=default,
        enforcement="startup-validated",
    )


def out_flag() -> FlagSpec:
    """--out path flag.  Required when --output=file (enforced by cross-validation)."""
    return FlagSpec(
        name="--out",
        type="path",
        default=None,
        enforcement="startup-validated",
        notes="Required when --output=file; enforced via cross-validation, not requires",
    )


def overwrite_flag() -> FlagSpec:
    """--overwrite flag."""
    return FlagSpec(
        name="--overwrite",
        type="bool",
        default=False,
        enforcement="startup-validated",
    )


# ---------------------------------------------------------------------------
# Intent / presentation
# ---------------------------------------------------------------------------


def intent_flag(
    *,
    default: str = "auto",
    enum_values: tuple[str, ...] = ("auto", "usage", "internals", "authoring", "math"),
    coerce: Coercion | None = None,
) -> FlagSpec:
    """--intent flag.  Default and enum_values vary by command."""
    return FlagSpec(
        name="--intent",
        type="enum",
        enum_values=enum_values,
        default=default,
        enforcement="startup-validated",
        coerce=coerce,
    )


def presentation_flag(*, default: str = "auto") -> FlagSpec:
    """--presentation flag."""
    return FlagSpec(
        name="--presentation",
        type="enum",
        enum_values=("informal", "supporting", "formal", "auto"),
        default=default,
        enforcement="startup-validated",
    )


# ---------------------------------------------------------------------------
# Source / claim-select
# ---------------------------------------------------------------------------


def source_flag(*, required: bool = False) -> FlagSpec:
    """--source flag for file/URL/PDF input."""
    return FlagSpec(
        name="--source",
        type="path",
        default=None,
        enforcement="startup-validated",
        notes="required" if required else "",
    )


def claim_select_flag(*, requires: tuple[str, ...] = ()) -> FlagSpec:
    """--claim-select noninteractive selection policy.

    ``requires`` is set only when the relationship is truly unconditional
    (e.g. in draft/formalize where --claim-select always needs --source).
    For autoformalize/autoprove where --claim-select is independently
    required, use a CrossValidation instead.
    """
    return FlagSpec(
        name="--claim-select",
        type="freeform",
        default=None,
        enforcement="startup-validated",
        requires=requires,
    )


# ---------------------------------------------------------------------------
# Deep-mode family
# ---------------------------------------------------------------------------


def deep_flag(
    *,
    default: str = "never",
    enum_values: tuple[str, ...] = ("never", "ask", "stuck", "always"),
    coerce: Coercion | None = None,
) -> FlagSpec:
    """--deep flag.  Default and coerce vary by command."""
    return FlagSpec(
        name="--deep",
        type="enum",
        enum_values=enum_values,
        default=default,
        enforcement="startup-validated",
        coerce=coerce,
    )


def deep_sorry_budget_flag(*, default: int = 1) -> FlagSpec:
    return FlagSpec(
        name="--deep-sorry-budget",
        type="int",
        default=default,
        int_min=1,
        enforcement="session-enforced",
    )


def deep_time_budget_flag(*, default: str = "10m") -> FlagSpec:
    return FlagSpec(
        name="--deep-time-budget",
        type="duration",
        default=default,
        enforcement="advisory",
        notes="Advisory: scopes deep-mode subagent work. Not tracked or enforced.",
    )


def max_deep_per_cycle_flag(*, default: int = 1) -> FlagSpec:
    return FlagSpec(
        name="--max-deep-per-cycle",
        type="int",
        default=default,
        int_min=1,
        enforcement="session-enforced",
    )


def deep_snapshot_flag(*, default: str = "stash") -> FlagSpec:
    return FlagSpec(
        name="--deep-snapshot",
        type="enum",
        enum_values=("stash",),
        default=default,
        enforcement="startup-validated",
        notes="V1: stash only",
    )


def deep_rollback_flag(
    *,
    default: str = "on-regression",
    coerce: Coercion | None = None,
) -> FlagSpec:
    return FlagSpec(
        name="--deep-rollback",
        type="enum",
        enum_values=("on-regression", "on-no-improvement", "always", "never"),
        default=default,
        enforcement="startup-validated",
        coerce=coerce,
    )


def deep_scope_flag(*, default: str = "target") -> FlagSpec:
    return FlagSpec(
        name="--deep-scope",
        type="enum",
        enum_values=("target", "cross-file"),
        default=default,
        enforcement="startup-validated",
    )


def deep_max_files_flag(*, default: int = 1) -> FlagSpec:
    return FlagSpec(
        name="--deep-max-files",
        type="int",
        default=default,
        int_min=1,
        enforcement="session-enforced",
    )


def deep_max_lines_flag(*, default: int = 120) -> FlagSpec:
    return FlagSpec(
        name="--deep-max-lines",
        type="int",
        default=default,
        int_min=1,
        enforcement="session-enforced",
    )


def deep_regression_gate_flag(
    *,
    default: str = "strict",
    coerce: Coercion | None = None,
) -> FlagSpec:
    return FlagSpec(
        name="--deep-regression-gate",
        type="enum",
        enum_values=("strict", "off"),
        default=default,
        enforcement="startup-validated",
        coerce=coerce,
    )


# ---------------------------------------------------------------------------
# Max-* family (session stop budgets)
# ---------------------------------------------------------------------------


def max_cycles_flag(*, default: int = 20) -> FlagSpec:
    return FlagSpec(
        name="--max-cycles",
        type="int",
        default=default,
        int_min=1,
        enforcement="session-enforced",
    )


def max_total_runtime_flag(*, default: str = "120m") -> FlagSpec:
    return FlagSpec(
        name="--max-total-runtime",
        type="duration",
        default=default,
        enforcement="best-effort",
        notes="Best-effort wall-clock session budget",
    )


def max_stuck_cycles_flag(*, default: int = 3) -> FlagSpec:
    return FlagSpec(
        name="--max-stuck-cycles",
        type="int",
        default=default,
        int_min=1,
        enforcement="session-enforced",
    )


# ---------------------------------------------------------------------------
# Common: --commit, --golf
# ---------------------------------------------------------------------------


def commit_flag(
    *,
    default: str = "ask",
    enum_values: tuple[str, ...] = ("ask", "auto", "never"),
    coerce: Coercion | None = None,
) -> FlagSpec:
    return FlagSpec(
        name="--commit",
        type="enum",
        enum_values=enum_values,
        default=default,
        enforcement="startup-validated",
        coerce=coerce,
    )


def golf_flag(
    *,
    default: str = "prompt",
    enum_values: tuple[str, ...] = ("prompt", "auto", "never"),
) -> FlagSpec:
    return FlagSpec(
        name="--golf",
        type="enum",
        enum_values=enum_values,
        default=default,
        enforcement="startup-validated",
    )


# ---------------------------------------------------------------------------
# Level flag (shared across draft, learn, formalize)
# ---------------------------------------------------------------------------


def level_flag(*, default: str = "intermediate") -> FlagSpec:
    return FlagSpec(
        name="--level",
        type="enum",
        enum_values=("beginner", "intermediate", "expert"),
        default=default,
        enforcement="startup-validated",
    )


def verify_flag(*, default: str = "best-effort") -> FlagSpec:
    return FlagSpec(
        name="--verify",
        type="enum",
        enum_values=("best-effort", "strict"),
        default=default,
        enforcement="startup-validated",
        notes="Verification strictness for key claims",
    )


# ---------------------------------------------------------------------------
# Module-level convenience constants
#
# Pre-instantiated FlagSpec objects for specs that use them as-is
# (e.g. learn.py, formalize.py).  Commands that need custom defaults or
# coercions should call the factory functions directly.
# ---------------------------------------------------------------------------

FLAG_LEVEL = level_flag()
FLAG_OUTPUT = output_flag()
FLAG_OUT = out_flag()
FLAG_OVERWRITE = overwrite_flag()
FLAG_PRESENTATION = presentation_flag()
FLAG_SOURCE = source_flag()
FLAG_VERIFY = verify_flag()

# learn uses the full 5-value intent enum with auto default
FLAG_INTENT_LEARN = intent_flag(
    default="auto",
    enum_values=("auto", "usage", "internals", "authoring", "math"),
)

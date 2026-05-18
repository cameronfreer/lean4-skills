"""Core data types for the lean4 slash-command parser."""

from __future__ import annotations

from collections.abc import Callable, Mapping
from dataclasses import dataclass, field
from typing import Literal

EnforcementClass = Literal[
    "startup-validated",
    "session-enforced",
    "best-effort",
    "advisory",
]

FlagType = Literal["bool", "enum", "int", "duration", "path", "freeform"]

Source = Literal["explicit", "default", "coerced"]

Severity = Literal["error", "warning"]


@dataclass(frozen=True)
class ParseContext:
    """Carries the user's workspace cwd through coercion/validation callables."""

    cwd: str  # absolute path to the user's workspace


# Bare callable signatures — wrapped in Coercion / CrossValidation records.
CoerceFn = Callable[
    [object, Mapping[str, object], ParseContext], tuple[object, str | None]
]
ValidateFn = Callable[[Mapping[str, object], ParseContext], list[str]]


@dataclass(frozen=True)
class Coercion:
    """A per-flag value-changing coercion rule with doc-sync metadata."""

    rule_id: str
    fn: CoerceFn
    doc_phrases: tuple[str, ...] = ()
    summary: str = ""
    # A Coercion ALWAYS changes the value and sets source="coerced".
    # "warn + ignore" is a coercion to spec.default.
    # For warning-only rules where value is UNCHANGED, use CrossValidation(severity="warning").


@dataclass(frozen=True)
class CrossValidation:
    """A multi-flag or warning-only validation rule with doc-sync metadata."""

    rule_id: str
    fn: ValidateFn
    severity: Severity = "error"
    doc_phrases: tuple[str, ...] = ()
    summary: str = ""
    # severity="error" → returned strings go to ParseResult.errors
    # severity="warning" → returned strings go to ParseResult.warnings
    # One CrossValidation is either entirely error-producing or entirely
    # warning-producing. Split into two records if a rule needs both.


@dataclass(frozen=True)
class FlagSpec:
    """Specification for a single command flag."""

    name: str
    aliases: tuple[str, ...] = ()
    type: FlagType = "freeform"
    enum_values: tuple[str, ...] = ()
    default: object = None
    enforcement: EnforcementClass = "startup-validated"
    requires: tuple[str, ...] = ()  # unconditional companion flags
    forbidden_with: tuple[str, ...] = ()
    coerce: Coercion | None = None
    int_min: int | None = None
    int_max: int | None = None
    notes: str = ""


@dataclass(frozen=True)
class PositionalSpec:
    """Specification for a positional argument."""

    name: str
    required: bool = False
    notes: str = ""


@dataclass(frozen=True)
class CommandSpec:
    """Full specification for a slash command's parser-decidable inputs."""

    name: str
    positionals: tuple[PositionalSpec, ...] = ()
    flags: tuple[FlagSpec, ...] = ()
    cross_validations: tuple[CrossValidation, ...] = ()


@dataclass(frozen=True)
class ResolvedFlag:
    """A single flag's resolved value with provenance metadata."""

    value: object
    source: Source
    enforcement: EnforcementClass
    coerced_from: object = None  # only set when source == "coerced"


@dataclass
class ParseResult:
    """The output of parse_invocation — a lossless representation of parsed inputs."""

    command: str
    raw_tail: str
    positionals: dict[str, str] = field(default_factory=dict)
    options: dict[str, ResolvedFlag] = field(default_factory=dict)
    coercions: list[str] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)
    errors: list[str] = field(default_factory=list)

    def to_dict(self) -> dict[str, object]:
        """Serialize to a plain dict for JSON output / artifact writing."""
        return {
            "command": self.command,
            "raw_tail": self.raw_tail,
            "positionals": dict(self.positionals),
            "options": {
                name: {
                    "value": rf.value,
                    "source": rf.source,
                    "enforcement": rf.enforcement,
                    **(
                        {"coerced_from": rf.coerced_from}
                        if rf.coerced_from is not None
                        else {}
                    ),
                }
                for name, rf in self.options.items()
            },
            "coercions": list(self.coercions),
            "warnings": list(self.warnings),
            "errors": list(self.errors),
        }

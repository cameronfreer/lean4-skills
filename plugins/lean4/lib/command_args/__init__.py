"""Host-agnostic slash-command parser for the lean4 plugin.

Public surface:
    COMMAND_SPECS     - dict of per-command specs
    parse_invocation  - runtime parser entry point
    format_validated_block  - ParseResult -> fenced markdown
    parse_validated_block   - fenced markdown -> ParseResult (inverse)
    ParseContext, ParseResult, ResolvedFlag, FlagSpec, CommandSpec,
    PositionalSpec, Coercion, CrossValidation, and Literal aliases.
"""

from __future__ import annotations

from .formatter import format_validated_block, parse_validated_block
from .parser import parse_invocation
from .specs import COMMAND_SPECS
from .types import (
    Coercion,
    CommandSpec,
    CrossValidation,
    EnforcementClass,
    FlagSpec,
    FlagType,
    ParseContext,
    ParseResult,
    PositionalSpec,
    ResolvedFlag,
    Severity,
    Source,
)

__all__ = [
    "COMMAND_SPECS",
    "Coercion",
    "CommandSpec",
    "CrossValidation",
    "EnforcementClass",
    "FlagSpec",
    "FlagType",
    "ParseContext",
    "ParseResult",
    "PositionalSpec",
    "ResolvedFlag",
    "Severity",
    "Source",
    "format_validated_block",
    "parse_invocation",
    "parse_validated_block",
]

"""Per-command specs, assembled into COMMAND_SPECS."""

from __future__ import annotations

from ..types import CommandSpec

# Import specs as they are added.  Each module exposes a single SPEC: CommandSpec.
from .autoformalize import SPEC as _AUTOFORMALIZE
from .autoprove import SPEC as _AUTOPROVE
from .draft import SPEC as _DRAFT
from .formalize import SPEC as _FORMALIZE
from .learn import SPEC as _LEARN
from .prove import SPEC as _PROVE

COMMAND_SPECS: dict[str, CommandSpec] = {
    _AUTOFORMALIZE.name: _AUTOFORMALIZE,
    _AUTOPROVE.name: _AUTOPROVE,
    _DRAFT.name: _DRAFT,
    _FORMALIZE.name: _FORMALIZE,
    _LEARN.name: _LEARN,
    _PROVE.name: _PROVE,
}

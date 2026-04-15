"""Per-command specs, assembled into COMMAND_SPECS."""
from __future__ import annotations

from ..types import CommandSpec

# Import specs as they are added.  Each module exposes a single SPEC: CommandSpec.
from .autoformalize import SPEC as _autoformalize
from .autoprove import SPEC as _autoprove
from .draft import SPEC as _draft
from .formalize import SPEC as _formalize
from .learn import SPEC as _learn
from .prove import SPEC as _prove

COMMAND_SPECS: dict[str, CommandSpec] = {
    _autoformalize.name: _autoformalize,
    _autoprove.name: _autoprove,
    _draft.name: _draft,
    _formalize.name: _formalize,
    _learn.name: _learn,
    _prove.name: _prove,
}

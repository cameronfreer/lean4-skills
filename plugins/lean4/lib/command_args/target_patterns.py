"""Shared regex patterns for target-shape recognition.

Used by /lean4:disprove (and any future command that accepts the same
target grammar). Keeping these in one place avoids silent drift between
the parser-side validators (`command_args/specs/`) and the runtime
resolver scripts (`lib/scripts/`).

Both `FILE_LINE_RE` and `QUALIFIED_NAME_RE` use named groups so the
resolver can extract structured fields; bare-match callers (e.g.
cross-validation predicates that only need a boolean) can ignore them.

Required validation order
-------------------------
`QUALIFIED_NAME_RE` admits literal paths like ``Foo.lean`` because
``.lean`` is a valid sequence of identifier characters separated by a
dot. Callers MUST therefore test in this order:

    1. ``FILE_LINE_RE``        — matches ``File.lean:LINE``
    2. ``str.endswith(".lean")`` — catches ``File.lean`` (missing line)
    3. ``QUALIFIED_NAME_RE``    — only after the .lean trap

Reordering or skipping step 2 will silently classify ``Foo.lean`` as a
qualified name. See ``specs/disprove.py:_target_shape_valid`` and
``scripts/disprove_target_resolve.py:classify`` for canonical examples.

``FILE_LINE_RE`` requires a 1-indexed line number (``[1-9]\\d*``) so the
parser rejects ``Foo.lean:0`` rather than passing it through to the LSP.
"""
from __future__ import annotations

import re

FILE_LINE_RE = re.compile(r"^(?P<file>[^\s:]+\.lean):(?P<line>[1-9]\d*)$")
QUALIFIED_NAME_RE = re.compile(r"^[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*$")

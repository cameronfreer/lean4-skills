"""CommandSpec for /lean4:checkpoint -- verify + commit a session checkpoint.

Checkpoint had no parser spec until #111 added the mathlib mk_all gate flags.
The spec is deliberately narrow: the optional custom-message positional plus
the two gate flags, nothing else. The gate behaviour itself (project-context
decision order, candidate detection, mk_all --check) lives in checkpoint.md.
"""

from __future__ import annotations

from ..coercions import MATHLIB_MK_ALL_CONFLICT
from ..types import CommandSpec, FlagSpec, PositionalSpec

FLAG_MATHLIB_MK_ALL = FlagSpec(
    name="--mathlib-mk-all",
    type="bool",
    default=False,
    enforcement="startup-validated",
    notes=(
        "Explicitly opt in to the checkpoint mk_all root-file gate, overriding "
        "project-context intent detection."
    ),
)

FLAG_NO_MATHLIB_MK_ALL = FlagSpec(
    name="--no-mathlib-mk-all",
    type="bool",
    default=False,
    enforcement="startup-validated",
    notes=(
        "Explicitly opt out of the checkpoint mk_all root-file gate, overriding "
        "project-context intent detection."
    ),
)

SPEC = CommandSpec(
    name="checkpoint",
    positionals=(
        PositionalSpec(
            name="message",
            required=False,
            notes="Custom commit-message suffix.",
        ),
    ),
    flags=(
        FLAG_MATHLIB_MK_ALL,
        FLAG_NO_MATHLIB_MK_ALL,
    ),
    cross_validations=(
        # --mathlib-mk-all + --no-mathlib-mk-all -> single startup error
        MATHLIB_MK_ALL_CONFLICT,
    ),
)

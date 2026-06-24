#!/usr/bin/env python3
"""Compute which /lean4:disprove methods are selectable, given a target profile.

Makes the Step 1 menu's "applicable AND available" filter reproducible: it
combines the method registry's ``applies_to_shapes`` (vs the profile's shape)
with the profile's LLM-filled prerequisite hints (``decidable``, ``sampleable``)
and the **scriptable** solver-on-PATH check for the ``external`` family.

Input: a target-profile JSON (from ``disprove_target_profile.py``, with the
LSP-derived ``shape``/``decidable`` fields completed by the cycling LLM; an
optional ``sampleable`` hint for ``plausible``). Output: one JSON object
``{method_id: {"selectable": bool, "reason": str}}``.

Usage:
    disprove_method_probe.py --profile=profile.json
    disprove_method_probe.py --profile=-      # read profile JSON from stdin

Exit codes:
    0 — probe result on stdout (JSON)
    2 — bad invocation / unreadable profile
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import sys

_LIB_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _LIB_ROOT not in sys.path:
    sys.path.insert(0, _LIB_ROOT)

from disprove_methods import load_registry  # noqa: E402

_TRUE = ("yes", True)


def _availability(method_id: str, profile: dict[str, object]) -> tuple[bool, str]:
    """Prerequisite check for an *applicable* method, given profile hints."""
    if method_id == "decide-cascade":
        if profile.get("decidable") in _TRUE:
            return True, "Decidable instance available"
        return False, f"target not Decidable (decidable={profile.get('decidable')!r})"
    if method_id == "plausible":
        if profile.get("sampleable") in _TRUE:
            return True, "SampleableExt instance available"
        return (
            False,
            f"no SampleableExt instance (sampleable={profile.get('sampleable')!r})",
        )
    if method_id == "external":
        found = [s for s in ("z3", "cvc5") if shutil.which(s)]
        if found:
            return True, f"SMT solver(s) on PATH: {', '.join(found)}"
        return False, "no SMT solver on PATH (z3/cvc5 not installed)"
    return True, "no special prerequisite"


def probe(profile: dict[str, object]) -> dict[str, dict[str, object]]:
    """Return {method_id: {selectable, reason}} for every registry method."""
    shape = profile.get("shape")
    out: dict[str, dict[str, object]] = {}
    for m in load_registry():
        if shape is None:
            out[m.id] = {
                "selectable": False,
                "reason": "profile.shape not set (LSP pending)",
            }
            continue
        if shape not in m.applies_to_shapes:
            out[m.id] = {
                "selectable": False,
                "reason": f"shape {shape} not in applies_to_shapes {m.applies_to_shapes}",
            }
            continue
        avail, reason = _availability(m.id, profile)
        out[m.id] = {"selectable": avail, "reason": reason}
    return out


def main(argv: list[str]) -> int:
    p = argparse.ArgumentParser(add_help=True)
    p.add_argument(
        "--profile", required=True, help="profile JSON path, or '-' for stdin"
    )
    args = p.parse_args(argv[1:])
    try:
        if args.profile == "-":
            raw = sys.stdin.read()
        else:
            with open(args.profile, encoding="utf-8") as f:
                raw = f.read()
        profile = json.loads(raw)
    except (OSError, json.JSONDecodeError) as e:
        print(f"error: cannot read profile JSON: {e}", file=sys.stderr)
        return 2
    if not isinstance(profile, dict):
        print("error: profile JSON must be an object", file=sys.stderr)
        return 2
    json.dump(probe(profile), sys.stdout)
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))

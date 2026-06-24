#!/usr/bin/env python3
"""Build the deterministic half of a /lean4:disprove target profile.

This script does only the *scriptable* parts of profiling and emits a JSON
envelope the cycling LLM augments with LSP/kernel facts. Specifically it:

  - classifies the TARGET (`File.lean:LINE` or `Namespace.name`), reusing the
    shared patterns in ``command_args.target_patterns``;
  - for a qualified name, best-effort resolves it to a project source location
    by grepping for the declaration header. This is **non-authoritative**: a
    grep cannot see namespaces/sections or fully-qualified headers, so it only
    resolves an *unambiguous single* match; 0 or >=2 matches yield
    ``needs_lsp_resolution`` (the LLM resolves via ``lean_declaration_file``);
  - classifies the resolved/given path as ``project`` vs read-only
    ``dependency`` (under ``.lake/``) and records ``writable``.

LSP/kernel fields (``shape``, ``decidable``, ``type``, ``free_vars``,
``candidate_grid``) are emitted as ``null`` and listed in ``_lsp_filled`` for
the LLM to complete.

Refusal: a target that resolves into a read-only ``dependency`` path is refused
here (exit 2) — disprove only writes artifacts into writable project sources. A
writable-but-chmod'd ``project`` file is NOT refused here; the artifact emitter
fails at append time instead.

Usage:
    disprove_target_profile.py <target> [--root DIR]

Exit codes:
    0 — profile on stdout (JSON)
    2 — bad target, or target resolves into a read-only dependency (stderr)
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys

_LIB_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _LIB_ROOT not in sys.path:
    sys.path.insert(0, _LIB_ROOT)

from command_args.target_patterns import (  # noqa: E402
    FILE_LINE_RE as _FILE_LINE_RE,
)
from command_args.target_patterns import (  # noqa: E402
    QUALIFIED_NAME_RE as _QUALIFIED_NAME_RE,
)

# LSP/kernel-derived profile fields the script cannot compute; the LLM fills them.
_LSP_FIELDS = ("shape", "decidable", "type", "free_vars", "candidate_grid")
_DECL_KW = "theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|axiom"
_MODS = r"(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"


def _is_dependency_path(path: str) -> bool:
    """True if PATH lies under a Lake dependency directory (``.lake/``)."""
    return ".lake" in os.path.normpath(path).split(os.sep)


def _grep_decl(root: str, leaf: str) -> list[dict[str, object]]:
    """Best-effort scan of project ``.lean`` files for a ``<kw> <leaf>`` header.

    Skips ``.lake/`` (dependencies). Non-authoritative: matches only simple
    ``keyword leaf`` headers, not namespaced or fully-qualified declarations.
    """
    header = re.compile(
        r"^" + _MODS + r"(?:" + _DECL_KW + r")\s+" + re.escape(leaf) + r"\b"
    )
    hits: list[dict[str, object]] = []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d != ".lake"]
        for fn in filenames:
            if not fn.endswith(".lean"):
                continue
            fpath = os.path.join(dirpath, fn)
            try:
                with open(fpath, encoding="utf-8") as f:
                    for i, line in enumerate(f, start=1):
                        if header.match(line):
                            hits.append(
                                {"file": os.path.relpath(fpath, root), "line": i}
                            )
            except OSError:
                continue
    return hits


def _envelope(kind: str, **fields: object) -> dict[str, object]:
    """Assemble a profile dict with the deterministic fields + LSP placeholders."""
    prof: dict[str, object] = {"kind": kind}
    prof.update(fields)
    for k in _LSP_FIELDS:
        prof[k] = None
    prof["_lsp_filled"] = list(_LSP_FIELDS)
    return prof


def build_profile(target: str, root: str) -> dict[str, object]:
    """Classify, (best-effort) resolve, and path-classify TARGET.

    Raises:
        ValueError: if TARGET matches neither supported shape.
    """
    m = _FILE_LINE_RE.match(target)
    if m:
        file = m.group("file")
        return _envelope(
            "file-line",
            source_file=file,
            line=int(m.group("line")),
            path_class="dependency" if _is_dependency_path(file) else "project",
            writable=os.access(os.path.join(root, file), os.W_OK),
        )
    if target.endswith(".lean"):
        raise ValueError(
            f"target {target!r}: file path is missing ':LINE'. "
            "Use 'File.lean:LINE' (e.g. 'Foo.lean:42')."
        )
    if not _QUALIFIED_NAME_RE.match(target):
        raise ValueError(
            f"target {target!r}: expected 'File.lean:LINE' or "
            "'Namespace.theoremName' (inline Props not supported in v1)."
        )
    leaf = target.rsplit(".", 1)[-1]
    hits = _grep_decl(root, leaf)
    if len(hits) != 1:
        return _envelope(
            "qualified-name",
            name=target,
            needs_lsp_resolution=True,
            grep_candidates=hits,
        )
    file = str(hits[0]["file"])
    return _envelope(
        "qualified-name",
        name=target,
        source_file=file,
        line=hits[0]["line"],
        decl_name=leaf,
        resolution="grep",
        authoritative=False,
        path_class="dependency" if _is_dependency_path(file) else "project",
        writable=os.access(os.path.join(root, file), os.W_OK),
    )


def main(argv: list[str]) -> int:
    p = argparse.ArgumentParser(add_help=True)
    p.add_argument("target", help="File.lean:LINE or Namespace.theoremName")
    p.add_argument(
        "--root", default=None, help="Project root to search (default: cwd)."
    )
    args = p.parse_args(argv[1:])
    root = args.root if args.root is not None else os.getcwd()
    try:
        prof = build_profile(args.target, root)
    except ValueError as e:
        print(str(e), file=sys.stderr)
        return 2
    if prof.get("path_class") == "dependency":
        print(
            f"target {args.target!r} resolves into a read-only dependency "
            f"({prof.get('source_file')!r}); use a writable 'File.lean:LINE' target.",
            file=sys.stderr,
        )
        return 2
    json.dump(prof, sys.stdout)
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))

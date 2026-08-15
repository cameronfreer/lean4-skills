#!/usr/bin/env python3
"""Candidate-set root-import change detection for /lean4:checkpoint (issue #111).

Stateless primitive behind ``lean4-skills-checkpoint-mathlib-roots``. Given a
candidate set of session-touched paths (NUL-delimited on stdin) and the
validated Lean project ``--root``, it classifies which of those paths are
**added** or **deleted** ``.lean`` files under ``<root>/Mathlib/`` — the
changes that make a generated root-import aggregator (``Mathlib.lean`` etc.)
stale. Modifications are ignored (they don't change the aggregator's import
list); renames surface as a delete + an add because git is queried with
``--no-renames``.

The candidate set scopes *activation*: only the paths on stdin are inspected,
so unrelated local changes never trigger the checkpoint gate. (Once the gate
fires, ``lake exe mk_all --check`` still examines the whole checkout — that
global-check limitation is documented in checkpoint.md, not worked around
here.)

Input:
    --root PATH        (required) absolute or relative path to the Lean
                       project root. ``Mathlib/`` is resolved relative to it,
                       not to $PWD or the wider git repository root.
    stdin              candidate paths, NUL-delimited, each relative to --root
                       or absolute. Empty stdin is a valid (no-candidate) run.

Output (stdout, JSON, deterministic — ``changes`` sorted by path):
    {
      "schema": "checkpoint-mathlib-roots/v1",
      "root": "/abs/project",
      "changes": [
        {"status": "added",   "path": "Mathlib/Foo.lean"},
        {"status": "deleted", "path": "Mathlib/Bar.lean"}
      ]
    }

``path`` is always root-relative and POSIX-style. ``added`` covers staged
adds and untracked files; ``deleted`` covers staged and worktree deletions.

Exit codes:
    0 — valid result emitted (INCLUDING the no-changes case)
    2 — bad input (missing/empty --root, non-NUL-delimited junk is tolerated
        as a single path, but a --root that is not a directory is a usage
        error)
    4 — git/operational failure (not a git work tree, git unavailable, git
        command failed) — activation cannot be determined; the caller must
        stop, not silently skip
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys

SCHEMA = "checkpoint-mathlib-roots/v1"

EXIT_OK = 0
EXIT_USAGE = 2
EXIT_OPERATIONAL = 4


class _GateError(Exception):
    def __init__(self, code: int, message: str) -> None:
        super().__init__(message)
        self.code = code
        self.message = message


def _git(args: list[str], cwd: str) -> tuple[int, str, str]:
    """Run git with a deterministic environment; return (code, stdout, stderr)."""
    env = dict(os.environ)
    env["LC_ALL"] = "C"
    env["GIT_OPTIONAL_LOCKS"] = "0"
    try:
        proc = subprocess.run(
            ["git", *args],
            cwd=cwd,
            env=env,
            capture_output=True,
            text=True,
            timeout=30,
        )
    except FileNotFoundError as exc:
        raise _GateError(EXIT_OPERATIONAL, "git executable not found") from exc
    except OSError as exc:
        raise _GateError(EXIT_OPERATIONAL, f"git invocation failed: {exc}") from exc
    except subprocess.TimeoutExpired as exc:
        raise _GateError(EXIT_OPERATIONAL, "git invocation timed out") from exc
    return proc.returncode, proc.stdout, proc.stderr


def _read_candidates() -> list[str]:
    """Read NUL-delimited candidate paths from stdin. Empty input is valid."""
    data = sys.stdin.buffer.read()
    if not data:
        return []
    # Split on NUL; drop the trailing empty field a well-formed producer emits.
    parts = data.split(b"\x00")
    out: list[str] = []
    for raw in parts:
        if raw == b"":
            continue
        try:
            out.append(raw.decode("utf-8"))
        except UnicodeDecodeError as exc:
            raise _GateError(EXIT_USAGE, "candidate path is not valid UTF-8") from exc
    return out


def _classify(status_xy: str) -> str | None:
    """Map a porcelain-v1 XY status to added/deleted, or None if irrelevant.

    With --no-renames, a rename is a delete of the old path and an add of the
    new one, so we never see 'R'. Only tree membership matters: a file that
    appears (A / untracked ??) or disappears (D) changes what mk_all would
    generate. Pure modifications (M) leave the aggregator's import list intact.
    """
    x = status_xy[0] if len(status_xy) > 0 else " "
    y = status_xy[1] if len(status_xy) > 1 else " "
    if x == "?" or y == "?":
        return "added"
    if x == "A" or y == "A":
        # 'AD' (added then deleted in worktree) nets to gone.
        if y == "D":
            return "deleted"
        return "added"
    if x == "D" or y == "D":
        return "deleted"
    return None


def _run(root_arg: str) -> dict[str, object]:
    root = os.path.abspath(root_arg)
    if not os.path.isdir(root):
        raise _GateError(EXIT_USAGE, f"--root is not a directory: {root_arg}")

    candidates = _read_candidates()
    if not candidates:
        return {"schema": SCHEMA, "root": root, "changes": []}

    # Resolve the git work tree that owns --root; classification paths are
    # reported relative to --root regardless of where the repo root sits.
    code, top, err = _git(["rev-parse", "--show-toplevel"], cwd=root)
    if code != 0:
        detail = err.strip().splitlines()[0] if err.strip() else "not a git work tree"
        raise _GateError(
            EXIT_OPERATIONAL, f"cannot locate git work tree for --root: {detail}"
        )
    repo_root = top.strip()
    if not repo_root:
        raise _GateError(EXIT_OPERATIONAL, "git reported an empty work-tree root")

    # Query status for exactly the candidate paths (activation is candidate-
    # scoped). Flags that matter for correctness:
    #   --literal-pathspecs   candidate filenames are literal, not globs — a
    #                         real name like `Foo[1].lean` must not also match
    #                         `Foo1.lean` (`--` ends option parsing but does
    #                         NOT disable pathspec magic).
    #   --untracked-files=all a newly created file is untracked precisely
    #                         because checkpoint staging runs AFTER this gate;
    #                         without this the repo/user `status.showUntracked-
    #                         Files` setting can silently hide the principal
    #                         case, yielding a false negative.
    #   --no-renames          collapse renames to delete+add.  -z is NUL-safe.
    code, out, err = _git(
        [
            "-C",
            root,
            "--literal-pathspecs",
            "status",
            "--porcelain=v1",
            "-z",
            "--untracked-files=all",
            "--no-renames",
            "--",
            *candidates,
        ],
        cwd=root,
    )
    if code != 0:
        detail = err.strip().splitlines()[0] if err.strip() else "git status failed"
        raise _GateError(EXIT_OPERATIONAL, f"git status failed: {detail}")

    # Containment is decided on PHYSICAL paths: `git rev-parse --show-toplevel`
    # returns the resolved repo path, so a symlinked --root would otherwise
    # never match a Mathlib/ prefix built from the logical path. The emitted
    # `root` stays the caller's original (possibly symlinked) absolute path.
    root_phys = os.path.realpath(root)
    repo_root_phys = os.path.realpath(repo_root)
    mathlib_dir = os.path.join(root_phys, "Mathlib")
    seen: dict[str, str] = {}
    for entry in out.split("\x00"):
        if not entry:
            continue
        # Each porcelain entry is 'XY<space>path'. X/Y may be spaces.
        if len(entry) < 4:
            continue
        status_xy = entry[:2]
        path = entry[3:]
        kind = _classify(status_xy)
        if kind is None:
            continue
        # Porcelain paths are repo-root-relative; resolve to a physical
        # absolute path, then keep only those under <root>/Mathlib/ ending in
        # .lean. commonpath compares whole path components (a trailing-slash
        # prefix would also exclude a `MathlibExtra` sibling, but commonpath
        # states the containment directly).
        abs_path = os.path.normpath(os.path.join(repo_root_phys, path))
        try:
            if os.path.commonpath([abs_path, mathlib_dir]) != mathlib_dir:
                continue
        except ValueError:
            # Different drives / mixed absolute-relative — not under Mathlib/.
            continue
        if not abs_path.endswith(".lean"):
            continue
        rel = os.path.relpath(abs_path, root_phys)
        rel_posix = rel.replace(os.sep, "/")
        # A path can only carry one net status; last classification wins but
        # the set of candidate paths is unique so collisions are benign.
        seen[rel_posix] = kind

    changes = [{"status": seen[p], "path": p} for p in sorted(seen)]
    return {"schema": SCHEMA, "root": root, "changes": changes}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="checkpoint_mathlib_roots",
        description=(
            "Classify candidate-set added/deleted .lean files under "
            "<root>/Mathlib/ for the /lean4:checkpoint mk_all gate."
        ),
    )
    parser.add_argument(
        "--root",
        required=True,
        help="Validated Lean project root; Mathlib/ is resolved relative to it.",
    )
    # argparse exits natively: 0 for --help, 2 for a usage error — both already
    # match this tool's contract, so let it propagate rather than remapping.
    args = parser.parse_args(argv)

    try:
        result = _run(args.root)
    except _GateError as fail:
        json.dump(
            {"schema": SCHEMA, "error": {"code": fail.code, "message": fail.message}},
            sys.stdout,
        )
        sys.stdout.write("\n")
        return fail.code

    json.dump(result, sys.stdout)
    sys.stdout.write("\n")
    return EXIT_OK


if __name__ == "__main__":
    sys.exit(main())

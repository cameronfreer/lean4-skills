#!/usr/bin/env python3
"""File-content baselines for dispatch-time drift detection (issue #102).

Stateless primitive behind ``lean4-skills-file-baseline``. Three subcommands:

    record <path>...
        Emit a versioned baseline record (JSON, stdout) for the given targets:
        normalized path identity (realpath), existence state, and exact
        sha256 content hash. Never consults git and never uses mtime — a
        dirty working file is a perfectly valid baseline.

    check --baseline FILE|- [--only PATH]...
        Recompute the current state of every baseline entry and compare.
        Default checks EVERY entry; ``--only`` restricts to a subset but
        rejects paths not present in the baseline and reports the entries
        it skipped, so omission is always explicit.

    advance --baseline FILE|- <changed-path>...
        Emit a new baseline in which ONLY the named entries (which the
        caller intentionally mutated) are re-recorded; every other entry is
        carried over byte-identical. This is how a writer advances its
        single-writer chain without blessing external drift on files it
        did not touch. Paths not present in the baseline are rejected.

Custody rule (documented in cycle-engine.md): a baseline is the last
*accepted* content revision in a single-writer chain — not merely whatever
the file contains when someone next records it. On drift the caller aborts
and reconciles; it must not re-record and retry.

Symlink semantics: identity is the resolved path (realpath). A symlink
whose resolved target changed is drift (``retargeted``) even when the new
target's bytes match; replacing a regular file at the same canonical path
with identical bytes is NOT drift (content-hash semantics).

Exit codes:
    0 — check: all entries match (or record/advance succeeded)
    2 — usage error, malformed/unsupported baseline, unknown ``--only`` /
        advance path, duplicate canonical paths among targets
    3 — drift detected (modified / deleted / created / retargeted)
    4 — operational error (target exists but is unreadable or not a
        regular file) — distinct from both bad input and genuine drift
When both operational errors and drift are present, exit 4 and report
every entry's status so the caller sees the full picture.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys

SCHEMA = "file-baseline/v1"
CHECK_SCHEMA = "file-baseline-check/v1"

EXIT_OK = 0
EXIT_USAGE = 2
EXIT_DRIFT = 3
EXIT_OPERATIONAL = 4


class OperationalError(Exception):
    """Target exists but cannot be baselined (unreadable / not a regular file)."""


def _hash_file(path: str) -> tuple[str, int]:
    h = hashlib.sha256()
    size = 0
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
            size += len(chunk)
    return h.hexdigest(), size


def _entry_for(path: str) -> dict[str, object]:
    real = os.path.realpath(path)
    if not os.path.lexists(path) or (os.path.islink(path) and not os.path.exists(path)):
        # Missing target, or a symlink dangling to nowhere: recordable as
        # absent so later creation is detectable drift.
        return {
            "path": path,
            "realpath": real,
            "exists": False,
            "sha256": None,
            "size": None,
        }
    if not os.path.isfile(real):
        raise OperationalError(f"{path}: not a regular file")
    try:
        digest, size = _hash_file(real)
    except OSError as exc:
        raise OperationalError(f"{path}: unreadable ({exc})") from exc
    return {
        "path": path,
        "realpath": real,
        "exists": True,
        "sha256": digest,
        "size": size,
    }


def _record_entries(paths: list[str]) -> list[dict[str, object]]:
    seen: dict[str, str] = {}
    entries: list[dict[str, object]] = []
    for p in paths:
        real = os.path.realpath(p)
        if real in seen:
            print(
                f"error: duplicate canonical path: {p!r} and {seen[real]!r} "
                f"both resolve to {real!r} — a single-writer chain needs one "
                "entry per canonical target",
                file=sys.stderr,
            )
            sys.exit(EXIT_USAGE)
        seen[real] = p
        entries.append(_entry_for(p))
    return entries


def _load_baseline(source: str) -> list[dict[str, object]]:
    try:
        if source == "-":
            text = sys.stdin.read()
        else:
            with open(source) as f:
                text = f.read()
    except OSError as exc:
        print(f"error: cannot read baseline {source!r}: {exc}", file=sys.stderr)
        sys.exit(EXIT_USAGE)
    try:
        data = json.loads(text)
    except json.JSONDecodeError as exc:
        print(f"error: malformed baseline JSON: {exc}", file=sys.stderr)
        sys.exit(EXIT_USAGE)
    if not isinstance(data, dict) or data.get("schema") != SCHEMA:
        print(
            f"error: unsupported baseline schema "
            f"{data.get('schema') if isinstance(data, dict) else None!r} "
            f"(expected {SCHEMA!r})",
            file=sys.stderr,
        )
        sys.exit(EXIT_USAGE)
    files = data.get("files")
    if not isinstance(files, list) or not all(isinstance(e, dict) for e in files):
        print(
            "error: malformed baseline: 'files' must be a list of entries",
            file=sys.stderr,
        )
        sys.exit(EXIT_USAGE)
    for e in files:
        if not isinstance(e.get("path"), str) or not isinstance(e.get("realpath"), str):
            print("error: malformed baseline entry (path/realpath)", file=sys.stderr)
            sys.exit(EXIT_USAGE)
    return list(files)


def _emit_baseline(entries: list[dict[str, object]]) -> None:
    json.dump({"schema": SCHEMA, "files": entries}, sys.stdout, indent=2)
    sys.stdout.write("\n")


def cmd_record(paths: list[str]) -> int:
    try:
        entries = _record_entries(paths)
    except OperationalError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return EXIT_OPERATIONAL
    _emit_baseline(entries)
    return EXIT_OK


def _check_one(entry: dict[str, object]) -> str:
    path = str(entry["path"])
    try:
        current = _entry_for(path)
    except OperationalError:
        return "error"
    if str(current["realpath"]) != str(entry["realpath"]):
        return "retargeted"
    was = bool(entry.get("exists"))
    now = bool(current["exists"])
    if was and not now:
        return "deleted"
    if not was and now:
        return "created"
    if not was and not now:
        return "unchanged"
    if current["sha256"] != entry.get("sha256"):
        return "modified"
    return "unchanged"


def cmd_check(baseline_src: str, only: list[str]) -> int:
    entries = _load_baseline(baseline_src)
    by_path = {str(e["path"]): e for e in entries}
    if only:
        unknown = [p for p in only if p not in by_path]
        if unknown:
            print(
                f"error: --only path(s) not in baseline: {unknown!r}",
                file=sys.stderr,
            )
            return EXIT_USAGE
        selected = [by_path[p] for p in only]
        unchecked = [str(e["path"]) for e in entries if str(e["path"]) not in set(only)]
    else:
        selected = entries
        unchecked = []

    results = [{"path": str(e["path"]), "status": _check_one(e)} for e in selected]
    statuses = {r["status"] for r in results}
    if "error" in statuses:
        overall, code = "error", EXIT_OPERATIONAL
    elif statuses - {"unchanged"}:
        overall, code = "drift", EXIT_DRIFT
    else:
        overall, code = "match", EXIT_OK
    json.dump(
        {
            "schema": CHECK_SCHEMA,
            "result": overall,
            "entries": results,
            "unchecked": unchecked,
        },
        sys.stdout,
        indent=2,
    )
    sys.stdout.write("\n")
    return code


def cmd_advance(baseline_src: str, changed: list[str]) -> int:
    entries = _load_baseline(baseline_src)
    by_path = {str(e["path"]): e for e in entries}
    unknown = [p for p in changed if p not in by_path]
    if unknown:
        print(
            f"error: advance path(s) not in baseline: {unknown!r} — new "
            "targets require a fresh dispatch-time record, not advancement",
            file=sys.stderr,
        )
        return EXIT_USAGE
    changed_set = set(changed)
    out: list[dict[str, object]] = []
    try:
        for e in entries:
            if str(e["path"]) in changed_set:
                out.append(_entry_for(str(e["path"])))
            else:
                out.append(e)
    except OperationalError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return EXIT_OPERATIONAL
    _emit_baseline(out)
    return EXIT_OK


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(prog="file_baseline.py", description=__doc__)
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_rec = sub.add_parser("record", help="emit a baseline for the given targets")
    p_rec.add_argument("paths", nargs="+")

    p_chk = sub.add_parser("check", help="compare current state against a baseline")
    p_chk.add_argument(
        "--baseline", required=True, help="baseline JSON file, or - for stdin"
    )
    p_chk.add_argument(
        "--only",
        action="append",
        default=[],
        help="restrict to this baseline path (repeatable); unknown paths are rejected",
    )

    p_adv = sub.add_parser(
        "advance", help="re-record only the named entries; carry the rest over"
    )
    p_adv.add_argument(
        "--baseline", required=True, help="baseline JSON file, or - for stdin"
    )
    p_adv.add_argument("changed", nargs="+")

    args = parser.parse_args(argv[1:])
    if args.cmd == "record":
        return cmd_record(list(args.paths))
    if args.cmd == "check":
        return cmd_check(str(args.baseline), list(args.only))
    return cmd_advance(str(args.baseline), list(args.changed))


if __name__ == "__main__":
    sys.exit(main(sys.argv))

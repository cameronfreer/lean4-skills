#!/usr/bin/env python3
"""Transactional artifact append/drop/rollback for /lean4:disprove.

A disprove cycle may append more than one declaration to the target file (the
committed `T_counterexample`, and for witness shapes a gate-only
`*_negates_target` wrapper used only to license the kernel gate). The wrapper is
dropped before commit, and on a gate failure *all* declarations appended this
cycle must be reverted. This script makes that enforceable instead of leaving it
to the model: each appended declaration is wrapped in comment markers carrying a
unique transaction id, and drop/rollback operate on that id.

Markers (Lean line comments, inert):
    -- lean4:disprove-begin txn=<id> cycle=<n> role=artifact|gate decl=<name>
    <declaration>
    -- lean4:disprove-end txn=<id>

Subcommands:
    begin                                   -> print a fresh txn id
    append  --scope-file F --txn ID --role R --decl NAME [--cycle N]  (stdin=decl)
    drop-role --scope-file F --txn ID --role R
    rollback  --scope-file F --txn ID

Append refuses (exit 2) if NAME is already declared outside this txn's blocks
(don't clobber a pre-existing or other-txn declaration); re-appending the same
NAME under the same txn is idempotent. drop/rollback only excise this txn's
marker blocks and never touch other content.

Exit codes:
    0 — success (begin prints the id; others report on stderr)
    2 — bad invocation / collision / refused operation
"""

from __future__ import annotations

import argparse
import os
import re
import sys
import uuid

_BEGIN_RE = re.compile(
    r"^-- lean4:disprove-begin txn=(?P<txn>\S+) cycle=(?P<cycle>\S+) "
    r"role=(?P<role>\S+) decl=(?P<decl>\S+)\s*$"
)
_END_RE = re.compile(r"^-- lean4:disprove-end txn=(?P<txn>\S+)\s*$")
_DECL_RE_TMPL = (
    r"^(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|axiom)\s+"
)


class _Block:
    """A marker-delimited block: line indices [begin, end] inclusive."""

    def __init__(self, begin: int, end: int, txn: str, role: str, decl: str) -> None:
        self.begin = begin
        self.end = end
        self.txn = txn
        self.role = role
        self.decl = decl


def _parse_blocks(lines: list[str]) -> list[_Block]:
    """Return all well-formed marker blocks in LINES (begin matched to next end)."""
    blocks: list[_Block] = []
    i = 0
    while i < len(lines):
        m = _BEGIN_RE.match(lines[i])
        if not m:
            i += 1
            continue
        for j in range(i + 1, len(lines)):
            e = _END_RE.match(lines[j])
            if e and e.group("txn") == m.group("txn"):
                blocks.append(
                    _Block(i, j, m.group("txn"), m.group("role"), m.group("decl"))
                )
                i = j + 1
                break
        else:
            i += 1
    return blocks


def _decl_declared_outside(lines: list[str], name: str, own_txn: str) -> bool:
    """True if NAME is declared on a line not inside an `own_txn` marker block."""
    own_ranges = [
        range(b.begin, b.end + 1) for b in _parse_blocks(lines) if b.txn == own_txn
    ]
    header = re.compile(_DECL_RE_TMPL + re.escape(name) + r"\b")
    for idx, line in enumerate(lines):
        if header.match(line) and not any(idx in r for r in own_ranges):
            return True
    return False


def _read(scope_file: str) -> list[str]:
    with open(scope_file, encoding="utf-8") as f:
        return f.read().splitlines()


def _write(scope_file: str, lines: list[str]) -> None:
    with open(scope_file, "w", encoding="utf-8") as f:
        f.write("\n".join(lines))
        if lines:
            f.write("\n")


def _require_lean_file(scope_file: str) -> int | None:
    if not scope_file.endswith(".lean"):
        print(
            f"error: --scope-file must end in .lean (got {scope_file!r})",
            file=sys.stderr,
        )
        return 2
    if not os.path.exists(scope_file):
        print(f"error: --scope-file does not exist: {scope_file}", file=sys.stderr)
        return 2
    return None


def _cmd_begin() -> int:
    print(uuid.uuid4().hex[:12])
    return 0


def _cmd_append(args: argparse.Namespace) -> int:
    err = _require_lean_file(args.scope_file)
    if err is not None:
        return err
    snippet = sys.stdin.read().strip("\n")
    if not snippet.strip():
        print("error: empty snippet on stdin", file=sys.stderr)
        return 2
    lines = _read(args.scope_file)
    if _decl_declared_outside(lines, args.decl, args.txn):
        print(
            f"error: declaration {args.decl!r} already exists outside txn "
            f"{args.txn!r}; refusing to append (collision).",
            file=sys.stderr,
        )
        return 2
    for b in _parse_blocks(lines):
        if b.txn == args.txn and b.role == args.role and b.decl == args.decl:
            print(
                f"note: {args.decl!r} (role={args.role}) already present under txn "
                f"{args.txn!r}; no change.",
                file=sys.stderr,
            )
            return 0
    block = [
        f"-- lean4:disprove-begin txn={args.txn} cycle={args.cycle} "
        f"role={args.role} decl={args.decl}",
        *snippet.splitlines(),
        f"-- lean4:disprove-end txn={args.txn}",
    ]
    out = lines + ([""] if lines and lines[-1].strip() else []) + block
    _write(args.scope_file, out)
    print(
        f"appended {args.decl!r} (role={args.role}) under txn {args.txn}",
        file=sys.stderr,
    )
    return 0


def _excise(args: argparse.Namespace, role: str | None) -> int:
    err = _require_lean_file(args.scope_file)
    if err is not None:
        return err
    lines = _read(args.scope_file)
    drop = {
        idx
        for b in _parse_blocks(lines)
        if b.txn == args.txn and (role is None or b.role == role)
        for idx in range(b.begin, b.end + 1)
    }
    if not drop:
        print(
            f"note: no blocks for txn {args.txn!r}{'' if role is None else f' role={role}'}.",
            file=sys.stderr,
        )
        return 0
    _write(args.scope_file, [ln for i, ln in enumerate(lines) if i not in drop])
    print(f"removed {len(drop)} line(s) for txn {args.txn}", file=sys.stderr)
    return 0


def main(argv: list[str]) -> int:
    p = argparse.ArgumentParser(add_help=True)
    sub = p.add_subparsers(dest="cmd", required=True)
    sub.add_parser("begin")
    for name in ("append", "drop-role", "rollback"):
        sp = sub.add_parser(name)
        sp.add_argument("--scope-file", required=True)
        sp.add_argument("--txn", required=True)
        if name == "append":
            sp.add_argument("--role", required=True, choices=["artifact", "gate"])
            sp.add_argument("--decl", required=True)
            sp.add_argument("--cycle", default="1")
        if name == "drop-role":
            sp.add_argument("--role", required=True, choices=["artifact", "gate"])
    args = p.parse_args(argv[1:])
    if args.cmd == "begin":
        return _cmd_begin()
    if args.cmd == "append":
        return _cmd_append(args)
    if args.cmd == "drop-role":
        return _excise(args, args.role)
    return _excise(args, None)  # rollback


if __name__ == "__main__":
    sys.exit(main(sys.argv))

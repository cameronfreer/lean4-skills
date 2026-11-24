#!/usr/bin/env python3
"""Turn a ``pair-audit/v1`` report into ``lean4-review-output/v2`` (issue #88, slice 2).

``/lean4:review --pairs=PATH`` runs ``lean4-skills-pair-audit PATH --json`` and
pipes the report through this script, which maps each audit finding to one
review suggestion and prints a complete ``lean4-review-output/v2`` object. The
review then validates it with ``lean4-skills-validate-review-output`` exactly as
it does a hook's output, and merges it.

The script is pure: it reads the pair file and the report, stats source files
to locate declarations, and runs no Lean. The mapping is fixed:

* ``category`` is ``formal-pair``; ``rule_id`` is the audit code
  (``drift``, ``sorry-in-proved``, ``declaration-missing``…).
* Severity: audit ``error`` → ``error``, ``warning`` → ``warning``,
  ``info`` → ``hint``.
* ``file`` is the claim's ``formal.file`` (``null`` when the pair gives none or
  the claim is unformalized); ``line`` is the first line declaring the
  declaration's last name component in that file, found by a plain text
  search, or ``null``. The location is a pointer for the reader, never a
  resolution: the auditor resolves by name.
* A ``drift`` suggestion asks the reader to re-read the informal statement
  against the new type. Neither this script nor the auditor says whether the
  informal and formal statements match.

``--files`` restricts the output to claims whose ``formal.file`` is one of the
given paths (relative to ``--project``); claims without a file are then left
out. Without ``--files`` every claim is kept (``--scope=project``).

Exit codes (CLI):
    0  a valid lean4-review-output/v2 object was printed
    2  usage error, unreadable file, or malformed JSON
    3  the report is not a pair-audit/v1 report, or the pair file is not
       formal-pair/v1
    4  operational failure (the shipped review schema is unreadable)
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from pathlib import Path
from typing import Any

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from review_validate import SchemaUnavailableError, load_output_schema, validate_output

PAIR_SCHEMA_ID = "formal-pair/v1"
REPORT_SCHEMA_ID = "pair-audit/v1"
CATEGORY = "formal-pair"
SEVERITY = {"error": "error", "warning": "warning", "info": "hint"}
SEVERITIES = ("error", "warning", "advisory", "hint", "style")

EXIT_OK = 0
EXIT_USAGE = 2
EXIT_INPUT = 3
EXIT_OPERATIONAL = 4

_DECL_KEYWORDS = (
    "theorem|lemma|def|abbrev|instance|structure|class|inductive|axiom|opaque"
)


class InputError(Exception):
    """The report or the pair file is not what this script consumes."""


def _norm(path: str) -> str:
    return os.path.normpath(path).replace(os.sep, "/")


def locate(base: Path, file: str | None, declaration: str | None) -> int | None:
    """First 1-indexed line declaring ``declaration``'s last name component."""
    if file is None or declaration is None:
        return None
    short = declaration.rsplit(".", 1)[-1]
    pattern = re.compile(
        r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|"
        r"nonrec|partial|unsafe)\s+)*(?:" + _DECL_KEYWORDS + r")\s+"
        r"(?:[\w.']+\.)?" + re.escape(short) + r"(?![\w'])"
    )
    try:
        with open(base / file, encoding="utf-8") as fh:
            for number, text in enumerate(fh, start=1):
                if pattern.match(text):
                    return number
    except OSError:
        return None
    return None


def message_for(finding: dict[str, Any]) -> str:
    claim = finding["claim"]
    decl = finding.get("declaration")
    if finding["code"] == "drift":
        return (
            f"claim {claim}: the type of {decl} changed since the pair was last "
            "checked. Re-read the informal statement of the claim against the "
            "new type, adjust `relation` if needed, then run "
            "`lean4-skills-pair-audit --update-hashes`."
        )
    where = f" ({decl})" if decl else ""
    return f"claim {claim}{where}: {finding['message']}"


def suggestions(
    pairs: dict[str, Any],
    report: dict[str, Any],
    base: Path,
    files: list[str] | None,
) -> list[dict[str, Any]]:
    if pairs.get("schema") != PAIR_SCHEMA_ID:
        raise InputError(f"pair file schema is not {PAIR_SCHEMA_ID}")
    if report.get("schema") != REPORT_SCHEMA_ID:
        raise InputError(f"report schema is not {REPORT_SCHEMA_ID}")
    findings = report.get("findings")
    if not isinstance(findings, list):
        raise InputError("report has no findings array")
    claims = {c["id"]: c for c in pairs.get("claims", []) if isinstance(c, dict)}
    wanted = None if files is None else {_norm(f) for f in files}
    out: list[dict[str, Any]] = []
    for f in findings:
        if not isinstance(f, dict) or f.get("severity") not in SEVERITY:
            raise InputError(f"malformed finding: {f!r}")
        claim = claims.get(f.get("claim"))
        if claim is None:
            raise InputError(f"finding names unknown claim {f.get('claim')!r}")
        formal = claim.get("formal") or {}
        file = formal.get("file")
        if wanted is not None and (file is None or _norm(file) not in wanted):
            continue
        # A stale path names no existing file: keep it as the file, with no line.
        line = (
            None
            if f["code"] == "stale-path"
            else locate(base, file, f.get("declaration"))
        )
        out.append(
            {
                "file": file,
                "line": line,
                "column": None,
                "severity": SEVERITY[f["severity"]],
                "category": CATEGORY,
                "rule_id": f["code"],
                "message": message_for(f),
                "fix": None,
            }
        )
    return out


def review_output(items: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "version": "2.0",
        "suggestions": items,
        "summary": {
            "total_suggestions": len(items),
            "by_severity": {
                s: sum(i["severity"] == s for i in items) for s in SEVERITIES
            },
        },
        "error": None,
    }


def _load(path: str) -> Any:
    if path == "-":
        return json.load(sys.stdin)
    with open(path, encoding="utf-8") as fh:
        return json.load(fh)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="lean4-skills-pair-review",
        description="Map a pair-audit/v1 report to lean4-review-output/v2.",
    )
    parser.add_argument("pairs", help="the formal-pair/v1 file that was audited")
    parser.add_argument(
        "--report", default="-", help="pair-audit/v1 report (default: stdin)"
    )
    parser.add_argument("--project", default=".", help="Lake project root (default: .)")
    parser.add_argument(
        "--files",
        nargs="+",
        default=None,
        help="keep only claims whose formal.file is one of these paths",
    )
    try:
        args = parser.parse_args(argv)
    except SystemExit as exc:
        return EXIT_USAGE if exc.code else EXIT_OK
    try:
        pairs = _load(args.pairs)
        report = _load(args.report)
    except (OSError, json.JSONDecodeError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return EXIT_USAGE
    if not isinstance(pairs, dict) or not isinstance(report, dict):
        print("error: expected JSON objects", file=sys.stderr)
        return EXIT_INPUT
    try:
        items = suggestions(pairs, report, Path(args.project), args.files)
    except (InputError, KeyError, TypeError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return EXIT_INPUT
    out = review_output(items)
    try:
        result = validate_output(out, load_output_schema())
    except SchemaUnavailableError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return EXIT_OPERATIONAL
    if not result.ok:  # a bug here, never the caller's input
        print(f"error: {result.error_code}: {result.errors}", file=sys.stderr)
        return EXIT_OPERATIONAL
    print(json.dumps(out, indent=2, ensure_ascii=False))
    return EXIT_OK


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Read-only auditor for ``formal-pair/v1`` files (issue #88, slice 1).

A pair file links informal claims (a statement in a paper, a page of notes) to
the Lean declarations that formalise them; the format is
``skills/lean4/references/formal-pair-schema.json`` and is described in
``formal-pairs.md``.  This script checks that the formal side still says what
the pair file records, and leaves the informal side to a human:

1. **Structure** — the shipped schema, through the JSON-Schema subset validator
   of ``review_validate.py`` (never duplicated here), plus cross-field rules the
   schema cannot express (unique ids, ``formal`` present unless
   ``unformalized``, ``type_hash`` keys among the declarations).
2. **Lean** — ONE ``lake lean`` process on a generated probe file (written under
   ``<project>/.lake/pair_audit/`` and removed afterwards; ``lake lean`` builds
   the imports first, so the probe never reads stale ``.olean`` files).  For
   each declaration the probe prints one JSON record: whether it exists, the
   module that defines it, its axioms (``Lean.collectAxioms``, the data behind
   ``#print axioms``) and its elaborated type.
3. **Findings** — missing declarations, ``sorry`` or non-standard axioms under a
   ``proved`` status, a declaration that moved to another module, and *drift*:
   the SHA-256 of the elaborated type differs from the recorded ``type_hash``,
   so a human should re-read the pair.  The script never decides whether the
   informal and the formal statements match.

Declarations are resolved by NAME; ``formal.module`` is the module to import
and ``formal.file`` is only a hint, reported when it no longer exists.  Module
names are never derived from paths.

The only write is ``--update-hashes``, which records the current type hashes
in the pair file (atomic replace).  Sources are never modified.

Exit codes (CLI):
    0  no error or warning (info findings allowed)
    1  findings with severity error or warning
    2  usage error, unreadable file, or malformed JSON
    3  the pair file fails the schema or a cross-field rule
    4  operational failure (no ``lake``, the probe does not elaborate, or a
       declaration got no record)
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from review_validate import validate_instance

SCHEMA_ID = "formal-pair/v1"
REPORT_SCHEMA_ID = "pair-audit/v1"
RECORD_TAG = "pair_audit_v1"
STANDARD_AXIOMS = frozenset({"propext", "Quot.sound", "Classical.choice"})
SORRY_AXIOM = "sorryAx"

EXIT_CLEAN = 0
EXIT_FINDINGS = 1
EXIT_USAGE = 2
EXIT_SCHEMA = 3
EXIT_OPERATIONAL = 4

SCHEMA_PATH = (
    Path(__file__).resolve().parent.parent.parent
    / "skills"
    / "lean4"
    / "references"
    / "formal-pair-schema.json"
)


class OperationalError(Exception):
    """The Lean side could not be consulted (exit 4)."""


@dataclass(frozen=True)
class Finding:
    """One audit finding, attached to a claim and possibly a declaration."""

    claim: str
    declaration: str | None
    code: str
    severity: str  # "error" | "warning" | "info"
    message: str


# ---------------------------------------------------------------------------
# Structure
# ---------------------------------------------------------------------------


def load_schema(path: Path = SCHEMA_PATH) -> dict[str, Any]:
    with open(path, encoding="utf-8") as fh:
        schema: dict[str, Any] = json.load(fh)
    return schema


def validate_pairs(pairs: object, schema: dict[str, Any]) -> list[str]:
    """Structural errors, then the cross-field rules; empty when valid."""
    errors = validate_instance(pairs, schema, schema)
    if errors or not isinstance(pairs, dict):
        return errors
    seen: set[str] = set()
    for i, claim in enumerate(pairs["claims"]):
        where = f"$.claims[{i}]"
        cid = claim["id"]
        if cid in seen:
            errors.append(f"{where}: duplicate id '{cid}'")
        seen.add(cid)
        formal = claim.get("formal")
        if claim["status"] == "unformalized":
            continue
        if formal is None:
            errors.append(f"{where}: status '{claim['status']}' needs 'formal'")
            continue
        decls = formal["declarations"]
        if not decls:
            errors.append(f"{where}.formal: 'declarations' is empty")
        for name, digest in claim.get("type_hash", {}).items():
            if name not in decls:
                errors.append(f"{where}.type_hash: '{name}' is not a declaration")
            if not isinstance(digest, str) or not digest.startswith("sha256:"):
                errors.append(f"{where}.type_hash['{name}']: expected 'sha256:<hex>'")
    return errors


# ---------------------------------------------------------------------------
# The Lean probe
# ---------------------------------------------------------------------------


def _lean_string(s: str) -> str:
    return json.dumps(s, ensure_ascii=False)


def declarations_to_probe(pairs: dict[str, Any]) -> list[str]:
    names: list[str] = []
    for claim in pairs["claims"]:
        formal = claim.get("formal")
        if formal is None or claim["status"] == "unformalized":
            continue
        for name in formal["declarations"]:
            if name not in names:
                names.append(name)
    return names


def modules_to_import(pairs: dict[str, Any]) -> list[str]:
    mods: list[str] = []
    for claim in pairs["claims"]:
        formal = claim.get("formal")
        if formal is None or claim["status"] == "unformalized":
            continue
        if formal["module"] not in mods:
            mods.append(formal["module"])
    return mods


def build_probe(modules: list[str], names: list[str]) -> str:
    """Lean source printing one JSON record per declaration name."""
    lines = ["import Lean"] + [f"import {m}" for m in modules] + [""]
    for name in names:
        lines += [
            "#eval show Lean.MetaM Unit from do",
            f"  let n := String.toName {_lean_string(name)}",
            '  let tag := ("tag", Lean.toJson ' + _lean_string(RECORD_TAG) + ")",
            f'  let nm := ("name", Lean.toJson {_lean_string(name)})',
            "  match (← Lean.getEnv).find? n with",
            "  | none =>",
            "    IO.println (Lean.Json.compress (Lean.Json.mkObj",
            '      [tag, nm, ("found", Lean.toJson false)]))',
            "  | some ci =>",
            "    let mod ← Lean.findModuleOf? n",
            "    let axs ← Lean.collectAxioms n",
            "    let pretty ← Lean.Meta.ppExpr ci.type",
            "    IO.println (Lean.Json.compress (Lean.Json.mkObj",
            '      [tag, nm, ("found", Lean.toJson true),',
            '       ("module", Lean.toJson ((mod.map toString).getD "")),',
            '       ("axioms", Lean.toJson (axs.map toString)),',
            '       ("type", Lean.toJson (toString ci.type)),',
            '       ("pretty", Lean.toJson (toString pretty))]))',
            "",
        ]
    return "\n".join(lines)


def parse_records(stdout: str) -> dict[str, dict[str, Any]]:
    """Records keyed by declaration name; other output lines are ignored."""
    records: dict[str, dict[str, Any]] = {}
    for line in stdout.splitlines():
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            rec = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(rec, dict) and rec.get("tag") == RECORD_TAG:
            name = rec.get("name")
            if isinstance(name, str):
                records[name] = rec
    return records


def run_probe(project: Path, source: str, timeout: float) -> str:
    """Elaborate ``source`` with ``lake lean`` inside ``project``; stdout."""
    lake = shutil.which("lake")
    if lake is None:
        raise OperationalError("`lake` not found on PATH")
    probe_dir = project / ".lake" / "pair_audit"
    probe_dir.mkdir(parents=True, exist_ok=True)
    fd, probe_path = tempfile.mkstemp(prefix="Probe", suffix=".lean", dir=probe_dir)
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as fh:
            fh.write(source)
        try:
            proc = subprocess.run(
                [lake, "lean", probe_path],
                cwd=project,
                capture_output=True,
                text=True,
                timeout=timeout,
            )
        except subprocess.TimeoutExpired as exc:
            raise OperationalError(f"probe timed out after {timeout:g}s") from exc
    finally:
        os.unlink(probe_path)
    if proc.returncode != 0:
        tail = "\n".join((proc.stdout + proc.stderr).splitlines()[-20:])
        raise OperationalError(
            f"probe did not elaborate (exit {proc.returncode}):\n{tail}"
        )
    return proc.stdout


# ---------------------------------------------------------------------------
# Findings
# ---------------------------------------------------------------------------


def type_digest(type_text: str) -> str:
    return "sha256:" + hashlib.sha256(type_text.encode("utf-8")).hexdigest()


def audit(
    pairs: dict[str, Any], records: dict[str, dict[str, Any]], base: Path
) -> list[Finding]:
    """Compare each claim with the probe records (pure; no I/O beyond stat)."""
    out: list[Finding] = []
    for claim in pairs["claims"]:
        cid = claim["id"]
        status = claim["status"]
        if claim["relation"] == "unchecked":
            out.append(
                Finding(
                    cid,
                    None,
                    "relation-unchecked",
                    "info",
                    "no human has compared the informal and formal statements",
                )
            )
        formal = claim.get("formal")
        if status == "unformalized" or formal is None:
            out.append(
                Finding(cid, None, "unformalized", "info", "no Lean counterpart yet")
            )
            continue
        hint = formal.get("file")
        if hint is not None and not (base / hint).exists():
            out.append(
                Finding(
                    cid,
                    None,
                    "stale-path",
                    "warning",
                    f"formal.file '{hint}' does not exist",
                )
            )
        hashes: dict[str, str] = claim.get("type_hash", {})
        any_sorry = False
        for name in formal["declarations"]:
            rec = records.get(name)
            if rec is None:
                raise OperationalError(f"no probe record for '{name}'")
            if not rec.get("found"):
                out.append(
                    Finding(
                        cid,
                        name,
                        "declaration-missing",
                        "error",
                        f"'{name}' is not in the environment",
                    )
                )
                continue
            module = rec.get("module", "")
            if module and module != formal["module"]:
                out.append(
                    Finding(
                        cid,
                        name,
                        "moved",
                        "warning",
                        f"defined in '{module}', pair says '{formal['module']}'",
                    )
                )
            axioms = [str(a) for a in rec.get("axioms", [])]
            if SORRY_AXIOM in axioms:
                any_sorry = True
                if status == "proved":
                    out.append(
                        Finding(
                            cid,
                            name,
                            "sorry-in-proved",
                            "error",
                            "status is 'proved' but the proof uses sorry",
                        )
                    )
            custom = sorted(
                a for a in axioms if a not in STANDARD_AXIOMS | {SORRY_AXIOM}
            )
            if custom:
                sev = "info" if status == "axiomatized" else "error"
                out.append(
                    Finding(
                        cid,
                        name,
                        "nonstandard-axiom",
                        sev,
                        "axioms outside the standard three: " + ", ".join(custom),
                    )
                )
            digest = type_digest(str(rec.get("type", "")))
            recorded = hashes.get(name)
            if recorded is None:
                out.append(
                    Finding(
                        cid,
                        name,
                        "hash-missing",
                        "info",
                        "no type_hash recorded (run with --update-hashes)",
                    )
                )
            elif recorded != digest:
                out.append(
                    Finding(
                        cid,
                        name,
                        "drift",
                        "warning",
                        "the statement changed since the pair was recorded; re-read it",
                    )
                )
        if status == "partial" and not any_sorry:
            out.append(
                Finding(
                    cid,
                    None,
                    "partial-without-sorry",
                    "warning",
                    "status is 'partial' but no declaration uses sorry",
                )
            )
    return out


def updated_hashes(
    pairs: dict[str, Any], records: dict[str, dict[str, Any]]
) -> dict[str, Any]:
    """A copy of ``pairs`` with ``type_hash`` set for every found declaration."""
    new = json.loads(json.dumps(pairs))
    for claim in new["claims"]:
        formal = claim.get("formal")
        if formal is None or claim["status"] == "unformalized":
            continue
        hashes: dict[str, str] = {}
        for name in formal["declarations"]:
            rec = records.get(name)
            if rec is not None and rec.get("found"):
                hashes[name] = type_digest(str(rec.get("type", "")))
        if hashes:
            claim["type_hash"] = hashes
    result: dict[str, Any] = new
    return result


def report(path: str, pairs: dict[str, Any], findings: list[Finding]) -> dict[str, Any]:
    counts = {
        s: sum(f.severity == s for f in findings) for s in ("error", "warning", "info")
    }
    return {
        "schema": REPORT_SCHEMA_ID,
        "pairs": path,
        "summary": {"claims": len(pairs["claims"]), **counts},
        "findings": [asdict(f) for f in findings],
    }


def exit_code_for(findings: list[Finding]) -> int:
    bad = any(f.severity in ("error", "warning") for f in findings)
    return EXIT_FINDINGS if bad else EXIT_CLEAN


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def _write_atomic(path: Path, data: dict[str, Any]) -> None:
    fd, tmp = tempfile.mkstemp(prefix=".pairs", dir=path.parent)
    with os.fdopen(fd, "w", encoding="utf-8") as fh:
        json.dump(data, fh, indent=2, ensure_ascii=False)
        fh.write("\n")
    os.replace(tmp, path)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="lean4-skills-pair-audit",
        description="Audit a formal-pair/v1 file against a Lake project (read-only).",
    )
    parser.add_argument("pairs", help="path to the formal-pair/v1 JSON file")
    parser.add_argument("--project", default=".", help="Lake project root (default: .)")
    parser.add_argument(
        "--json", action="store_true", help="print a pair-audit/v1 report"
    )
    parser.add_argument(
        "--update-hashes",
        action="store_true",
        help="record the current type hashes in the pair file",
    )
    parser.add_argument(
        "--timeout",
        type=float,
        default=1800.0,
        help="seconds allowed for the Lean probe (default: 1800)",
    )
    try:
        args = parser.parse_args(argv)
    except SystemExit as exc:
        return EXIT_USAGE if exc.code else EXIT_CLEAN

    pairs_path = Path(args.pairs)
    try:
        with open(pairs_path, encoding="utf-8") as fh:
            pairs = json.load(fh)
    except (OSError, json.JSONDecodeError) as exc:
        print(f"error: cannot read {pairs_path}: {exc}", file=sys.stderr)
        return EXIT_USAGE
    try:
        schema = load_schema()
    except (OSError, json.JSONDecodeError) as exc:
        print(f"error: shipped schema unreadable: {exc}", file=sys.stderr)
        return EXIT_OPERATIONAL
    errors = validate_pairs(pairs, schema)
    if errors:
        for e in errors:
            print(f"schema-invalid: {e}", file=sys.stderr)
        return EXIT_SCHEMA

    project = Path(args.project).resolve()
    names = declarations_to_probe(pairs)
    try:
        records: dict[str, dict[str, Any]] = {}
        if names:
            source = build_probe(modules_to_import(pairs), names)
            records = parse_records(run_probe(project, source, args.timeout))
        findings = audit(pairs, records, project)
    except OperationalError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return EXIT_OPERATIONAL

    if args.update_hashes:
        _write_atomic(pairs_path, updated_hashes(pairs, records))

    rep = report(str(pairs_path), pairs, findings)
    if args.json:
        print(json.dumps(rep, indent=2, ensure_ascii=False))
    else:
        s = rep["summary"]
        print(
            f"{s['claims']} claims: {s['error']} errors, {s['warning']} warnings, {s['info']} info"
        )
        for f in findings:
            target = f" {f.declaration}" if f.declaration else ""
            print(f"  [{f.severity}] {f.claim}{target}: {f.code} — {f.message}")
        if args.update_hashes:
            print(f"type hashes written to {pairs_path}")
    return exit_code_for(findings)


if __name__ == "__main__":
    sys.exit(main())

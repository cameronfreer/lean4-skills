#!/usr/bin/env python3
"""Runtime validator for ``lean4-review-output/v2`` (Issue #110).

``/lean4:review`` runs every hook/Codex output through this validator *before*
incorporating its findings.  It loads the **shipped** output schema
(``lean4-review-schema.json``) — it never duplicates the schema's fields in code
— and validates a complete output object against two layers:

1. **Structural** — the JSON-Schema *subset* this repo's schemas actually use
   (``$ref`` / ``const`` / ``enum`` / ``type`` + nullability / object with
   ``properties`` / ``required`` / ``additionalProperties`` / ``minimum`` /
   typed arrays, plus ``allOf`` / ``if`` / ``then`` / ``else`` for the input
   schema's conditionals).  This is deliberately NOT a general Draft-2020-12
   validator — see ``tests/test_review_schema.py`` for why OpenAI's own
   ``--output-schema`` acceptance still needs a live smoke.

2. **Cross-field semantics** the JSON Schema cannot express:
     - ``total_suggestions == len(suggestions)``
     - ``by_severity[sev]`` equals the observed count for every severity
     - a non-null ``error`` implies ``suggestions`` is empty

The module is stdlib-only and importable: ``test_review_schema.py`` consumes
``validate_instance`` / ``type_ok`` / ``validate_output`` directly, so the
normative JSON schema, the validator, and review behaviour cannot drift apart.

It **never** normalizes or repairs: on any failure the caller reports the
structured ``error_code`` and excludes the invalid findings.

Exit codes (CLI):
    0  valid output
    2  usage error, empty input, or malformed JSON
    3  validation failure — structural or semantic (``error_code`` on stdout)
    4  operational failure (e.g. the shipped schema is unreadable)
"""

from __future__ import annotations

import json
import os
import sys
from dataclasses import dataclass
from typing import Any

USAGE = (
    "usage: lean4-skills-validate-review-output < output.json\n"
    "  Reads one complete lean4-review-output/v2 object on stdin and validates it\n"
    "  against the shipped schema plus the cross-field invariants."
)

# Structured error codes for a validation failure (exit 3).
SCHEMA_INVALID = "schema-invalid"
SEMANTIC_INVALID = "semantic-invalid"


class SchemaUnavailableError(Exception):
    """The shipped output schema could not be read or parsed (operational)."""


@dataclass(frozen=True)
class Result:
    """Outcome of validating one output object."""

    ok: bool
    error_code: str | None
    errors: list[str]


# ---------------------------------------------------------------------------
# Structural subset validator (shared with the schema test suite)
# ---------------------------------------------------------------------------


def type_ok(value: object, typ: str) -> bool:
    """True when ``value`` matches a single JSON-Schema ``type`` keyword."""
    if typ == "null":
        return value is None
    if typ == "boolean":
        return isinstance(value, bool)
    if typ == "integer":
        return isinstance(value, int) and not isinstance(value, bool)
    if typ == "number":
        return isinstance(value, (int, float)) and not isinstance(value, bool)
    if typ == "string":
        return isinstance(value, str)
    if typ == "array":
        return isinstance(value, list)
    if typ == "object":
        return isinstance(value, dict)
    raise AssertionError(f"unhandled type keyword: {typ}")


def validate_instance(
    instance: object, node: dict[str, Any], root: dict[str, Any], path: str = "$"
) -> list[str]:
    """Validate ``instance`` against the JSON-Schema *subset* this repo uses.

    Handles ``$ref``, ``const``, ``enum``, ``type`` (incl. nullable via a type
    list), objects (``properties`` / ``required`` / ``additionalProperties``),
    ``minimum``, typed arrays, and the applicator keywords ``allOf`` / ``if`` /
    ``then`` / ``else`` (used only by the input schema's scope conditionals).
    Deliberately NOT a general Draft-2020-12 validator.
    """
    errors: list[str] = []
    if "$ref" in node:
        ref = node["$ref"]
        assert isinstance(ref, str) and ref.startswith("#/$defs/")
        return validate_instance(
            instance, root["$defs"][ref.split("/")[-1]], root, path
        )

    # Applicator keywords accumulate (they co-exist with type/object at a node).
    for i, sub in enumerate(node.get("allOf", [])):
        errors += validate_instance(instance, sub, root, f"{path}/allOf[{i}]")
    if "if" in node:
        cond_errors = validate_instance(instance, node["if"], root, f"{path}/if")
        branch = "then" if not cond_errors else "else"
        if branch in node:
            errors += validate_instance(
                instance, node[branch], root, f"{path}/{branch}"
            )

    # const/enum do NOT early-return: Structured Outputs requires a type
    # alongside them, so the type block below must still run and be checked.
    if "const" in node and instance != node["const"]:
        errors.append(f"{path}: {instance!r} != const {node['const']!r}")
    if "enum" in node and instance not in node["enum"]:
        errors.append(f"{path}: {instance!r} not in enum {node['enum']}")
    if "type" in node:
        types = node["type"] if isinstance(node["type"], list) else [node["type"]]
        if not any(type_ok(instance, t) for t in types):
            errors.append(f"{path}: {type(instance).__name__} not in types {types}")
            return errors
        if isinstance(instance, dict) and "object" in types:
            props = node.get("properties", {})
            for req in node.get("required", []):
                if req not in instance:
                    errors.append(f"{path}: missing required '{req}'")
            if node.get("additionalProperties") is False:
                for key in instance:
                    if key not in props:
                        errors.append(f"{path}: unexpected property '{key}'")
            for key, sub in instance.items():
                if key in props:
                    errors += validate_instance(sub, props[key], root, f"{path}.{key}")
        if (
            "minimum" in node
            and isinstance(instance, (int, float))
            and not isinstance(instance, bool)
            and instance < node["minimum"]
        ):
            errors.append(f"{path}: {instance} < minimum {node['minimum']}")
        if isinstance(instance, list) and "array" in types and "items" in node:
            for i, item in enumerate(instance):
                errors += validate_instance(item, node["items"], root, f"{path}[{i}]")
    return errors


# ---------------------------------------------------------------------------
# Cross-field semantic invariants (not expressible in JSON Schema)
# ---------------------------------------------------------------------------


def check_cross_field(obj: dict[str, Any]) -> list[str]:
    """Check the three cross-field invariants.

    Assumes ``obj`` already passed structural validation, so ``suggestions`` is
    a list, ``summary`` carries an integer ``total_suggestions`` and a full
    ``by_severity`` histogram, and ``error`` is a string or None.
    """
    errors: list[str] = []
    suggestions = obj["suggestions"]
    summary = obj["summary"]
    total = summary["total_suggestions"]
    by_severity = summary["by_severity"]
    error = obj["error"]

    if total != len(suggestions):
        errors.append(
            f"total_suggestions ({total}) != len(suggestions) ({len(suggestions)})"
        )

    observed: dict[str, int] = {}
    for sug in suggestions:
        sev = sug["severity"]
        observed[sev] = observed.get(sev, 0) + 1
    for sev, count in by_severity.items():
        if observed.get(sev, 0) != count:
            errors.append(
                f"by_severity[{sev}] ({count}) != observed count ({observed.get(sev, 0)})"
            )

    if error is not None and len(suggestions) != 0:
        errors.append(
            f"error is non-null but suggestions is non-empty ({len(suggestions)} findings)"
        )
    return errors


# ---------------------------------------------------------------------------
# Shipped-schema loading (never duplicate the schema's fields in code)
# ---------------------------------------------------------------------------


def _default_schema_path() -> str:
    """Resolve the shipped output schema: $LEAN4_REFS first, then repo-relative."""
    refs = os.environ.get("LEAN4_REFS")
    if refs:
        candidate = os.path.join(refs, "lean4-review-schema.json")
        if os.path.isfile(candidate):
            return candidate
    here = os.path.dirname(os.path.abspath(__file__))  # plugins/lean4/lib/scripts
    return os.path.normpath(
        os.path.join(
            here,
            "..",
            "..",
            "skills",
            "lean4",
            "references",
            "lean4-review-schema.json",
        )
    )


def load_output_schema(path: str | None = None) -> dict[str, Any]:
    """Load and parse the shipped output schema, or raise SchemaUnavailableError."""
    resolved = path or _default_schema_path()
    try:
        with open(resolved, encoding="utf-8") as f:
            schema: dict[str, Any] = json.load(f)
    except (OSError, json.JSONDecodeError) as exc:
        raise SchemaUnavailableError(
            f"cannot load shipped review schema at {resolved}: {exc}"
        ) from exc
    return schema


def validate_output(obj: object, schema: dict[str, Any] | None = None) -> Result:
    """Validate one output object: structural first, then cross-field.

    Structural failures short-circuit — a broken shape makes the cross-field
    checks meaningless (and their field accesses unsafe). Never repairs.
    """
    if schema is None:
        schema = load_output_schema()
    structural = validate_instance(obj, schema, schema, "$")
    if structural:
        return Result(False, SCHEMA_INVALID, structural)
    assert isinstance(obj, dict)
    semantic = check_cross_field(obj)
    if semantic:
        return Result(False, SEMANTIC_INVALID, semantic)
    return Result(True, None, [])


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main(argv: list[str] | None = None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)
    if argv:
        if argv[0] in ("-h", "--help"):
            print(USAGE)
            return 0
        print(USAGE, file=sys.stderr)
        return 2

    data = sys.stdin.read()
    if not data.strip():
        print(
            "error: empty input (expected a lean4-review-output/v2 object on stdin)",
            file=sys.stderr,
        )
        return 2
    try:
        obj = json.loads(data)
    except json.JSONDecodeError as exc:
        print(f"error: malformed JSON on stdin: {exc}", file=sys.stderr)
        return 2

    try:
        schema = load_output_schema()
    except SchemaUnavailableError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 4

    result = validate_output(obj, schema)
    json.dump(
        {"ok": result.ok, "error_code": result.error_code, "errors": result.errors},
        sys.stdout,
    )
    sys.stdout.write("\n")
    return 0 if result.ok else 3


if __name__ == "__main__":
    sys.exit(main())

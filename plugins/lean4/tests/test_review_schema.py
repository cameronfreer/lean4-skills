"""Structural tests for the review schema files (Issue #115).

Stdlib only — no `jsonschema` dependency. This (a) asserts the OpenAI
Structured Outputs *shape* constraints recursively, (b) runs a NARROW instance
validator over the subset the schemas actually use ($ref, const, enum,
type + nullability, required, additionalProperties, minimum, arrays) against
representative fixtures, and (c) checks that the doc examples use canonical
enum values. It is NOT a general Draft-2020-12 validator, and OpenAI accepts
only a subset of JSON Schema, so a real `codex exec --output-schema` smoke
against the PR worktree's schema remains a required manual pre-merge check.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import unittest
from collections.abc import Iterator
from typing import Any

# The narrow subset validator + cross-field checks are PRODUCTION code
# (lib/scripts/review_validate.py); this suite consumes that same module so the
# schema, the validator, and /lean4:review behaviour cannot drift apart.
_LIB_SCRIPTS = os.path.join(
    os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "lib", "scripts"
)
sys.path.insert(0, _LIB_SCRIPTS)
import review_validate  # noqa: E402
from review_validate import validate_instance as _validate  # noqa: E402

_REF_DIR = os.path.join(
    os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
    "skills",
    "lean4",
    "references",
)
_WRAPPER = os.path.join(
    os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
    "bin",
    "lean4-skills-validate-review-output",
)
_OUT = os.path.join(_REF_DIR, "lean4-review-schema.json")
_IN = os.path.join(_REF_DIR, "lean4-review-input-schema.json")
_HOOK_MD = os.path.join(_REF_DIR, "review-hook-schema.md")
_REVIEW_MD = os.path.join(
    os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "commands", "review.md"
)


def _load(path: str) -> dict[str, Any]:
    with open(path, encoding="utf-8") as f:
        data: dict[str, Any] = json.load(f)
    return data


def _const_enum_without_type(node: object, path: str) -> list[str]:
    """Every schema node carrying const or enum must also declare a type —
    OpenAI Structured Outputs requires it, and plain Draft-2020-12 tolerates it.
    """
    bad: list[str] = []
    if isinstance(node, dict):
        if ("const" in node or "enum" in node) and "type" not in node:
            bad.append(path)
        for key, value in node.items():
            bad += _const_enum_without_type(value, f"{path}.{key}")
    elif isinstance(node, list):
        for i, item in enumerate(node):
            bad += _const_enum_without_type(item, f"{path}[{i}]")
    return bad


def _resolve_enum(schema: dict[str, Any], node: dict[str, Any]) -> list[Any] | None:
    """Return the enum list a node denotes, following a single local $ref."""
    if "enum" in node:
        return list(node["enum"])
    ref = node.get("$ref")
    if isinstance(ref, str) and ref.startswith("#/$defs/"):
        target = schema["$defs"][ref.split("/")[-1]]
        return list(target["enum"]) if "enum" in target else None
    return None


class OutputSchemaStructuredOutputs(unittest.TestCase):
    """Every object node must satisfy OpenAI Structured Outputs constraints."""

    def setUp(self) -> None:
        self.schema = _load(_OUT)

    def _iter_object_nodes(self, node: object) -> Iterator[dict[str, Any]]:
        """Yield every dict that declares an object type (root, $defs, items)."""
        if isinstance(node, dict):
            if node.get("type") == "object":
                yield node
            for value in node.values():
                yield from self._iter_object_nodes(value)
        elif isinstance(node, list):
            for item in node:
                yield from self._iter_object_nodes(item)

    def test_root_is_object_not_anyof(self) -> None:
        self.assertEqual(self.schema.get("type"), "object")
        self.assertNotIn("anyOf", self.schema)

    def test_version_const(self) -> None:
        self.assertEqual(
            self.schema["properties"]["version"], {"type": "string", "const": "2.0"}
        )

    def test_every_object_additionalproperties_false_and_required_equals_properties(
        self,
    ) -> None:
        nodes = list(self._iter_object_nodes(self.schema))
        # Root + every object under $defs (suggestion, summary, by_severity).
        self.assertGreaterEqual(len(nodes), 4)
        for obj in nodes:
            self.assertIs(
                obj.get("additionalProperties"),
                False,
                f"object missing additionalProperties:false: {sorted(obj.get('properties', {}))}",
            )
            props = set(obj.get("properties", {}))
            required = set(obj.get("required", []))
            self.assertEqual(
                required,
                props,
                f"required != properties for object with props {sorted(props)}: "
                f"missing {sorted(props - required)}, extra {sorted(required - props)}",
            )

    def test_semantic_optionals_are_nullable(self) -> None:
        sug = self.schema["$defs"]["suggestion"]["properties"]
        for field in ("file", "line", "column", "rule_id", "fix"):
            self.assertIn(
                "null",
                sug[field]["type"],
                f"{field} should be nullable-typed (required-but-nullable)",
            )
        # message is genuinely required and non-null.
        self.assertEqual(sug["message"], {"type": "string"})

    def test_by_severity_is_nonnullable_ints_keyed_by_severity_enum(self) -> None:
        by_sev = self.schema["$defs"]["by_severity"]
        sev = set(_resolve_enum(self.schema, self.schema["$defs"]["severity"]) or [])
        # Property names are exactly the severity enum.
        self.assertEqual(set(by_sev["properties"]), sev)
        # Counts are non-null nonnegative integers (0 for absent).
        for name, prop in by_sev["properties"].items():
            self.assertEqual(
                prop,
                {"type": "integer", "minimum": 0},
                f"{name} count should be a nonnegative non-null integer",
            )

    def test_settled_vacuous_api_triple_is_expressible(self) -> None:
        sev = _resolve_enum(
            self.schema, self.schema["$defs"]["suggestion"]["properties"]["severity"]
        )
        cat = _resolve_enum(
            self.schema, self.schema["$defs"]["suggestion"]["properties"]["category"]
        )
        assert sev is not None and cat is not None
        self.assertIn("advisory", sev)
        self.assertIn("api", cat)

    def test_every_const_or_enum_node_declares_a_type(self) -> None:
        # OpenAI Structured Outputs rejects a const/enum node without a type
        # ("schema must have a type key") — the live smoke failed on exactly
        # this. Enforce it recursively so it cannot regress.
        missing = _const_enum_without_type(self.schema, "$")
        self.assertEqual(missing, [], f"const/enum nodes missing 'type': {missing}")

    def test_category_enum_has_new_and_legacy(self) -> None:
        cat = set(_resolve_enum(self.schema, self.schema["$defs"]["category"]) or [])
        new = {
            "docstring",
            "module-doc",
            "api",
            "generalization",
            "attribute",
            "simp",
            "instance",
            "file-placement",
            "import-hygiene",
            "module-system",
            "metadata",
        }
        legacy = {"sorry", "axiom", "style", "structure", "naming", "golf", "import"}
        self.assertTrue(new <= cat, f"missing new categories: {sorted(new - cat)}")
        self.assertTrue(
            legacy <= cat, f"missing legacy categories: {sorted(legacy - cat)}"
        )


class InputSchema(unittest.TestCase):
    def setUp(self) -> None:
        self.schema = _load(_IN)

    def test_version_const(self) -> None:
        self.assertEqual(
            self.schema["properties"]["version"], {"type": "string", "const": "2.0"}
        )

    def test_reuses_project_context_repository_kind(self) -> None:
        # Must be repository_kind with project-context/v1's enum, NOT a new repo_kind.
        self.assertNotIn("repo_kind", self.schema["properties"])
        self.assertEqual(
            self.schema["properties"]["repository_kind"]["enum"],
            ["mathlib", "other-lean", "not-lean", "unknown"],
        )
        self.assertEqual(
            self.schema["properties"]["contributing_upstream"]["enum"],
            ["yes", "no", "unknown"],
        )

    def test_every_const_or_enum_node_declares_a_type(self) -> None:
        missing = _const_enum_without_type(self.schema, "$")
        self.assertEqual(missing, [], f"const/enum nodes missing 'type': {missing}")

    def test_repo_state_fields_present(self) -> None:
        for field in (
            "new_files",
            "renamed_files",
            "deleted_files",
            "generated_root_files",
        ):
            self.assertIn(field, self.schema["properties"])

    def test_core_v1_fields_required_repo_state_optional(self) -> None:
        # The established v1 core is required and typed; only the new repo-state
        # fields are optional. `{ "version": "2.0" }` must NOT validate.
        self.assertEqual(
            set(self.schema["required"]),
            {"version", "request_type", "focus", "files", "build_status"},
        )
        for optional in (
            "repository_kind",
            "contributing_upstream",
            "new_files",
            "renamed_files",
            "deleted_files",
            "generated_root_files",
        ):
            self.assertNotIn(optional, self.schema["required"])
        # A meaningful contract: no arbitrary extra top-level keys.
        self.assertIs(self.schema["additionalProperties"], False)


class DocExamplesUseCanonicalEnums(unittest.TestCase):
    """Every category/severity value shown in the docs is a member of the JSON enums."""

    def setUp(self) -> None:
        self.schema = _load(_OUT)
        self.categories = set(
            _resolve_enum(self.schema, self.schema["$defs"]["category"]) or []
        )
        self.severities = set(
            _resolve_enum(self.schema, self.schema["$defs"]["severity"]) or []
        )

    def _values(self, text: str, key: str) -> set[str]:
        # A literal example value only — skip `a|b` enum-shorthand placeholders.
        found = set(re.findall(rf'"{key}"\s*:\s*"([^"]+)"', text))
        return {v for v in found if "|" not in v}

    def _read(self, path: str) -> str:
        with open(path, encoding="utf-8") as f:
            return f.read()

    def test_hook_md_examples_in_enums(self) -> None:
        text = self._read(_HOOK_MD)
        for cat in self._values(text, "category"):
            self.assertIn(
                cat,
                self.categories,
                f"review-hook-schema.md category '{cat}' not in enum",
            )
        for sev in self._values(text, "severity"):
            self.assertIn(
                sev,
                self.severities,
                f"review-hook-schema.md severity '{sev}' not in enum",
            )

    def test_review_md_examples_in_enums(self) -> None:
        text = self._read(_REVIEW_MD)
        for cat in self._values(text, "category"):
            self.assertIn(
                cat, self.categories, f"review.md category '{cat}' not in enum"
            )
        for sev in self._values(text, "severity"):
            self.assertIn(
                sev, self.severities, f"review.md severity '{sev}' not in enum"
            )

    def test_external_handoff_uses_v2_not_stale_fragment(self) -> None:
        # The `_values` enum test deliberately skips `a|b` placeholders, so it
        # cannot catch the old handoff pseudo-schema. Pin that fragment's
        # removal and that the handoff points at the v2 contract instead.
        text = self._read(_REVIEW_MD)
        self.assertNotIn(
            '"severity": "hint|warning"',
            text,
            "stale external-handoff pseudo-schema must be removed",
        )
        self.assertNotIn(
            '"severity":"hint|warning"',
            text,
            "stale external-handoff pseudo-schema must be removed",
        )
        self.assertIn(
            "lean4-review-output/v2",
            text,
            "external handoff should reference the v2 output contract",
        )


class OutputSchemaInstanceValidation(unittest.TestCase):
    """Fixtures conform to the output schema under the narrow subset validator."""

    def setUp(self) -> None:
        self.schema = _load(_OUT)

    def _assert_valid(self, instance: dict[str, Any]) -> None:
        errors = _validate(instance, self.schema, self.schema, "$")
        self.assertEqual(errors, [], f"unexpected schema errors: {errors}")

    def _sug(self, **over: Any) -> dict[str, Any]:
        base = {
            "file": "Core.lean",
            "line": 1,
            "column": None,
            "severity": "hint",
            "category": "sorry",
            "rule_id": None,
            "message": "m",
            "fix": None,
        }
        base.update(over)
        return base

    def _by_sev(self, **counts: int) -> dict[str, int]:
        d = {"error": 0, "warning": 0, "advisory": 0, "hint": 0, "style": 0}
        d.update(counts)
        return d

    def test_success_fixture_validates(self) -> None:
        self._assert_valid(
            {
                "version": "2.0",
                "suggestions": [
                    self._sug(fix="ring"),
                    self._sug(line=42, severity="style", category="naming"),
                ],
                "summary": {
                    "total_suggestions": 2,
                    "by_severity": self._by_sev(hint=1, style=1),
                },
                "error": None,
            }
        )

    def test_error_fixture_validates(self) -> None:
        self._assert_valid(
            {
                "version": "2.0",
                "suggestions": [],
                "summary": {"total_suggestions": 0, "by_severity": self._by_sev()},
                "error": "PARSE_ERROR: could not parse",
            }
        )

    def test_vacuous_api_fixture_validates(self) -> None:
        self._assert_valid(
            {
                "version": "2.0",
                "suggestions": [
                    self._sug(
                        file="G.lean",
                        line=10,
                        severity="advisory",
                        category="api",
                        rule_id="vacuous-api",
                        message="Public API collapses to True.",
                    )
                ],
                "summary": {
                    "total_suggestions": 1,
                    "by_severity": self._by_sev(advisory=1),
                },
                "error": None,
            }
        )

    def test_metadata_finding_may_omit_location(self) -> None:
        # file/line null is the reason they are required-but-nullable.
        self._assert_valid(
            {
                "version": "2.0",
                "suggestions": [
                    self._sug(
                        file=None,
                        line=None,
                        category="metadata",
                        message="PR title should follow mathlib convention",
                    )
                ],
                "summary": {
                    "total_suggestions": 1,
                    "by_severity": self._by_sev(hint=1),
                },
                "error": None,
            }
        )

    def test_validator_rejects_bad_instances(self) -> None:
        # The validator must actually catch violations, else the above prove nothing.
        self.assertTrue(_validate({"version": "1.0"}, self.schema, self.schema, "$"))
        self.assertTrue(
            _validate(
                {
                    "version": "2.0",
                    "suggestions": [self._sug(severity="nope")],
                    "summary": {"total_suggestions": 1, "by_severity": self._by_sev()},
                    "error": None,
                },
                self.schema,
                self.schema,
                "$",
            )
        )
        self.assertTrue(
            _validate(
                {
                    "version": "2.0",
                    "suggestions": [{"file": "x", "line": 1}],
                    "summary": {"total_suggestions": 1, "by_severity": self._by_sev()},
                    "error": None,
                },
                self.schema,
                self.schema,
                "$",
            )
        )
        # Negative counts violate minimum: 0.
        self.assertTrue(
            _validate(
                {
                    "version": "2.0",
                    "suggestions": [],
                    "summary": {
                        "total_suggestions": -1,
                        "by_severity": self._by_sev(hint=-2),
                    },
                    "error": None,
                },
                self.schema,
                self.schema,
                "$",
            )
        )

    def test_index_bounds(self) -> None:
        def out(sug: dict[str, Any]) -> dict[str, Any]:
            return {
                "version": "2.0",
                "suggestions": [sug],
                "summary": {
                    "total_suggestions": 1,
                    "by_severity": self._by_sev(hint=1),
                },
                "error": None,
            }

        # line is 1-indexed: 0 and negatives rejected, null still allowed.
        self.assertTrue(
            _validate(out(self._sug(line=0)), self.schema, self.schema, "$")
        )
        self.assertTrue(
            _validate(out(self._sug(line=-1)), self.schema, self.schema, "$")
        )
        self.assertEqual(
            _validate(
                out(self._sug(line=None, file=None)), self.schema, self.schema, "$"
            ),
            [],
        )
        # column is 0-indexed: negatives rejected, 0 and null allowed.
        self.assertTrue(
            _validate(out(self._sug(column=-1)), self.schema, self.schema, "$")
        )
        self.assertEqual(
            _validate(out(self._sug(column=0)), self.schema, self.schema, "$"), []
        )


class InputSchemaInstanceValidation(unittest.TestCase):
    """Instance-validate the input schema, not just inspect its structure."""

    def setUp(self) -> None:
        self.schema = _load(_IN)

    def _valid_input(self, **over: Any) -> dict[str, Any]:
        base: dict[str, Any] = {
            "version": "2.0",
            "request_type": "review",
            "focus": {"scope": "file", "file": "Core.lean"},
            "files": [{"path": "Core.lean"}],
            "build_status": "passing",
        }
        base.update(over)
        return base

    def _errs(self, instance: dict[str, Any]) -> list[str]:
        return _validate(instance, self.schema, self.schema, "$")

    def test_complete_v2_input_validates(self) -> None:
        self.assertEqual(
            self._errs(
                self._valid_input(
                    repository_kind="mathlib",
                    contributing_upstream="yes",
                    new_files=["Mathlib/New.lean"],
                    renamed_files=[{"from": "A.lean", "to": "B.lean"}],
                    deleted_files=[],
                    generated_root_files=["Mathlib.lean"],
                )
            ),
            [],
        )

    def test_version_only_is_rejected(self) -> None:
        self.assertTrue(self._errs({"version": "2.0"}))

    def test_bad_repository_kind_rejected(self) -> None:
        self.assertTrue(self._errs(self._valid_input(repository_kind="downstream")))

    def test_renamed_files_missing_to_rejected(self) -> None:
        self.assertTrue(
            self._errs(self._valid_input(renamed_files=[{"from": "A.lean"}]))
        )

    def test_unexpected_root_field_rejected(self) -> None:
        self.assertTrue(self._errs(self._valid_input(surprise=1)))

    def test_input_index_bounds(self) -> None:
        self.assertTrue(
            self._errs(
                self._valid_input(files=[{"path": "C.lean", "sorries": [{"line": 0}]}])
            )
        )
        self.assertTrue(
            self._errs(
                self._valid_input(
                    files=[{"path": "C.lean", "sorries": [{"line": 1, "column": -1}]}]
                )
            )
        )
        self.assertEqual(
            self._errs(
                self._valid_input(
                    files=[{"path": "C.lean", "sorries": [{"line": 1, "column": 0}]}]
                )
            ),
            [],
        )


class InputSchemaScopeConstraints(unittest.TestCase):
    """The input schema's if/then conditionals on focus.scope (#110).

    sorry/deps require a non-null file AND line; file requires a non-null file;
    changed/project are unconstrained. `required` alone is insufficient, so the
    then-branches also pin the value types.
    """

    def setUp(self) -> None:
        self.schema = _load(_IN)

    def _with_focus(self, focus: dict[str, Any]) -> dict[str, Any]:
        return {
            "version": "2.0",
            "request_type": "review",
            "focus": focus,
            "files": [{"path": "C.lean"}],
            "build_status": "passing",
        }

    def _errs(self, focus: dict[str, Any]) -> list[str]:
        return _validate(self._with_focus(focus), self.schema, self.schema, "$")

    def test_sorry_requires_file_and_line(self) -> None:
        self.assertEqual(
            self._errs({"scope": "sorry", "file": "C.lean", "line": 9}), []
        )
        self.assertTrue(self._errs({"scope": "sorry", "file": "C.lean"}))
        self.assertTrue(self._errs({"scope": "sorry", "line": 9}))
        self.assertTrue(self._errs({"scope": "sorry"}))

    def test_deps_requires_file_and_line(self) -> None:
        self.assertEqual(self._errs({"scope": "deps", "file": "C.lean", "line": 3}), [])
        self.assertTrue(self._errs({"scope": "deps", "file": "C.lean"}))

    def test_file_requires_file(self) -> None:
        self.assertEqual(self._errs({"scope": "file", "file": "C.lean"}), [])
        self.assertTrue(self._errs({"scope": "file"}))

    def test_changed_and_project_unconstrained(self) -> None:
        self.assertEqual(self._errs({"scope": "changed"}), [])
        self.assertEqual(self._errs({"scope": "project"}), [])

    def test_line_must_be_positive_under_sorry(self) -> None:
        # then-branch pins line >= 1 (0 rejected), so a bad line is caught
        # both by the base focus.line minimum and the conditional.
        self.assertTrue(self._errs({"scope": "sorry", "file": "C.lean", "line": 0}))

    def test_validator_actually_enforces_conditionals(self) -> None:
        # Guard against a no-op: the missing-line error must mention the branch.
        errs = self._errs({"scope": "sorry", "file": "C.lean"})
        self.assertTrue(
            any("line" in e for e in errs), f"expected a line requirement, got {errs}"
        )


class CrossFieldSemantics(unittest.TestCase):
    """check_cross_field / validate_output enforce the invariants JSON Schema
    cannot express, exercised on NON-EMPTY output (the #115 live smoke only
    covered the empty-result path)."""

    def setUp(self) -> None:
        self.schema = _load(_OUT)

    def _sug(self, severity: str = "hint") -> dict[str, Any]:
        return {
            "file": "C.lean",
            "line": 1,
            "column": None,
            "severity": severity,
            "category": "sorry",
            "rule_id": None,
            "message": "m",
            "fix": None,
        }

    def _by_sev(self, **counts: int) -> dict[str, int]:
        d = {"error": 0, "warning": 0, "advisory": 0, "hint": 0, "style": 0}
        d.update(counts)
        return d

    def _out(self, suggestions, total, by_severity, error=None) -> dict[str, Any]:
        return {
            "version": "2.0",
            "suggestions": suggestions,
            "summary": {"total_suggestions": total, "by_severity": by_severity},
            "error": error,
        }

    def test_nonempty_consistent_output_passes(self) -> None:
        obj = self._out(
            [self._sug("hint"), self._sug("advisory")],
            2,
            self._by_sev(hint=1, advisory=1),
        )
        self.assertEqual(review_validate.check_cross_field(obj), [])
        result = review_validate.validate_output(obj, self.schema)
        self.assertTrue(result.ok, result.errors)

    def test_total_mismatch_is_semantic_invalid(self) -> None:
        obj = self._out([self._sug("hint")], 2, self._by_sev(hint=1))
        result = review_validate.validate_output(obj, self.schema)
        self.assertFalse(result.ok)
        self.assertEqual(result.error_code, review_validate.SEMANTIC_INVALID)
        self.assertTrue(any("total_suggestions" in e for e in result.errors))

    def test_histogram_mismatch_is_semantic_invalid(self) -> None:
        # Two hints, but the histogram claims one hint and one style.
        obj = self._out(
            [self._sug("hint"), self._sug("hint")], 2, self._by_sev(hint=1, style=1)
        )
        result = review_validate.validate_output(obj, self.schema)
        self.assertFalse(result.ok)
        self.assertEqual(result.error_code, review_validate.SEMANTIC_INVALID)
        self.assertTrue(any("by_severity" in e for e in result.errors))

    def test_error_with_findings_is_semantic_invalid(self) -> None:
        obj = self._out([self._sug("hint")], 1, self._by_sev(hint=1), error="boom")
        result = review_validate.validate_output(obj, self.schema)
        self.assertFalse(result.ok)
        self.assertEqual(result.error_code, review_validate.SEMANTIC_INVALID)
        self.assertTrue(any("error is non-null" in e for e in result.errors))

    def test_structural_failure_short_circuits_before_semantics(self) -> None:
        # Bad severity is structural; error_code must be schema-invalid even
        # though the histogram is also inconsistent.
        obj = self._out([self._sug("nope")], 5, self._by_sev())
        result = review_validate.validate_output(obj, self.schema)
        self.assertFalse(result.ok)
        self.assertEqual(result.error_code, review_validate.SCHEMA_INVALID)

    def test_load_output_schema_missing_raises(self) -> None:
        with self.assertRaises(review_validate.SchemaUnavailableError):
            review_validate.load_output_schema(path="/nonexistent/review-schema.json")


class OutputValidatorWrapperEndToEnd(unittest.TestCase):
    """End-to-end wrapper fixtures: exact exit codes for empty and NON-EMPTY
    valid output plus each failure class."""

    def _run(self, stdin: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [_WRAPPER],
            input=stdin,
            capture_output=True,
            text=True,
            timeout=30,
        )

    def _by_sev(self, **counts: int) -> dict[str, int]:
        d = {"error": 0, "warning": 0, "advisory": 0, "hint": 0, "style": 0}
        d.update(counts)
        return d

    def test_valid_empty_output_exits_0(self) -> None:
        obj = {
            "version": "2.0",
            "suggestions": [],
            "summary": {"total_suggestions": 0, "by_severity": self._by_sev()},
            "error": None,
        }
        proc = self._run(json.dumps(obj))
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertTrue(json.loads(proc.stdout)["ok"])

    def test_valid_nonempty_output_exits_0(self) -> None:
        obj = {
            "version": "2.0",
            "suggestions": [
                {
                    "file": "C.lean",
                    "line": 10,
                    "column": None,
                    "severity": "advisory",
                    "category": "api",
                    "rule_id": "vacuous-api",
                    "message": "Public API collapses to True.",
                    "fix": None,
                }
            ],
            "summary": {
                "total_suggestions": 1,
                "by_severity": self._by_sev(advisory=1),
            },
            "error": None,
        }
        proc = self._run(json.dumps(obj))
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertTrue(json.loads(proc.stdout)["ok"])

    def test_semantic_violation_exits_3(self) -> None:
        obj = {
            "version": "2.0",
            "suggestions": [],
            "summary": {"total_suggestions": 3, "by_severity": self._by_sev()},
            "error": None,
        }
        proc = self._run(json.dumps(obj))
        self.assertEqual(proc.returncode, 3, proc.stderr)
        self.assertEqual(
            json.loads(proc.stdout)["error_code"], review_validate.SEMANTIC_INVALID
        )

    def test_schema_violation_exits_3(self) -> None:
        obj = {"version": "1.0", "suggestions": [], "summary": {}, "error": None}
        proc = self._run(json.dumps(obj))
        self.assertEqual(proc.returncode, 3, proc.stderr)
        self.assertEqual(
            json.loads(proc.stdout)["error_code"], review_validate.SCHEMA_INVALID
        )

    def test_malformed_json_exits_2(self) -> None:
        proc = self._run("{not json")
        self.assertEqual(proc.returncode, 2)
        self.assertTrue(proc.stderr.strip())

    def test_empty_stdin_exits_2(self) -> None:
        proc = self._run("")
        self.assertEqual(proc.returncode, 2)
        self.assertTrue(proc.stderr.strip())

    def test_unreadable_shipped_schema_exits_4(self) -> None:
        # LEAN4_REFS is consulted first; a malformed schema there is an
        # operational failure (exit 4), distinct from a validation failure (3).
        import tempfile

        obj = {
            "version": "2.0",
            "suggestions": [],
            "summary": {"total_suggestions": 0, "by_severity": self._by_sev()},
            "error": None,
        }
        with tempfile.TemporaryDirectory() as refs:
            with open(
                os.path.join(refs, "lean4-review-schema.json"), "w", encoding="utf-8"
            ) as f:
                f.write("{ this is not valid json")
            proc = subprocess.run(
                [_WRAPPER],
                input=json.dumps(obj),
                capture_output=True,
                text=True,
                timeout=30,
                env={**os.environ, "LEAN4_REFS": refs},
            )
        self.assertEqual(proc.returncode, 4, proc.stderr)
        self.assertTrue(proc.stderr.strip())


if __name__ == "__main__":
    unittest.main()

"""Structural tests for the review schema files (Issue #115).

Stdlib only — this does NOT run a Draft-2020-12 validator (no `jsonschema`
dependency), and therefore does not prove OpenAI accepts the output schema.
It asserts the OpenAI Structured Outputs *shape* constraints recursively and
that the documentation examples use values that belong to the canonical enums.
A real `codex exec --output-schema "$LEAN4_REFS/lean4-review-schema.json"`
smoke remains a required manual pre-merge check, because OpenAI supports only
a subset of JSON Schema.
"""

from __future__ import annotations

import json
import os
import re
import unittest
from collections.abc import Iterator
from typing import Any

_REF_DIR = os.path.join(
    os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
    "skills",
    "lean4",
    "references",
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
        self.assertEqual(self.schema["properties"]["version"], {"const": "2.0"})

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
        self.assertEqual(self.schema["properties"]["version"], {"const": "2.0"})

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

    def test_repo_state_fields_present(self) -> None:
        for field in (
            "new_files",
            "renamed_files",
            "deleted_files",
            "generated_root_files",
        ):
            self.assertIn(field, self.schema["properties"])

    def test_lenient_only_version_required(self) -> None:
        # Existing callers omitting repo-state fields must still validate.
        self.assertEqual(self.schema["required"], ["version"])
        self.assertIs(self.schema["additionalProperties"], True)


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


if __name__ == "__main__":
    unittest.main()

"""Schema + integration tests for the /lean4:disprove Method Registry."""
from __future__ import annotations

import os
import re
import sys
import tempfile
import unittest

_TESTS = os.path.dirname(os.path.abspath(__file__))
_LIB = os.path.join(_TESTS, "..", "lib")
sys.path.insert(0, _LIB)

from disprove_methods import (  # noqa: E402
    DEFAULT_REGISTRY_PATH,
    MethodEntry,
    ParamSpec,
    RegistryError,
    find_by_id,
    load_registry,
)

# Path to disprove-engine.md, used by anchor-resolution tests.
_ENGINE_MD = os.path.normpath(
    os.path.join(
        _TESTS,
        "..",
        "skills",
        "lean4",
        "references",
        "disprove-engine.md",
    )
)


def _slugify_heading(text: str) -> str:
    """Approximate the GitHub-flavored markdown heading slug.

    Lowercases, replaces spaces with hyphens, strips characters that aren't
    word characters or hyphens. Good enough for in-repo anchor validation;
    not a full GFM implementation.
    """
    text = text.strip().lower()
    text = re.sub(r"[\s]+", "-", text)
    text = re.sub(r"[^\w\-]", "", text)
    return text


def _heading_slugs(path: str) -> set[str]:
    """Collect every `# ... #####` heading's slug from a markdown file."""
    slugs: set[str] = set()
    with open(path, encoding="utf-8") as f:
        in_fence = False
        for line in f:
            if line.startswith("```"):
                in_fence = not in_fence
                continue
            if in_fence:
                continue
            m = re.match(r"^(#{1,6})\s+(.+?)\s*$", line)
            if m:
                slugs.add(_slugify_heading(m.group(2)))
    return slugs


# ---------------------------------------------------------------------------
# Default-registry tests (the shipped data file)
# ---------------------------------------------------------------------------

class TestDefaultRegistry(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.entries = load_registry()

    def test_six_methods_loaded(self):
        self.assertEqual(
            len(self.entries),
            6,
            f"expected 6 methods (decide-cascade, mine, enumerate, plausible, "
            f"tactics, external), got {len(self.entries)}",
        )

    def test_expected_ids_present(self):
        ids = {e.id for e in self.entries}
        expected = {
            "decide-cascade",
            "mine",
            "enumerate",
            "plausible",
            "tactics",
            "external",
        }
        self.assertEqual(ids, expected)

    def test_ids_unique(self):
        ids = [e.id for e in self.entries]
        self.assertEqual(len(ids), len(set(ids)), f"duplicate ids in {ids}")

    def test_applies_to_shapes_in_range(self):
        for e in self.entries:
            self.assertTrue(
                set(e.applies_to_shapes).issubset(range(1, 8)),
                f"{e.id}: applies_to_shapes={e.applies_to_shapes} has values outside 1..7",
            )
            self.assertGreater(
                len(e.applies_to_shapes),
                0,
                f"{e.id}: applies_to_shapes is empty",
            )

    def test_cost_class_valid(self):
        for e in self.entries:
            self.assertIn(e.cost_class, {"cheap", "medium", "expensive"})

    def test_cert_template_ref_anchor_resolves(self):
        """Every cert_template_ref must point to a real heading in the
        referenced engine doc."""
        engine_slugs = _heading_slugs(_ENGINE_MD)
        for e in self.entries:
            ref = e.cert_template_ref
            self.assertIn("#", ref, f"{e.id}: cert_template_ref missing anchor: {ref!r}")
            file_part, _, anchor = ref.partition("#")
            self.assertEqual(
                file_part,
                "disprove-engine.md",
                f"{e.id}: only disprove-engine.md anchors are supported (got {file_part!r})",
            )
            self.assertIn(
                anchor,
                engine_slugs,
                f"{e.id}: anchor {anchor!r} not found in {_ENGINE_MD}",
            )

    def test_external_language_param(self):
        ext = find_by_id(self.entries, "external")
        self.assertIsNotNone(ext)
        lang = ext.params.get("language")
        self.assertIsNotNone(lang, "external must have language param")
        self.assertEqual(lang.type, "enum")
        for v in ("python", "bash", "sat-z3", "smt-z3"):
            self.assertIn(v, lang.enum_values, f"language enum missing {v!r}")

    def test_audit_worthy_native_decide(self):
        dc = find_by_id(self.entries, "decide-cascade")
        self.assertIsNotNone(dc)
        nd = dc.params.get("native_decide")
        self.assertIsNotNone(nd, "decide-cascade must have native_decide param")
        self.assertTrue(nd.audit_worthy, "native_decide must be audit_worthy")
        self.assertEqual(nd.default, False, "native_decide default must be off")

    def test_native_decide_not_in_tactics_default(self):
        # native_decide is audit-worthy opt-in only; it must not ride in by
        # default via the tactics cascade.
        tac = find_by_id(self.entries, "tactics")
        self.assertIsNotNone(tac)
        spec = tac.params.get("tactics")
        self.assertIsNotNone(spec, "tactics method must have a 'tactics' param")
        self.assertIsInstance(spec.default, list)
        self.assertNotIn(
            "native_decide", spec.default,
            "native_decide must NOT be in the tactics default list (opt-in only)",
        )

    def test_enumerate_param_schema(self):
        en = find_by_id(self.entries, "enumerate")
        self.assertIsNotNone(en)
        rt = en.params["range_type"]
        self.assertEqual(rt.type, "enum")
        self.assertIn("Fin", rt.enum_values)
        self.assertIn("range", rt.enum_values)
        self.assertIn("both", rt.enum_values)
        self.assertEqual(en.params["range_start"].type, "int")
        self.assertEqual(en.params["range_end"].type, "int")


# ---------------------------------------------------------------------------
# Loader error-path tests
# ---------------------------------------------------------------------------

class TestLoaderRejections(unittest.TestCase):
    def _write(self, body: str) -> str:
        fd, path = tempfile.mkstemp(suffix=".toml")
        with os.fdopen(fd, "w") as f:
            f.write(body)
        self.addCleanup(os.unlink, path)
        return path

    def _minimal_entry(self, **overrides) -> str:
        fields = {
            "id": '"x"',
            "display_name": '"x"',
            "applies_to_shapes": "[1]",
            "cost_class": '"cheap"',
            "budget_hint_seconds": "1",
            "false_negative_notes": '"none"',
            "cert_template_ref": '"disprove-engine.md#per-shape-recipes"',
        }
        fields.update(overrides)
        body = "[[methods]]\n"
        for k, v in fields.items():
            body += f"{k} = {v}\n"
        return body

    def test_empty_methods_rejected(self):
        path = self._write("")
        with self.assertRaises(RegistryError):
            load_registry(path)

    def test_duplicate_id_rejected(self):
        path = self._write(self._minimal_entry() + self._minimal_entry())
        with self.assertRaisesRegex(RegistryError, "duplicate"):
            load_registry(path)

    def test_invalid_shape_rejected(self):
        path = self._write(self._minimal_entry(applies_to_shapes="[1, 9]"))
        with self.assertRaisesRegex(RegistryError, "1..7"):
            load_registry(path)

    def test_invalid_cost_class_rejected(self):
        path = self._write(self._minimal_entry(cost_class='"slow"'))
        with self.assertRaisesRegex(RegistryError, "cost_class"):
            load_registry(path)

    def test_missing_required_rejected(self):
        body = '[[methods]]\nid = "x"\n'
        path = self._write(body)
        with self.assertRaisesRegex(RegistryError, "missing required"):
            load_registry(path)

    def test_zero_budget_rejected(self):
        path = self._write(self._minimal_entry(budget_hint_seconds="0"))
        with self.assertRaisesRegex(RegistryError, "budget"):
            load_registry(path)

    def test_invalid_param_type_rejected(self):
        body = self._minimal_entry() + '[methods.params]\nfoo = { type = "ulong", default = 0 }\n'
        path = self._write(body)
        with self.assertRaisesRegex(RegistryError, "ulong"):
            load_registry(path)

    def test_enum_default_not_in_values_rejected(self):
        body = (
            self._minimal_entry()
            + '[methods.params]\nfoo = { type = "enum", enum_values = ["a", "b"], default = "c" }\n'
        )
        path = self._write(body)
        with self.assertRaisesRegex(RegistryError, "not in enum_values"):
            load_registry(path)

    def test_enum_missing_values_rejected(self):
        body = (
            self._minimal_entry()
            + '[methods.params]\nfoo = { type = "enum", default = "a" }\n'
        )
        path = self._write(body)
        with self.assertRaisesRegex(RegistryError, "enum_values"):
            load_registry(path)


if __name__ == "__main__":
    unittest.main()

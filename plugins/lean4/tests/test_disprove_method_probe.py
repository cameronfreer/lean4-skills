"""Tests for disprove_method_probe.probe() (deterministic selectability)."""

import os
import sys
import tempfile
import unittest

_TESTS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(_TESTS, "..", "lib", "scripts"))
sys.path.insert(0, os.path.join(_TESTS, "..", "lib"))

import disprove_method_probe as probe_mod  # noqa: E402


class TestMethodProbe(unittest.TestCase):
    def test_shape_filters_inapplicable_methods(self):
        # shape 7 (decidable atom): mine/enumerate/plausible apply only to {1,2}.
        r = probe_mod.probe({"shape": 7, "decidable": "yes"})
        self.assertFalse(r["mine"]["selectable"])
        self.assertIn("not in applies_to_shapes", r["mine"]["reason"])
        self.assertTrue(r["tactics"]["selectable"])  # tactics applies to all shapes

    def test_decide_cascade_needs_decidable(self):
        self.assertTrue(
            probe_mod.probe({"shape": 7, "decidable": "yes"})["decide-cascade"][
                "selectable"
            ]
        )
        r = probe_mod.probe({"shape": 1, "decidable": "no"})
        self.assertFalse(r["decide-cascade"]["selectable"])
        self.assertIn("not Decidable", r["decide-cascade"]["reason"])

    def test_plausible_needs_sampleable(self):
        self.assertFalse(
            probe_mod.probe({"shape": 1, "decidable": "no"})["plausible"]["selectable"]
        )
        self.assertTrue(
            probe_mod.probe({"shape": 1, "sampleable": "yes"})["plausible"][
                "selectable"
            ]
        )

    def test_shape_unset_makes_all_unselectable(self):
        r = probe_mod.probe({"decidable": "yes"})
        self.assertTrue(all(not v["selectable"] for v in r.values()))
        self.assertIn("shape not set", r["tactics"]["reason"])

    def test_external_depends_on_solver_on_path(self):
        saved = os.environ.get("PATH", "")
        tmp = tempfile.mkdtemp()
        try:
            fake_z3 = os.path.join(tmp, "z3")
            with open(fake_z3, "w", encoding="utf-8") as f:
                f.write("#!/bin/sh\n")
            os.chmod(fake_z3, 0o755)

            os.environ["PATH"] = tmp  # z3 present
            self.assertTrue(
                probe_mod.probe({"shape": 7, "decidable": "no"})["external"][
                    "selectable"
                ]
            )

            os.environ["PATH"] = ""  # no z3/cvc5
            r = probe_mod.probe({"shape": 7, "decidable": "no"})
            self.assertFalse(r["external"]["selectable"])
            self.assertIn("not installed", r["external"]["reason"])
        finally:
            os.environ["PATH"] = saved
            import shutil

            shutil.rmtree(tmp, ignore_errors=True)


if __name__ == "__main__":
    unittest.main()

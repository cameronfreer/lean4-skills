#!/usr/bin/env python3
"""Tests for project_context.py (issue #174).

Real ``git init`` + ``git remote`` fixtures, plus one narrow git shim
(house pattern from the lake shim in test_check_axioms_inline) that
delegates to real git except ``remote get-url``, injecting the
otherwise-unreachable URL-scan failure. Covers the issue's
fixture list: not-a-Lean-project; Lean project without git; consumer
project with complete scan and no canonical URL -> no; fork-origin +
canonical-upstream -> yes; canonical push-URL only -> yes; mathlib-kind
checkout without canonical remote -> unknown; URL-form matrix; env
override valid/invalid; deterministic ordering; --from variants;
schema/exit-code contract; kind derivation; mk_all_declared diagnostics.
"""

from __future__ import annotations

import io
import json
import os
import subprocess
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import project_context


def run(argv: list[str], env: dict[str, str] | None = None) -> tuple[int, str, str]:
    out, err = io.StringIO(), io.StringIO()
    old_env: dict[str, str | None] = {}
    env = env or {}
    for k, v in env.items():
        old_env[k] = os.environ.get(k)
        os.environ[k] = v
    if "LEAN4_MATHLIB_INTENT" not in env:
        old_env.setdefault(
            "LEAN4_MATHLIB_INTENT", os.environ.pop("LEAN4_MATHLIB_INTENT", None)
        )
    try:
        with redirect_stdout(out), redirect_stderr(err):
            try:
                code = project_context.main(["project_context.py", *argv])
            except SystemExit as exc:
                code = int(exc.code) if exc.code is not None else 0
    finally:
        for key, old in old_env.items():
            if old is None:
                os.environ.pop(key, None)
            else:
                os.environ[key] = old
    return code, out.getvalue(), err.getvalue()


def git(cwd: str, *args: str) -> None:
    subprocess.run(["git", *args], cwd=cwd, check=True, capture_output=True, text=True)


class ProjectContextTests(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.dir = self._tmp.name
        self.addCleanup(self._tmp.cleanup)

    def mkproj(
        self,
        name: str = "proj",
        markers: tuple[str, ...] = ("lakefile.toml", "lean-toolchain"),
        lakefile_toml: str = 'name = "myproj"\n',
        git_init: bool = True,
    ) -> str:
        root = os.path.join(self.dir, name)
        os.makedirs(root, exist_ok=True)
        for m in markers:
            content = lakefile_toml if m == "lakefile.toml" else ""
            if m == "lean-toolchain":
                content = "leanprover/lean4:v4.32.0\n"
            with open(os.path.join(root, m), "w") as f:
                f.write(content)
        if git_init:
            git(root, "init", "-q")
        return root

    def ctx(self, *argv: str, env: dict[str, str] | None = None) -> dict[str, object]:
        code, out, err = run(list(argv), env=env)
        self.assertEqual(code, 0, err)
        data: dict[str, object] = json.loads(out)
        self.assertEqual(data["schema"], "project-context/v1")
        return data

    def intent(self, data: dict[str, object]) -> tuple[str, str]:
        i = data["intent"]
        assert isinstance(i, dict)
        return i["contributing_upstream"], i["source"]

    def facts(self, data: dict[str, object]) -> dict[str, object]:
        f = data["facts"]
        assert isinstance(f, dict)
        return f

    def test_not_a_lean_project(self) -> None:
        empty = os.path.join(self.dir, "empty")
        os.makedirs(empty)
        data = self.ctx("--from", empty)
        self.assertIsNone(data["root"])
        self.assertEqual(self.facts(data)["repository_kind"], "not-lean")
        self.assertEqual(self.intent(data), ("unknown", "default"))

    def test_lean_project_without_git(self) -> None:
        root = self.mkproj(git_init=False)
        data = self.ctx("--from", root)
        f = self.facts(data)
        self.assertEqual(data["root"], root)
        self.assertEqual(f["repository_kind"], "other-lean")
        git_f = f["git"]
        assert isinstance(git_f, dict)
        self.assertFalse(git_f["is_repository"])
        self.assertEqual(git_f["remote_scan"], "skipped")
        warnings = data["warnings"]
        assert isinstance(warnings, list)
        self.assertTrue(any(w["code"] == "not-git-repository" for w in warnings))
        # Not a confident 'no': remote scan did not complete.
        self.assertEqual(self.intent(data), ("unknown", "default"))

    def test_consumer_project_complete_scan_no_canonical_is_no(self) -> None:
        root = self.mkproj()
        git(root, "remote", "add", "origin", "https://github.com/user/myproj.git")
        data = self.ctx("--from", root)
        self.assertEqual(self.intent(data), ("no", "remote-heuristic"))

    def test_fork_origin_plus_canonical_upstream_is_yes(self) -> None:
        root = self.mkproj(lakefile_toml='name = "mathlib"\n')
        git(root, "remote", "add", "origin", "https://github.com/user/mathlib4.git")
        git(
            root,
            "remote",
            "add",
            "upstream",
            "https://github.com/leanprover-community/mathlib4.git",
        )
        data = self.ctx("--from", root)
        self.assertEqual(self.intent(data), ("yes", "remote-heuristic"))
        remotes = self.facts(data)["remotes"]
        assert isinstance(remotes, list)
        flags = {r["name"]: r["is_canonical_mathlib"] for r in remotes}
        self.assertEqual(flags, {"origin": False, "upstream": True})
        self.assertEqual([r["name"] for r in remotes], ["origin", "upstream"])

    def test_canonical_push_url_only_is_yes(self) -> None:
        root = self.mkproj()
        git(root, "remote", "add", "origin", "https://github.com/user/fork.git")
        git(
            root,
            "remote",
            "set-url",
            "--push",
            "origin",
            "git@github.com:leanprover-community/mathlib4.git",
        )
        data = self.ctx("--from", root)
        self.assertEqual(self.intent(data), ("yes", "remote-heuristic"))

    def test_mathlib_checkout_without_canonical_remote_is_unknown(self) -> None:
        root = self.mkproj(lakefile_toml='name = "mathlib"\n')
        git(root, "remote", "add", "origin", "https://github.com/user/mathlib4.git")
        data = self.ctx("--from", root)
        self.assertEqual(self.facts(data)["repository_kind"], "mathlib")
        # Kind alone never implies intent.
        self.assertEqual(self.intent(data), ("unknown", "default"))

    def test_consumer_require_stanza_is_not_mathlib(self) -> None:
        # The standard consumer lakefile: root name plus a [[require]] on
        # mathlib and a [[lean_lib]] named mk_all. Must classify other-lean
        # with mk_all_declared false — a table-unaware scan would misread
        # both (the exact false-positive the review caught).
        toml = (
            'name = "consumer"\n\n'
            "[[require]]\n"
            'name = "mathlib"\n'
            'git = "https://github.com/leanprover-community/mathlib4.git"\n\n'
            "[[lean_lib]]\n"
            'name = "mk_all"\n'
        )
        root = self.mkproj(name="consumer", lakefile_toml=toml)
        git(root, "remote", "add", "origin", "https://github.com/user/consumer.git")
        data = self.ctx("--from", root)
        f = self.facts(data)
        self.assertEqual(f["repository_kind"], "other-lean")
        self.assertFalse(f["mk_all_declared"])
        self.assertEqual(self.intent(data), ("no", "remote-heuristic"))

    def test_lean_exe_table_declares_mk_all(self) -> None:
        toml = 'name = "consumer"\n\n[[lean_exe]]\nname = "mk_all"\n'
        root = self.mkproj(name="exedecl", lakefile_toml=toml, git_init=False)
        data = self.ctx("--from", root)
        self.assertTrue(self.facts(data)["mk_all_declared"])
        self.assertEqual(self.facts(data)["repository_kind"], "other-lean")

    def test_unknown_option_exits_2(self) -> None:
        code, _, _ = run(["--bogus-option"])
        self.assertEqual(code, 2)

    def test_multiple_fetch_urls_canonical_not_first(self) -> None:
        root = self.mkproj(git_init=True)
        git(root, "remote", "add", "origin", "https://github.com/user/fork.git")
        git(
            root,
            "remote",
            "set-url",
            "--add",
            "origin",
            "https://github.com/leanprover-community/mathlib4.git",
        )
        data = self.ctx("--from", root)
        remotes = self.facts(data)["remotes"]
        assert isinstance(remotes, list)
        self.assertEqual(len(remotes[0]["fetch_urls"]), 2)
        self.assertTrue(remotes[0]["is_canonical_mathlib"])
        self.assertEqual(self.intent(data), ("yes", "remote-heuristic"))

    def test_url_form_matrix(self) -> None:
        forms = [
            "https://github.com/leanprover-community/mathlib4",
            "https://github.com/leanprover-community/mathlib4.git",
            "https://github.com/Leanprover-Community/Mathlib4.git",
            "git@github.com:leanprover-community/mathlib4.git",
            "ssh://git@github.com/leanprover-community/mathlib4",
            "https://github.com/leanprover-community/mathlib4/",
        ]
        for url in forms:
            self.assertTrue(project_context._is_canonical(url), url)
        for url in [
            "https://github.com/user/mathlib4.git",
            "https://gitlab.com/leanprover-community/mathlib4",
            "https://github.com/leanprover-community/mathlib4-fork",
            "file://github.com/leanprover-community/mathlib4",
            "ftp://github.com/leanprover-community/mathlib4",
            "ssh+bogus://github.com/leanprover-community/mathlib4",
            "  https://github.com/leanprover-community/mathlib4",
            "https://github.com/leanprover-community/mathlib4  ",
        ]:
            self.assertFalse(project_context._is_canonical(url), url)

    def test_env_override_valid_and_invalid(self) -> None:
        root = self.mkproj()
        git(root, "remote", "add", "origin", "https://github.com/user/x.git")
        data = self.ctx("--from", root, env={"LEAN4_MATHLIB_INTENT": "yes"})
        self.assertEqual(self.intent(data), ("yes", "env-override"))
        data = self.ctx("--from", root, env={"LEAN4_MATHLIB_INTENT": "totally"})
        self.assertEqual(self.intent(data), ("unknown", "invalid-env-override"))
        warnings = data["warnings"]
        assert isinstance(warnings, list)
        self.assertTrue(
            any(w["code"] == "invalid-env-override" for w in warnings), warnings
        )

    def test_kind_derivation_and_mk_all(self) -> None:
        # mathlib via tree signature, mk_all via lakefile.lean decl
        root = self.mkproj(
            name="ml",
            markers=("lakefile.lean", "lean-toolchain"),
            git_init=False,
        )
        with open(os.path.join(root, "lakefile.lean"), "w") as f:
            f.write("package mathlib\n\nlean_exe mk_all where\n")
        data = self.ctx("--from", root)
        f2 = self.facts(data)
        self.assertEqual(f2["repository_kind"], "mathlib")
        self.assertTrue(f2["mk_all_declared"])
        # toolchain-only marker: no lakefile to inspect -> mk_all null
        root2 = self.mkproj(name="tc", markers=("lean-toolchain",), git_init=False)
        data2 = self.ctx("--from", root2)
        self.assertIsNone(self.facts(data2)["mk_all_declared"])
        self.assertEqual(self.facts(data2)["repository_kind"], "other-lean")

    def test_from_file_and_nested_dir_and_missing(self) -> None:
        root = self.mkproj()
        nested = os.path.join(root, "Sub", "Dir")
        os.makedirs(nested)
        target = os.path.join(nested, "Foo.lean")
        with open(target, "w") as f:
            f.write("theorem t : True := trivial\n")
        for start in (target, nested):
            data = self.ctx("--from", start)
            self.assertEqual(data["root"], root)
        code, _, err = run(["--from", os.path.join(self.dir, "nope")])
        self.assertEqual(code, 4)
        self.assertIn("does not exist", err)

    def test_git_executable_unavailable(self) -> None:
        root = self.mkproj(git_init=True)
        empty_bin = os.path.join(self.dir, "emptybin")
        os.makedirs(empty_bin, exist_ok=True)
        data = self.ctx("--from", root, env={"PATH": empty_bin})
        f = self.facts(data)
        git_f = f["git"]
        assert isinstance(git_f, dict)
        self.assertFalse(git_f["available"])
        self.assertIsNone(git_f["is_repository"])
        self.assertEqual(git_f["remote_scan"], "skipped")
        warnings = data["warnings"]
        assert isinstance(warnings, list)
        self.assertTrue(any(w["code"] == "git-unavailable" for w in warnings))
        self.assertEqual(self.intent(data), ("unknown", "default"))

    def test_membership_inspection_failure_is_null_not_false(self) -> None:
        root = self.mkproj(git_init=True)
        with open(os.path.join(root, ".git", "config"), "w") as f:
            f.write("[core\ngarbage")
        data = self.ctx("--from", root)
        git_f = self.facts(data)["git"]
        assert isinstance(git_f, dict)
        self.assertIsNone(git_f["is_repository"])  # never a confident false
        self.assertEqual(git_f["remote_scan"], "failed")
        warnings = data["warnings"]
        assert isinstance(warnings, list)
        self.assertTrue(any(w["code"] == "git-inspection-failed" for w in warnings))
        self.assertEqual(self.intent(data), ("unknown", "default"))

    def test_remote_url_scan_failure(self) -> None:
        # Modern git resolves even URL-less remotes (name-as-URL), so a
        # config fixture can't force a get-url failure. Use a git shim
        # (house pattern: the lake shim in test_check_axioms_inline) that
        # delegates to real git except `remote get-url`, which fails.
        real_git = __import__("shutil").which("git")
        assert real_git is not None
        root = self.mkproj(git_init=True)
        git(root, "remote", "add", "origin", "https://github.com/user/x.git")
        shim_dir = os.path.join(self.dir, "shim")
        os.makedirs(shim_dir, exist_ok=True)
        shim = os.path.join(shim_dir, "git")
        with open(shim, "w") as f:
            f.write(
                "#!/bin/bash\n"
                'if [ "$1" = remote ] && [ "$2" = get-url ]; then\n'
                '  echo "fatal: shimmed get-url failure" >&2; exit 2\n'
                "fi\n"
                f'exec "{real_git}" "$@"\n'
            )
        os.chmod(shim, 0o755)
        data = self.ctx(
            "--from", root, env={"PATH": shim_dir + os.pathsep + "/usr/bin:/bin"}
        )
        git_f = self.facts(data)["git"]
        assert isinstance(git_f, dict)
        self.assertEqual(git_f["remote_scan"], "failed")
        warnings = data["warnings"]
        assert isinstance(warnings, list)
        self.assertTrue(any(w["code"] == "remote-scan-failed" for w in warnings))
        # Failed scan can never license a confident 'no'.
        self.assertEqual(self.intent(data), ("unknown", "default"))

    def test_remote_url_with_spaces_preserved_exactly(self) -> None:
        root = self.mkproj(git_init=True)
        weird = os.path.join(self.dir, "path with  spaces")
        os.makedirs(weird, exist_ok=True)
        git(root, "remote", "add", "local", weird)
        data = self.ctx("--from", root)
        remotes = self.facts(data)["remotes"]
        assert isinstance(remotes, list)
        self.assertEqual(remotes[0]["fetch_urls"], [weird])
        self.assertEqual(remotes[0]["push_urls"], [weird])

    def test_padded_url_round_trips_verbatim(self) -> None:
        # A URL with leading/trailing spaces, configured directly via git
        # config: our record must match git's own get-url output verbatim.
        root = self.mkproj(git_init=True)
        padded = "  /padded path  "
        git(root, "config", "remote.pad.url", padded)
        emitted = subprocess.run(
            ["git", "remote", "get-url", "pad"],
            cwd=root,
            capture_output=True,
            text=True,
            check=True,
        ).stdout.splitlines()[0]
        data = self.ctx("--from", root)
        remotes = self.facts(data)["remotes"]
        assert isinstance(remotes, list)
        pad = next(r for r in remotes if r["name"] == "pad")
        self.assertEqual(pad["fetch_urls"], [emitted])

    def test_tree_signature_classifies_mathlib(self) -> None:
        # Non-mathlib package name, but root Mathlib.lean + Mathlib/ tree:
        # the TREE signature alone must classify as mathlib.
        root = self.mkproj(
            name="tree", lakefile_toml='name = "someport"\n', git_init=False
        )
        with open(os.path.join(root, "Mathlib.lean"), "w") as f:
            f.write("import Mathlib.Init\n")
        os.makedirs(os.path.join(root, "Mathlib"), exist_ok=True)
        data = self.ctx("--from", root)
        self.assertEqual(self.facts(data)["repository_kind"], "mathlib")

    def test_unreadable_or_empty_toolchain_warns_and_blocks_confident_kind(
        self,
    ) -> None:
        root = self.mkproj(name="emptytc", markers=("lean-toolchain",), git_init=False)
        with open(os.path.join(root, "lean-toolchain"), "w") as f:
            f.write("   \n")
        data = self.ctx("--from", root)
        f2 = self.facts(data)
        self.assertIsNone(f2["toolchain"])
        self.assertEqual(f2["repository_kind"], "unknown")
        warnings = data["warnings"]
        assert isinstance(warnings, list)
        self.assertTrue(
            any(w["code"] == "toolchain-inspection-failed" for w in warnings)
        )

    def test_toolchain_and_markers_sorted(self) -> None:
        root = self.mkproj(markers=("lean-toolchain", "lakefile.toml"))
        data = self.ctx("--from", root)
        f = self.facts(data)
        self.assertEqual(f["project_markers"], ["lakefile.toml", "lean-toolchain"])
        self.assertEqual(f["toolchain"], "leanprover/lean4:v4.32.0")

    def test_deterministic_output(self) -> None:
        root = self.mkproj()
        git(root, "remote", "add", "zeta", "https://github.com/user/z.git")
        git(root, "remote", "add", "alpha", "https://github.com/user/a.git")
        a = self.ctx("--from", root)
        b = self.ctx("--from", root)
        self.assertEqual(a, b)
        remotes = self.facts(a)["remotes"]
        assert isinstance(remotes, list)
        self.assertEqual([r["name"] for r in remotes], ["alpha", "zeta"])


if __name__ == "__main__":
    unittest.main(verbosity=2)

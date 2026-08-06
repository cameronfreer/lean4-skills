#!/usr/bin/env python3
"""Mathlib project-context detection (issue #174, Track 1 foundation).

Stateless primitive behind ``lean4-skills-project-context``. Emits a
versioned ``project-context/v1`` record for the Lean project containing
``--from`` (default: cwd): repository facts, git/remote facts, and the
derived upstream-contribution intent.

Design invariants (issue #174 / roadmap #151):
    - Inspect ALL configured remotes, all fetch and push URLs.
    - Repository KIND is kept separate from contribution INTENT.
    - Intent is ``yes | no | unknown`` with explicit override
      (``LEAN4_MATHLIB_INTENT``); invalid overrides fall to the
      non-enforcing ``unknown`` with an auditable warning.
    - Unknown context must never silently become an enforcement gate
      (consumers' responsibility; this tool just reports honestly).
    - "Could not determine" is never recorded as a confident fact:
      classification fields are tri-state or nullable.

Failure behavior:
    - Nonexistent explicit ``--from`` path -> exit 4 (operational).
    - Git absence or remote-scan failure is NOT a helper failure:
      exit 0 with the corresponding facts unknown/null and a structured
      ``{code, message}`` warning.

Exit codes: 0 context emitted; 2 usage; 4 operational.

Deterministic: no network, no caching; all emitted lists sorted.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys

SCHEMA = "project-context/v1"

EXIT_OK = 0
EXIT_USAGE = 2
EXIT_OPERATIONAL = 4

MARKERS = ("lakefile.lean", "lakefile.toml", "lean-toolchain")
CANONICAL_HOST = "github.com"
CANONICAL_PATH = "leanprover-community/mathlib4"


def _warn(warnings: list[dict[str, str]], code: str, message: str) -> None:
    warnings.append({"code": code, "message": message})


def _find_root(start: str) -> str | None:
    cur = os.path.abspath(start)
    while True:
        if any(os.path.exists(os.path.join(cur, m)) for m in MARKERS):
            return cur
        parent = os.path.dirname(cur)
        if parent == cur:
            return None
        cur = parent


def _normalize_url(url: str) -> str | None:
    """Normalize a git URL to ``host/path`` (lowercase, no .git) — no network."""
    u = url.strip().lower().rstrip("/")
    m = re.match(r"^[a-z+]+://(?:[^@/]+@)?([^/:]+)(?::\d+)?/(.+)$", u)
    if m:
        host, path = m.group(1), m.group(2)
    else:
        m = re.match(r"^(?:[^@/]+@)?([^/:]+):(.+)$", u)
        if not m:
            return None
        host, path = m.group(1), m.group(2)
    path = path.removesuffix(".git").strip("/")
    return f"{host}/{path}"


def _is_canonical(url: str) -> bool:
    return _normalize_url(url) == f"{CANONICAL_HOST}/{CANONICAL_PATH}"


def _git(args: list[str], cwd: str) -> tuple[int, str, str]:
    """Run git with a stable diagnostic locale; return (code, stdout, stderr)."""
    env = dict(os.environ)
    env["LC_ALL"] = "C"
    try:
        proc = subprocess.run(
            ["git", *args],
            cwd=cwd,
            capture_output=True,
            text=True,
            timeout=30,
            check=False,
            env=env,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        return 125, "", str(exc)
    return proc.returncode, proc.stdout, proc.stderr


def _scan_git(
    anchor: str, warnings: list[dict[str, str]]
) -> tuple[dict[str, object], list[dict[str, object]]]:
    git_facts: dict[str, object] = {
        "available": False,
        "is_repository": None,
        "remote_scan": "skipped",
    }
    remotes: list[dict[str, object]] = []
    if shutil.which("git") is None:
        _warn(warnings, "git-unavailable", "git executable not found on PATH")
        return git_facts, remotes
    git_facts["available"] = True

    code, out, err = _git(["rev-parse", "--is-inside-work-tree"], anchor)
    if code == 0 and out.strip() == "true":
        git_facts["is_repository"] = True
    elif code == 0 and out.strip() == "false":
        # Inside a git-controlled area but not a work tree (e.g. .git dir).
        git_facts["is_repository"] = False
        _warn(
            warnings,
            "not-git-repository",
            "directory is not inside a git work tree; remote scan skipped",
        )
        return git_facts, remotes
    elif code != 0 and "not a git repository" in err.lower():
        # Unambiguous non-repository (LC_ALL=C makes the message stable).
        git_facts["is_repository"] = False
        _warn(
            warnings,
            "not-git-repository",
            "directory is not inside a git repository; remote scan skipped",
        )
        return git_facts, remotes
    else:
        # Timeout, permission, corrupt config, dubious ownership, … —
        # inspection FAILED; a confident false would violate the
        # could-not-determine-is-never-confident guarantee.
        git_facts["remote_scan"] = "failed"
        _warn(
            warnings,
            "git-inspection-failed",
            f"could not determine repository membership: {(err or out).strip().splitlines()[0] if (err or out).strip() else f'git exited {code}'}",
        )
        return git_facts, remotes

    code, out, err = _git(["remote"], anchor)
    if code != 0:
        git_facts["remote_scan"] = "failed"
        _warn(warnings, "remote-scan-failed", "git remote enumeration failed")
        return git_facts, remotes
    scan_ok = True
    for name in sorted(n.strip() for n in out.splitlines() if n.strip()):
        fetch_code, fetch_out, _ = _git(["remote", "get-url", "--all", name], anchor)
        push_code, push_out, _ = _git(
            ["remote", "get-url", "--push", "--all", name], anchor
        )
        if fetch_code != 0 or push_code != 0:
            scan_ok = False
            _warn(
                warnings,
                "remote-scan-failed",
                f"could not read URLs for remote {name!r}",
            )
            continue
        # splitlines, not split(), and NO per-URL strip: a configured URL
        # may contain interior or even leading/trailing spaces and must be
        # preserved verbatim, one URL per line exactly as git emits them.
        fetch_urls = sorted({u for u in fetch_out.splitlines() if u})
        push_urls = sorted({u for u in push_out.splitlines() if u})
        remotes.append(
            {
                "name": name,
                "fetch_urls": fetch_urls,
                "push_urls": push_urls,
                "is_canonical_mathlib": any(
                    _is_canonical(u) for u in [*fetch_urls, *push_urls]
                ),
            }
        )
    git_facts["remote_scan"] = "complete" if scan_ok else "failed"
    return git_facts, remotes


def _read_text(path: str) -> str | None:
    try:
        with open(path, encoding="utf-8", errors="replace") as f:
            return f.read()
    except OSError:
        return None


def _classify_kind(
    root: str | None, markers: list[str], warnings: list[dict[str, str]]
) -> tuple[str, bool | None]:
    """Return (repository_kind, mk_all_declared)."""
    if root is None:
        return "not-lean", None
    lakefiles = [m for m in markers if m.startswith("lakefile")]
    texts: list[str] = []
    for lf in lakefiles:
        text = _read_text(os.path.join(root, lf))
        if text is None:
            _warn(warnings, "kind-inspection-failed", f"could not read {lf}")
            return "unknown", None
        texts.append(text)
    name_is_mathlib = any(
        re.search(r'(?m)^\s*name\s*=\s*"mathlib"', t)
        or re.search(r"(?m)^\s*package\s+«?mathlib»?\b", t)
        for t in texts
    )
    tree_is_mathlib = os.path.isfile(
        os.path.join(root, "Mathlib.lean")
    ) and os.path.isdir(os.path.join(root, "Mathlib"))
    mk_all_declared: bool | None
    if texts:
        mk_all_declared = any(
            re.search(r"(?m)^\s*name\s*=\s*\"mk_all\"", t)
            or re.search(r"(?m)^\s*lean_exe\s+«?mk_all»?\b", t)
            for t in texts
        )
    else:
        mk_all_declared = None  # toolchain-only marker: no lakefile to inspect
    kind = "mathlib" if (name_is_mathlib or tree_is_mathlib) else "other-lean"
    return kind, mk_all_declared


def _derive_intent(
    kind: str,
    remotes: list[dict[str, object]],
    remote_scan: str,
    warnings: list[dict[str, str]],
) -> dict[str, str]:
    env = os.environ.get("LEAN4_MATHLIB_INTENT")
    if env is not None:
        if env in ("yes", "no"):
            return {"contributing_upstream": env, "source": "env-override"}
        _warn(
            warnings,
            "invalid-env-override",
            f"LEAN4_MATHLIB_INTENT={env!r} is not yes|no — falling back to the "
            "non-enforcing 'unknown'",
        )
        return {"contributing_upstream": "unknown", "source": "invalid-env-override"}
    if any(r.get("is_canonical_mathlib") for r in remotes):
        return {"contributing_upstream": "yes", "source": "remote-heuristic"}
    if kind == "other-lean" and remote_scan == "complete":
        return {"contributing_upstream": "no", "source": "remote-heuristic"}
    return {"contributing_upstream": "unknown", "source": "default"}


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(prog="project_context.py", description=__doc__)
    parser.add_argument(
        "--from",
        dest="start",
        default=None,
        help="file or directory to start from (default: cwd)",
    )
    args = parser.parse_args(argv[1:])

    if args.start is not None:
        start = str(args.start)
        if not os.path.exists(start):
            print(f"error: --from path does not exist: {start!r}", file=sys.stderr)
            return EXIT_OPERATIONAL
        if os.path.isfile(start):
            start = os.path.dirname(os.path.abspath(start)) or "/"
    else:
        start = os.getcwd()

    warnings: list[dict[str, str]] = []
    root = _find_root(start)
    markers = (
        sorted(m for m in MARKERS if os.path.exists(os.path.join(root, m)))
        if root is not None
        else []
    )
    toolchain: str | None = None
    toolchain_ok = True
    if root is not None and "lean-toolchain" in markers:
        text = _read_text(os.path.join(root, "lean-toolchain"))
        if text is None:
            toolchain_ok = False
            _warn(
                warnings, "toolchain-inspection-failed", "could not read lean-toolchain"
            )
        elif not text.strip():
            toolchain_ok = False
            _warn(warnings, "toolchain-inspection-failed", "lean-toolchain is empty")
        else:
            toolchain = text.strip().splitlines()[0].strip()

    git_facts, remotes = _scan_git(root if root is not None else start, warnings)
    kind, mk_all_declared = _classify_kind(root, markers, warnings)
    if not toolchain_ok and kind == "other-lean":
        # A malformed/unreadable marker must not license a confident
        # classification.
        kind = "unknown"
    intent = _derive_intent(kind, remotes, str(git_facts["remote_scan"]), warnings)

    record: dict[str, object] = {
        "schema": SCHEMA,
        "root": root,
        "facts": {
            "repository_kind": kind,
            "project_markers": markers,
            "toolchain": toolchain,
            "git": git_facts,
            "remotes": remotes,
            "mk_all_declared": mk_all_declared,
        },
        "intent": intent,
        "warnings": sorted(warnings, key=lambda w: (w["code"], w["message"])),
    }
    json.dump(record, sys.stdout, indent=2)
    sys.stdout.write("\n")
    return EXIT_OK


if __name__ == "__main__":
    sys.exit(main(sys.argv))

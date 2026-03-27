#!/usr/bin/env python3
"""Sync and verify Codex plugin package copies.

This script keeps Codex package directories equivalent to their canonical
source plugins so local marketplace installs stay stable and drift-free.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

REPO_ROOT = Path(__file__).resolve().parents[1]


@dataclass(frozen=True)
class CopyMapping:
    src_rel: str
    dst_rel: str


@dataclass(frozen=True)
class PackageConfig:
    name: str
    source_root: Path
    package_root: Path
    copy_mappings: tuple[CopyMapping, ...]


LEAN4_SKILLS_PACKAGE = PackageConfig(
    name="lean4-skills",
    source_root=REPO_ROOT / "plugins" / "lean4",
    package_root=REPO_ROOT / "plugins" / "lean4-skills",
    copy_mappings=(
        CopyMapping("skills", "skills"),
        CopyMapping("lib", "lib"),
        CopyMapping("commands", "commands"),
        CopyMapping("agents", "agents"),
        CopyMapping("hooks", "hooks"),
        CopyMapping("tools", "tools"),
        CopyMapping("README.md", "README.md"),
        CopyMapping("MIGRATION.md", "MIGRATION.md"),
    ),
)

LEAN4_CONTRIBUTE_PACKAGE = PackageConfig(
    name="lean4-contribute-codex",
    source_root=REPO_ROOT / "plugins" / "lean4-contribute",
    package_root=REPO_ROOT / "plugins" / "lean4-contribute-codex",
    copy_mappings=(
        CopyMapping("commands", "commands"),
        CopyMapping("tools", "tools"),
        CopyMapping("README.md", "README.md"),
    ),
)

PACKAGES: dict[str, PackageConfig] = {
    LEAN4_SKILLS_PACKAGE.name: LEAN4_SKILLS_PACKAGE,
    LEAN4_CONTRIBUTE_PACKAGE.name: LEAN4_CONTRIBUTE_PACKAGE,
}


def _sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _iter_files(root: Path) -> list[Path]:
    return sorted(p for p in root.rglob("*") if p.is_file())


def _remove_path(path: Path) -> None:
    if path.is_symlink() or path.is_file():
        path.unlink()
    elif path.is_dir():
        shutil.rmtree(path)


def _copy_path(src: Path, dst: Path) -> None:
    if src.is_dir():
        shutil.copytree(src, dst, copy_function=shutil.copy2, dirs_exist_ok=False)
    else:
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(src, dst)


def _parse_frontmatter(md_path: Path) -> dict[str, str]:
    text = md_path.read_text(encoding="utf-8")
    m = re.match(r"\A---\n(.*?)\n---\n", text, flags=re.DOTALL)
    if not m:
        raise ValueError(f"Missing frontmatter in {md_path}")
    data: dict[str, str] = {}
    for raw in m.group(1).splitlines():
        line = raw.strip()
        if not line or ":" not in line:
            continue
        key, value = line.split(":", 1)
        data[key.strip()] = value.strip()
    return data


def _build_lean4_contribute_skill(commands_dir: Path) -> str:
    command_rows: list[tuple[str, str]] = []
    for cmd_file in sorted(commands_dir.glob("*.md")):
        meta = _parse_frontmatter(cmd_file)
        name = meta.get("name", cmd_file.stem)
        desc = meta.get("description", "")
        command_rows.append((name, desc))

    if not command_rows:
        raise ValueError(f"No command specs found in {commands_dir}")

    table_lines = ["| Command | Purpose | Spec |", "|---|---|---|"]
    for name, desc in command_rows:
        table_lines.append(
            f"| `/lean4-contribute:{name}` | {desc} | "
            f"[`{name}.md`](../../commands/{name}.md) |"
        )

    ordered_names = ", ".join(f"`{name}`" for name, _ in command_rows)
    table_text = "\n".join(table_lines)

    return (
        "---\n"
        "name: lean4-contribute\n"
        "description: Draft and submit lean4-skills bug reports, feature requests, and reusable insights with explicit consent gates.\n"
        "---\n\n"
        "# Lean4 Contribute (Codex)\n\n"
        "Use this skill when the user wants to send actionable feedback to "
        "`cameronfreer/lean4-skills` as a bug report, feature request, or "
        "reusable insight.\n\n"
        "Do not use this skill for theorem-proving help in Lean files; route that "
        "work to `lean4`.\n\n"
        "## Command Surface\n\n"
        f"{table_text}\n\n"
        "## Required Execution Contract\n\n"
        "1. Require explicit opt-in before gathering structured context or mining diffs/logs.\n"
        "2. Follow exactly one command spec at a time; do not blend templates across commands.\n"
        "3. Show the complete draft (title, labels, full body) before any submit action.\n"
        "4. Require explicit submit confirmation even after draft approval.\n"
        "5. Submit via the fallback order in the command spec and report the final artifact URL or draft output.\n\n"
        "## Command Specs\n\n"
        f"Read and execute the matching spec in `../../commands/`: {ordered_names}.\n"
    )


def sync_package(cfg: PackageConfig) -> None:
    if not cfg.source_root.exists():
        raise FileNotFoundError(f"Missing source root: {cfg.source_root}")
    if not cfg.package_root.exists():
        raise FileNotFoundError(f"Missing package root: {cfg.package_root}")

    for mapping in cfg.copy_mappings:
        src = cfg.source_root / mapping.src_rel
        dst = cfg.package_root / mapping.dst_rel
        if not src.exists():
            raise FileNotFoundError(f"Missing source path: {src}")
        if dst.exists():
            _remove_path(dst)
        _copy_path(src, dst)

    if cfg.name == "lean4-contribute-codex":
        skill_path = cfg.package_root / "skills" / "lean4-contribute" / "SKILL.md"
        skill_path.parent.mkdir(parents=True, exist_ok=True)
        skill_text = _build_lean4_contribute_skill(cfg.source_root / "commands")
        skill_path.write_text(skill_text, encoding="utf-8")


def _compare_file_pair(src: Path, dst: Path, label: str, errors: list[str]) -> None:
    if not dst.exists():
        errors.append(f"{label}: missing destination file {dst}")
        return
    if _sha256(src) != _sha256(dst):
        errors.append(f"{label}: content mismatch {src} != {dst}")


def _compare_tree_pair(src_root: Path, dst_root: Path, label: str, errors: list[str]) -> None:
    if not dst_root.exists():
        errors.append(f"{label}: missing destination path {dst_root}")
        return

    src_files = _iter_files(src_root)
    dst_files = _iter_files(dst_root)
    src_rel = {p.relative_to(src_root) for p in src_files}
    dst_rel = {p.relative_to(dst_root) for p in dst_files}

    missing = sorted(src_rel - dst_rel)
    extra = sorted(dst_rel - src_rel)

    for rel in missing:
        errors.append(f"{label}: missing file {dst_root / rel}")
    for rel in extra:
        errors.append(f"{label}: unexpected file {dst_root / rel}")

    for rel in sorted(src_rel & dst_rel):
        src = src_root / rel
        dst = dst_root / rel
        if _sha256(src) != _sha256(dst):
            errors.append(f"{label}: content mismatch {src} != {dst}")


def validate_package_equivalence(cfg: PackageConfig, errors: list[str]) -> None:
    for mapping in cfg.copy_mappings:
        src = cfg.source_root / mapping.src_rel
        dst = cfg.package_root / mapping.dst_rel
        label = f"{cfg.name}:{mapping.dst_rel}"
        if src.is_dir():
            _compare_tree_pair(src, dst, label, errors)
        else:
            _compare_file_pair(src, dst, label, errors)

    if cfg.name == "lean4-contribute-codex":
        generated = cfg.package_root / "skills" / "lean4-contribute" / "SKILL.md"
        expected = _build_lean4_contribute_skill(cfg.source_root / "commands")
        if not generated.exists():
            errors.append(f"{cfg.name}: missing generated skill {generated}")
        else:
            actual = generated.read_text(encoding="utf-8")
            if actual != expected:
                errors.append(f"{cfg.name}: generated skill is out of sync ({generated})")


def _load_json(path: Path, errors: list[str]) -> dict | None:
    try:
        with path.open("r", encoding="utf-8") as f:
            return json.load(f)
    except FileNotFoundError:
        errors.append(f"Missing JSON file: {path}")
    except json.JSONDecodeError as exc:
        errors.append(f"Invalid JSON {path}: {exc}")
    return None


def validate_json_integrity(errors: list[str]) -> None:
    plugin_files = {
        "lean4-skills": REPO_ROOT / "plugins" / "lean4-skills" / ".codex-plugin" / "plugin.json",
        "lean4-contribute-codex": REPO_ROOT
        / "plugins"
        / "lean4-contribute-codex"
        / ".codex-plugin"
        / "plugin.json",
    }

    for plugin_name, plugin_json_path in plugin_files.items():
        payload = _load_json(plugin_json_path, errors)
        if payload is None:
            continue

        if payload.get("name") != plugin_name:
            errors.append(
                f"{plugin_json_path}: expected name={plugin_name!r}, got {payload.get('name')!r}"
            )

        skills_rel = payload.get("skills")
        if not isinstance(skills_rel, str) or not skills_rel.startswith("./"):
            errors.append(f"{plugin_json_path}: skills must be a ./-prefixed string path")
        else:
            resolved = plugin_json_path.parent.parent / skills_rel
            if not resolved.exists():
                errors.append(f"{plugin_json_path}: skills path does not exist: {resolved}")

        interface = payload.get("interface")
        if not isinstance(interface, dict):
            errors.append(f"{plugin_json_path}: missing interface object")
        else:
            for key in ("displayName", "shortDescription", "longDescription", "category"):
                if key not in interface:
                    errors.append(f"{plugin_json_path}: interface missing {key!r}")

    marketplace_path = REPO_ROOT / ".agents" / "plugins" / "marketplace.json"
    marketplace = _load_json(marketplace_path, errors)
    if marketplace is None:
        return

    plugins = marketplace.get("plugins")
    if not isinstance(plugins, list):
        errors.append(f"{marketplace_path}: plugins must be an array")
        return

    required = {"lean4-skills", "lean4-contribute-codex"}
    seen: set[str] = set()
    for entry in plugins:
        if not isinstance(entry, dict):
            errors.append(f"{marketplace_path}: plugin entries must be objects")
            continue

        name = entry.get("name")
        if isinstance(name, str):
            seen.add(name)

        policy = entry.get("policy")
        if not isinstance(policy, dict):
            errors.append(f"{marketplace_path}: plugin {name!r} missing policy object")
        else:
            if policy.get("installation") not in {
                "NOT_AVAILABLE",
                "AVAILABLE",
                "INSTALLED_BY_DEFAULT",
            }:
                errors.append(f"{marketplace_path}: plugin {name!r} has invalid policy.installation")
            if policy.get("authentication") not in {"ON_INSTALL", "ON_USE"}:
                errors.append(
                    f"{marketplace_path}: plugin {name!r} has invalid policy.authentication"
                )

        if not entry.get("category"):
            errors.append(f"{marketplace_path}: plugin {name!r} missing category")

        source = entry.get("source")
        if not isinstance(source, dict):
            errors.append(f"{marketplace_path}: plugin {name!r} missing source object")
            continue

        src_path = source.get("path")
        if not isinstance(src_path, str) or not src_path.startswith("./"):
            errors.append(
                f"{marketplace_path}: plugin {name!r} source.path must be ./-prefixed"
            )
            continue

        resolved = marketplace_path.parent.parent.parent / src_path
        if not resolved.exists():
            errors.append(f"{marketplace_path}: plugin {name!r} source path missing: {resolved}")

    missing_plugins = required - seen
    if missing_plugins:
        errors.append(
            f"{marketplace_path}: missing required plugin entries: {', '.join(sorted(missing_plugins))}"
        )


def select_packages(names: Iterable[str]) -> list[PackageConfig]:
    if not names:
        return [PACKAGES[name] for name in sorted(PACKAGES)]

    result: list[PackageConfig] = []
    for name in names:
        if name not in PACKAGES:
            allowed = ", ".join(sorted(PACKAGES))
            raise ValueError(f"Unknown package {name!r}. Allowed: {allowed}")
        result.append(PACKAGES[name])
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)

    sync_parser = sub.add_parser("sync", help="Synchronize Codex package directories")
    sync_parser.add_argument(
        "--package",
        action="append",
        default=[],
        help="Limit to a package (repeatable): lean4-skills, lean4-contribute-codex",
    )

    check_parser = sub.add_parser("check", help="Validate sync equivalence + JSON integrity")
    check_parser.add_argument(
        "--package",
        action="append",
        default=[],
        help="Limit equivalence checks to a package (repeatable)",
    )

    args = parser.parse_args()

    try:
        selected = select_packages(args.package)
    except ValueError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2

    if args.command == "sync":
        for pkg in selected:
            sync_package(pkg)
        print("Synced packages:")
        for pkg in selected:
            print(f"  - {pkg.name}")
        return 0

    errors: list[str] = []
    for pkg in selected:
        validate_package_equivalence(pkg, errors)
    validate_json_integrity(errors)

    if errors:
        print("Codex plugin checks failed:")
        for err in errors:
            print(f"  - {err}")
        return 1

    print("Codex plugin checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""
sorry_analyzer.py - Extract and analyze sorry statements in Lean 4 code

Usage:
    ./sorry_analyzer.py <file-or-directory> [--format=FORMAT | --format FORMAT] [--interactive] [--include-deps] [--exit-zero-on-findings]

This script finds all 'sorry' instances in Lean files and extracts:
- Location (file, line number)
- Context (surrounding code)
- Documentation (TODO comments)
- Type information (from goal state if available)

Modes:
    --interactive: Interactive mode to pick which sorry to work on
    --format=FORMAT (or --format FORMAT): Output format (text, json, markdown, summary)
    --include-deps: Include .lake/ directories (dependencies) in search (excluded by default)
    --exit-zero-on-findings (or --report-only): Exit 0 even when sorries are found (real errors still exit 1)

Exit codes:
    0 - scanned at least one file, no sorries found (or findings present
        with --exit-zero-on-findings)
    1 - sorries found (without --exit-zero-on-findings); also usage errors
    2 - coverage failure: zero .lean files were scanned, or one or more
        paths could not be read. NOT excused by --exit-zero-on-findings:
        that flag means "findings are non-fatal for reporting" — a gate
        that scanned nothing (or missed part of the tree) must not pass.

Examples:
    ./sorry_analyzer.py MyFile.lean
    ./sorry_analyzer.py src/DeFinetti/ --format=markdown
    ./sorry_analyzer.py . --format=json > sorries.json
    ./sorry_analyzer.py . --format=summary
    ./sorry_analyzer.py . --interactive
    ./sorry_analyzer.py . --format json              # space-separated format flag
    ./sorry_analyzer.py . --format=detail            # alias for text
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
from dataclasses import asdict, dataclass
from pathlib import Path


@dataclass
class Sorry:
    """Represents a sorry instance with context"""

    file: str
    line: int
    context_before: list[str]
    context_after: list[str]
    documentation: list[str]
    in_declaration: str | None = None


@dataclass
class ScanResult:
    """Findings plus the coverage they rest on.

    files_scanned counts .lean files actually read; files_failed counts
    paths (files OR directories) that could not be read. Coverage travels
    with the findings so callers can distinguish "clean" from "checked
    nothing" — the distinction whose absence caused the silent-green
    failure modes fixed in #145/#146 for the sibling bash tools.
    """

    sorries: list[Sorry]
    files_scanned: int
    files_failed: int


SORRY_TOKEN_PATTERN = re.compile(r"(?<![A-Za-z0-9_!?'])sorry(?![A-Za-z0-9_!?'])")


def strip_lean_comments_and_strings(
    line: str, block_comment_depth: int
) -> tuple[str, int]:
    """Return code-only text for a line and updated Lean block-comment depth.

    Handles:
    - line comments: -- ...
    - nested block comments: /- ... -/
    - string literals: "..."
    """
    result: list[str] = []
    i = 0
    n = len(line)
    in_string = False

    while i < n:
        ch = line[i]
        nxt = line[i + 1] if i + 1 < n else ""

        if block_comment_depth > 0:
            if ch == "/" and nxt == "-":
                block_comment_depth += 1
                i += 2
                continue
            if ch == "-" and nxt == "/":
                block_comment_depth -= 1
                i += 2
                continue
            i += 1
            continue

        if in_string:
            if ch == "\\" and i + 1 < n:
                i += 2
                continue
            if ch == '"':
                in_string = False
            i += 1
            continue

        if ch == '"' and block_comment_depth == 0:
            in_string = True
            i += 1
            continue

        if ch == "-" and nxt == "-":
            break

        if ch == "/" and nxt == "-":
            block_comment_depth += 1
            i += 2
            continue

        result.append(ch)
        i += 1

    return "".join(result), block_comment_depth


def extract_declaration_name(lines: list[str], sorry_idx: int) -> str | None:
    """Extract the declaration name containing this sorry.

    Returns "keyword name" (e.g. "def foo") — visibility and decl
    modifiers are deliberately dropped from the label: keyword+name is
    the declaration's identity; modifiers are noise for attribution.
    Anonymous `example : ...` has no name to capture and stays
    unattributed (None).
    """
    # Search backwards for declaration.
    # Support Unicode and qualified names (e.g., Foo.bar, foo', foo'').
    # Handles optional same-line attributes (@[...]), visibility
    # (private/protected/local), and decl modifiers
    # (noncomputable/unsafe/partial/nonrec). An attribute on its OWN
    # line above the declaration also works — the backward search hits
    # the declaration line before the attribute line.
    # axiom/constant deliberately absent: they have no proof body, so a
    # sorry can never be inside one; matching them would only create
    # misattribution risk for the nearest-header-wins backward search.
    #
    # The search STARTS AT the sorry's own line (not the line before):
    # single-line declarations (`def foo : Nat := by sorry`) put the
    # header and the sorry on the same line, and starting one line up
    # left every such sorry unattributed. Stop bound is -1 so line 0 is
    # included in the window.
    for i in range(sorry_idx, max(-1, sorry_idx - 50), -1):
        match = re.match(
            r"^\s*(?:@\[.*?\]\s*)?"
            r"(?:(?:private|protected|local)\s+)?"
            r"(?:(?:noncomputable|unsafe|partial|nonrec)\s+)?"
            r"(theorem|lemma|def|abbrev|example|instance|structure|class|inductive)\s+([\w.']+)",
            lines[i],
        )
        if match:
            return f"{match.group(1)} {match.group(2)}"
    return None


def extract_documentation(lines: list[str], sorry_idx: int) -> list[str]:
    """Extract TODO/NOTE comments near the sorry"""
    docs = []
    keywords = ["TODO", "NOTE", "FIXME", "STRATEGY", "DEPENDENCIES"]

    # Check lines BEFORE sorry (often comments precede the sorry)
    for i in range(max(0, sorry_idx - 5), sorry_idx):
        line = lines[i].strip()
        if line.startswith("--"):
            comment = line[2:].strip()
            if any(keyword in comment.upper() for keyword in keywords):
                docs.append(comment)

    # Check lines AFTER sorry
    for i in range(sorry_idx + 1, min(len(lines), sorry_idx + 10)):
        line = lines[i].strip()
        if line.startswith("--"):
            comment = line[2:].strip()
            if any(keyword in comment.upper() for keyword in keywords):
                docs.append(comment)
        elif line and not line.startswith("--"):
            break
    return docs


def find_sorries_in_file(filepath: Path) -> list[Sorry] | None:
    """Find all sorries in a single Lean file.

    Returns None when the file could not be read — callers must count
    that as a coverage failure, not an empty result. (Returning [] here
    previously let a directory of unreadable files report clean.)
    """
    try:
        with open(filepath, encoding="utf-8") as f:
            lines = f.readlines()
    except Exception as e:
        print(f"Warning: Could not read {filepath}: {e}", file=sys.stderr)
        return None

    sorries = []
    block_comment_depth = 0
    for i, line in enumerate(lines):
        # Fast path when we're not inside a block comment and the line has no
        # token of interest for sorry/comment/string parsing.
        if (
            block_comment_depth == 0
            and "sorry" not in line
            and "/-" not in line
            and '"' not in line
        ):
            continue

        code_part, block_comment_depth = strip_lean_comments_and_strings(
            line, block_comment_depth
        )
        if "sorry" not in code_part:
            continue

        if SORRY_TOKEN_PATTERN.search(code_part):
            context_before = [ln.rstrip() for ln in lines[max(0, i - 3) : i]]
            context_after = [
                ln.rstrip() for ln in lines[i + 1 : min(len(lines), i + 4)]
            ]

            sorry = Sorry(
                file=str(filepath),
                line=i + 1,  # 1-indexed
                context_before=context_before,
                context_after=context_after,
                documentation=extract_documentation(lines, i),
                in_declaration=extract_declaration_name(lines, i),
            )
            sorries.append(sorry)

    return sorries


def find_sorries(target: Path, include_deps: bool = False) -> ScanResult:
    """Find all sorries in target file or directory, with coverage counts.

    Args:
        target: File or directory to search
        include_deps: If False (default), exclude .lake/ directories (dependencies)
    """
    if target.is_file():
        # Guard: Also exclude .lake/ files unless --include-deps
        if not include_deps and ".lake" in target.parts:
            print(
                f"Skipping dependency file: {target} (use --include-deps to include)",
                file=sys.stderr,
            )
            return ScanResult(sorries=[], files_scanned=0, files_failed=0)
        file_sorries = find_sorries_in_file(target)
        if file_sorries is None:
            return ScanResult(sorries=[], files_scanned=0, files_failed=1)
        return ScanResult(sorries=file_sorries, files_scanned=1, files_failed=0)
    elif target.is_dir():
        # Guard: Exclude .lake directory or any subpath unless --include-deps
        if not include_deps and ".lake" in target.parts:
            print(
                f"Skipping dependency directory: {target} (use --include-deps to include)",
                file=sys.stderr,
            )
            return ScanResult(sorries=[], files_scanned=0, files_failed=0)
        sorries: list[Sorry] = []
        files_scanned = 0
        files_failed = 0

        # os.walk silently swallows errors (e.g. an unreadable subdirectory
        # just doesn't get descended into) unless onerror is passed — the
        # directory-level analog of an unreadable file. Both count as
        # coverage failures.
        def _walk_error(err: OSError) -> None:
            nonlocal files_failed
            print(f"Warning: Could not read {err.filename}: {err}", file=sys.stderr)
            files_failed += 1

        # Use os.walk for early termination of .lake/ directories (performance)
        for root, dirs, files in os.walk(target, onerror=_walk_error):
            # Prune .lake directories from traversal (don't descend into them)
            if not include_deps:
                dirs[:] = [d for d in dirs if d != ".lake"]
            for filename in files:
                if filename.endswith(".lean"):
                    lean_file = Path(root) / filename
                    file_sorries = find_sorries_in_file(lean_file)
                    if file_sorries is None:
                        files_failed += 1
                    else:
                        files_scanned += 1
                        sorries.extend(file_sorries)
        return ScanResult(
            sorries=sorries, files_scanned=files_scanned, files_failed=files_failed
        )
    else:
        raise ValueError(f"{target} is not a file or directory")


def format_text(sorries: list[Sorry]) -> str:
    """Format sorries as human-readable text"""
    output = []
    output.append(f"Found {len(sorries)} sorry statement(s)\n")
    output.append("=" * 80)

    for i, sorry in enumerate(sorries, 1):
        output.append(f"\n[{i}] {sorry.file}:{sorry.line}")
        if sorry.in_declaration:
            output.append(f"    In: {sorry.in_declaration}")

        if sorry.documentation:
            output.append("    Documentation:")
            for doc in sorry.documentation:
                output.append(f"      • {doc}")

        output.append("\n    Context:")
        for line in sorry.context_before[-2:]:
            output.append(f"      {line}")
        output.append("      >>> SORRY <<<")
        for line in sorry.context_after[:2]:
            output.append(f"      {line}")
        output.append("")

    return "\n".join(output)


def format_markdown(sorries: list[Sorry]) -> str:
    """Format sorries as Markdown"""
    output = []
    output.append("# Sorry Analysis Report\n")
    output.append(f"**Total sorries found:** {len(sorries)}\n")

    # Group by file
    by_file: dict[str, list[Sorry]] = {}
    for sorry in sorries:
        by_file.setdefault(sorry.file, []).append(sorry)

    for filepath, file_sorries in sorted(by_file.items()):
        output.append(f"## {filepath}\n")
        output.append(f"**Count:** {len(file_sorries)}\n")

        for sorry in file_sorries:
            output.append(f"### Line {sorry.line}")
            if sorry.in_declaration:
                output.append(f"**Declaration:** `{sorry.in_declaration}`\n")

            if sorry.documentation:
                output.append("**Documentation:**")
                for doc in sorry.documentation:
                    output.append(f"- {doc}")
                output.append("")

            output.append("**Context:**")
            output.append("```lean")
            for line in sorry.context_before[-2:]:
                output.append(line)
            output.append("sorry  -- ⚠️")
            for line in sorry.context_after[:2]:
                output.append(line)
            output.append("```\n")

    return "\n".join(output)


def format_json(result: ScanResult) -> str:
    """Format scan result as JSON (additive coverage fields)"""
    return json.dumps(
        {
            "total_count": len(result.sorries),
            "files_scanned": result.files_scanned,
            "files_failed": result.files_failed,
            "sorries": [asdict(s) for s in result.sorries],
        },
        indent=2,
    )


def format_summary(result: ScanResult) -> str:
    """Format scan result as a brief summary (file counts + total + coverage)"""
    sorries = result.sorries
    output = []
    # Group by file
    by_file: dict[str, list[Sorry]] = {}
    for sorry in sorries:
        by_file.setdefault(sorry.file, []).append(sorry)

    output.append(
        f"Sorry Summary: {len(sorries)} total across {len(by_file)} file(s) "
        f"with sorries; {result.files_scanned} file(s) scanned"
    )
    output.append("-" * 50)

    for filepath, file_sorries in sorted(by_file.items(), key=lambda x: -len(x[1])):
        output.append(f"  {filepath}: {len(file_sorries)} sorries")

    return "\n".join(output)


def interactive_mode(sorries: list[Sorry]) -> None:
    """Interactive mode to navigate and select sorries"""
    if not sorries:
        print("No sorries found!")
        return

    # Group by file
    by_file: dict[str, list[Sorry]] = {}
    for sorry in sorries:
        by_file.setdefault(sorry.file, []).append(sorry)

    print(f"\n{'=' * 80}")
    print(f"Found {len(sorries)} sorry statement(s) across {len(by_file)} file(s)")
    print(f"{'=' * 80}\n")

    # Display files with sorry counts
    files = sorted(by_file.items(), key=lambda x: len(x[1]), reverse=True)
    print("Files with sorries:")
    for i, (filepath, file_sorries) in enumerate(files, 1):
        print(f"  [{i}] {filepath} ({len(file_sorries)} sorries)")

    print("\nOptions:")
    print("  [1-N] - View sorries in file N")
    print("  [q]   - Quit")

    while True:
        try:
            choice = input("\nSelect file (or 'q' to quit): ").strip()
            if choice.lower() == "q":
                break

            idx = int(choice) - 1
            if 0 <= idx < len(files):
                filepath, file_sorries = files[idx]
                show_file_sorries(filepath, file_sorries)
            else:
                print("Invalid selection")
        except (ValueError, EOFError, KeyboardInterrupt):
            print("\nExiting...")
            break


def show_file_sorries(filepath: str, sorries: list[Sorry]) -> None:
    """Show sorries in a specific file with navigation"""
    print(f"\n{'=' * 80}")
    print(f"File: {filepath}")
    print(f"{'=' * 80}\n")

    for i, sorry in enumerate(sorries, 1):
        print(f"[{i}] Line {sorry.line}", end="")
        if sorry.in_declaration:
            print(f" - {sorry.in_declaration}", end="")
        print()

    print("\nOptions:")
    print("  [1-N]  - View sorry details")
    print("  [o N]  - Open file at sorry N in $EDITOR")
    print("  [b]    - Back to file list")
    print("  [q]    - Quit")

    while True:
        try:
            choice = input("\nSelect sorry (or 'b'/'q'): ").strip()

            if choice.lower() == "q":
                sys.exit(0)
            elif choice.lower() == "b":
                return
            elif choice.lower().startswith("o "):
                # Open in editor
                try:
                    idx = int(choice.split()[1]) - 1
                    if 0 <= idx < len(sorries):
                        sorry = sorries[idx]
                        editor = os.environ.get("EDITOR", "vim")
                        subprocess.call([editor, f"+{sorry.line}", sorry.file])
                    else:
                        print("Invalid selection")
                except (ValueError, IndexError):
                    print("Usage: o <number>")
            else:
                idx = int(choice) - 1
                if 0 <= idx < len(sorries):
                    show_sorry_details(sorries[idx])
                else:
                    print("Invalid selection")
        except (ValueError, EOFError, KeyboardInterrupt):
            print("\nExiting...")
            sys.exit(0)


def show_sorry_details(sorry: Sorry) -> None:
    """Show detailed information about a specific sorry"""
    print(f"\n{'─' * 80}")
    print(f"Sorry at {sorry.file}:{sorry.line}")
    if sorry.in_declaration:
        print(f"Declaration: {sorry.in_declaration}")
    print(f"{'─' * 80}")

    if sorry.documentation:
        print("\nDocumentation:")
        for doc in sorry.documentation:
            print(f"  • {doc}")

    print("\nContext:")
    print("─" * 40)
    for line in sorry.context_before[-5:]:
        print(f"  {line}")
    print("  >>> SORRY HERE <<<")
    for line in sorry.context_after[:5]:
        print(f"  {line}")
    print("─" * 40)

    input("\nPress Enter to continue...")


def main() -> None:
    if len(sys.argv) < 2:
        # lstrip() avoids printing a leading blank line when the module
        # docstring is block-form (opening `"""` on its own line).
        print((__doc__ or "").lstrip())
        sys.exit(1)

    # Catch common mistake: flag where target path is expected
    if sys.argv[1].startswith("-"):
        print(
            "Error: missing target path (first argument must be a file or directory)",
            file=sys.stderr,
        )
        print(
            "Usage: sorry_analyzer.py <file-or-directory> [--format=FORMAT | --format FORMAT]",
            file=sys.stderr,
        )
        sys.exit(1)

    target = Path(sys.argv[1])
    format_type = "text"
    interactive = False
    include_deps = False
    exit_zero_on_findings = False

    # Parse arguments
    valid_formats = ("text", "json", "markdown", "summary")
    format_aliases = {"detail": "text"}
    i = 2
    while i < len(sys.argv):
        arg = sys.argv[i]
        if arg.startswith("--format="):
            format_type = arg.split("=", 1)[1]
            format_type = format_aliases.get(format_type, format_type)
            if format_type not in valid_formats:
                print(
                    f"Error: Unknown format '{format_type}'. Valid: {', '.join(valid_formats)} (alias: detail -> text)",
                    file=sys.stderr,
                )
                sys.exit(1)
        elif arg == "--format":
            i += 1
            if i >= len(sys.argv):
                print("Error: --format requires a value", file=sys.stderr)
                sys.exit(1)
            format_type = sys.argv[i]
            format_type = format_aliases.get(format_type, format_type)
            if format_type not in valid_formats:
                print(
                    f"Error: Unknown format '{format_type}'. Valid: {', '.join(valid_formats)} (alias: detail -> text)",
                    file=sys.stderr,
                )
                sys.exit(1)
        elif arg == "--interactive":
            interactive = True
        elif arg == "--include-deps":
            include_deps = True
        elif arg in ("--exit-zero-on-findings", "--report-only"):
            exit_zero_on_findings = True
        else:
            print(f"Error: Unknown flag: {arg}", file=sys.stderr)
            sys.exit(1)
        i += 1

    if not target.exists():
        print(f"Error: {target} does not exist", file=sys.stderr)
        sys.exit(1)

    # Find all sorries (excludes .lake/ by default)
    result = find_sorries(target, include_deps=include_deps)
    sorries = result.sorries

    # Coverage failures exit 2 regardless of --exit-zero-on-findings: that
    # flag makes FINDINGS non-fatal for reporting; a run that scanned
    # nothing (or couldn't read part of the tree) is a different category —
    # a gate that can't answer must not pass. Same policy as
    # check_axioms_inline.sh (#145) and unused_declarations.sh (#146).
    coverage_failed = result.files_scanned == 0 or result.files_failed > 0
    if coverage_failed:
        if result.files_scanned == 0:
            print(
                f"Warning: no .lean files were scanned under {target} — "
                "nothing was analyzed",
                file=sys.stderr,
            )
        if result.files_failed > 0:
            print(
                f"Warning: {result.files_failed} path(s) could not be read — "
                "coverage is incomplete",
                file=sys.stderr,
            )

    # Interactive mode takes precedence — but not on coverage failure:
    # interactive_mode's "No sorries found!" greeting would be exactly the
    # false reassurance the coverage check exists to remove.
    if interactive:
        if coverage_failed:
            sys.exit(2)
        interactive_mode(sorries)
        sys.exit(0 if len(sorries) == 0 or exit_zero_on_findings else 1)

    # Format output
    if format_type == "json":
        print(format_json(result))
    elif format_type == "markdown":
        print(format_markdown(sorries))
    elif format_type == "summary":
        print(format_summary(result))
    else:
        print(format_text(sorries))

    # Exit codes: 2 coverage failure > 1 findings > 0 clean.
    if coverage_failed:
        sys.exit(2)
    sys.exit(0 if len(sorries) == 0 or exit_zero_on_findings else 1)


if __name__ == "__main__":
    main()

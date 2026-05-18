"""Forward-direction exclusions for the doc-sync test (Layer 3).

Each entry is a (command_name, distinctive_substring) pair for a documented
rule that is intentionally NOT encoded in COMMAND_SPECS because encoding it
would require I/O beyond os.path.exists, interactive user prompting, or
repo-level search.

The doc-sync test's forward pass (step 5) checks extracted doc fragments
against this list BEFORE asserting they are encoded in specs. If a fragment
matches an exclusion, it is skipped.

This list must stay under ~10 entries. If it grows much larger, reconsider
either the parser's I/O budget or the doc format.
"""

from __future__ import annotations

EXCLUSIONS: list[tuple[str, str]] = [
    # --- Class (a): file-content I/O beyond os.path.exists ---
    # .gitignore hints — requires reading .gitignore
    ("draft", "not in `.gitignore`"),
    ("learn", "not in `.gitignore`"),
    ("formalize", "not in `.gitignore`"),
    # --source unreadable/unsupported format — requires content sniffing
    ("draft", "unreadable format"),
    ("formalize", "unreadable format"),
    ("learn", "Unsupported source type"),
    # --- Class (b): interactive user prompting ---
    # learn track picker — model-side interactive flow
    ("learn", "prompt track picker"),
    # --- Class (c): repo-level search ---
    # learn scope-coercion exception — requires local-declaration resolution
    ("learn", "unless topic resolves to a local declaration"),
]

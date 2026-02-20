---
name: zulip-extract
description: Extract Zulip thread HTML dumps into readable plain text. Use when the user provides a Zulip HTML file or asks to parse/read/convert/summarize a Zulip thread.
---

# Zulip Thread Extractor

Run the bundled script to convert a Zulip HTML page dump into plain text.

## Usage
```bash
uv run "$LEAN4_PLUGIN_ROOT/skills/zulip-extract/scripts/zulip_thread_extract.py" input.html output.txt
```

The script has zero dependencies beyond Python 3 stdlib.
It extracts sender, timestamp, message content (with code blocks,
links, quotes, mentions), and reactions.

If `LEAN4_PLUGIN_ROOT` is unavailable, call the script by repo-relative path:
```bash
uv run plugins/lean4/skills/zulip-extract/scripts/zulip_thread_extract.py input.html output.txt
```

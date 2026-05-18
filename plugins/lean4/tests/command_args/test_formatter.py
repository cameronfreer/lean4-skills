"""Snapshot tests for format_validated_block / parse_validated_block round-trip."""

from __future__ import annotations

import json
import os
import sys
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "lib"))

from command_args.formatter import format_validated_block, parse_validated_block
from command_args.types import ParseResult, ResolvedFlag


class TestFormatterRoundTrip(unittest.TestCase):
    """format_validated_block and parse_validated_block are exact inverses."""

    def test_basic_round_trip(self):
        result = ParseResult(
            command="draft",
            raw_tail='"Theorem 1" --mode=attempt',
            positionals={"topic": "Theorem 1"},
            options={
                "--mode": ResolvedFlag(
                    value="attempt",
                    source="explicit",
                    enforcement="startup-validated",
                ),
                "--level": ResolvedFlag(
                    value="intermediate",
                    source="default",
                    enforcement="startup-validated",
                ),
            },
        )
        block = format_validated_block(result)
        parsed = parse_validated_block(block)
        self.assertEqual(parsed.command, result.command)
        self.assertEqual(parsed.raw_tail, result.raw_tail)
        self.assertEqual(parsed.positionals, result.positionals)
        self.assertEqual(parsed.options["--mode"], result.options["--mode"])
        self.assertEqual(parsed.options["--level"], result.options["--level"])

    def test_round_trip_with_coerced_flag(self):
        result = ParseResult(
            command="autoprove",
            raw_tail="--commit=ask",
            options={
                "--commit": ResolvedFlag(
                    value="auto",
                    source="coerced",
                    enforcement="startup-validated",
                    coerced_from="ask",
                ),
            },
        )
        block = format_validated_block(result)
        parsed = parse_validated_block(block)
        self.assertEqual(parsed.options["--commit"].value, "auto")
        self.assertEqual(parsed.options["--commit"].source, "coerced")
        self.assertEqual(parsed.options["--commit"].coerced_from, "ask")

    def test_round_trip_empty_positionals(self):
        result = ParseResult(
            command="prove",
            raw_tail="",
            positionals={},
            options={
                "--repair-only": ResolvedFlag(
                    value=False,
                    source="default",
                    enforcement="startup-validated",
                ),
            },
        )
        block = format_validated_block(result)
        parsed = parse_validated_block(block)
        self.assertEqual(parsed.positionals, {})

    def test_round_trip_with_warnings_and_coercions(self):
        result = ParseResult(
            command="learn",
            raw_tail='"groups" --source=notes.md --scope=file',
            positionals={"topic": "groups"},
            options={
                "--scope": ResolvedFlag(
                    value="file",
                    source="explicit",
                    enforcement="startup-validated",
                ),
            },
            coercions=["--scope stayed file (no coercion)"],
            warnings=["source overrides scope for initial discovery"],
        )
        block = format_validated_block(result)
        parsed = parse_validated_block(block)
        self.assertEqual(parsed.coercions, result.coercions)
        self.assertEqual(parsed.warnings, result.warnings)

    def test_block_fencing(self):
        result = ParseResult(
            command="prove",
            raw_tail="MyFile.lean",
            positionals={"scope": "MyFile.lean"},
            options={
                "--repair-only": ResolvedFlag(
                    value=False,
                    source="default",
                    enforcement="startup-validated",
                ),
            },
        )
        block = format_validated_block(result)
        lines = block.split("\n")
        self.assertEqual(lines[0], "```validated-invocation")
        self.assertEqual(lines[-1], "```")

    def test_block_body_is_valid_json(self):
        result = ParseResult(
            command="draft",
            raw_tail='"x"',
            positionals={"topic": "x"},
            options={
                "--mode": ResolvedFlag(
                    value="skeleton",
                    source="default",
                    enforcement="startup-validated",
                ),
            },
        )
        block = format_validated_block(result)
        # Extract body between fences and parse as JSON
        body = "\n".join(block.split("\n")[1:-1])
        data = json.loads(body)
        self.assertEqual(data["command"], "draft")

    def test_round_trip_string_that_looks_like_int(self):
        """String '123' must not become int 123 after round-trip (lossless)."""
        result = ParseResult(
            command="draft",
            raw_tail='--source=123 "x"',
            positionals={"topic": "x"},
            options={
                "--source": ResolvedFlag(
                    value="123",
                    source="explicit",
                    enforcement="startup-validated",
                ),
            },
        )
        block = format_validated_block(result)
        parsed = parse_validated_block(block)
        self.assertEqual(parsed.options["--source"].value, "123")
        self.assertIsInstance(parsed.options["--source"].value, str)

    def test_round_trip_string_none_literal(self):
        """String 'None' as a value must not become Python None."""
        result = ParseResult(
            command="draft",
            raw_tail='"x"',
            positionals={"topic": "x"},
            options={
                "--source": ResolvedFlag(
                    value="None",
                    source="explicit",
                    enforcement="startup-validated",
                ),
            },
        )
        block = format_validated_block(result)
        parsed = parse_validated_block(block)
        self.assertEqual(parsed.options["--source"].value, "None")
        self.assertIsInstance(parsed.options["--source"].value, str)

    def test_round_trip_multiline_raw_tail(self):
        """Multiline raw_tail must survive round-trip (JSON handles this)."""
        result = ParseResult(
            command="draft",
            raw_tail='"line one\nline two" --mode=skeleton',
            positionals={"topic": "line one\nline two"},
            options={},
        )
        block = format_validated_block(result)
        parsed = parse_validated_block(block)
        self.assertEqual(parsed.raw_tail, result.raw_tail)
        self.assertEqual(parsed.positionals["topic"], "line one\nline two")

    def test_round_trip_embedded_backticks(self):
        """Backticks in values must not corrupt the fence."""
        result = ParseResult(
            command="draft",
            raw_tail='"has ``` backticks"',
            positionals={"topic": "has ``` backticks"},
            options={},
        )
        block = format_validated_block(result)
        parsed = parse_validated_block(block)
        self.assertEqual(parsed.positionals["topic"], "has ``` backticks")


if __name__ == "__main__":
    unittest.main()

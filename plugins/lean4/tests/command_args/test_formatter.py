"""Snapshot tests for format_validated_block / parse_validated_block round-trip."""
import os
import sys
import unittest

# Ensure the library package is importable.
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "lib"))

from command_args.formatter import format_validated_block, parse_validated_block
from command_args.types import ParseResult, ResolvedFlag


class TestFormatterRoundTrip(unittest.TestCase):
    """format_validated_block and parse_validated_block are exact inverses."""

    def test_basic_round_trip(self):
        """Build a ParseResult with known values, format it, parse it back."""
        original = ParseResult(
            command="draft",
            raw_tail='"Theorem 1" --mode=skeleton',
            positionals={"topic": "Theorem 1"},
            options={
                "--mode": ResolvedFlag(
                    value="skeleton", source="explicit",
                    enforcement="startup-validated",
                ),
                "--level": ResolvedFlag(
                    value="intermediate", source="default",
                    enforcement="startup-validated",
                ),
            },
            coercions=[],
            warnings=[],
            errors=[],
        )
        block = format_validated_block(original)
        restored = parse_validated_block(block)

        self.assertEqual(restored.command, original.command)
        self.assertEqual(restored.raw_tail, original.raw_tail)
        self.assertEqual(restored.positionals, original.positionals)
        self.assertEqual(restored.errors, original.errors)
        self.assertEqual(restored.coercions, original.coercions)
        self.assertEqual(restored.warnings, original.warnings)
        for name in original.options:
            self.assertEqual(restored.options[name].value, original.options[name].value)
            self.assertEqual(restored.options[name].source, original.options[name].source)
            self.assertEqual(restored.options[name].enforcement, original.options[name].enforcement)
            self.assertIsNone(restored.options[name].coerced_from)

    def test_round_trip_with_coerced_flag(self):
        """Coerced flag preserves source='coerced' and coerced_from value."""
        original = ParseResult(
            command="draft",
            raw_tail='"x" --intent=auto',
            positionals={"topic": "x"},
            options={
                "--intent": ResolvedFlag(
                    value="usage", source="coerced",
                    enforcement="startup-validated",
                    coerced_from="auto",
                ),
            },
            coercions=["--intent=auto coerced to usage"],
            warnings=[],
            errors=[],
        )
        block = format_validated_block(original)
        restored = parse_validated_block(block)

        self.assertEqual(restored.options["--intent"].value, "usage")
        self.assertEqual(restored.options["--intent"].source, "coerced")
        self.assertEqual(restored.options["--intent"].coerced_from, "auto")
        self.assertEqual(restored.coercions, ["--intent=auto coerced to usage"])

    def test_round_trip_empty_positionals(self):
        """A result with no positionals round-trips through (none) sentinel."""
        original = ParseResult(
            command="autoprove",
            raw_tail="--planning=on",
            positionals={},
            options={
                "--planning": ResolvedFlag(
                    value="on", source="explicit",
                    enforcement="startup-validated",
                ),
            },
        )
        block = format_validated_block(original)
        restored = parse_validated_block(block)

        self.assertEqual(restored.positionals, {})
        self.assertEqual(restored.options["--planning"].value, "on")

    def test_round_trip_with_warnings_and_coercions(self):
        """Both warnings and coercions lists survive the round-trip."""
        original = ParseResult(
            command="learn",
            raw_tail="topology --track=nng-like",
            positionals={"topic": "topology"},
            options={
                "--track": ResolvedFlag(
                    value=None, source="coerced",
                    enforcement="startup-validated",
                    coerced_from="nng-like",
                ),
                "--style": ResolvedFlag(
                    value="tour", source="default",
                    enforcement="startup-validated",
                ),
            },
            coercions=["--track ignored: only valid with --style=game"],
            warnings=["--source overrides --scope for initial discovery"],
            errors=[],
        )
        block = format_validated_block(original)
        restored = parse_validated_block(block)

        self.assertEqual(restored.coercions, original.coercions)
        self.assertEqual(restored.warnings, original.warnings)

    def test_block_fencing(self):
        """Formatted block starts with ```validated-invocation and ends with ```."""
        result = ParseResult(
            command="prove",
            raw_tail="MyFile.lean",
            positionals={"scope": "MyFile.lean"},
            options={
                "--repair-only": ResolvedFlag(
                    value=False, source="default",
                    enforcement="startup-validated",
                ),
            },
        )
        block = format_validated_block(result)
        lines = block.split("\n")
        self.assertEqual(lines[0], "```validated-invocation")
        self.assertEqual(lines[-1], "```")


if __name__ == "__main__":
    unittest.main()

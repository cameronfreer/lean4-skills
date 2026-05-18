"""Core parser: parse_invocation(spec, raw_tail, *, cwd) -> ParseResult."""

from __future__ import annotations

import os

from .tokenizer import normalize_flags, tokenize
from .types import (
    CommandSpec,
    FlagSpec,
    ParseContext,
    ParseResult,
    ResolvedFlag,
    Source,
)


def parse_invocation(spec: CommandSpec, raw_tail: str, *, cwd: str) -> ParseResult:
    """Parse a slash-command raw tail against a CommandSpec.

    Args:
        spec: The command's specification.
        raw_tail: Everything after ``/lean4:<name> ``.
        cwd: Absolute path to the user's workspace cwd.

    Returns:
        A ParseResult with all flags resolved, defaults applied, coercions run,
        and cross-validations evaluated.
    """
    cwd = os.path.abspath(cwd)
    ctx = ParseContext(cwd=cwd)
    result = ParseResult(command=spec.name, raw_tail=raw_tail)

    # Build lookup tables
    flag_by_name: dict[str, FlagSpec] = {}
    for fs in spec.flags:
        flag_by_name[fs.name] = fs
        for alias in fs.aliases:
            flag_by_name[alias] = fs

    # Tokenize
    try:
        tokens = normalize_flags(tokenize(raw_tail))
    except ValueError as e:
        result.errors.append(str(e))
        return result

    # Parse tokens into positionals and raw flag values
    positional_idx = 0
    raw_flags: dict[str, str | bool] = {}
    i = 0
    while i < len(tokens):
        token = tokens[i]
        if token.startswith("--"):
            canonical_spec = flag_by_name.get(token)
            if canonical_spec is None:
                result.errors.append(f"Unknown flag: {token}")
                i += 1
                continue
            canonical_name = canonical_spec.name
            if canonical_spec.type == "bool":
                # Bool flags: if next token looks like a bool value, consume it.
                # This handles both --flag (presence = true) and --flag=false
                # (expanded to --flag false by normalize_flags).
                if i + 1 < len(tokens) and tokens[i + 1].lower() in (
                    "true",
                    "false",
                    "1",
                    "0",
                    "yes",
                    "no",
                ):
                    raw_flags[canonical_name] = tokens[i + 1]
                    i += 1
                else:
                    raw_flags[canonical_name] = True
            else:
                if i + 1 >= len(tokens):
                    result.errors.append(f"Flag {token} requires a value")
                    i += 1
                    continue
                raw_flags[canonical_name] = tokens[i + 1]
                i += 1
        else:
            # Positional
            if positional_idx < len(spec.positionals):
                ps = spec.positionals[positional_idx]
                result.positionals[ps.name] = token
                positional_idx += 1
            else:
                result.errors.append(f"Unexpected positional argument: {token!r}")
        i += 1

    if result.errors:
        return result

    # Build the raw options dict for coercions/validations to read
    raw_options: dict[str, object] = {}
    for fs in spec.flags:
        raw_options[fs.name] = raw_flags.get(fs.name, fs.default)

    # Validate and resolve each flag
    for fs in spec.flags:
        user_supplied = fs.name in raw_flags
        raw_value = raw_flags.get(fs.name, fs.default)

        # Type validation
        parsed_value, type_error = _validate_type(fs, raw_value)
        if type_error:
            result.errors.append(type_error)
            continue

        # Coercion
        coerced = False
        coerced_from = None
        if user_supplied and fs.coerce is not None:
            try:
                new_value, note = fs.coerce.fn(parsed_value, raw_options, ctx)
            except Exception as e:
                result.errors.append(f"Coercion error for {fs.name}: {e}")
                continue
            if new_value != parsed_value:
                coerced_from = parsed_value
                parsed_value = new_value
                coerced = True
            if note:
                result.coercions.append(note)

        # Determine source
        source: Source
        if coerced:
            source = "coerced"
        elif user_supplied:
            source = "explicit"
        else:
            source = "default"

        result.options[fs.name] = ResolvedFlag(
            value=parsed_value,
            source=source,
            enforcement=fs.enforcement,
            coerced_from=coerced_from,
        )

    if result.errors:
        return result

    # Companion-flag checks (requires / forbidden_with)
    for fs in spec.flags:
        if fs.name not in raw_flags:
            continue
        for req in fs.requires:
            if req not in raw_flags:
                result.errors.append(f"{fs.name} requires {req}")
        for forbidden in fs.forbidden_with:
            if forbidden in raw_flags:
                result.errors.append(f"{fs.name} is incompatible with {forbidden}")

    # Cross-validations — inject positionals as __positional_<name> sentinels
    # so cross-validation functions can check for positional presence.
    resolved_values: dict[str, object] = {
        name: rf.value for name, rf in result.options.items()
    }
    for pos_name, pos_value in result.positionals.items():
        resolved_values[f"__positional_{pos_name}"] = pos_value
    for cv in spec.cross_validations:
        try:
            messages = cv.fn(resolved_values, ctx)
        except Exception as e:
            result.errors.append(f"Validation error ({cv.rule_id}): {e}")
            continue
        if cv.severity == "error":
            result.errors.extend(messages)
        else:
            result.warnings.extend(messages)

    return result


def _validate_type(fs: FlagSpec, raw_value: object) -> tuple[object, str | None]:
    """Validate and parse a raw flag value according to its type spec."""
    if raw_value is None:
        return None, None

    if fs.type == "bool":
        if isinstance(raw_value, bool):
            return raw_value, None
        s = str(raw_value).lower()
        if s in ("true", "1", "yes"):
            return True, None
        if s in ("false", "0", "no"):
            return False, None
        return raw_value, f"{fs.name}: invalid boolean value {raw_value!r}"

    if fs.type == "enum":
        s = str(raw_value)
        if s not in fs.enum_values:
            valid = ", ".join(fs.enum_values)
            return raw_value, f"{fs.name}: invalid value {s!r}; valid values: {valid}"
        return s, None

    if fs.type == "int":
        try:
            n = int(str(raw_value))
        except (ValueError, TypeError):
            return raw_value, f"{fs.name}: expected integer, got {raw_value!r}"
        if fs.int_min is not None and n < fs.int_min:
            return n, f"{fs.name}: value {n} is below minimum {fs.int_min}"
        if fs.int_max is not None and n > fs.int_max:
            return n, f"{fs.name}: value {n} is above maximum {fs.int_max}"
        return n, None

    if fs.type == "duration":
        return _parse_duration(fs.name, raw_value)

    # path and freeform: pass through as string
    return str(raw_value) if raw_value is not None else None, None


def _parse_duration(flag_name: str, raw_value: object) -> tuple[object, str | None]:
    """Validate and normalize a duration string like '30s', '10m', '2h'.

    Returns the duration as a suffix-bearing string (e.g. "900s", "15m")
    so the downstream consumer (cycle_tracker.sh) always receives an
    explicit unit. cycle_tracker.sh interprets bare numbers as minutes,
    so we never emit bare integers — that avoids the ambiguity where
    the parser means seconds but the tracker reads minutes.

    Accepted input forms: '30s', '15m', '2h', bare number (= minutes,
    normalized to '<N>m').
    """
    s = str(raw_value).strip().lower()
    if not s:
        return raw_value, f"{flag_name}: empty duration"

    # Try pure numeric — interpreted as minutes (matches tracker convention),
    # normalized to explicit '<N>m' suffix.
    try:
        n = int(s)
        return f"{n}m", None
    except ValueError:
        pass

    # Try suffix-based — validate as integer prefix + suffix to match
    # cycle_tracker.sh's _parse_duration which requires ^[0-9]+[mshMSH]?$.
    valid_suffixes = {"s", "m", "h"}
    if s[-1] in valid_suffixes:
        prefix = s[:-1]
        if prefix.isdigit():
            return s, None
        # Reject fractional values — tracker only accepts integers.
        try:
            float(prefix)
            return raw_value, (
                f"{flag_name}: fractional duration {raw_value!r} not supported; "
                "use an integer with s/m/h suffix (e.g. 90s, 15m, 2h)"
            )
        except ValueError:
            pass

    return (
        raw_value,
        f"{flag_name}: invalid duration {raw_value!r}; expected e.g. '10m', '2h', '120s'",
    )

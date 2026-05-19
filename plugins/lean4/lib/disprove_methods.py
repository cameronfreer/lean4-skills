"""Loader for the /lean4:disprove Method Registry.

The registry is a stable vocabulary that the cycling LLM draws from to
specialize the Step 1 / Step 2 menus. Data lives in
``data/disprove_methods.toml`` next to this module. Python 3.11+ stdlib
``tomllib`` is the only parser dependency — no PyYAML.

The loader validates the registry on every load (no caching of unchecked
data); it is cheap and runs at session startup. Errors are raised eagerly
with the offending method ``id`` in the message.
"""
from __future__ import annotations

import os
import tomllib
from dataclasses import dataclass, field
from typing import Mapping


_HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT_REGISTRY_PATH = os.path.join(_HERE, "data", "disprove_methods.toml")

# Canonical shape ids — keep in sync with disprove-engine.md § Shape Normalization.
_VALID_SHAPES = frozenset(range(1, 8))
_VALID_COST_CLASSES = frozenset({"cheap", "medium", "expensive"})
_VALID_PARAM_TYPES = frozenset({"bool", "int", "string", "enum", "list[string]"})


@dataclass(frozen=True)
class ParamSpec:
    """Per-parameter schema for a method.

    The ``custom-config`` extra in Step 2 is validated against this; the
    cycling LLM also reads it to specialize candidate configs.
    """

    type: str
    default: object
    int_min: int | None = None
    int_max: int | None = None
    enum_values: tuple[str, ...] = ()
    audit_worthy: bool = False


@dataclass(frozen=True)
class MethodEntry:
    """A single method entry in the registry."""

    id: str
    display_name: str
    applies_to_shapes: tuple[int, ...]
    cost_class: str
    budget_hint_seconds: int
    false_negative_notes: str
    cert_template_ref: str
    params: Mapping[str, ParamSpec] = field(default_factory=dict)


class RegistryError(ValueError):
    """Raised when the registry fails schema validation."""


def load_registry(path: str | None = None) -> tuple[MethodEntry, ...]:
    """Load and validate the Method Registry.

    Args:
        path: Optional override for testing. Defaults to
            ``data/disprove_methods.toml`` next to this module.

    Returns:
        Tuple of validated ``MethodEntry`` records in declaration order.

    Raises:
        RegistryError: If any entry fails schema validation, or if two
            entries share an ``id``.
        OSError: If the file is unreadable.
        tomllib.TOMLDecodeError: If the file is malformed TOML.
    """
    p = path or DEFAULT_REGISTRY_PATH
    with open(p, "rb") as f:
        data = tomllib.load(f)

    raw_methods = data.get("methods")
    if not isinstance(raw_methods, list) or not raw_methods:
        raise RegistryError(
            f"registry at {p!r}: top-level [[methods]] array is missing or empty"
        )

    entries: list[MethodEntry] = []
    seen_ids: set[str] = set()
    for raw in raw_methods:
        entry = _build_entry(raw, source=p)
        if entry.id in seen_ids:
            raise RegistryError(f"duplicate method id: {entry.id!r}")
        seen_ids.add(entry.id)
        entries.append(entry)
    return tuple(entries)


def _build_entry(raw: object, source: str) -> MethodEntry:
    if not isinstance(raw, dict):
        raise RegistryError(f"registry at {source!r}: entry is not a table: {raw!r}")

    required = (
        "id",
        "display_name",
        "applies_to_shapes",
        "cost_class",
        "budget_hint_seconds",
        "false_negative_notes",
        "cert_template_ref",
    )
    missing = [k for k in required if k not in raw]
    if missing:
        rid = raw.get("id", "<unknown>")
        raise RegistryError(
            f"method {rid!r}: missing required fields: {', '.join(missing)}"
        )

    rid = str(raw["id"])
    shapes = tuple(int(s) for s in raw["applies_to_shapes"])
    bad_shapes = [s for s in shapes if s not in _VALID_SHAPES]
    if bad_shapes:
        raise RegistryError(
            f"method {rid!r}: applies_to_shapes contains values outside {{1..7}}: {bad_shapes}"
        )
    if not shapes:
        raise RegistryError(f"method {rid!r}: applies_to_shapes must be non-empty")

    cost_class = str(raw["cost_class"])
    if cost_class not in _VALID_COST_CLASSES:
        raise RegistryError(
            f"method {rid!r}: invalid cost_class {cost_class!r} "
            f"(expected one of {sorted(_VALID_COST_CLASSES)})"
        )

    budget = int(raw["budget_hint_seconds"])
    if budget <= 0:
        raise RegistryError(
            f"method {rid!r}: budget_hint_seconds must be a positive integer, "
            f"got {raw['budget_hint_seconds']!r}"
        )

    params_raw = raw.get("params", {})
    if not isinstance(params_raw, dict):
        raise RegistryError(
            f"method {rid!r}: params must be a table, got {type(params_raw).__name__}"
        )
    params = {name: _build_param(rid, name, spec) for name, spec in params_raw.items()}

    return MethodEntry(
        id=rid,
        display_name=str(raw["display_name"]),
        applies_to_shapes=shapes,
        cost_class=cost_class,
        budget_hint_seconds=budget,
        false_negative_notes=str(raw["false_negative_notes"]),
        cert_template_ref=str(raw["cert_template_ref"]),
        params=params,
    )


def _build_param(method_id: str, name: str, spec: object) -> ParamSpec:
    if not isinstance(spec, dict):
        raise RegistryError(
            f"method {method_id!r} param {name!r}: spec is not a table"
        )
    if "type" not in spec:
        raise RegistryError(f"method {method_id!r} param {name!r}: missing 'type'")
    ptype = str(spec["type"])
    if ptype not in _VALID_PARAM_TYPES:
        raise RegistryError(
            f"method {method_id!r} param {name!r}: invalid type {ptype!r} "
            f"(expected one of {sorted(_VALID_PARAM_TYPES)})"
        )
    if "default" not in spec:
        raise RegistryError(f"method {method_id!r} param {name!r}: missing 'default'")

    enum_values: tuple[str, ...] = ()
    if ptype == "enum":
        ev = spec.get("enum_values")
        if not isinstance(ev, list) or not ev:
            raise RegistryError(
                f"method {method_id!r} param {name!r}: enum requires non-empty enum_values"
            )
        enum_values = tuple(str(v) for v in ev)
        if spec["default"] not in enum_values:
            raise RegistryError(
                f"method {method_id!r} param {name!r}: default {spec['default']!r} "
                f"not in enum_values {enum_values}"
            )

    return ParamSpec(
        type=ptype,
        default=spec["default"],
        int_min=spec.get("int_min"),
        int_max=spec.get("int_max"),
        enum_values=enum_values,
        audit_worthy=bool(spec.get("audit_worthy", False)),
    )


def find_by_id(
    entries: tuple[MethodEntry, ...], method_id: str
) -> MethodEntry | None:
    """Return the entry whose ``id`` matches, or ``None``."""
    for e in entries:
        if e.id == method_id:
            return e
    return None

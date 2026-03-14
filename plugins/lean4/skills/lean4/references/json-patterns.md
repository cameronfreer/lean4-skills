# JSON Patterns

> **Version note:** The `json%` elaboration syntax lives in `Lean.Data.Json.Elab`. Antiquotation and object-key rules may evolve across toolchain versions; verify against the current source if behavior differs from what is documented here.

## Scope

Reference for constructing JSON values in Lean 4 using `json%` elaboration syntax, `Json.mkObj`, and `ToJson` instances. Useful for any Lean code that constructs JSON — scripts, plugins, metaprograms, tooling.

**Read when:** building JSON payloads, interpolating Lean values into JSON, deriving or using `ToJson`, or debugging `json%` elaboration errors.

**Not part of the prove/autoprove default loop.** This is supplemental reference material for projects that produce JSON output.

## When to Use

- Constructing JSON payloads in Lean code
- Using `json%` elaboration syntax
- Deriving or using `ToJson` instances
- Debugging `json%` syntax or elaboration errors

## Quick Start

1. Import `Lean.Data.Json` (or at least `Lean.Data.Json.Elab` and `Lean.Data.Json.FromToJson`).
2. Build a static skeleton with `json%{...}` or `json%[...]`.
3. Interpolate computed values with `$expr` (requires `ToJson` for `expr`'s type).
4. Keep object keys static (`ident` or string literal); switch to `Json.mkObj` for dynamic keys.
5. Inspect output with `#eval j.pretty` or `#eval j.compress`.

```lean
import Lean.Data.Json
open Lean

def payload (user : String) (scores : Array Nat) : Json :=
  json%{
    user: $user,
    scores: $scores,
    active: true,
    "meta": {"source": "cli", "version": 1}
  }
```

## Stdlib Semantics

Ground truth from `Lean/Data/Json/Elab.lean`:

- `json% null` elaborates to `Lean.Json.null`.
- `json% true` / `json% false` elaborate to `Lean.Json.bool ...`.
- String and numeric literals elaborate to `Lean.Json.str` / `Lean.Json.num`.
- Arrays elaborate recursively to `Lean.Json.arr #[...]`.
- Objects elaborate to `Lean.Json.mkObj [...]`. Because `mkObj` builds a `Std.TreeMap`, duplicate keys collapse (last value wins) and output order is map order, not insertion order.
- Object keys accept either `ident` or string literal. Keys that are Lean keywords must be quoted.
  - `ident` keys are converted with `Name.toString`.
  - String keys are preserved as written.
- Antiquotation uses `Lean.toJson`:
  - `json%{x: $expr}` elaborates via `toJson expr`.
  - Top-level antiquotation works too: `json% $expr` elaborates to `toJson expr`. If `expr : Json`, this embeds it unchanged (`ToJson Json = id`).
  - Missing `ToJson` instance causes elaboration failure.
- `ToJson Float` serializes `NaN` and `±Infinity` as JSON strings, not numbers.

## Patterns

### Interpolate structured data with `ToJson`

```lean
import Lean.Data.Json
open Lean

structure User where
  name : String
  age : Nat
  deriving ToJson

def envelope (u : User) : Json :=
  json%{"kind": "user", "payload": $u}
```

### Dynamic keys with `Json.mkObj`

`json%` does not support antiquotation in key position. Build dynamic-key objects manually.

```lean
import Lean.Data.Json
open Lean

def singletonObj [ToJson α] (k : String) (v : α) : Json :=
  Json.mkObj [(k, toJson v)]
```

### Static skeleton + dynamic fields with `Json.mergeObj`

Combine a `json%` skeleton with dynamic fields built separately.

```lean
import Lean.Data.Json
open Lean

def annotated (base : Json) (tag : String) : Json :=
  base.mergeObj (Json.mkObj [("tag", toJson tag)])
```

### Optional fields with `Json.opt`

`Json.opt` emits nothing for `none` and a key-value pair for `some`, avoiding explicit branching.

```lean
import Lean.Data.Json
open Lean

def withOptional (name : String) (tag? : Option String) : Json :=
  Json.mkObj ([("name", toJson name)] ++ Json.opt "tag" tag?)
```

### Mix static and computed values

```lean
import Lean.Data.Json
open Lean

def stats (count : Nat) (ok : Bool) : Json :=
  json%{
    count: $count,
    ok: $ok,
    ratio: $(if count == 0 then 0.0 else 1.0),
    tags: ["lean", "json"]
  }
```

## Failure Modes and Fixes

- **`unsupported syntax` around `json%`:**
  - Ensure JSON fragments are valid `json` syntax, not arbitrary Lean terms.
  - Wrap Lean expressions as `$expr`.
- **`failed to synthesize ToJson ...`:**
  - Add/derive `ToJson` for the interpolated type.
  - Convert to a supported type before interpolation.
- **Fields reordered in `pretty`/`compress`:**
  - This is expected. Objects are stored in `TreeMap` order, not insertion order. Do not rely on field ordering.
- **Key-related parse issues:**
  - Use `ident: value` or `"string key": value`.
  - Keys that are Lean keywords (e.g. `meta`, `where`, `import`) must be quoted as string literals.
  - For computed keys, stop using `json%` object syntax and use `Json.mkObj`.

## See Also

- [lean4-custom-syntax](lean4-custom-syntax.md) — if building new syntax that emits JSON
- [metaprogramming-patterns](metaprogramming-patterns.md) — if building elaborators that produce JSON

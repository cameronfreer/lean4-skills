---
name: lean-json-writing
description: Write and refactor JSON-producing Lean 4 code using stdlib `json%` elaboration and `Lean.Json` APIs. Use when the task involves JSON literals, interpolation with `$...`, deriving/using `ToJson` instances, or fixing `json%` syntax/elaboration errors.
---

# Lean Json Writing

## Overview

Use this skill to produce readable, correct JSON terms in Lean 4, centered on `json%` from stdlib.
Model behavior on `Lean/Data/Json/Elab.lean`, especially antiquotation and object-key rules.

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
    meta: {"source": "cli", "version": 1}
  }
```

## Stdlib Semantics To Follow

Treat these as ground truth from `Lean/Data/Json/Elab.lean`:

- `json% null` elaborates to `Lean.Json.null`.
- `json% true` / `json% false` elaborate to `Lean.Json.bool ...`.
- String and numeric literals elaborate to `Lean.Json.str` / `Lean.Json.num`.
- Arrays elaborate recursively to `Lean.Json.arr #[...]`.
- Objects elaborate to `Lean.Json.mkObj [...]`.
- Object keys accept either `ident` or string literal.
  - `ident` keys are converted with `Name.toString`.
  - String keys are preserved as written.
- Antiquotation uses `Lean.toJson`:
  - `json%{x: $expr}` elaborates via `toJson expr`.
  - Missing `ToJson` instance causes elaboration failure.

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

### Use explicit builders for dynamic keys

`json%` does not support antiquotation in key position. Build dynamic-key objects manually.

```lean
import Lean.Data.Json
open Lean

def singletonObj (k : String) (v : Json) : Json :=
  Json.mkObj [(k, v)]
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

## Failure Modes And Fixes

- `unsupported syntax` around `json%`:
  - Ensure JSON fragments are valid `json` syntax, not arbitrary Lean terms.
  - Wrap Lean expressions as `$expr`.
- `failed to synthesize ToJson ...`:
  - Add/derive `ToJson` for the interpolated type.
  - Convert to a supported type before interpolation.
- Key-related parse issues:
  - Use `ident: value` or `"string key": value`.
  - For computed keys, stop using `json%` object syntax and use `Json.mkObj`.

## Output Style

- Prefer `json%` for readability whenever keys are static.
- Keep payload code close to domain semantics (avoid deeply nested manual constructors).
- Fall back to `Json.mkObj` and `Json.arr` only for dynamic shape/key requirements.

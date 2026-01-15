---
name: lean4-metaprogramming
description: Use when building Lean 4 DSLs, macros, elaborators, or custom pretty-printing. Focuses on syntax categories, validation, error spans, and hygiene.
---

# Lean 4 Metaprogramming

## When to use

- You are defining new syntax or a DSL.
- You need validation with precise error spans.
- You need type-aware parsing or environment checks.
- You want custom pretty-printing (unexpanders or delaborators).

## Decision tree

| Need | Use | Notes |
| --- | --- | --- |
| Pure syntax rewrite | `macro_rules` | Fast, no type info |
| Validation + good error spans | `macro_rules` + `throwErrorAt` | Use raw syntax nodes |
| Type or environment info | `elab_rules` | Use `elabTerm` and `inferType` |
| Custom pretty output | `@[app_unexpander]` or `@[app_delab]` | Keep UX stable |

## Minimal DSL pattern

```lean
/-- Example DSL front door. -/
syntax "mydsl" "{" term "}" : term

macro_rules
  | `(mydsl{$t}) => `($t)
```

## Validation with precise error spans

Attach errors to the exact token that is invalid (not the whole file).

```lean
open Lean

/-- Validate a literal attribute value. -/
def validateAttr (key : String) (value : String) (stx : Syntax) : MacroM Unit := do
  if key == "rank" && value != "same" then
    throwErrorAt stx "invalid rank value: {value}"

syntax ident "=" str : term

macro_rules
  | `($k:ident = $v:str) => do
      let key := k.getId.toString
      let val := v.getString
      validateAttr key val v.raw
      `(($k, $v))
```

Notes:
- Use `throwErrorAt` on the smallest syntax node (`v.raw` here).
- Use `stx.reprint` in messages if you need the original user text.

## Interpolation with antiquotation

Use `Syntax.isAntiquot` to allow `$(expr)` within DSL values.

```lean
open Lean

syntax (name := dslValue) str : term
syntax (name := dslValue) ident : term

macro_rules
  | `(dslValue| $v:str) => `($v)
  | `(dslValue| $v:ident) => `($(Lean.quote v.getId.toString))
```

## Escalate to elaborators when needed

```lean
open Lean Elab Term

syntax (name := view) "view[" term "]" : term

elab_rules : term
  | `(view[$t]) => do
      let e <- elabTerm t none
      let ty <- inferType e
      -- Use type info here
      return e
```

## Hygiene and name control

- Macros are hygienic by default.
- To keep user-facing names, use `mkIdentFrom` or `withFreshMacroScope`.
- When you want the exact user text, use `stx.reprint`.

## Unexpanders and delaborators

```lean
/-- Print `view` applications as `view[...]`. -/
@[app_unexpander My.view]
def unexpandView : Lean.PrettyPrinter.Unexpander
  | `($_ $t) => `(view[$t])
  | _ => throw ()
```

Use `@[app_delab]` when matching is more complex (implicit args, dependent types).

## Debugging checklist

- `set_option trace.Macro.expand true` to see macro expansions.
- `set_option trace.Elab.step true` for elaboration steps.
- `set_option pp.all true` to inspect implicit arguments.

## Common gotchas

- Left recursion in syntax causes parse loops; use precedence or `:n` annotations.
- `getString` loses formatting; prefer `stx.reprint`.
- If an unexpander does not fire, check the head constant and arity.

## Recommended structure

```
MyDSL/
  Syntax.lean      -- syntax categories, macros, validation helpers
  Elab.lean        -- elaborators when type info is needed
  Pretty.lean      -- unexpanders/delaborators
```

## External references

- Lean 4 Reference Manual: Notations and Macros
- lean4-metaprogramming-book (community)

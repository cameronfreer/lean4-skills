# Metaprogramming Patterns

> **Scope:** Not part of the prove/autoprove default loop. Consulted when building Lean 4 DSLs, macros, elaborators, or custom pretty-printing.

> **Version:** Legacy-tested (4.25/4.27 nightly), unverified on 4.28.0-rc1. MetaM/TacticM API is drift-prone across toolchains.

## When to Use

- Defining new syntax or a DSL
- Validating DSL inputs with precise error spans
- Needing type- or environment-aware parsing
- Adding custom pretty-printing

## Decision Tree

| Need | Use | Notes |
| --- | --- | --- |
| Pure syntax rewrite | `macro_rules` | Fast, no type info |
| Validation + good error spans | `macro_rules` + `throwErrorAt` | Attach to smallest node |
| Type or environment info | `elab_rules` | Use `elabTerm` + `inferType` |
| Custom pretty output | `@[app_unexpander]` / `@[app_delab]` | Keep UX stable |

## Composable Blocks (Interfaces)

Think in small blocks you can reuse across DSLs:

- `SyntaxCat` = syntax categories and terminals
- `ValueParser` = parse literal or antiquotation to `term`
- `Validator` = reject invalid literal values with precise spans
- `Bridge` = build Lean terms from parsed pieces
- `ElabBridge` = type-aware elaboration when needed
- `PrettyBridge` = unexpanders or delabs for readable output

Each block should accept `Syntax` (or `TSyntax`) and produce either:
- a `term`, or
- a `MacroM/ElabM Unit` side effect (validation), or
- an error attached to the smallest syntax node

## Minimal DSL Pattern

```lean
/-- Example DSL front door. -/
syntax "mydsl" "{" term "}" : term

macro_rules
  | `(mydsl{$t}) => `($t)
```

## Validation with Precise Error Spans

Attach errors to the exact token that is invalid (not the whole file):

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
- Use `throwErrorAt` on the smallest syntax node (`v.raw` here)
- Use `stx.reprint` in messages if you need the original user text

## Interpolation with Antiquotation

Use `Syntax.isAntiquot` to allow `$(expr)` within DSL values:

```lean
open Lean

syntax (name := dslValue) str : term
syntax (name := dslValue) ident : term

macro_rules
  | `(dslValue| $v:str) => `($v)
  | `(dslValue| $v:ident) => `($(Lean.quote v.getId.toString))
```

## Escalate to Elaborators When Needed

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

## Hygiene and Name Control

- Macros are hygienic by default
- To keep user-facing names, use `mkIdentFrom` or `withFreshMacroScope`
- When you want the exact user text, use `stx.reprint`

## Unexpanders and Delaborators

```lean
/-- Print `view` applications as `view[...]`. -/
@[app_unexpander My.view]
def unexpandView : Lean.PrettyPrinter.Unexpander
  | `($_ $t) => `(view[$t])
  | _ => throw ()
```

Use `@[app_delab]` when matching is more complex (implicit args, dependent types).

## Debugging Checklist

- `set_option trace.Macro.expand true` to see macro expansions
- `set_option trace.Elab.step true` for elaboration steps
- `set_option pp.all true` to inspect implicit arguments

## Common Gotchas

- Left recursion in syntax causes parse loops; use precedence or `:n` annotations
- `getString` loses formatting; prefer `stx.reprint`
- If an unexpander does not fire, check the head constant and arity

## Recommended Structure

```
MyDSL/
  Syntax.lean      -- syntax categories, macros, validation helpers
  Elab.lean        -- elaborators when type info is needed
  Pretty.lean      -- unexpanders/delaborators
```

## Composition Recipes

1. **DSL + validation + pretty printing:** SyntaxCat + ValueParser + Validator + Bridge + PrettyBridge
2. **DSL with type-aware checks:** SyntaxCat + ValueParser + ElabBridge (+ Validator if needed)
3. **Readable error spans:** Validator uses `throwErrorAt` on literal token, not the whole macro

## See Also

- [lean4-custom-syntax.md](lean4-custom-syntax.md) — notations, macros, elaborators from the user perspective
- [scaffold-dsl.md](scaffold-dsl.md) — copy-paste DSL template
- [Lean 4 Reference Manual: Notations and Macros](https://lean-lang.org/doc/reference/latest/)
- [lean4-metaprogramming-book](https://github.com/leanprover-community/lean4-metaprogramming-book) (community)

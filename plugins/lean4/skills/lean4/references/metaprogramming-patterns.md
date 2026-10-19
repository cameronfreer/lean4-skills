# Metaprogramming Patterns

> **Scope:** Not part of the prove/autoprove default loop. Consulted when building Lean 4 DSLs, macros, elaborators, or custom pretty-printing.

> **Version metadata:**
> - **Verified on:** Lean `v4.33.1` and `v4.35.0` (every block compiled and exercised)
> - **Last validated:** 2026-10-19
> - **Confidence:** medium (the blocks run in CI: `tests/fixtures/reference_snippets/meta_snippets.lean`; MetaM/TacticM APIs remain drift-prone across toolchains, and the design guidance is not machine-checked)

The examples assume `import Lean` (as their fixture does).

## When to Use

- Defining new syntax or a DSL
- Validating DSL inputs with precise error spans
- Needing type- or environment-aware parsing
- Adding custom pretty-printing

## Decision Tree

| Need | Use | Notes |
| --- | --- | --- |
| Pure syntax rewrite | `macro_rules` | Fast, no type info |
| Validation + good error spans | `macro_rules` + `Macro.throwErrorAt` | Attach to smallest node |
| Type or environment info | `elab_rules` | Use `elabTerm` + `inferType` |
| Custom pretty output | `@[app_unexpander]` / `@[app_delab]` | Keep UX stable |

## Composable Blocks (Interfaces)

Think in small blocks you can reuse across DSLs:

- `SyntaxCat` = syntax categories and terminals
- `ValueParser` = parse a literal or an embedded term to `term`
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
def validateAttr (key value : String) (stx : Syntax) : MacroM Unit := do
  if key == "rank" && value != "same" then
    Macro.throwErrorAt stx s!"invalid rank value: {value}"

syntax "dslattr " ident " := " str : term

macro_rules
  | `(dslattr $k:ident := $v:str) => do
      validateAttr k.getId.toString v.getString v
      `(($(quote k.getId.toString), $v))
```

`dslattr rank := "other"` reports `invalid rank value: other` at the string literal.

Notes:
- In `MacroM`, use `Macro.throwErrorAt` with a `String` (`s!"…"`). The `throwErrorAt stx "…{x}"` form builds a `MessageData` and needs `MonadError`, which `MacroM` lacks, so it fails to elaborate.
- Pass the smallest syntax node (`v` here) as the span.
- Give a DSL its own leading keyword (`dslattr`). A bare `syntax ident "=" str : term` competes with ordinary `=` everywhere.

## Embedding Terms in DSL Values

Give DSL values their own syntax category, with an escape that embeds an ordinary term:

```lean
open Lean

declare_syntax_cat dslValue
syntax str : dslValue
syntax ident : dslValue
syntax "(" term ")" : dslValue

syntax "value[" dslValue "]" : term

macro_rules
  | `(value[$s:str]) => `($s)
  | `(value[$x:ident]) => `($(quote x.getId.toString))
  | `(value[($t)]) => `(toString $t)
```

`value["a"]`, `value[abc]` and `value[(1 + 1)]` evaluate to `"a"`, `"abc"` and `"2"`. Each `syntax` alternative needs its own name (or none); reusing one `(name := …)` for two alternatives is an error.

## Escalate to Elaborators When Needed

```lean
open Lean Elab Term Meta

syntax (name := view) "view[" term "]" : term

elab_rules : term
  | `(view[$t]) => do
      let e ← elabTerm t none
      let ty ← inferType e
      logInfo m!"view: {e} : {ty}"
      return e
```

`inferType` lives in `Lean.Meta`. Without `open … Meta` it is an unknown identifier, the `elab_rules` fails, and every use reports "elaboration function … has not been implemented".

## Hygiene and Name Control

- Macros are hygienic by default: a name written inside a quotation, such as `` `(def hidden …) ``, gets macro scopes, and the user cannot refer to `hidden`.
- To introduce a name the user can refer to, build the identifier with `mkIdent` (or `mkIdentFrom stx n` to reuse a source position): `` `(def $(mkIdent `visible) : Nat := 2) ``. (`withFreshMacroScope` does not do this: it only gives the quotations inside it a fresh macro scope.)
- `set_option hygiene false` turns hygiene off for the macros defined under it; prefer `mkIdent` for a single name.
- When you want the exact user text, use `stx.reprint` (an `Option String`).

## Unexpanders and Delaborators

The unexpander's target must be a real constant. Here `wrap[t]` expands to `My.wrap t` and prints back as `wrap[t]`:

```lean
def My.wrap (x : α) : α := x

syntax "wrap[" term "]" : term
macro_rules
  | `(wrap[$t]) => `(My.wrap $t)

/-- Print `My.wrap` applications as `wrap[...]`. -/
@[app_unexpander My.wrap]
def unexpandWrap : Lean.PrettyPrinter.Unexpander
  | `($_ $t) => `(wrap[$t])
  | _ => throw ()
```

`#check (wrap[1] : Nat)` prints `wrap[1] : Nat`.

Use `@[app_delab]` when matching is more complex (implicit args, dependent types).

## Debugging Checklist

- `set_option trace.Elab.step true` to see each term and tactic elaboration step, including term and tactic macro expansions
- `set_option trace.Elab.command true` to see command elaboration, including command macro expansions (`trace.Elab.step` shows only the terms inside the expanded command)
- There is no `trace.Macro.expand` option
- `set_option pp.all true` to inspect implicit arguments

## Common Gotchas

- Without precedences, an infix such as `syntax term " +++ " term : term` parses but associates to the right (`10 +++ 3 +++ 2` is `10 +++ (3 +++ 2)`); write `syntax:65 term:65 " +++ " term:66 : term` for left associativity
- `getString` returns the decoded literal value (escapes resolved); `reprint` returns the source text, quotes included — use each for its purpose
- If an unexpander does not fire, check the head constant and arity
- A token that starts with `--` begins a comment, so it can never be a DSL operator

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
3. **Readable error spans:** Validator uses `Macro.throwErrorAt` on the literal token, not the whole macro

## See Also

- [lean4-custom-syntax.md](lean4-custom-syntax.md) — notations, macros, elaborators from the user perspective
- [scaffold-dsl.md](scaffold-dsl.md) — copy-paste DSL template
- [Lean 4 Reference Manual: Notations and Macros](https://lean-lang.org/doc/reference/latest/)
- [lean4-metaprogramming-book](https://github.com/leanprover-community/lean4-metaprogramming-book) (community)

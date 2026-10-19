# Verso Docs

> **Scope:** Not part of the prove/autoprove default loop. Consulted when writing or fixing Lean doc comments that use Verso roles.

> **Version metadata:**
> - **Verified on:** Lean `v4.33.1` and `v4.35.0` with `set_option doc.verso true` (built-in roles listed from `Lean/Elab/DocString/Builtin.lean`; examples and diagnostics compiled). The separate Verso documentation package was not checked.
> - **Last validated:** 2026-10-19
> - **Confidence:** high for the compiled examples and diagnostics (run in CI: `tests/fixtures/reference_snippets/verso_snippets.lean`); medium for the role-priority guidance

## When to Use

- Fixing `doc.verso` diagnostics about code elements or roles
- Writing `/-- ... -/` doc comments with inline code
- Ensuring hoverable references are precise

Verso docstrings are enabled with `set_option doc.verso true`. That option also makes `/-! … -/` module docs Verso, with header-nesting rules and no mixing with Markdown-format module docs in the same file.

## Role Priority

1. `{name}` for declarations (constants, structures, theorems) and in-scope variables. A namespace that is not itself a declaration is not a valid target: ``{name}`Foo` `` reports ``Unknown constant `Foo` `` when `Foo` only contains `Foo.bar` (`Nat` works because it is also an inductive type). Use `{lit}` for a namespace-only label and `{module}` for a module
2. `{lean}` for Lean expressions or snippets
3. `{lit}` for literal code that should not resolve (last resort)

Other built-in roles: `{given}` and `{givenInstance}` (introduce variables), `{tactic}`, `{conv}`, `{attr}`, `{option}`, `{module}`, `{syntax cat}`, `{syntaxCat}`, `{assert}`, `{manual}`.

## Composable Fixups

Use these small transforms in sequence:

1. `RoleForIdent`: if the snippet is a declared name, wrap with `{name}`
2. `RoleForExpr`: if it is an expression, wrap with `{lean}`
3. `RoleForLiteral`: for pseudo-code or undefined vars, use `{lit}`
4. `RoleForGiven`: introduce variables with `{given}` (with their type) before use

## Quick Rules

- Write inline code in backticks and put the role in front of it:
  - ``{name}`TensorLayout.transpose` ``
  - ``{lean}`fun x ↦ x + 1` ``
  - ``{lit}`x[i,j]` ``
- Use double backticks when the code itself contains a backtick: ```{lit}``a`b`` ```
- Use `{given}` to declare variables, with their type, then reference them with `{lean}`:
  - ``{given}`n : Nat` `` or ``{given (type := "Nat")}`n` ``, then ``{lean}`#[n]` ``
  - an untyped ``{given}`n` `` leaves the type unknown; ``{lean}`#[n]`` then fails with "unresolved metavariable in `given`"
- Use `{lit}` for examples with undefined variables or pseudo-code: `{lean}` elaborates its contents, so an undeclared variable is an "Unknown identifier" error

## Fixing Common Diagnostics

- **Warning "Code element could be more specific.":** a bare `` `foo` ``. The hint offers the roles that fit:
  - Replace `` `foo` `` with ``{name}`foo` `` if it is a declared identifier
  - Replace `` `foo x` `` with ``{lean}`foo x` `` if it is an expression
  - Use ``{lit}`foo` `` to mark it as literal text and silence the suggestion
- **Error ``Unknown role `frobnicate` ``:** use one of the built-in roles above (custom roles were not checked for this reference).

## Examples

```lean
set_option doc.verso true

def transpose (xs : List Nat) : List Nat := xs.reverse

/--
For {given (type := "Nat")}`n`, returns {lean}`transpose [n]`.
Use {lean}`#[n]` for a rank-1 shape literal.
Prefer {lit}`x[i,j]` when writing pseudo-indexing.
-/
def shape (n : Nat) : List Nat := transpose [n]
```

## Checklist

- All inline code has an explicit role
- `{lit}` is used only when resolution should be disabled
- Variables referenced in prose are introduced with `{given}`, typed

## See Also

- [mathlib-style.md](mathlib-style.md) — general style conventions

---
name: lean4-verso-docs
description: Use when writing or fixing Lean doc comments that use Verso roles. Focuses on composable role fixes and precise hovers.
---

# Lean 4 Verso Docs

## When to use

- Fixing doc.verso warnings about unresolved code elements or roles.
- Writing `/-- ... -/` doc comments with inline code.
- Ensuring hoverable references are precise.

## Role priority

1) `{name}` for declared names (constants, structures, namespaces, theorems)
2) `{lean}` for Lean expressions or snippets
3) `{lit}` for literal code that should not resolve (last resort)

## Composable fixups

Use these small transforms in sequence:

1) `RoleForIdent`: if the snippet is a declared name, wrap with `{name}`.
2) `RoleForExpr`: if it is an expression, wrap with `{lean}`.
3) `RoleForLiteral`: for pseudo-code or undefined vars, use `{lit}`.
4) `RoleForGiven`: introduce variables with `{given}` before use.

## Quick rules

- Wrap inline code in backticks and add a role:
  - `{name}``TensorLayout.transpose``
  - `{lean}``fun x => x + 1``
  - `{lit}``x[i,j]``
- Use `{given}` to declare variables, then reference with `{lean}`:
  - `{given}``n`` then `{lean}``#[n]``
- Use `{lit}` for examples with undefined variables or pseudo-code.

## Fixing common warnings

- "code element is not specific":
  - Replace `` `foo` `` with `{name}``foo`` if it is a declared identifier.
  - Replace `` `foo x` `` with `{lean}``foo x`` if it is an expression.
- "unknown role":
  - Use one of the standard roles `{name}`, `{lean}`, `{lit}`, `{given}`.
  - If a custom role is required, define it in your doc prelude.

## Examples

```lean
/--
Returns {name}``TensorLayout.transpose`` for {given}``n``.
Use {lean}``#[n]`` for a rank-1 shape literal.
Prefer {lit}``x[i,j]`` when writing pseudo-indexing.
-/
```

## Checklist

- All inline code has an explicit role.
- `{lit}` is used only when resolution should be disabled.
- Variables referenced in prose are introduced with `{given}`.

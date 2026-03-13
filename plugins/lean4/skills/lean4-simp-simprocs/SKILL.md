---
name: lean4-simp-simprocs
description: Use when debugging or authoring `simp`/`dsimp`, curating `@[simp]` lemmas, tracing simplifier behavior, or writing custom `simproc`/`dsimproc` rewrites.
---

# Lean4 Simp + Simprocs

Use this skill when the simplifier is close to the proof, but normalization or a reusable computed rewrite is missing.

Grounding for this skill:
- Lean community blog: [Simp made simple](https://leanprover-community.github.io/blog/posts/simp-made-simple/)
- Lean community blog: [Fantastic Simprocs and How to Write Them](https://leanprover-community.github.io/blog/posts/simprocs-tutorial/)
- Lean community blog: [Simprocs for the Working Mathematician](https://leanprover-community.github.io/blog/posts/simprocs-for-the-working-mathematician/)
- Shared plugin references: `../lean4/references/simp-normal-forms.md`, `../lean4/references/simp-hygiene.md`, `../lean4/references/simproc-patterns.md`, `../lean4/references/grind-tactic.md`

## Decision Rule

- Start with `simp?`, `simp only [...]`, and better `@[simp]` lemmas.
- Use a plain `@[simp]` lemma when the rewrite is canonical and proof-producing without computation.
- Use `dsimproc` when the result is definitional and computable from explicit data.
- Use `simproc` when the rewrite needs proof construction, a custom discharger, or proposition-level reasoning.
- Use a pre-simproc when the outer form should simplify before visiting children, such as `ite`-style rewrites.
- Switch to `grind`, `omega`, `linarith`, or `nlinarith` when the problem is closure after normalization rather than rewriting.

## Debug Loop

1. Inspect what `simp` wants to do.
   ```lean
   simp?
   simp only [lemma1, lemma2]
   set_option trace.Meta.Tactic.simp true in
   ```
2. If a candidate lemma is not canonical, do not mark it `[simp]`; keep it local via `simp only [...]`.
3. If the missing rewrite would require infinitely many numerically specialized lemmas, repeated local calculation, or different pre/post behavior, write a simproc.
4. If the simproc only fires on explicit numerals or other concrete syntax, return `.continue` on symbolic inputs rather than guessing.
5. After normalization, if the remaining goal is mixed-constraint closure, hand off to `grind` rather than forcing more simp machinery.

## Simp Hygiene Rules

- The left-hand side should already be in simp normal form.
- The right-hand side must be strictly simpler and loop-free.
- Avoid `[simp]` on commutativity and similarly non-canonical rewrites.
- Prefer narrowing the simp set before adding new global lemmas.
- Use `@[simp, nolint simpNF]` only when the non-normal-form orientation is intentional and justified.

For precise definitions of simp normal form and canonical versus non-canonical rewrites, read `../lean4/references/simp-normal-forms.md`.

## Simproc Authoring Rules

- Match narrowly; small patterns are easier to trust and cheaper to run.
- Prefer explicit-data rewrites. If you cannot extract concrete data from the syntax, usually return `.continue`.
- Keep the rewrite one-way and terminating.
- Use `.visit` when the produced expression should be resimplified.
- Use `.done` only when you are confident the new expression is already in final simp normal form.
- Register locally before making a simproc part of a shared simp set.

## Implementation Sketch

```lean
import Lean
open Lean Meta Qq Simp

-- Sketch only: real code must also build a proof-backed replacement.
simproc_decl reduceFoo (foo _) := fun e => do
  let_expr foo arg := e | return .continue
  let some n := arg.nat? | return .continue
  let rhs := mkNatLit (n + 1)
  let result := <construct a proof-backed rewrite to rhs and revisit it>
  pure result
```

Treat this as a shape, not a copy-paste recipe. Real simprocs usually need:
- better pattern matching via `let_expr`
- extraction helpers like `.nat?` or `Nat.fromExpr?`
- proof construction with `Qq`/`toExpr`
- careful choice of `.continue` vs `.visit` vs `.done`

## Escalation Targets

- unclear canonical form or `simpNF` dispute: read `../lean4/references/simp-normal-forms.md`
- `simp` problem with noisy lemmas or wrong orientation: read `../lean4/references/simp-hygiene.md`
- custom deterministic rewrite inside `simp`: read `../lean4/references/simproc-patterns.md`
- goal should close after normalization: read `../lean4/references/grind-tactic.md`

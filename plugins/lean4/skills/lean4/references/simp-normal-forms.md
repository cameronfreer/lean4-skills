# Simp Normal Forms and Canonical Rewrites

> **Scope:** Consult when deciding whether a rewrite belongs in `@[simp]`, when a simproc should return `.continue` versus rewriting, or when "canonical" versus "non-canonical" is the real source of a simp design dispute.

> **Grounding:** Distilled from the Lean community posts [Simp made simple](https://leanprover-community.github.io/blog/posts/simp-made-simple/), [Fantastic Simprocs and How to Write Them](https://leanprover-community.github.io/blog/posts/simprocs-tutorial/), and [Simprocs for the Working Mathematician](https://leanprover-community.github.io/blog/posts/simprocs-for-the-working-mathematician/).

## Core Definitions

### `simp` Normal Form

An expression is in **simp normal form** when the current simp set and simp configuration would stop rewriting it.

Important consequences:
- simp normal form is **relative**, not absolute
- it depends on the active simp lemmas, simprocs, and configuration
- "normal form" means "the form chosen by this simp setup", not "the only mathematically natural form"

Operational test:

```lean
example : goal := by
  simp only [candidate_lemmas]
```

If your proposed left-hand side would itself be rewritten by that call, it is not in simp normal form.

### Canonical Rewrite

A rewrite is **canonical** when it moves expressions toward the representative that the project wants simp to prefer globally.

Canonical rewrites usually have these properties:
- one direction is clearly preferred
- the right-hand side is simpler or more stable
- repeated simp use should keep terms there
- the same orientation makes sense across many proofs

Typical canonical examples:
- `x + 0 -> x`
- `id x -> x`
- expanding an abbreviation to its chosen underlying definition

### Non-Canonical Rewrite

A rewrite is **non-canonical** when it may be mathematically true and locally useful, but it does not point to a globally preferred representative.

Common signs of a non-canonical rewrite:
- both directions look equally natural
- the rewrite mostly rearranges structure rather than simplifying it
- the rewrite exposes more syntax on symbolic terms without reaching a stable endpoint
- different proofs would reasonably want different orientations

Typical non-canonical examples:
- commutativity like `a + b = b + a`
- ad hoc reassociation without a clear project-wide policy
- partial unfolding of a recursive definition on symbolic inputs

## Practical Tests

Ask these questions before adding `@[simp]`:

1. Would the current simp set rewrite my left-hand side before my lemma sees it?
   If yes, the left-hand side is not in simp normal form.

2. After rewriting once, does the result look like the form I want to see everywhere?
   If no, the rewrite is probably not canonical.

3. Would the reverse direction look equally reasonable to another author?
   If yes, keep it out of global `@[simp]`.

4. On symbolic inputs, does the rewrite merely expose more structure without reaching a stable shape?
   If yes, it is usually non-canonical for simp.

## Symbolic vs Explicit Data

The simproc posts make an important distinction: a rewrite may be canonical on **explicit** inputs and non-canonical on **symbolic** ones.

Pattern:
- explicit numerals often have a clear computed normal form
- symbolic expressions often do not

Example shape:
- good: reduce arithmetic on concrete naturals
- bad: partially unfold a recursive definition on arbitrary symbolic `n`

This is why simprocs often:
- extract concrete data first
- rewrite only when that succeeds
- return `.continue` on symbolic inputs

The `revRange` discussion in the working-mathematician post is the model warning: unfolding on symbolic inputs can produce a true equation that is still the wrong simp normal form.

## Relationship to `simpNF`

`simpNF` is the lint-level version of the same idea:
- the left-hand side should already be in simp normal form
- the right-hand side should be the chosen destination

If a lemma fails that smell test, it may still be a fine local rewrite. It just should not usually be a global simp lemma.

## Relationship to Simprocs

Simprocs should respect the same normal-form discipline as simp lemmas.

Good simproc behavior:
- rewrite only when you can produce a better normal form
- use `.visit` when the replacement still needs simp to finish normalizing
- use `.done` only when the replacement is already in simp normal form
- use `.continue` when the term is too symbolic to choose a canonical rewrite

Bad simproc behavior:
- performing arbitrary true rewrites with no normal-form policy
- partially evaluating symbolic terms into less stable syntax
- encoding proof search instead of deterministic normalization

## Decision Table

| Situation | Right tool |
|---|---|
| Globally preferred stable orientation | `@[simp]` lemma |
| Useful only in one proof | `simp only [...]` or `simp [lemma]` |
| Canonical rewrite depends on explicit computation | `dsimproc` or `simproc` |
| Symbolic term has no obvious normal form | leave it alone (`.continue`) |
| Goal is normalized but not closed | `grind` or a domain solver |

## See Also

- [simp-hygiene.md](simp-hygiene.md) - Broader rules for `@[simp]` lemma design
- [simproc-patterns.md](simproc-patterns.md) - Simproc authoring workflow and performance discipline
- [grind-tactic.md](grind-tactic.md) - Closure after normalization

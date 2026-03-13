# Simp Lemma Hygiene

> **Scope:** Consult when deciding whether a rewrite belongs in `@[simp]`, when `simp` is doing the wrong thing, or when a proof feels "one lemma away" from closing.

> **Grounding:** Distilled from the Lean community posts [Simp made simple](https://leanprover-community.github.io/blog/posts/simp-made-simple/) and [Simprocs for the Working Mathematician](https://leanprover-community.github.io/blog/posts/simprocs-for-the-working-mathematician/), plus current plugin conventions.

Best practices for `@[simp]` lemmas to avoid common issues.

For precise definitions of `simp` normal form and canonical versus non-canonical rewrites, read [simp-normal-forms.md](simp-normal-forms.md) first.

## First Question: Should This Be a Simp Lemma?

Use a global `@[simp]` lemma only if all of the following are true:
- the rewrite is canonical, not merely convenient for one proof
- the direction is obvious and stable across the codebase
- the right-hand side is simpler
- the lemma will help many proofs, not just the current one

If any of these fail, prefer one of:
- `simp only [lemma]` locally
- `simp [lemma]` in one proof
- a dedicated simproc if the rewrite depends on computation over explicit syntax

## Common Issues

### 1. LHS Not in Normal Form

The left-hand side should already be irreducible by other simp lemmas.

**Bad:**
```lean
@[simp] lemma bad_form : a + (b + c) = (a + b) + c := ...
-- LHS contains a non-canonical subterm that simp may rewrite first.
```

**Good:**
```lean
@[simp] lemma good_form : (a + b) + c = a + (b + c) := ...
-- LHS already matches the chosen normal form.
```

This is the central `simpNF` rule: do not ask the simplifier to orient terms toward a form that some other simp lemma will immediately change again.

### 2. Potential Infinite Loops

The right-hand side must be strictly simpler than the left-hand side.

**Dangerous:**
```lean
@[simp] lemma may_loop : f x = g (f x) := ...
-- The LHS reappears on the RHS.
```

**Test the lemma in isolation:**
```lean
example : f x = expected := by
  simp only [may_loop]
```

If this is not obviously terminating, it should not be a simp lemma.

### 3. Conflicting Simp Lemmas

Avoid lemmas that simplify the same pattern differently.

**Conflict:**
```lean
@[simp] lemma simp1 : f (g x) = A := ...
@[simp] lemma simp2 : f (g x) = B := ...
```

Resolution options:
- remove one global lemma
- keep both ordinary lemmas and choose locally with `simp only [...]`
- rethink the canonical normal form

## Direction Matters

Simplify toward canonical forms:
- expand abbreviations to their intended base form
- eliminate neutral elements
- normalize arithmetic into the project's preferred shape
- reduce structure, not increase it

Good `@[simp]` lemmas tend to erase administrative structure:

```lean
@[simp] lemma my_def_simp : myDef x = underlyingDef x := rfl
@[simp] lemma id_left : id x = x := rfl
@[simp] lemma add_zero : x + 0 = x := ...
@[simp] lemma sub_self : x - x = 0 := ...
```

Bad candidates usually introduce symmetry without a preferred orientation:

```lean
-- DON'T: no canonical direction.
@[simp] lemma bad_comm : a + b = b + a := ...

-- DON'T: only acceptable with a very deliberate normal-form policy.
@[simp] lemma bad_assoc : a + (b + c) = (a + b) + c := ...
```

## Specificity and Locality

More specific lemmas fire before more general ones:

```lean
@[simp] lemma general : f x = A := ...
@[simp] lemma specific : f 0 = B := ...
```

That can be useful, but it is also how surprising interactions happen. Before promoting a lemma to `@[simp]`, ask whether local use is enough:

```lean
example : goal := by
  simp only [specific, general]
```

Long-term bias:
- default to local `simp only [...]`
- upgrade to global `@[simp]` only after repeated successful use

## Debugging Workflow

### 1. Ask `simp` for Its Intended Rewrite Set

```lean
example : goal := by
  simp?
```

This is the fastest way to learn whether the problem is "missing lemma", "wrong orientation", or "too many lemmas".

### 2. Minimize the Active Set

```lean
example : goal := by
  simp only [lemma1, lemma2]

example : goal := by
  simp [-bad_lemma]
```

If a tiny `simp only` call works and the default `simp` call does not, the issue is almost always hygiene, not proof search.

### 3. Trace Rewrites

```lean
set_option trace.Meta.Tactic.simp true in
example : goal := by
  simp
```

Use tracing after `simp?` and `simp only` have narrowed the problem. Raw simp traces can be noisy.

## When to Escalate Beyond `@[simp]`

Do not fight the simplifier with dozens of narrowly targeted lemmas. Escalate when:
- the rewrite depends on explicit computation over syntax
- you would need infinitely many numeral-specific lemmas
- the rewrite should happen only before or after children are simplified
- local side conditions need a discharger

Those are simproc problems, not more-lemma problems. See [simproc-patterns.md](simproc-patterns.md).

## Simp Attributes

### `@[simp]`
Standard simplification lemma. Use for broad, canonical rewrites.

### `@[simp, nolint simpNF]`
Suppress normal-form lint. Use only when a non-normal-form orientation is both deliberate and documented.

### `@[simp high]` / `@[simp low]`
Priority control. Higher priority means tried earlier.

## Testing Checklist

Before adding `@[simp]`, verify:
- [ ] LHS is in simp normal form
- [ ] RHS is strictly simpler
- [ ] No conflicting lemma already owns this pattern
- [ ] `simp only [lemma]` terminates immediately
- [ ] The rewrite helps more than one proof
- [ ] A local `simp only [...]` call would not be enough

## See Also

- [simp-normal-forms.md](simp-normal-forms.md) - Definitions for simp normal form, canonical rewrites, and non-canonical rewrites
- [simproc-patterns.md](simproc-patterns.md) - Custom deterministic rewrites inside the simp pipeline
- [tactics-reference.md](tactics-reference.md) - Full tactic docs including simp variants
- [performance-optimization.md](performance-optimization.md) - `simp only` for speed
- [mathlib-style.md](mathlib-style.md) - Style conventions

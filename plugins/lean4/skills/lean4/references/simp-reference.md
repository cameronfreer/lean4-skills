# Simp Reference

> **Scope:** Not part of the prove/autoprove default loop. Consulted when `simp` needs a deterministic, reusable rewrite that simp lemmas alone cannot provide.

> **Version metadata:**
> - **Verified on:** Lean reference + release notes through `v4.27.0`
> - **Last validated:** 2026-02-17
> - **Confidence:** medium (docs reviewed; snippets not batch-compiled)

## Simp Lemma Hygiene

Best practices for `@[simp]` lemmas to avoid common issues.

### Common Issues

#### 1. LHS Not in Normal Form

The left-hand side should be irreducible by other simp lemmas.

**Bad:**
```lean
@[simp] lemma bad_form : a + (b + c) = (a + b) + c := sorry
-- LHS contains (b + c) which might be simplified first
```

**Good:**
```lean
@[simp] lemma good_form : (a + b) + c = a + (b + c) := sorry
-- LHS is already in normal form
```

#### 2. Potential Infinite Loops

The RHS should be simpler than the LHS.

**Dangerous:**
```lean
@[simp] lemma may_loop : f x = g (f x) := sorry
-- LHS appears in RHS!
```

**Test your lemma:**
```lean
example : f x = expected := by simp only [may_loop]  -- Check it terminates
```

#### 3. Conflicting Simp Lemmas

Avoid lemmas that simplify the same pattern differently.

**Conflict:**
```lean
@[simp] lemma simp1 : f (g x) = A := sorry
@[simp] lemma simp2 : f (g x) = B := sorry  -- Same LHS, different RHS
```

**Resolution:** Remove one, or use `simp only [simp1]` explicitly.

### Best Practices

#### Direction Matters

Simplify toward canonical forms:
- Expand abbreviations to definitions
- Normalize arithmetic (`a - b` → `a + (-b)`)
- Reduce complexity

#### Specificity

More specific lemmas are tried first:
```lean
@[simp] lemma general : f x = A := sorry
@[simp] lemma specific : f 0 = B := sorry  -- Tried before general
```

#### Use `@[simp]` Sparingly

Not every equality should be a simp lemma. Consider:
- Will this be useful in many proofs?
- Does it simplify in the right direction?
- Could it interfere with other lemmas?

#### Testing

Always test new simp lemmas:

Note: this section uses schematic placeholders like `LHS`, `RHS`, and `goal` to illustrate tactic structure.

```lean
-- Test 1: Direct application works
example : LHS = RHS := by simp [your_lemma]

-- Test 2: Doesn't loop
example : f x = f x := by simp [your_lemma]  -- Should complete instantly

-- Test 3: Works in context
example (h : some_hypothesis) : goal := by simp [your_lemma]
```

### Simp Attributes

#### `@[simp]`
Standard simplification lemma. Use for common simplifications.

#### `@[simp, nolint simpNF]`
Suppress normal form lint. Use when you know the LHS isn't in NF but it's intentional.

#### `@[simp high]` / `@[simp low]`
Priority control. Higher priority means tried earlier.

#### `@[simp?]`
Debug: shows which lemmas are being applied.

### Debugging Simp

#### See what simp does
```lean
example : goal := by simp?  -- Shows applied lemmas
```

#### Test specific lemmas
```lean
example : goal := by simp only [lemma1, lemma2]
```

#### Disable problematic lemmas
```lean
example : goal := by simp [-bad_lemma]
```

#### Trace simp
```lean
set_option trace.Meta.Tactic.simp true in
example : goal := by simp
```

### Common Patterns

#### Good Simp Lemmas

```lean
-- Definition expansion
@[simp] lemma my_def_simp : myDef x = underlying_def x := rfl

-- Identity elimination
@[simp] lemma id_left : id x = x := rfl

-- Neutral element
@[simp] lemma add_zero : x + 0 = x := sorry

-- Cancellation
@[simp] lemma sub_self : x - x = 0 := sorry
```

#### Lemmas to Avoid as Simp

```lean
-- Commutativity (no preferred form)
-- DON'T: @[simp] lemma bad : a + b = b + a

-- Associativity without normalization direction
-- DON'T: @[simp] lemma bad : (a + b) + c = a + (b + c)

-- Anything with LHS appearing in RHS
-- DON'T: @[simp] lemma bad : f x = g (f x)
```

### Checklist Before Adding `@[simp]`

- [ ] LHS is in simp normal form
- [ ] RHS is simpler than LHS
- [ ] Doesn't conflict with existing simp lemmas
- [ ] Tested: `simp only [lemma]` terminates
- [ ] Tested: works in example proofs
- [ ] Actually useful in multiple places

## Simproc Patterns

### When to Use

- `simp` is close but needs a deterministic rewrite
- You repeat the same rewrite in multiple places
- A rewrite depends on local computation (e.g., normalization)

### Composable Simp Pipeline

Think of simprocs as a block inside `simp`:

1. `simp set` (lemmas, simp attributes)
2. `simp config` (zeta, eta, simp theorems)
3. `simproc` (deterministic rewrite)
4. `simp` final normalization

### Minimal Simproc Shape

Start with a plain `@[simp]` lemma when possible:

```lean
import Lean
open Lean Meta Simp

-- Prefer this first: simple deterministic rewrites belong in simp lemmas.
@[simp] theorem foo_eq_bar (x) : foo x = bar x := by rfl
```

Escalate to a real simproc only when the rewrite needs custom computation:

```lean
open Lean Meta Simp

simproc_decl mySimproc (foo _) := fun e => do
  -- compute a rewrite or return .none
  return .none
```

### Rules of Thumb

- Prefer simp lemmas; use simprocs only when needed
- Keep patterns small and oriented (avoid loops)
- Make simproc deterministic and fast
- Register locally if the rewrite is not global

### Simproc Checklist

- The simproc rewrite is one-way and terminating
- `simp` set remains minimal (no noisy lemmas)
- The simproc is only enabled where it helps

## See Also

- [tactics-reference.md](tactics-reference.md) - Full tactic docs including simp variants
- [performance-optimization.md](performance-optimization.md) - `simp only` for speed
- [mathlib-style.md](mathlib-style.md) - Style conventions

# Simp Lemma Hygiene

Best practices for `@[simp]` lemmas to avoid common issues.

## Common Issues

### 1. LHS Not in Normal Form

The left-hand side should be irreducible by other simp lemmas.

**Bad:**
```lean
@[simp] lemma bad_form : a + (b + c) = (a + b) + c := ...
-- LHS contains (b + c) which might be simplified first
```

**Good:**
```lean
@[simp] lemma good_form : (a + b) + c = a + (b + c) := ...
-- LHS is already in normal form
```

### 2. Potential Infinite Loops

The RHS should be simpler than the LHS.

**Dangerous:**
```lean
@[simp] lemma may_loop : f x = g (f x) := ...
-- LHS appears in RHS!
```

**Test your lemma:**
```lean
example : f x = expected := by simp only [may_loop]  -- Check it terminates
```

### 3. Conflicting Simp Lemmas

Avoid lemmas that simplify the same pattern differently.

**Conflict:**
```lean
@[simp] lemma simp1 : f (g x) = A := ...
@[simp] lemma simp2 : f (g x) = B := ...  -- Same LHS, different RHS
```

**Resolution:** Remove one, or use `simp only [simp1]` explicitly.

## Best Practices

### Direction Matters

Simplify toward canonical forms:
- Expand abbreviations to definitions
- Normalize arithmetic (`a - b` → `a + (-b)`)
- Reduce complexity

### Specificity

More specific lemmas are tried first:
```lean
@[simp] lemma general : f x = A := ...
@[simp] lemma specific : f 0 = B := ...  -- Tried before general
```

### Use `@[simp]` Sparingly

Not every equality should be a simp lemma. Consider:
- Will this be useful in many proofs?
- Does it simplify in the right direction?
- Could it interfere with other lemmas?

### Testing

Always test new simp lemmas:
```lean
-- Test 1: Direct application works
example : LHS = RHS := by simp [your_lemma]

-- Test 2: Doesn't loop
example : f x = f x := by simp [your_lemma]  -- Should complete instantly

-- Test 3: Works in context
example (h : some_hypothesis) : goal := by simp [your_lemma]
```

## Simp Attributes

### `@[simp]`
Standard simplification lemma. Use for common simplifications.

### `@[simp, nolint simpNF]`
Suppress normal form lint. Use when you know the LHS isn't in NF but it's intentional.

### `@[simp high]` / `@[simp low]`
Priority control. Higher priority means tried earlier.

### `@[simp?]`
Debug: shows which lemmas are being applied.

## Debugging Simp

### See what simp does
```lean
example : goal := by simp?  -- Shows applied lemmas
```

### Test specific lemmas
```lean
example : goal := by simp only [lemma1, lemma2]
```

### Disable problematic lemmas
```lean
example : goal := by simp [-bad_lemma]
```

### Trace simp
```lean
set_option trace.Meta.Tactic.simp true in
example : goal := by simp
```

## Common Patterns

### Good Simp Lemmas

```lean
-- Definition expansion
@[simp] lemma my_def_simp : myDef x = underlying_def x := rfl

-- Identity elimination
@[simp] lemma id_left : id x = x := rfl

-- Neutral element
@[simp] lemma add_zero : x + 0 = x := ...

-- Cancellation
@[simp] lemma sub_self : x - x = 0 := ...
```

### Lemmas to Avoid as Simp

```lean
-- Commutativity (no preferred form)
-- DON'T: @[simp] lemma bad : a + b = b + a

-- Associativity without normalization direction
-- DON'T: @[simp] lemma bad : (a + b) + c = a + (b + c)

-- Anything with LHS appearing in RHS
-- DON'T: @[simp] lemma bad : f x = g (f x)
```

## Checklist Before Adding `@[simp]`

- [ ] LHS is in simp normal form
- [ ] RHS is simpler than LHS
- [ ] Doesn't conflict with existing simp lemmas
- [ ] Tested: `simp only [lemma]` terminates
- [ ] Tested: works in example proofs
- [ ] Actually useful in multiple places

## See Also

- [tactics-reference.md](tactics-reference.md) - Full tactic docs including simp variants
- [performance-optimization.md](performance-optimization.md) - `simp only` for speed
- [mathlib-style.md](mathlib-style.md) - Style conventions

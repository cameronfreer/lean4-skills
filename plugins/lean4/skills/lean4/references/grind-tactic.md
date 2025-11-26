# The `grind` Tactic

## TLDR

**What it is:** An SMT-inspired automated reasoning tactic that coordinates multiple reasoning engines to construct proofs by contradiction.

**When to use `grind`:**
- Goals combining multiple constraint types (equalities, inequalities, algebraic laws)
- Problems requiring cross-domain reasoning
- Finite-domain reasoning (like `Fin` arithmetic)
- When you need "just figure it out" automation

**When to use `simp` instead:**
- Pure rewriting/normalization tasks
- When you know which lemmas apply
- Performance-critical proofs (simp is faster for simple cases)
- When you want explicit, reviewable proofs

**Key difference:** `simp` applies rewrite rules sequentially. `grind` maintains a global constraint store and coordinates multiple reasoning engines simultaneously.

---

## How `grind` Works

### Core Mechanism

All `grind` proofs work by **contradiction**: the expected conclusion and premises are treated uniformly as facts. The tactic maintains a "virtual whiteboard" where discovered equalities, inequalities, and Boolean literals are tracked.

When facts are added:
1. Equivalent terms merge into equivalence classes
2. Each engine reads from and contributes to shared state
3. All true propositions equal `True`, all false equal `False`

### Five Cooperating Engines

| Engine | What It Does |
|--------|--------------|
| **Congruence Closure** | Discovers equivalent terms, merges them into equivalence classes |
| **Constraint Propagation** | Propagates domain constraints across variables |
| **E-matching** | Pattern-based equation discovery and application |
| **Case Analysis** | Strategic branching when splits are necessary |
| **Theory Solvers** | Specialized reasoning for arithmetic, rings, fields |

### Theory Solvers Include

- **Linear integer arithmetic (CUTSAT)** - Integer systems with linear constraints
- **Commutative rings** - Polynomial reasoning with `CommRing` instances
- **Fields** - Division and field arithmetic
- **Linear arithmetic** - General linear inequalities

---

## `grind` vs `simp`: Decision Guide

```
What's the goal structure?
│
├─ Pure rewriting/simplification
│  └─ Use `simp` (faster, more predictable)
│
├─ Linear/polynomial arithmetic
│  ├─ Integers only → `omega` (fastest)
│  ├─ Reals/rationals → `linarith` or `ring`
│  └─ Mixed constraints → `grind` (coordinates solvers)
│
├─ Multiple constraint types combined
│  └─ Use `grind` (coordinates all engines)
│
├─ Need cross-domain reasoning
│  └─ Use `grind` (shares facts across engines)
│
├─ Finite domain (Fin, Bool, small enums)
│  └─ Use `grind` (handles bounded search well)
│
└─ Unsure what's needed
   └─ Try `simp`, then `grind`, then specialized tactics
```

### Concrete Comparisons

**Transitive equality chains:**
```lean
-- Both work, grind discovers automatically
example (h1 : a = b) (h2 : b = c) (h3 : c = d) : a = d := by simp [h1, h2, h3]
example (h1 : a = b) (h2 : b = c) (h3 : c = d) : a = d := by grind
```

**Algebraic with constraints:**
```lean
-- grind shines when algebra meets constraints
example [CommRing R] [NoZeroDivisors R] (h : x * y = 0) (hx : x ≠ 0) : y = 0 := by
  grind  -- Coordinates ring solver + constraint propagation
```

**Finite arithmetic (Fin):**
```lean
-- grind handles modular arithmetic in Fin
example : (3 : Fin 7) + 5 = 1 := by grind  -- Knows 8 mod 7 = 1
```

**Pure simplification:**
```lean
-- simp is cleaner for pure rewrites
example : x + 0 + y * 1 = x + y := by simp  -- Faster, explicit
```

---

## Usage Patterns

### Basic Usage

```lean
-- Just let grind figure it out
example (h1 : P → Q) (h2 : Q → R) (hp : P) : R := by grind

-- With hints (rarely needed)
example : complex_goal := by grind [helpful_lemma]
```

### Common Patterns

**Pattern 1: Cross-domain goals**
```lean
-- Combines Boolean reasoning with arithmetic
example (h : n < m ∨ n = m) (h2 : n ≠ m) : n < m := by grind
```

**Pattern 2: Algebraic systems**
```lean
-- Ring solver + constraints
example [Field F] (h : x * y = 1) : x ≠ 0 := by grind
```

**Pattern 3: After case splits**
```lean
-- Clean up each branch
by_cases h : condition
· grind  -- Handles first case
· grind  -- Handles second case
```

**Pattern 4: Finite enumeration**
```lean
-- Bounded domains
example (x : Fin 3) : x = 0 ∨ x = 1 ∨ x = 2 := by grind
```

---

## When NOT to Use `grind`

### Combinatorial Explosion

`grind` is NOT designed for problems requiring exhaustive search:

- Large pigeonhole arguments
- Graph coloring with many vertices
- N-queens for large N
- Multi-variable Boolean puzzles

**For these, use `bv_decide`** which calls an external SAT solver and returns verifiable certificates.

### Simple Cases Where Specialized Tactics Are Faster

| Goal Type | Better Tactic |
|-----------|---------------|
| Pure integer arithmetic | `omega` |
| Real linear arithmetic | `linarith` |
| Ring/field equations | `ring` / `field_simp` |
| Pure rewriting | `simp` |
| Decidable equality | `decide` |

---

## The `@[grind]` Attribute

### Automatic Discovery

The standard library and mathlib are annotated with `@[grind]` attributes. Common lemmas are discovered automatically without explicit citation.

```lean
-- These work without importing specific lemmas
example : a + b = b + a := by grind  -- Finds add_comm
example : a * (b + c) = a * b + a * c := by grind  -- Finds mul_add
```

### Registering Custom Theorems

For your own lemmas:

```lean
@[grind] lemma my_useful_fact : P → Q := ...

-- Now grind can use it automatically
example (hp : P) : Q := by grind
```

### Attribute Variants

| Attribute | Effect |
|-----------|--------|
| `@[grind]` | General grind lemma (default behavior) |
| `@[grind =]` | Register as rewrite (equality lemma) |
| `@[grind ->]` | Forward reasoning (implications) |

---

## Integration with Other Tactics

### Tactic Sequences

```lean
-- Simplify first, then grind
example : goal := by
  simp only [normalize_defs]
  grind

-- Try fast tactics first
example : goal := by
  first
  | omega
  | linarith
  | grind
```

### After Structure Work

```lean
example (h : ∃ x, P x ∧ Q x) : R := by
  obtain ⟨x, hp, hq⟩ := h
  grind  -- Use the extracted facts
```

### With `calc`

```lean
calc a = b := by grind
   _ = c := by grind
   _ = d := by simp [specific_lemma]
```

---

## Performance Considerations

### When `grind` Is Efficient

- Problems with bounded branching
- Goals where constraint propagation prunes search
- Cross-domain reasoning (cheaper than manual coordination)

### When `grind` Is Slow

- Deep case analysis trees
- Goals requiring many lemma applications
- Pure rewriting (use `simp`)
- Large finite domains

### Optimization Tips

1. **Provide hints when you know key lemmas:**
   ```lean
   grind [key_lemma1, key_lemma2]
   ```

2. **Simplify first to reduce term complexity:**
   ```lean
   simp only [defs]; grind
   ```

3. **Split manually if you know the key cases:**
   ```lean
   by_cases key_condition <;> grind
   ```

---

## Debugging `grind`

### When `grind` Fails

1. **Check if goal is actually provable** - `grind` fails on false goals too
2. **Try adding hints** - Key lemmas might not be `@[grind]`
3. **Simplify first** - Complex terms can hide simple facts
4. **Check for missing instances** - Theory solvers need type class instances

### Diagnostic Approach

```lean
-- Step 1: Does simp make progress?
example : goal := by simp?  -- See what applies

-- Step 2: Can specialized tactics solve it?
example : goal := by omega  -- or linarith, ring, etc.

-- Step 3: What does grind need?
example : goal := by grind [?_]  -- Add lemmas incrementally
```

---

## Examples

### Example 1: Transitive Reasoning

```lean
example (h1 : a = b) (h2 : b = c) (h3 : c = d) : f a = f d := by
  grind  -- Discovers a = d, applies congruence for f
```

### Example 2: Polynomial System

```lean
example [CommRing R] [NoZeroDivisors R]
    (h1 : x^2 = y^2) (h2 : x + y = 0) (hx : x ≠ 0) :
    x = -y := by
  grind  -- Ring solver + constraint propagation
```

### Example 3: Linear Integer Constraints

```lean
example (h1 : 2 * x + 3 * y ≤ 10) (h2 : x ≥ 0) (h3 : y ≥ 0)
    (h4 : x + y ≥ 3) : y ≤ 4 := by
  grind  -- CUTSAT handles integer linear system
```

### Example 4: Fin Arithmetic

```lean
example : (5 : Fin 3) = 2 := by grind  -- 5 mod 3 = 2
example (x : Fin 4) (h : x ≠ 0) (h2 : x ≠ 1) (h3 : x ≠ 2) : x = 3 := by grind
```

### Example 5: Boolean with Arithmetic

```lean
example (h : n = m ∨ n < m) (h2 : ¬(n < m)) : n = m := by grind
```

---

## Quick Reference

| Situation | Recommendation |
|-----------|---------------|
| Pure rewrites | `simp` |
| Integer constraints | `omega` |
| Real linear | `linarith` |
| Ring equations | `ring` |
| Multiple constraint types | `grind` |
| Cross-domain reasoning | `grind` |
| Finite domains | `grind` |
| Combinatorial search | `bv_decide` |
| "Just figure it out" | `grind` (but be prepared to fall back) |

---

## Related References

- [tactics-reference.md](tactics-reference.md) - Comprehensive tactic catalog with simp deep-dive
- [domain-patterns.md](domain-patterns.md) - Domain-specific patterns
- [Lean 4 Reference: The grind tactic](https://lean-lang.org/doc/reference/latest/The--grind--tactic/) - Official documentation

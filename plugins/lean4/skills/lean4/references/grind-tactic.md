# The `grind` Tactic

> **Scope:** Not part of the prove/autoprove default loop. Consulted when the agent encounters goals that `simp` cannot close, or when cross-domain reasoning is needed.

## Table of Contents

- [Quick Path](#quick-path) — decision tree + basic patterns (start here)
- [TLDR](#tldr) — what grind is and when to use it
- [How grind Works](#how-grind-works) — core mechanism, engines, theory solvers
- [grind vs simp: Decision Guide](#grind-vs-simp-decision-guide)
- [Usage Patterns](#usage-patterns) — common patterns by category
- [When NOT to Use grind](#when-not-to-use-grind) — combinatorial explosion, specialized alternatives
- [The @\[grind\] Attribute](#the-grind-attribute) — discovery, registration, variants
- [Integration with Other Tactics](#integration-with-other-tactics) — sequences, after structure work, calc
- [Performance Considerations](#performance-considerations)
- [Common Gotchas](#common-gotchas) — precedence, hypotheses, NoZeroDivisors, BitVec
- [Debugging grind](#debugging-grind) — trace options, diagnostic approach
- [Examples](#examples) — concrete worked examples
- [Real-World Usage: Cryptographic Verification](#real-world-usage-cryptographic-verification)
- [Interactive Mode (Advanced)](#interactive-mode-advanced) — step-by-step exploration DSL
- [Known Limitations](#known-limitations-of-grind) — E-matching depth, nonlinear, bit-shifts
- [Quick Reference](#quick-reference) — situation → recommendation table

## Quick Path

**When to reach for `grind`:**
- `simp` normalizes but does not close the goal
- Goal mixes equalities, inequalities, and algebraic constraints
- Finite-domain reasoning (`Fin`, `Bool`, small enums)
- Cross-domain: arithmetic + propositional + congruence in one goal

**Decision tree:**
```
Can simp close it?
├─ Yes → use simp
└─ No
   ├─ Pure integer arithmetic? → omega
   ├─ Real/rational linear? → linarith
   ├─ Ring/field equation? → ring / field_simp
   ├─ Multiple constraint types? → grind
   ├─ Finite domain? → grind
   └─ Unsure → try simp, then grind, then specialized
```

**Basic patterns:**
```lean
-- After simp normalizes but doesn't close:
simp only [normalize_defs]; grind

-- Cross-domain:
example (h : n < m ∨ n = m) (h2 : n ≠ m) : n < m := by grind

-- With case split:
by_cases h : condition <;> grind
```

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

- **Linear integer arithmetic (`lia`)** - CUTSAT-based solver for integer systems with linear constraints, divisibility
- **Linear arithmetic (`linarith`)** - General linear inequalities (inspired by Mathlib's `linarith`)
- **Commutative rings (`ring`)** - Polynomial reasoning with `CommRing` instances
- **Associative-commutative (`ac`)** - Normalization of AC operators like `+` and `*`
- **Fields** - Division and field arithmetic

**Note:** `lia` and `linarith` are both enabled by default and work together. Disable with `grind -lia` or `grind -linarith`.

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
@[grind] theorem my_useful_fact : ∀ x, f x = g x := ...

-- Now grind can use it automatically
example : f a = g a := by grind
```

**Note:** Not all theorems can use `@[grind]`. The attribute requires the theorem to have a usable pattern for E-matching. Simple facts like `∀ n, n + 0 = n` may fail with "failed to find an usable pattern". In such cases, the lemma is likely already available through the standard library.

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

## Common Gotchas

### Operator Precedence with Bool

**Critical:** Boolean operators have lower precedence than equality!

```lean
-- WRONG: This parses as b && (false = false), which is b && true = b
example (b : Bool) : b && false = false := by grind  -- FAILS!

-- CORRECT: Use explicit parentheses
example (b : Bool) : (b && false) = false := by grind  -- Works
```

### Local Hypotheses Are Automatic

`grind` automatically uses all local hypotheses. Don't pass them explicitly:

```lean
-- Redundant (will warn in nightly):
example (h : ∀ x, f x = x) : f a = a := by grind [h]  -- h is redundant

-- Correct:
example (h : ∀ x, f x = x) : f a = a := by grind  -- Uses h automatically
```

### NoZeroDivisors Requirement

For `x * y = 0 → x = 0 ∨ y = 0` reasoning, `grind` needs a `NoZeroDivisors` instance:

```lean
-- Works: Type has NoZeroDivisors instance
example [CommRing R] [NoZeroDivisors R] (h : x * y = 0) (hx : x ≠ 0) : y = 0 := by grind

-- Fails: Int alone doesn't have NoZeroDivisors visible to grind
example (x y : Int) (h : x * y = 0) (hx : x ≠ 0) : y = 0 := by grind  -- May fail
```

### BitVec Limitations

`grind` struggles with some BitVec patterns that require bit-level reasoning:

```lean
-- May fail: Requires proving all bits of 0xFF are true
example (x : BitVec 8) : x &&& 0xFF#8 = x := by grind  -- Use native_decide instead

-- Works: Simple equality propagation
example (x y : BitVec 8) (h : x = y) : x + 1 = y + 1 := by grind
```

For complex BitVec reasoning, prefer `bv_decide` or `native_decide`.

---

## Debugging `grind`

### When `grind` Fails

1. **Check if goal is actually provable** - `grind` fails on false goals too
2. **Try adding hints** - Key lemmas might not be `@[grind]`
3. **Simplify first** - Complex terms can hide simple facts
4. **Check for missing instances** - Theory solvers need type class instances (e.g., `NoZeroDivisors`)

### Trace Options for Debugging

Use trace options to see `grind`'s internal reasoning:

```lean
-- General grind tracing
set_option trace.grind true in
example ... := by grind

-- Specific subsystems
set_option trace.grind.split true in      -- Case split decisions
set_option trace.grind.lia true in        -- Linear integer arithmetic
set_option trace.grind.lia.model true in  -- Show satisfying models
set_option trace.grind.ematch true in     -- E-matching
set_option trace.grind.mbtc true in       -- Model-based theory combination
```

When `grind` fails, it shows a diagnostic summary including:
- **Asserted facts**: What propositions grind is working with
- **Equivalence classes**: Terms known to be equal
- **CUTSAT assignment**: Variable assignments satisfying linear constraints
- **Ring basis**: Polynomial constraints being tracked

### Diagnostic Approach

```lean
-- Step 1: Does simp make progress?
example : goal := by simp?  -- See what applies

-- Step 2: Can specialized tactics solve it?
example : goal := by omega  -- or linarith, ring, etc.

-- Step 3: What does grind need?
example : goal := by grind [?_]  -- Add lemmas incrementally

-- Step 4: Enable tracing to understand the failure
set_option trace.grind true in
example : goal := by grind
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

### Example 6: AC (Associative-Commutative) Reasoning

```lean
-- grind's AC module handles reordering
example (a b c : Nat) : a + b + c = c + b + a := by grind
example (a b c : Nat) : a * b * c = c * a * b := by grind

-- Combining AC with equality constraints
example (a b c d : Nat) (h : a + b = c + d) : b + a = d + c := by grind
```

### Example 7: Integer Linear Systems (CUTSAT)

```lean
-- From cryptographic verification: solving simultaneous equations
example (x y : Int) (h1 : 2*x + 3*y = 12) (h2 : x - y = 1) : x = 3 := by grind

-- Proving infeasibility
example (x y : Int) : 4*x + 6*y = 9 → 5*x - 2*y = 1 → False := by grind
```

---

## Real-World Usage: Cryptographic Verification

Based on the curve25519-dalek-lean-verify project, here are patterns for cryptographic proofs:

### When `grind` Helps

```lean
-- Closing simple arithmetic branches after structure work
theorem high_bit_zero_of_lt_L (bytes : Array U8 32) (h : U8x32_as_Nat bytes < L) :
    bytes[31].val >>> 7 = 0 := by
  refine high_bit_zero_of_lt_255 bytes ?_
  have : L ≤ 2 ^ 255 := by decide
  grind  -- Combines inequality transitivity

-- After unfolding definitions and simplifying sums
example : 2 ^ 255 ≤ some_sum := by
  simp_all; grind  -- Handles the arithmetic
```

### When `grind` Doesn't Help (Use Alternatives)

```lean
-- BitVec bounds: use bv_decide or bvify
theorem U64_shiftRight_le (a : U64) : a.val >>> 51 ≤ 2 ^ 13 - 1 := by
  bvify 64 at *; bv_decide  -- NOT grind

-- BitVec identities: use native_decide
example : ∀ x : BitVec 64, (x &&& 0) = 0 := by native_decide  -- NOT grind

-- Injectivity proofs: require structural reasoning
lemma byte_array_injective : Function.Injective U8x32_as_Nat := by
  -- Requires induction, not SMT-style reasoning
  intro a b h
  ext i
  -- ... structural proof
```

### Combining `grind` with Domain Tactics

```lean
-- Pattern: Use domain tactics first, then grind for cleanup
example : some_property := by
  progress*  -- Aeneas framework unfolds definitions
  simp_all   -- Simplify what we can
  grind      -- Handle remaining arithmetic/propositional goals
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

## Interactive Mode (Advanced)

> **Version:** Legacy-tested (4.25/4.27 nightly), unverified on 4.28.0-rc1

`grind` has an interactive DSL accessed via `grind =>` for step-by-step proof exploration.

### How to Use Interactive Mode

```lean
example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  grind =>
    show_state  -- Inspect grind's internal state
    done        -- Complete the proof
```

### Interactive Commands

| Command | Description |
|---------|-------------|
| `done` / `finish` | Complete the proof (fails if unsolved) |
| `finish?` | Suggest a finishing tactic |
| `show_state` | Display grind's internal state (facts, eqcs, patterns) |
| `show_eqcs` | Show equivalence classes only |
| `show_cases` | Show available case splits |
| `cases?` | Suggest case splits |
| `cases_next` | Perform the next case split |
| `instantiate [thm]` | Trigger E-matching with a specific theorem |

### Solver Actions (Lean 4.25.0+)

The following solver actions can be invoked inside `grind =>` mode:

| Action | Description |
|--------|-------------|
| `lia` | Invoke Linear Integer Arithmetic solver explicitly |
| `linarith` | Invoke linarith-style linear arithmetic solver |
| `ac` | Invoke associative-commutative normalization |
| `ring` | Invoke ring solver for polynomial equations |

**Note:** These solvers are also config options that are enabled by default. The interactive actions are useful for:
- Debugging: Understanding which solver is handling a goal
- Selective solving: When you want just one solver's reasoning

```lean
-- Config options to disable/enable solvers:
grind -lia        -- Disable LIA solver (cutsat-based)
grind -linarith   -- Disable linarith solver
grind +qlia       -- Accept rational models (incomplete for ℤ)
```

### Key Limitation: `instantiate` Only Works with Constants

**Critical:** `instantiate [thm]` expects `@[grind]`-registered theorems, NOT local hypotheses:

```lean
-- FAILS: h is a local hypothesis, not a constant
example (f : Nat → Nat) (h : ∀ n, f n = n + 1) : f 0 = 1 := by
  grind =>
    instantiate [h]  -- Error: Unknown constant `h`
    done

-- WORKS: my_thm is a registered @[grind] theorem
@[grind] theorem my_add : ∀ n : Nat, n + 0 = n := Nat.add_zero

example (x : Nat) : x + 0 = x := by
  grind =>
    instantiate [my_add]
    done
```

### When Interactive Mode Is (and Isn't) Useful

**Limited utility in practice:**
1. Most goals `grind` can solve, it solves IMMEDIATELY - no time for interaction
2. Goals `grind` CAN'T solve stay unsolved even with `instantiate`
3. Commands like `show_cases` often report "no case splits" because grind auto-solved

**Main value is DEBUGGING:**
```lean
-- Use interactive mode to understand why grind fails
set_option trace.grind true in
example (f : Nat → Nat) (h : ∀ n, f n = n + 1) : f (f 0) = 2 := by
  grind =>
    show_state  -- See: pattern [f #0], CUTSAT assigns f(f 0):=1, f 0:=3
  -- Grind fails! E-matching doesn't iterate enough. Use simp instead:
  simp [h]
```

**For most proofs, use plain `grind` with trace options instead:**
```lean
set_option trace.grind.eqc true in
example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  grind  -- Trace shows equivalence class merging
```

### Configuration Modifiers

```lean
-- Use only specified lemmas
grind only [lemma1, lemma2]

-- Add lemmas to default set
grind [extra_lemma]

-- Exclude a lemma
grind [-excluded_lemma]
```

### What `grind` Handles Well

Based on testing against cryptographic verification patterns:

```lean
-- PASS: Equality chain reasoning (congruence closure)
example (a b c d : Nat) (h1 : a = b) (h2 : b = c) (h3 : c = d) : a = d := by grind

-- PASS: Congruence under function application
example (f : Nat → Nat) (a b : Nat) (h : a = b) : f a = f b := by grind

-- PASS: Mixed inequality and equality
example (x y z : Nat) (h1 : x < y) (h2 : y = z) : x < z := by grind

-- PASS: Modular equality propagation
example (x y z : Nat) (h : x = y) : x % z = y % z := by grind

-- PASS: Multi-constraint integer solving
example (x y : Nat) (h1 : x ≤ 10) (h2 : y ≤ 10) (h3 : x + y = 20) : x = 10 ∧ y = 10 := by grind

-- PASS: Bounded arithmetic (no shifts)
example (x y : Nat) (hx : x < 2^52) (hy : y < 2^52) : x + y < 2^53 := by grind
```

### Known Limitations of `grind`

> **Version:** Legacy-tested (4.25/4.27 nightly), unverified on 4.28.0-rc1

Based on testing (4.25.1 stable and 4.27.0-nightly-2025-11-25):

1. **E-matching doesn't iterate enough for nested applications:**
   ```lean
   -- h : ∀ n, f n = n + 1 has pattern [f #0]
   -- But grind won't instantiate twice to prove f (f 0) = 2
   example (f : Nat → Nat) (h : ∀ n, f n = n + 1) : f (f 0) = 2 := by
     simp [h]  -- Use simp for repeated rewriting
   ```

2. **CUTSAT handles linear arithmetic well (updated finding):**
   ```lean
   -- Plain grind with lia enabled (default) solves linear arithmetic
   example (x y : Int) (h1 : x > 0) (h2 : y > 0) : x + y > 0 := by grind  -- Works!
   example (x y : Int) (h1 : 2*x + 3*y ≤ 10) (h2 : x ≥ 0) (h3 : y ≥ 2) : x ≤ 2 := by grind  -- Works!

   -- For complex cases or when grind fails, omega is the fallback
   ```

3. **Nonlinear arithmetic is outside scope:**
   ```lean
   -- CUTSAT treats x and x*x as independent variables
   example (x : Int) (h : x ≥ 0) (h2 : x < 10) : x * x < 100 := by
     -- grind FAILS: CUTSAT assigns x := 0, x^2 := 100
     nlinarith [sq_nonneg x]  -- Use nlinarith for nonlinear bounds
   ```

4. **CUTSAT doesn't understand bit-shift semantics:**
   ```lean
   -- Grind assigns x and (x >>> 51) independently without linking them
   example (x : Nat) (hx : x < 2^64) : x >>> 51 < 2^13 := by
     -- grind FAILS: CUTSAT assigns x := 0, x >>> 51 := 8192
     omega  -- Use omega (understands x >>> n = x / 2^n)
   ```
   This is critical for cryptographic verification where bit-shifting bounds are common.

5. **`@[grind]` requires discoverable patterns:**
   ```lean
   -- Fails: No usable pattern for iff
   @[grind] theorem bad : P ↔ Q := ...  -- Error: failed to find usable pattern

   -- Works: Function application gives clear pattern
   @[grind] theorem good (n : Nat) : n + n = 2 * n := by omega
   ```

6. **Function injectivity requires structural reasoning:**
   ```lean
   -- Grind can't prove injectivity of sum-based interpretations
   lemma U8x32_as_Nat_injective : Function.Injective U8x32_as_Nat := by
     -- Requires ext + induction, not SMT
     intro a b hab; ext i; ...
   ```

---

## Related References

- [tactics-reference.md](tactics-reference.md) - Comprehensive tactic catalog with simp deep-dive
- [domain-patterns.md](domain-patterns.md) - Domain-specific patterns
- [Lean 4 Reference: The grind tactic](https://lean-lang.org/doc/reference/latest/The--grind--tactic/) - Official documentation

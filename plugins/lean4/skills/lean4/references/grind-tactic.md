# The `grind` Tactic

> **Scope:** Not part of the prove/autoprove default loop. Consulted when the agent encounters goals that `simp` cannot close, or when cross-domain reasoning is needed.

> **Version metadata:**
> - **Verified on:** Lean reference + release notes through `v4.27.0`
> - **Last validated:** 2026-02-17
> - **Confidence:** medium (mixed: official docs + targeted examples, not full snippet CI)

## Table of Contents

- [Quick Path](#quick-path)
- [What `grind` Does](#what-grind-does)
- [Version Matrix](#version-matrix)
- [Usage Patterns](#usage-patterns)
- [Controls and Performance](#controls-and-performance)
- [The `@[grind]` and `@[grind_pattern]` Attributes](#the-grind-and-grind_pattern-attributes)
- [Common Gotchas](#common-gotchas)
- [Interactive Mode](#interactive-mode)
- [Known Limitations](#known-limitations)
- [Related References](#related-references)

## Quick Path

Use `grind` when:
- `simp` normalizes but does not close
- the goal mixes equalities, inequalities, and algebraic facts
- finite-domain reasoning is involved (`Fin`, `Bool`, small enums)

Use specialized tactics when one domain is dominant:
- integer linear arithmetic -> `omega`
- real/rational linear arithmetic -> `linarith`
- nonlinear arithmetic -> `nlinarith`
- pure rewriting -> `simp` / `simp only`
- combinatorial bit-level search -> `bv_decide`

### Single Decision Flow

```text
Can simp close it?
├─ Yes -> use simp
└─ No
   ├─ Integer-linear only? -> omega
   ├─ Real/rational-linear only? -> linarith
   ├─ Nonlinear arithmetic? -> nlinarith
   ├─ Combinatorial bit-level goal? -> bv_decide
   └─ Mixed constraints/cross-domain? -> grind
```

### Triage Recipe (Safe Default)

```lean
-- 1) Inspect simplification candidates.
simp?

-- 2) Ask grind for a suggested call.
grind?

-- 3) Start with bounded splitting to avoid search blowups.
grind (splits := 0)

-- 4) If still stuck, switch to a domain solver (omega/linarith/nlinarith/bv_decide).
```

## What `grind` Does

`grind` is SMT-style automation for Lean goals. It coordinates:
- congruence closure
- E-matching
- case splitting
- arithmetic/algebraic sub-solvers

The tactic works by contradiction over a shared fact store. Compared to `simp` (local rewrite normalization), `grind` is designed for mixed-constraint closure.

```lean
example (h1 : a = b) (h2 : b = c) : a = c := by
  grind

example [CommRing R] [NoZeroDivisors R] (h : x * y = 0) (hx : x ≠ 0) : y = 0 := by
  grind

example : (5 : Fin 3) = 2 := by
  grind
```

## Version Matrix

| Feature | Available Since | Notes |
|---|---|---|
| `grind?` companion tactic | `v4.17.0` | Reimplemented in `v4.26.0` using newer suggestion infra |
| `grind -splitMatch` / `grind -splitIte` | `v4.17.0` | Disable selected case-splitting sources |
| `grind +splitImp` | `v4.20.0` | Allow implication splitting |
| Interactive `instantiate` supports local theorems/hyps | `v4.25.0` | Older toolchains may require global constants |
| `@[grind_pattern]` constraints | `v4.26.0` | Pattern shaping became more expressive |
| `@[grind_pattern]` guards | `v4.27.0` | More precise pattern activation |
| `grind -funCC`, `grind +revert`, `grind -reducible` | `v4.27.0` | Additional control over congruence/reduction/search |

If your toolchain is older than these entries, expect option/behavior differences.

## Usage Patterns

### Baseline Sequence

```lean
example (h : n < m ∨ n = m) (hne : n ≠ m) : n < m := by
  simp at *
  grind
```

### With Hints

```lean
example (h1 : a = b) (h2 : b = c) : a = c := by
  grind [h1, h2]
```

### After Manual Case Structure

```lean
example (p : Prop) [Decidable p] (h1 : p → q) (h2 : ¬p → q) : q := by
  by_cases hp : p
  · grind
  · grind
```

### Restricting / Excluding Lemmas

```lean
-- Restrict to explicit lemmas only.
grind only [lemma1, lemma2]

-- Exclude a noisy lemma from the default pool.
grind [-lemma3]
```

## Controls and Performance

Key knobs:

```lean
-- Case-splitting budget.
grind (splits := 0)
grind (splits := 8)

-- Split sources.
grind -splitIte -splitMatch +splitImp

-- Solver toggles.
grind -lia -linarith -ring

grind -funCC +revert -reducible
```

Performance tips:
1. Start with `simp`/`simp only` to reduce term size.
2. Keep splitting bounded before adding large hint sets.
3. Disable subsystems you do not need (`-ring`, `-linarith`, etc.).
4. Prefer specialized tactics when a single theory dominates.

## The `@[grind]` and `@[grind_pattern]` Attributes

### `@[grind]` Registration

```lean
@[grind] theorem my_refl (x : Nat) : x = x := by
  rfl

@[grind =] theorem my_add_zero (x : Nat) : x + 0 = x := by
  exact Nat.add_zero x

@[grind ->] theorem my_left (h : p ∧ q) : p := by
  exact h.left
```

Use `@[grind]` sparingly on lemmas with stable, reusable patterns.

### `@[grind_pattern]` for E-matching Shape

When automatic pattern extraction is poor, `@[grind_pattern]` can improve matching behavior (especially on newer versions with constraints/guards):

```lean
-- Sketch: attach grind_pattern metadata to shape triggering.
@[grind_pattern] theorem map_fusion (f g : α → α) (x : α) :
    List.map f (List.map g [x]) = List.map (fun y => f (g y)) [x] := by
  simp
```

Use this only when ordinary `@[grind]` registration is insufficient and profiling shows matching misses.

## Common Gotchas

### Boolean Precedence

```lean
-- Parses as b && (false = false), usually not what you intend.
example (b : Bool) : b && false = false := by
  -- Parenthesize explicitly to avoid precedence ambiguity.
  exact Bool.and_false b

-- Prefer explicit parentheses.
example (b : Bool) : (b && false) = false := by
  grind
```

### Redundant Local-Hypothesis Hints

`grind` already sees local hypotheses; `grind [h]` is often redundant when `h` is local.

### Typeclass Assumptions Matter

Zero-product reasoning typically needs `NoZeroDivisors`:

```lean
example [CommRing R] [NoZeroDivisors R] (h : x * y = 0) (hx : x ≠ 0) : y = 0 := by
  grind
```

## Interactive Mode

Interactive mode (`grind =>`) is useful mainly for debugging and targeted control.

```lean
example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  grind =>
    show_state
    done
```

Common commands:
- `show_state`, `show_eqcs`, `show_cases`
- `cases?`, `cases_next`
- `instantiate [thm]`
- `done` / `finish` / `finish?`

### Version-Sensitive `instantiate`

On `v4.25.0+`, `instantiate` may use local hypotheses/theorems directly:

```lean
example (f : Nat → Nat) (h : ∀ n, f n = n + 1) : f 0 = 1 := by
  grind =>
    instantiate [h]
    done
```

If your toolchain reports `Unknown constant` for locals, fall back to global `@[grind]` lemmas or plain `grind`/`simp`.

## Known Limitations

Observed patterns where `grind` may not be the best tool:

1. Nonlinear arithmetic is often better handled by `nlinarith`.

```lean
example (x : Int) (h1 : 0 ≤ x) (h2 : x < 10) : x * x < 100 := by
  nlinarith [h1, h2]
```

2. Bit-level/algebraic bitvector goals are often better with `bv_decide` or `native_decide`.

```lean
example : ∀ x : BitVec 64, (x &&& 0) = 0 := by
  intro x
  native_decide
```

3. Large case-splitting spaces may blow up; cap `splits` first.

4. Structural proofs (e.g., injectivity with induction/extensionality) usually need explicit proof structure.

## Related References

- [tactics-reference.md](tactics-reference.md) - Compact tactic catalog with quick `grind` entry
- [simproc-patterns.md](simproc-patterns.md) - `simp`-side deterministic rewrite patterns
- [Lean 4 Reference: The grind tactic](https://lean-lang.org/doc/reference/latest/The--grind--tactic/)
- [Lean Releases](https://lean-lang.org/doc/reference/latest/releases/) - version-specific behavior

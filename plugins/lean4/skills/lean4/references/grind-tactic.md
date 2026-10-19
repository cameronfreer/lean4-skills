# The `grind` Tactic

> **Scope:** Not part of the prove/autoprove default loop. Consulted when the agent encounters goals that `simp` cannot close, or when cross-domain reasoning is needed.

> **Version metadata:**
> - **Verified on:** Lean `v4.33.1` and `v4.35.0` (core examples, options, attribute and interactive syntax checked against each toolchain's source and compiled), plus `v4.34.0` for the entries marked `v4.34.0`; Mathlib `346a4bd3f9` on Lean `v4.35.0-rc3` (ring and arithmetic examples)
> - **Last validated:** 2026-10-19
> - **Confidence:** high for the compiled examples (core ones run in CI: `tests/fixtures/reference_snippets/grind_snippets.lean`, `grind_suggestions_snippets.lean`; `grind_bv_snippets.lean` needs `v4.34.0`+ and is run by the runner only on such a toolchain; Mathlib ones local-only: `grind_mathlib_snippets.lean`); medium for the Version Matrix "since" column (release notes, not rechecked on older toolchains)

## Table of Contents

- [Quick Path](#quick-path)
- [What `grind` Does](#what-grind-does)
- [Version Matrix](#version-matrix)
- [Usage Patterns](#usage-patterns)
- [Controls and Performance](#controls-and-performance)
- [The `@[grind]` Attribute and the `grind_pattern` Command](#the-grind-attribute-and-the-grind_pattern-command)
- [Common Gotchas](#common-gotchas)
- [Interactive Mode](#interactive-mode)
- [Known Limitations](#known-limitations)
- [Suggestions and Locals](#suggestions-and-locals)
- [Simproc Escalation](#simproc-escalation)
- [Anti-Patterns](#anti-patterns)
- [Related References](#related-references)

## Quick Path

Use `grind` when:
- `simp` normalizes but does not close
- the goal mixes equalities, inequalities, and algebraic facts
- finite-domain reasoning is involved (`Fin`, `Bool`, small enums)

Use specialized tactics when one domain is dominant:
- integer linear arithmetic -> `omega` (or `lia`: `grind` restricted to its linear-integer solver)
- real/rational linear arithmetic -> `linarith` (Mathlib)
- nonlinear arithmetic -> `nlinarith` (Mathlib)
- pure rewriting -> `simp` / `simp only`
- combinatorial bit-level search -> `bv_decide` (`import Std.Tactic.BVDecide`)

### Single Decision Flow

```text
Can simp close it?
├─ Yes -> use simp
└─ No
   ├─ Integer-linear only? -> omega / lia
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

example : (5 : Fin 3) = 2 := by
  grind

-- Mathlib: in a field, zero-product reasoning is built in.
example {K : Type*} [Field K] (x y : K) (h : x * y = 0) (hx : x ≠ 0) : y = 0 := by
  grind
```

## Version Matrix

Every feature below, except the entries marked `v4.34.0`, exists and parses on `v4.33.1` and `v4.35.0` (`grind_snippets.lean`); those exist from `v4.34.0` on. The "Available since" column is taken from the Lean release notes and was not rechecked against older toolchains.

| Feature | Available since | Notes |
|---|---|---|
| `grind?` companion tactic | `v4.17.0` | Reimplemented in `v4.26.0` using newer suggestion infra |
| `grind -splitMatch` / `grind -splitIte` | `v4.17.0` | Disable selected case-splitting sources |
| `grind +splitImp` | `v4.20.0` | Allow implication splitting |
| Interactive `instantiate` with local theorems | `v4.25.0` | On `v4.33.1`/`v4.35.0` a local is used by plain `instantiate` or by its anchor; `instantiate [h]` by hypothesis name is rejected (see [Interactive Mode](#interactive-mode)) |
| `grind_pattern` constraints | `v4.26.0` | Pattern shaping became more expressive |
| `grind_pattern` guards | `v4.27.0` | More precise pattern activation |
| `grind -funCC`, `grind +revert`, `grind -reducible` | `v4.27.0` | Additional control over congruence/reduction/search |
| `@[grind hom]`, `@[grind hom_pred]` | `v4.34.0` | Homomorphism rules into a solver domain (renamed from `homo`/`homo_pred`); absent on `v4.33.1`, accepted on `v4.34.0` (checked) |
| `bv_decide` inside `grind => …` | `v4.34.0` | Bit-blasts after grind's congruence closure; a parse error on `v4.33.1` (checked; see [Interactive Mode](#interactive-mode)) |

If your toolchain is older than these entries, expect option/behavior differences.

## Usage Patterns

### Baseline Sequence

```lean
example (n m : Nat) (h : n < m ∨ n = m) (hne : n ≠ m) : n < m := by
  simp at *
  grind
```

Give binders their types: with auto-bound `n m` the statement's instances are stuck before `grind` runs.

### With Hints

Hints are theorems to instantiate or definitions to unfold:

```lean
def dbl (x : Nat) : Nat := x + x

example (a : Nat) : dbl a = 2 * a := by
  grind [dbl]
```

`grind` already uses every local hypothesis. Passing one as a hint is an **error**, not a no-op: `grind [h1]` reports ``redundant parameter `h1`, `grind` uses local hypotheses automatically``.

### After Manual Case Structure

```lean
example (p q : Prop) [Decidable p] (h1 : p → q) (h2 : ¬p → q) : q := by
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

`-lemma3` only applies to a lemma registered with `@[grind]`; for any other name it is an error.

## Controls and Performance

Key knobs (defaults from `Init/Grind/Config.lean`, identical on `v4.33.1` and `v4.35.0`):

```lean
-- Case-splitting budget (default 9).
grind (splits := 0)
grind (splits := 8)

-- E-matching rounds per split phase (default 5).
grind (ematch := 3)

-- Theorem-instantiation generation limit (default 8).
grind (gen := 5)

-- Max E-matching instances per branch (default 1000).
grind (instances := 300)

-- Split sources.
grind -splitIte -splitMatch +splitImp

-- Solver toggles.
grind -lia -linarith -ring -ac

-- Faster but incomplete integer arithmetic (rational relaxation).
grind +qlia

grind -funCC +revert -reducible
```

Good first pass for slowdown diagnosis:

```lean
grind (splits := 4) (ematch := 3) (instances := 300) (gen := 5) -splitIte -splitMatch
```

Performance tips:
1. Start with `simp`/`simp only` to reduce term size.
2. Keep splitting bounded before adding large hint sets.
3. Disable subsystems you do not need (`-ring`, `-linarith`, etc.).
4. Prefer specialized tactics when a single theory dominates.
5. Use traces to diagnose search behavior:

```lean
set_option trace.grind.ematch.instance true in
set_option trace.grind.split true in
grind
```

## The `@[grind]` Attribute and the `grind_pattern` Command

### `@[grind]` Registration

```lean
def dbl (x : Nat) : Nat := x + x

@[grind =] theorem dbl_def (x : Nat) : dbl x = x + x := rfl

def Pos (n : Nat) : Prop := 0 < n

@[grind →] theorem Pos.ne_zero {n : Nat} (h : Pos n) : n ≠ 0 := by
  unfold Pos at h; omega

example (a : Nat) : dbl a = 2 * a := by grind
example (n : Nat) (h : Pos n) : n ≠ 0 := by grind
```

Registration fails loudly when no usable pattern exists: `@[grind]` on `x = x`, `@[grind =]` on `x + 0 = x` (the left side normalises away), and `@[grind →]` on `p ∧ q → p` are all rejected.

A bare `@[grind]` can also succeed with a pattern that never fires. On `0 < x → 0 < trip x` it selects `1 ≤ trip x`, the normalised conclusion, and `grind` then fails on goals the lemma would close. Lean reports the alternatives as `Try these` info. Use `@[grind?]` to print the selected pattern, and pick a modifier deliberately.

Attribute variants (`Init/Grind/Attr.lean`):
- `@[grind]` / `@[grind .]`: default — conclusion, then hypotheses left to right
- `@[grind =]`, `@[grind =_]`, `@[grind _=_]`: left side, right side, or both sides of an equation
- `@[grind ←=]`: instantiate an equation when the matching disequality is assumed
- `@[grind →]`, `@[grind ←]`: patterns from the hypotheses (forward) or from the conclusion (backward)
- `@[grind ⇒]`, `@[grind ⇐]`: hypotheses then conclusion, or conclusion then hypotheses right to left
- `@[grind cases]`, `@[grind cases eager]`: split guidance for inductive predicates
- `@[grind intro]`: use constructors of an inductive predicate as matching rules
- `@[grind ext]`, `@[grind inj]`, `@[grind funCC]`, `@[grind norm]`, `@[grind unfold]`
- `@[grind symbol <prio>]`: priority of a constant during pattern selection
- `@[grind hom]`, `@[grind hom_pred]`: homomorphism rules and predicates (`v4.34.0`+)
- `gen` suffix (accepted after `=`, `=_`, `_=_`, `←`, `.`); `usr`, in tactic hints (`grind [usr thm]`), selects the pattern declared with `grind_pattern`
- `@[grind!]`: minimal indexable subexpression pattern selection; `@[grind?]` / `@[grind!?]` also print the selected patterns

Use `@[grind]` sparingly on lemmas with stable, reusable patterns. Keep exploratory annotations local first (`@[local grind ...]`); promote to global only after repeated wins across files.

### `grind_pattern` for E-matching Shape

When automatic pattern extraction is poor, use explicit patterns. This is the command's own docstring example:

```lean
opaque f : Nat → Nat
axiom fMono : x ≤ y → f x ≤ f y

grind_pattern fMono => f x, f y where
  guard x ≤ y
  x =/= y

example : f b = f c → a ≤ f a → f (f a) ≤ f (f (f a)) := by
  grind
```

Supported constraints: `guard`, `check`, `size`, `depth`, `gen`, `max_insts`, value/ground predicates (`is_ground`, `is_value`, `is_strict_value`, `not_value`, `not_strict_value`), and definitional equality/inequality guards (`x =?= t`, `x =/= t`).

Use this command only when ordinary `@[grind]` registration is insufficient and profiling shows matching misses.

## Common Gotchas

### Boolean Precedence

`b && false = false` parses as `b && (false = false)`; the `Prop` is coerced back with `decide`, so the statement is `(b && decide (false = false)) = true`. A proof of `(b && false) = false` does not fit it.

```lean
-- Prefer explicit parentheses.
example (b : Bool) : (b && false) = false := by
  grind
```

### Redundant Local-Hypothesis Hints

`grind` already sees local hypotheses; `grind [h]` with a local `h` is an error (see [With Hints](#with-hints)).

### Typeclass Assumptions Matter

`grind`'s ring reasoning does not derive the zero-product property from `NoZeroDivisors` or `IsDomain`, nor on `ℤ`. In a field it does (see [What `grind` Does](#what-grind-does)). Elsewhere, pass the lemma:

```lean
-- Mathlib
example {R : Type*} [CommRing R] [NoZeroDivisors R] (x y : R) (h : x * y = 0) (hx : x ≠ 0) :
    y = 0 := by
  grind [mul_eq_zero]
```

Bind `x y : R` explicitly. With auto-bound implicits they are elaborated as natural numbers, not elements of `R`.

## Interactive Mode

Use `grind => ...` as the default development mode — it is the most observable and steerable path.

```lean
def h1 (n : Nat) : Nat := n + 1

@[grind =] theorem h1_def (n : Nat) : h1 n = n + 1 := rfl

example : h1 0 = 1 := by
  grind =>
    show_state
    instantiate
```

If `grind` closes the goal on entry, the first command fails with "No goals to be solved". For example, `a = c` from `a = b` and `b = c` is closed by congruence closure before `show_state` runs.

Common commands:
- `show_state`, `show_eqcs`, `show_cases`, `show_asserted`, `show_true`, `show_false`, `show_local_thms`, `show_goals`
- `cases?`, `cases #anchor`, `cases_next`
- `instantiate`, `instantiate [thm]`, `instantiate only [thm]` (`use [thm]` is shorthand for the last)
- `have` (inject missing intermediate facts)
- `done` / `finish` / `finish?`
- `try t` (shorthand for `first (t) (skip)`), `first (t₁) (t₂)`

### Bit-Blasting Inside `grind` (`v4.34.0`+)

From `v4.34.0` on, `bv_decide` is also a `grind` interactive command. It bit-blasts the goal using the equalities grind has already derived. On its own, `bv_decide` treats `f x` and `f y` as unrelated; grind's congruence closure first makes them equal:

```lean
import Std.Tactic.BVDecide

opaque f : BitVec 8 → BitVec 8

example (x y : BitVec 8) (h : x = y) : f x ^^^ f y = 0 := by
  grind =>
    bv_decide
```

Standalone `bv_decide` fails on this goal. Without `import Std.Tactic.BVDecide`, the command reports "to use `bv_decide`, please include `import Std.Tactic.BVDecide`". On `v4.33.1` it is a parse error.

### Debugging Loop

```lean
example : h1 0 = 1 := by
  grind =>
    show_state
    try show_asserted
    try show_cases
    try cases_next
    instantiate
    try finish
```

`instantiate` may close the goal entirely. Guard trailing steps with `try` (or `first ... (skip)`), which stay silent once no goal remains. Once stable, replace ad-hoc `have` steps with annotations or `grind_pattern` so the proof can collapse toward `grind`/`grind only [...]`.

### Local Hypotheses in `instantiate`

A local hypothesis such as `hk : ∀ n, k n = n + 1` is a local theorem. Plain `instantiate` uses it:

```lean
example (k : Nat → Nat) (hk : ∀ n, k n = n + 1) : k 0 = 1 := by
  grind =>
    instantiate
```

`instantiate [hk]` / `instantiate only [hk]` do **not** resolve a local by name on `v4.33.1`/`v4.35.0`; they report ``Unknown constant `hk` ``. To target one local theorem, run `show_local_thms` and pass the anchor it prints (`instantiate [#0c1c]`).

An anchor is a stable hash of an expression; for a local theorem, of its type. It does not change between runs, but editing that expression changes it: renaming `k` to `k2` in `hk` turns `#0c1c` into `#cbee`. Anchors are supported in checked proofs. `grind?` itself can suggest both an anchor-restricted call and an anchor-free one:

```lean
example (k : Nat → Nat) (hk : ∀ n, k n = n + 1) (_hz : ∀ n, k n ≠ 0) : k 0 = 1 := by
  grind?  -- Try these: grind only [#0c1c]; grind only; grind => instantiate only [#0c1c]
```

Prefer the anchor-free suggestion when it is equally clear and reliable.

## Known Limitations

Observed patterns where `grind` may not be the best tool:

1. Nonlinear arithmetic is often better handled by `nlinarith`. On this goal `grind` fails and `nlinarith` succeeds (Mathlib):

```lean
example (x : Int) (h1 : 0 ≤ x) (h2 : x < 10) : x * x < 100 := by
  nlinarith [h1, h2]
```

2. Bit-level bitvector goals are often better with `bv_decide` or `simp`:

```lean
import Std.Tactic.BVDecide

example : ∀ x : BitVec 64, (x &&& 0) = 0 := by
  intro x
  bv_decide
```

`native_decide` needs a closed goal: after `intro x` it fails with "Expected type must not contain free variables".

3. Large case-splitting spaces may blow up; cap `splits` first.

4. Structural proofs (e.g., injectivity with induction/extensionality) usually need explicit proof structure.

## Suggestions and Locals

`grind` supports premise selection via `+suggestions`, and `+locals` harvests definitions from the current file. Local hypotheses are always available; `+locals` is not needed for them.

`+suggestions` needs a library-suggestions engine. Without one it fails with "No library suggestions engine registered". Add `import Lean.LibrarySuggestions.Default` to use Lean's built-in engine, or configure one with `set_library_suggestions`.

Staged workflow:
1. Prototype: `grind +suggestions +locals`
2. Minimize: run `grind? +suggestions +locals`, adopt the `grind only [...]` it suggests when stable. The suggestion names the premises it used, so it no longer needs the flags. Keep the flags on `grind?`: bare `grind?` drops those premise pools, and on a goal that needed them it can only suggest `grind => sorry`
3. Stabilize: convert repeatedly selected lemmas into `@[local grind ...]` / `@[local simp]`
4. Promote to global annotations only after repeated success across files

In large API files, prefer aggressive local annotations first so repetitive theorem arguments disappear. This keeps exploration fast while converging to deterministic proofs.

## Simproc Escalation

Create a simproc only when all are true:
- the same rewrite pattern recurs across multiple goals/files
- `simp` lemmas are noisy, fragile, or expensive
- the reduction is deterministic and terminating

Authoring mechanics — `dsimproc` vs `simproc`, pre/post placement, result semantics, verified templates, and performance discipline — are owned by [simp-reference.md § Simproc Authoring](simp-reference.md#simproc-authoring).

## Anti-Patterns

- Running `grind` first on unsimplified goals with large contexts
- Adding broad global simp lemmas to help one stubborn goal
- Introducing simprocs for one-off rewrites
- Keeping fallback tactic chains in final proof scripts
- Long-term dependence on `+suggestions` when stable annotations would make proofs deterministic

## Related References

- [tactics-reference.md](tactics-reference.md) - Compact tactic catalog with quick `grind` entry
- [simp-reference.md](simp-reference.md) - Simp hygiene + deterministic rewrite patterns
- [Lean 4 Reference: The grind tactic](https://lean-lang.org/doc/reference/latest/The--grind--tactic/)
- [Lean Releases](https://lean-lang.org/doc/reference/latest/releases/) - version-specific behavior

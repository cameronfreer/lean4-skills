-- Compile-check for the Mathlib-dependent claims in references/grind-tactic.md
-- (#181). Requires a Mathlib project; run from one:
--
--   lake env lean /path/to/lean4-skills/plugins/lean4/tests/fixtures/reference_snippets/grind_mathlib_snippets.lean
--
-- Not wired into CI (CI has no Mathlib). Last checked against Mathlib commit
-- 346a4bd3f95e8591976c91259badc6d2c300f638 (Lean 4.35.0-rc3, local checkout),
-- full file, exit 0. If you change a documented snippet, change it here too
-- and re-run. Documented failures are `fail_if_success`.
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Tactic.Linarith

-- § Typeclass Assumptions Matter: zero-product reasoning.
-- In a field, `grind` closes it on its own.
example {K : Type*} [Field K] (x y : K) (h : x * y = 0) (hx : x ≠ 0) : y = 0 := by
  grind

-- With only `NoZeroDivisors` (or a domain, or even `ℤ`) it does not ...
example {R : Type*} [CommRing R] [NoZeroDivisors R] (x y : R) (h : x * y = 0) (hx : x ≠ 0) :
    y = 0 := by
  fail_if_success grind
  -- ... until it is given the zero-product lemma.
  grind [mul_eq_zero]

example {R : Type*} [CommRing R] [IsDomain R] (x y : R) (h : x * y = 0) (hx : x ≠ 0) :
    y = 0 := by
  fail_if_success grind
  grind [mul_eq_zero]

example (x y : ℤ) (h : x * y = 0) (hx : x ≠ 0) : y = 0 := by
  fail_if_success grind
  grind [mul_eq_zero]

-- Auto-bound implicits are a trap here: without binders for `x y`, they are
-- elaborated as natural numbers, not elements of `R`.
example [CommRing R] [NoZeroDivisors R] (h : x * y = 0) (_hx : x ≠ 0) : x * y = (0 : ℕ) := by
  exact h

-- § Known Limitations: nonlinear arithmetic.
example (x : Int) (h1 : 0 ≤ x) (h2 : x < 10) : x * x < 100 := by
  fail_if_success grind
  nlinarith [h1, h2]

-- § Quick Path: rational-linear arithmetic.
example (x y : ℚ) (h1 : x < y) (h2 : y < 3) : x < 3 := by
  linarith

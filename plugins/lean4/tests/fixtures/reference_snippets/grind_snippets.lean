import Std.Tactic.BVDecide

/-!
Core-Lean evidence (no Mathlib) for `references/grind-tactic.md` (#181).
Run by the `lean-integration` workflow with the `lean_file_gate` fixture's pinned
toolchain (messages pinned to Lean 4.33.1; a toolchain bump updates them
deliberately), via `run_core_snippets.sh`:

    cd plugins/lean4/tests/fixtures/lean_file_gate
    lean ../reference_snippets/grind_snippets.lean

Every documented repair is elaborated as written. Every documented failure is
`fail_if_success` (the tactic must keep failing) or a `#guard_msgs` block (the
message must not drift). The `Mathlib`-dependent claims (`CommRing`, `Field`,
`nlinarith`, `linarith`) live in `grind_mathlib_snippets.lean`.
-/

/-! ### § What `grind` Does -/

example (h1 : a = b) (h2 : b = c) : a = c := by
  grind

example : (5 : Fin 3) = 2 := by
  grind

/-! ### § Usage Patterns -/

example (n m : Nat) (h : n < m ∨ n = m) (hne : n ≠ m) : n < m := by
  simp at *
  grind

def dbl (x : Nat) : Nat := x + x

-- A hint is a theorem or a definition to unfold, not a local hypothesis.
example (a : Nat) : dbl a = 2 * a := by
  grind [dbl]

-- Passing a local hypothesis is an error, not a no-op.
/-- error: redundant parameter `h1`, `grind` uses local hypotheses automatically -/
#guard_msgs in
example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  grind [h1, h2]

example (p q : Prop) [Decidable p] (h1 : p → q) (h2 : ¬p → q) : q := by
  by_cases hp : p
  · grind
  · grind

/-! ### § Controls and Performance (every documented knob parses and runs) -/

example (a b : Nat) (h : a = b) : b = a := by grind (splits := 0)
example (a b : Nat) (h : a = b) : b = a := by grind (splits := 8)
example (a b : Nat) (h : a = b) : b = a := by grind (ematch := 3)
example (a b : Nat) (h : a = b) : b = a := by grind (gen := 5)
example (a b : Nat) (h : a = b) : b = a := by grind (instances := 300)
example (a b : Nat) (h : a = b) : b = a := by grind -splitIte -splitMatch +splitImp
example (a b : Nat) (h : a = b) : b = a := by grind -lia -linarith -ring -ac
example (a b : Nat) (h : a = b) : b = a := by grind +qlia
example (a b : Nat) (h : a = b) : b = a := by grind -funCC +revert -reducible
example (a b : Nat) (h : a = b) : b = a := by
  grind (splits := 4) (ematch := 3) (instances := 300) (gen := 5) -splitIte -splitMatch
example (a b : Nat) (h : a = b) : b = a := by
  set_option trace.grind.ematch.instance true in
  set_option trace.grind.split true in
  grind
example (x y : Int) (h : x < y) : x + 1 ≤ y := by lia

/-! ### § The `@[grind]` Attribute and the `grind_pattern` Command -/

section Attributes

@[grind =] theorem dbl_def (x : Nat) : dbl x = x + x := rfl

example (a : Nat) : dbl a = 2 * a := by grind

def Pos (n : Nat) : Prop := 0 < n

@[grind →] theorem Pos.ne_zero {n : Nat} (h : Pos n) : n ≠ 0 := by
  unfold Pos at h; omega

example (n : Nat) (h : Pos n) : n ≠ 0 := by grind

-- Restricting / excluding: `-` only applies to a `[grind]`-registered lemma.
example (a : Nat) : dbl a = 2 * a := by grind only [dbl_def]
example (a : Nat) : dbl a = 2 * a := by grind [-dbl_def, dbl]

/-- error: `Nat.add_zero` is not marked with the `[grind]` attribute -/
#guard_msgs in
example (x : Nat) : x + 0 = x := by grind [-Nat.add_zero]

-- Registration fails loudly when no usable pattern exists.
/-- error: invalid `grind` theorem, failed to find -/
#guard_msgs (substring := true) in
@[grind] theorem my_refl (x : Nat) : x = x := rfl

/-- error: invalid pattern -/
#guard_msgs (substring := true) in
@[grind =] theorem my_add_zero (x : Nat) : x + 0 = x := Nat.add_zero x

/-- error: `@[grind →] theorem my_left` failed to find patterns in the antecedents -/
#guard_msgs (substring := true) in
@[grind →] theorem my_left (h : p ∧ q) : p := h.left

def trip (x : Nat) : Nat := 3 * x

-- A bare `@[grind]` can pick a pattern that never fires: here the
-- conclusion `0 < trip x` is normalised to `1 ≤ trip x`, and `grind`
-- fails on a goal the lemma would close.
#guard_msgs (drop info) in
@[grind] theorem trip_pos {x : Nat} (h : 0 < x) : 0 < trip x := by
  unfold trip; omega

example (a : Nat) (h : 0 < a) : 0 < trip a := by
  fail_if_success grind
  exact trip_pos h

end Attributes

-- `grind_pattern` with constraints (the command's own docstring example).
opaque f : Nat → Nat
axiom fMono : x ≤ y → f x ≤ f y

grind_pattern fMono => f x, f y where
  guard x ≤ y
  x =/= y

example : f b = f c → a ≤ f a → f (f a) ≤ f (f (f a)) := by
  grind

opaque g : Nat → Nat
axiom gMono : x ≤ y → g x ≤ g y

grind_pattern gMono => g x, g y where
  guard x ≤ y
  x =/= y
  depth x < 8

/-! ### § Common Gotchas -/

-- `b && false = false` parses as `b && (false = false)`, coerced back to `Bool`.
example (b : Bool) : (b && false = false) = ((b && decide (false = false)) = true) := rfl

example (b : Bool) : (b && false) = false := by
  grind

/-! ### § Interactive Mode -/

def h1 (n : Nat) : Nat := n + 1

@[grind =] theorem h1_def (n : Nat) : h1 n = n + 1 := rfl

#guard_msgs (drop info, drop trace) in
example : h1 0 = 1 := by
  grind =>
    show_state
    instantiate

-- The debugging loop, `try`-guarded (`try t` is `first (t) (skip)`).
#guard_msgs (drop info, drop trace) in
example : h1 0 = 1 := by
  grind =>
    show_state
    try show_asserted
    try show_cases
    try cases_next
    instantiate
    try finish

-- A goal `grind` closes on entry leaves nothing for the first command.
example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  fail_if_success grind =>
    show_state
  grind

-- A local hypothesis is a local theorem: plain `instantiate` uses it ...
example (k : Nat → Nat) (hk : ∀ n, k n = n + 1) : k 0 = 1 := by
  grind =>
    instantiate

-- ... but `instantiate [hk]` does not resolve a local by name ...
/-- error: Unknown constant `hk` -/
#guard_msgs in
example (k : Nat → Nat) (hk : ∀ n, k n = n + 1) : k 0 = 1 := by
  grind =>
    instantiate only [hk]

-- ... while the anchor that `show_local_thms` prints does.
/-- trace: [thms] Local theorems
  [thm] #0c1c := ∀ (n : Nat), k n = n + 1 -/
#guard_msgs in
example (k : Nat → Nat) (hk : ∀ n, k n = n + 1) : k 0 = 1 := by
  grind =>
    show_local_thms
    instantiate [#0c1c]

-- An anchor hashes the expression (here the local theorem's type): renaming
-- `k` to `k2` changes it.
/-- trace: [thms] Local theorems
  [thm] #cbee := ∀ (n : Nat), k2 n = n + 1 -/
#guard_msgs in
example (k2 : Nat → Nat) (hk : ∀ n, k2 n = n + 1) : k2 0 = 1 := by
  grind =>
    show_local_thms
    instantiate

-- `grind?` suggests an anchor-restricted call and an anchor-free one; both check.
/-- info: Try these:
  [apply] grind only [#0c1c]
  [apply] grind only
  [apply] grind => instantiate only [#0c1c] -/
#guard_msgs in
example (k : Nat → Nat) (hk : ∀ n, k n = n + 1) (_hz : ∀ n, k n ≠ 0) : k 0 = 1 := by
  grind?

example (k : Nat → Nat) (hk : ∀ n, k n = n + 1) (_hz : ∀ n, k n ≠ 0) : k 0 = 1 := by
  grind only [#0c1c]

example (k : Nat → Nat) (hk : ∀ n, k n = n + 1) (_hz : ∀ n, k n ≠ 0) : k 0 = 1 := by
  grind only

/-! ### § Known Limitations -/

-- `native_decide` needs a closed goal; after `intro x` it fails.
example : ∀ x : BitVec 64, (x &&& 0) = 0 := by
  intro x
  fail_if_success native_decide
  simp

example : ∀ x : BitVec 64, (x &&& 0) = 0 := by
  intro x
  bv_decide

/-! ### § Suggestions and Locals -/

example (a b : Nat) (h : a = b) : b = a := by
  grind +locals

-- `+locals` harvests definitions from the current file: an untagged
-- definition is out of reach for plain `grind` ...
def dblLocal (x : Nat) : Nat := x + x

example (a : Nat) : dblLocal a = 2 * a := by
  fail_if_success grind
  grind +locals

-- ... `grind? +locals` minimizes to an explicit call without the flag ...
/-- info: Try these:
  [apply] grind only [dblLocal]
  [apply] grind => instantiate only [dblLocal] -/
#guard_msgs in
example (a : Nat) : dblLocal a = 2 * a := by
  grind? +locals

example (a : Nat) : dblLocal a = 2 * a := by
  grind only [dblLocal]

-- ... while bare `grind?` drops the pool and can only suggest `sorry`.
/-- info: Try this:
  [apply] grind => sorry
---
warning: declaration uses `sorry` -/
#guard_msgs in
example (a : Nat) : dblLocal a = 2 * a := by
  grind?

-- `+suggestions` needs a library-suggestions engine.
example (a b : Nat) (h : a = b) : b = a := by
  fail_if_success grind +suggestions
  grind

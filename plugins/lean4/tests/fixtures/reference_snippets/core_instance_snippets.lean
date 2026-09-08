/-!
Core-Lean evidence (no Mathlib) for the rule SKILL.md § Type Class Patterns
states: a plain `have`/`let` of a class-typed local registers it as an instance
for the rest of the proof, so a DOWNSTREAM consumer synthesizes it; `haveI` /
`letI` differ only by inlining the value into the term.

Run by the `lean-integration` workflow with the `lean_file_gate` fixture's pinned
toolchain (no Mathlib needed):

    cd plugins/lean4/tests/fixtures/lean_file_gate
    lean ../reference_snippets/core_instance_snippets.lean

Every negative control is a `#guard_msgs` block: the file stops elaborating if a
documented failure stops failing, or its message drifts.
-/

class Marker (α : Type) where
  tag : Nat

/-- A consumer that needs the instance: elaborating `useTag Nat` is the test. -/
def useTag (α : Type) [Marker α] : Nat := Marker.tag α

-- ✅ `have` registers the instance; the consumer BELOW it synthesizes it.
theorem have_registers_instance : True := by
  have : Marker Nat := ⟨7⟩
  have _consumer : useTag Nat = useTag Nat := rfl
  trivial

-- ✅ `let` registers it too, and keeps the value visible (so `rfl` sees `7`).
theorem let_registers_instance : True := by
  let _inst : Marker Nat := ⟨7⟩
  have _consumer : useTag Nat = 7 := rfl
  trivial

-- ✅ Term mode, both keywords.
example : True :=
  have : Marker Nat := ⟨7⟩
  have _consumer : 0 ≤ useTag Nat := Nat.zero_le _
  trivial

example : True :=
  let _inst : Marker Nat := ⟨7⟩
  have _consumer : useTag Nat = 7 := rfl
  trivial

-- ✅ Control: `haveI` behaves the same for the consumer (only inlining differs).
example : True := by
  haveI : Marker Nat := ⟨7⟩
  have _consumer : 0 ≤ useTag Nat := Nat.zero_le _
  trivial

-- ❌ Negative control: with no instance in scope the consumer fails to elaborate.
/--
error: failed to synthesize instance of type class
  Marker Nat

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : True := by
  have _consumer : 0 ≤ useTag Nat := Nat.zero_le _
  trivial

-- ❌ Negative control: the circular recipe. `have : C := inferInstance` re-runs
-- the search that just failed; it supplies nothing.
/--
error: failed to synthesize instance of type class
  Marker Nat

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : True := by
  have : Marker Nat := inferInstance
  trivial

-- ❌ Negative control: the probe mistake recorded in PR #200. The STATEMENT is
-- elaborated before the proof body, so an instance supplied inside the proof
-- cannot serve a consumer that sits in the statement.
/--
error: failed to synthesize instance of type class
  Marker Nat

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : useTag Nat = 7 := by
  have : Marker Nat := ⟨7⟩
  rfl

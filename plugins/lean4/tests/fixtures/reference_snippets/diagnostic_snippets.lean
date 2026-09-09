/-!
Core-Lean evidence (no Mathlib) for three diagnostic entries (#167, #168, #169).
Run by the `lean-integration` workflow with the `lean_file_gate` fixture's pinned
toolchain (messages pinned to Lean 4.33.1; a toolchain bump updates them
deliberately):

    cd plugins/lean4/tests/fixtures/lean_file_gate
    lean ../reference_snippets/diagnostic_snippets.lean

Every documented failure is a `#guard_msgs` block (or, for the one parse
error, a separate must-fail file checked by `run_core_snippets.sh`), so the
check breaks if a failure stops failing or its message drifts; every documented
repair is elaborated as written.
-/

/-! ### #167 — a bare `Type` result annotation means `Type 0` -/

universe u

def WrappedType (α : Type u) : Type u := α

-- ❌ The constraint propagates backwards: the error is reported at the ARGUMENT.
/--
error: Application type mismatch: The argument
  α
has type
  Type u
of sort `Type (u + 1)` but is expected to have type
  Type
of sort `Type 1` in the application
  WrappedType α
-/
#guard_msgs in
example (α : Type u) : Type := WrappedType α

-- ❌ An explicit universe argument cannot override the annotation; the error moves
-- to the application.
/--
error: Type mismatch
  WrappedType α
has type
  Type u
of sort `Type (u + 1)` but is expected to have type
  Type
of sort `Type 1`
-/
#guard_msgs in
example (α : Type u) : Type := WrappedType.{u} α

-- ✅ Let the result universe be inferred …
example (α : Type u) : Type _ := WrappedType α
-- ✅ … or state the universe relationship explicitly.
example (α : Type u) : Type u := WrappedType α

/-! ### #168 — `rintro … rfl` can eliminate the OUTER variable -/

-- ❌ After `rintro m' rfl` the outer `m` is gone and `hP` speaks about `m'`.
/--
error: Unknown identifier `m`
-/
#guard_msgs in
example (m : Nat) (P : Nat → Prop) (hP : P m) : ∀ m', m' = m → P m' := by
  rintro m' rfl
  show P m
  exact hP

-- ✅ Keep the context intact: introduce the equation and rewrite with it.
example (m : Nat) (P : Nat → Prop) (hP : P m) : ∀ m', m' = m → P m' := by
  intro m' h
  rw [h]
  show P m
  exact hP

-- ✅ Or substitute the INTRODUCED variable by name, preserving the outer `m`.
example (m : Nat) (P : Nat → Prop) (hP : P m) : ∀ m', m' = m → P m' := by
  intro m' h
  subst m'
  show P m
  exact hP

/-! ### #169 — `omit [...] in` must precede the docstring -/

section
variable [Inhabited Nat]

-- ❌ The failing form is a PARSE error, which `#guard_msgs` cannot capture, so it
-- lives in `diagnostic_omit_negative.lean`; `run_core_snippets.sh` requires that
-- file to FAIL with `unexpected token 'omit'` reported at the docstring position.

-- ✅ `omit … in` first, then the docstring, then the declaration.
omit [Inhabited Nat] in
/-- Doc comment after omit. -/
theorem good : True := trivial

end

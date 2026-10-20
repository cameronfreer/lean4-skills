/-!
Core-Lean evidence (no Mathlib, no Verso package) for `references/verso-docs.md`
(#181): the Verso docstring roles built into Lean. Run by the
`lean-integration` workflow with the `lean_file_gate` fixture's pinned
toolchain (messages pinned to Lean 4.33.1), via `run_core_snippets.sh`:

    cd plugins/lean4/tests/fixtures/lean_file_gate
    lean ../reference_snippets/verso_snippets.lean

Every documented docstring is elaborated with `doc.verso` on; the documented
diagnostics are `#guard_msgs` blocks.
-/

set_option doc.verso true

def transpose (xs : List Nat) : List Nat := xs.reverse

-- § Examples (the documented docstring). With `doc.verso` on, `/-! … -/`
-- module docs are Verso too, so section markers here are plain comments.

/--
For {given (type := "Nat")}`n`, returns {lean}`transpose [n]`.
Use {lean}`#[n]` for a rank-1 shape literal.
Prefer {lit}`x[i,j]` when writing pseudo-indexing.
-/
def shape (n : Nat) : List Nat := transpose [n]

-- § Role Priority: `{name}` takes declarations and in-scope variables ...
/-- Doubles {name}`n`; {name}`Nat` is an inductive type, so it resolves. -/
def twice (n : Nat) : Nat := n + n

-- ... but not a namespace that is not also a declaration.
namespace OnlyNs
def inner : Nat := 1
end OnlyNs

/-- error: Unknown constant `OnlyNs` -/
#guard_msgs in
/-- Lives in {name}`OnlyNs`. -/
def nsName : Nat := 0

-- Use `{lit}` for a namespace-only label and `{module}` for a module.
/-- Lives in {lit}`OnlyNs`; see {module}`Init.Prelude`. -/
def nsLit : Nat := 0

-- `{given}` can also carry the type inline.
/-- For {given}`xs : List Nat`, {name}`transpose` reverses {lean}`xs`. -/
def shape2 : Nat := 0

-- Double backticks are accepted too (needed when the code holds a backtick).
/-- Returns {name}``transpose``; shows {lit}``a`b`` with an inner backtick. -/
def shape3 : Nat := 0

-- Other built-in roles.
/-- Use {tactic}`simp`, the {attr}`simp` attribute and {option}`pp.all`. -/
def shape4 : Nat := 0

-- § Fixing Common Diagnostics

-- An untyped `{given}` leaves the variable's type unknown.
/-- error: unresolved metavariable in `given` (type of variable `n`) -/
#guard_msgs (substring := true) in
/-- For {given}`n`, {lean}`#[n]` is a rank-1 shape. -/
def untyped : Nat := 0

-- A bare code element is a warning with role suggestions.
/-- warning: Code element could be more specific. -/
#guard_msgs (substring := true) in
/-- Calls `transpose`. -/
def bare : Nat := 0

-- An unknown role is an error.
/-- error: Unknown role `frobnicate` -/
#guard_msgs in
/-- Uses {frobnicate}`transpose`. -/
def unknownRole : Nat := 0

-- `{lean}` elaborates its contents: an undeclared variable is an error.
/-- error: Unknown identifier `m` -/
#guard_msgs in
/-- Uses {lean}`m + 1`. -/
def undeclared : Nat := 0

import Lean.LibrarySuggestions.Default

/-!
Core-Lean evidence for `references/grind-tactic.md` § Suggestions and Locals
(#181): with Lean's built-in library-suggestions engine imported,
`grind +suggestions` runs (`grind_snippets.lean` pins that it fails without
one). Run by `run_core_snippets.sh` with the `lean_file_gate` toolchain.
-/

example (a b : Nat) (h : a = b) : b = a := by
  grind +suggestions

example (a b : Nat) (h : a = b) : b = a := by
  grind +suggestions +locals

-- The staged workflow on a goal that needs discovery: an untagged definition
-- from this file. Plain `grind` fails; `grind? +suggestions +locals` finds it
-- and suggests an explicit call that needs neither flag.
def dblSugg (x : Nat) : Nat := x + x

example (a : Nat) : dblSugg a = 2 * a := by
  fail_if_success grind
  grind +suggestions +locals

/-- info: Try these:
  [apply] grind only [dblSugg]
  [apply] grind => instantiate only [dblSugg] -/
#guard_msgs in
example (a : Nat) : dblSugg a = 2 * a := by
  grind? +suggestions +locals

example (a : Nat) : dblSugg a = 2 * a := by
  grind only [dblSugg]

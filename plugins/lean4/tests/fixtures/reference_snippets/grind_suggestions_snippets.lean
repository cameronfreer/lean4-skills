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

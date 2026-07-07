-- Fixture: one used theorem + eight dead decls spanning the expanded
-- keyword classes (axiom, constant, structure, and the four
-- modifier-prefixed def forms). Locks in the Step 1 extraction regex.
theorem used_thm : True := trivial
axiom dead_axiom : False
constant dead_constant : Nat
noncomputable def dead_noncomp : Nat := 0
unsafe def dead_unsafe : Nat := 0
partial def dead_partial : Nat := 0
nonrec def dead_nonrec : Nat := 0
structure DeadStruct where
  x : Nat
def uses_thm := used_thm
-- uses_thm is referenced here so it counts as used: uses_thm

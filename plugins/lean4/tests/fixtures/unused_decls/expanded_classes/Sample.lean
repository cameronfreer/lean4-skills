-- Fixture: two used decls (used_thm + uses_thm, the latter via a real
-- #check) and nine dead decls spanning the expanded keyword classes
-- (axiom, constant, structure, class, inductive, and the four
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
class DeadClass where
  y : Nat
inductive DeadInductive where
  | one
def uses_thm := used_thm
#check uses_thm

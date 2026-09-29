import Lean
open Lean
-- Fixture (#185 review): interpolation is decided by the token before the
-- string, not by adjacency — `s! "…"`, `s! /- c -/ "…"` and the core
-- `throwError "…"` all interpolate, so `live` is used; `dead` is not.
def live : Nat := 1
#eval s! "value: {live}"
#eval s! /- separator -/ "value: {live}"
def act : CoreM Unit := throwError "value: {live}"
#check act
def dead : Nat := 0

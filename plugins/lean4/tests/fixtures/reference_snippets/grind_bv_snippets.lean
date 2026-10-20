import Std.Tactic.BVDecide

/-!
Core-Lean evidence for `references/grind-tactic.md` § Interactive Mode,
"Bit-Blasting Inside `grind`" (#212). Needs Lean `v4.34.0`+: on `v4.33.1`,
`bv_decide` is not a `grind` command (a parse error). `run_core_snippets.sh`
elaborates this file only when the toolchain is `v4.34.0` or newer; checked
locally on `v4.34.0` and `v4.35.0`.
-/

opaque f : BitVec 8 → BitVec 8

-- Standalone `bv_decide` treats `f x` and `f y` as unrelated atoms ...
example (x y : BitVec 8) (h : x = y) : f x ^^^ f y = 0 := by
  fail_if_success bv_decide
  grind =>
    bv_decide

-- ... the documented example: grind's congruence closure equates them first.
example (x y : BitVec 8) (h : x = y) : f x ^^^ f y = 0 := by
  grind =>
    bv_decide

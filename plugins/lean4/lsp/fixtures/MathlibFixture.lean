import Mathlib.Data.Nat.Basic

namespace NativeLspFixture

/-- A complete proof using a theorem supplied by Mathlib's narrow Nat import. -/
theorem div_right_comm_mathlib (a b c : ℕ) : a / b / c = a / c / b := by
  exact Nat.div_right_comm a b c

/-- The deliberate hole provides an LSP goal and an expected sorry diagnostic. -/
theorem add_comm_goal (a b : ℕ) : a + b = b + a := by
  sorry

#check Nat.div_right_comm
#check NativeLspFixture.div_right_comm_mathlib

end NativeLspFixture

namespace Pairs

/-- Proved, no axioms. -/
theorem add_zero' (n : Nat) : n + 0 = n := rfl

/-- Left as sorry: the pair calls it `partial`. -/
theorem mul_comm' (a b : Nat) : a * b = b * a := by
  sorry

/-- A custom axiom. -/
axiom choice_like : ∀ n : Nat, ∃ m : Nat, n < m

theorem exists_gt (n : Nat) : ∃ m : Nat, n < m := choice_like n

end Pairs

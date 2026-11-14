import Mathlib.Data.Nat.GCD.Basic

/-! Computation induction in the second argument of Euclid's algorithm.
The recursive hypothesis is available only in the nonzero branch. No new gcd
implementation is required. Source: FDSA, July 27, 2026, section 1.4.1.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Arithmetic.Euclid

/-- The exact branch-sensitive computation-induction rule stated in FDSA. -/
theorem induction {P : Nat → Nat → Prop}
    (step : ∀ m n, (n ≠ 0 → P n (m % n)) → P m n)
    (m n : Nat) : P m n := by
  induction n using Nat.strong_induction_on generalizing m with
  | h n ih =>
      apply step m n
      intro hn
      exact ih (m % n) (Nat.mod_lt m (Nat.pos_of_ne_zero hn)) n

/-- Lean's standard gcd has the source's second-argument recursive equation. -/
theorem gcd_equation (m n : Nat) :
    Nat.gcd m n = if n = 0 then m else Nat.gcd n (m % n) := by
  by_cases hn : n = 0
  · simp [hn]
  · simp only [ite_eq_right hn]
    rw [Nat.gcd_comm, Nat.gcd_rec, Nat.gcd_comm (m % n) n]

end Arithmetic.Euclid

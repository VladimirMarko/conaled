/-!
# Fixed connected specializations of the natural-polynomial normal form

This body requires the parent NormalFormDraft148 namespace and the ordinary
Mathlib.Algebra.Polynomial.Degree.Lemmas import. The query assembly records
those inputs explicitly and includes each proof body once.
-/

namespace Resources.PolynomialTime.NormalFormDraft148.Cases

open Polynomial

theorem zero_exponent : exponent (0 : Polynomial Nat) = 0 := by
  simp [exponent]

theorem constant_seven_exponent : exponent (C 7 : Polynomial Nat) = 7 := by
  simp [exponent]

theorem indeterminate_exponent : exponent (X : Polynomial Nat) = 2 := by
  simp [exponent]

noncomputable def mixed : Polynomial Nat := C 2 * X ^ 2 + C 3 * X + C 5

theorem mixed_degree : mixed.natDegree = 2 := by
  unfold mixed
  rw [natDegree_add_C]
  have quadratic : (C 2 * X ^ 2 : Polynomial Nat).natDegree = 2 := by
    rw [natDegree_C_mul (by decide), natDegree_X_pow]
  have linear : (C 3 * X : Polynomial Nat).natDegree = 1 := by
    rw [natDegree_C_mul (by decide), natDegree_X]
  rw [natDegree_add_eq_left_of_natDegree_lt (by rw [linear, quadratic]; decide), quadratic]

theorem mixed_values : mixed.eval 0 = 5 ∧ mixed.eval 1 = 10 ∧ mixed.eval 2 = 19 := by
  simp [mixed]

theorem mixed_exponent : exponent mixed = 12 := by
  simp [exponent, mixed_degree, mixed_values.2.1]

theorem zero_bound (N : Nat) : 0 ≤ N ^ 0 + 0 := by
  simpa only [zero_exponent, Polynomial.eval_zero] using
    eval_le_power_add_exponent (0 : Polynomial Nat) N

theorem constant_seven_bound (N : Nat) : 7 ≤ N ^ 7 + 7 := by
  simpa only [constant_seven_exponent, Polynomial.eval_C] using
    eval_le_power_add_exponent (C 7 : Polynomial Nat) N

theorem indeterminate_bound (N : Nat) : N ≤ N ^ 2 + 2 := by
  simpa only [indeterminate_exponent, Polynomial.eval_X] using
    eval_le_power_add_exponent (X : Polynomial Nat) N

theorem mixed_bound (N : Nat) : mixed.eval N ≤ N ^ 12 + 12 := by
  simpa only [mixed_exponent] using eval_le_power_add_exponent mixed N

end Resources.PolynomialTime.NormalFormDraft148.Cases

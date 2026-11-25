import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option warningAsError true

/-!
# Fixed powers bounding natural polynomials

A proof-side exponent is fixed from a natural polynomial before its
argument. The bound retains the zero and one boundaries.
-/

/- Complete preserved component: normal_core. -/
section

namespace Resources.PolynomialTime.NormalForm

open Polynomial

/-- The fixed coefficient sum and degree determine the exponent. -/
def exponent (p : Polynomial Nat) : Nat := p.natDegree + p.eval 1

/-- Natural-coefficient evaluation is monotone on natural inputs. -/
theorem eval_monotone (p : Polynomial Nat) : Monotone p.eval := by
  intro a b hab
  change p.eval a ≤ p.eval b
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum fun i _ =>
    Nat.mul_le_mul_left (p.coeff i) (pow_le_pow_left' hab i)

/-- For input at least one, each monomial is bounded at the total degree. -/
theorem eval_le_coefficient_sum_mul_power (p : Polynomial Nat) (N : Nat)
    (positive : 1 ≤ N) : p.eval N ≤ p.eval 1 * N ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range N, Polynomial.eval_eq_sum_range 1]
  simp only [one_pow, mul_one]
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  apply Nat.mul_le_mul_left
  exact pow_le_pow_right' positive (Nat.le_of_lt_succ (Finset.mem_range.mp hi))

/-- The zero-size input is covered without a positive-input assumption. -/
theorem eval_zero_le_exponent (p : Polynomial Nat) : p.eval 0 ≤ exponent p :=
  (eval_monotone p (Nat.zero_le 1)).trans (Nat.le_add_left _ _)

/-- The one-size input is covered by the fixed additive constant. -/
theorem eval_one_le_exponent (p : Polynomial Nat) : p.eval 1 ≤ exponent p :=
  Nat.le_add_left _ _

/-- Every natural input is bounded by one fixed power plus its exponent. -/
theorem eval_le_power_add_exponent (p : Polynomial Nat) (N : Nat) :
    p.eval N ≤ N ^ exponent p + exponent p := by
  by_cases zero : N = 0
  · subst N
    exact (eval_zero_le_exponent p).trans (Nat.le_add_left _ _)
  by_cases one : N = 1
  · subst N
    exact (eval_one_le_exponent p).trans (Nat.le_add_left _ _)
  have two : 2 ≤ N := by omega
  have coefficient_sum : p.eval 1 ≤ N ^ p.eval 1 :=
    (p.eval 1).lt_two_pow_self.le.trans (pow_le_pow_left' two (p.eval 1))
  calc
    p.eval N ≤ p.eval 1 * N ^ p.natDegree :=
      eval_le_coefficient_sum_mul_power p N (by omega)
    _ ≤ N ^ p.eval 1 * N ^ p.natDegree :=
      Nat.mul_le_mul_right _ coefficient_sum
    _ = N ^ exponent p := by rw [← pow_add, exponent, Nat.add_comm]
    _ ≤ N ^ exponent p + exponent p := Nat.le_add_right _ _

/-- The existential order fixes the exponent before every input length. -/
theorem exists_power_add_bound (p : Polynomial Nat) :
    ∃ k : Nat, ∀ N : Nat, p.eval N ≤ N ^ k + k :=
  ⟨exponent p, eval_le_power_add_exponent p⟩

end Resources.PolynomialTime.NormalForm

end

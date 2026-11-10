import SquareKit.FiniteSums
import Examples.JetScan
import Mathlib.Tactic.NormNum

/-!
# Evaluate geometric derivatives through the existing scan backend

The input polynomial is the actual finite sum of powers of X, and its formal
derivative supplies the coefficients. Prepared plans have one more slot than
the derivative's natural degree, including for the zero polynomial. These are
value and representation contracts; no scan-work or physical-cost claim is made.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.GeometricSumScan

open Finset Applications.Parallel
open scoped BigOperators

variable {R : Type} [CommRing R]

/-- Every adequate certified scan plan evaluates the actual derivative. -/
theorem shaped_derivative_evaluation (plan : ScanPlan) (n : Nat)
    (h : (Polynomial.derivative
      (∑ k ∈ range (n + 1), (Polynomial.X : Polynomial R) ^ k)).natDegree <
        plan.shape.size) (x : R) :
    evaluatePolynomial plan
        (JetScan.coefficients plan.shape
          (Polynomial.derivative
            (∑ k ∈ range (n + 1), (Polynomial.X : Polynomial R) ^ k)) 0) x =
      ∑ j ∈ range n, (j + 1 : R) * x ^ j := by
  rw [JetScan.shaped_evaluation_correct plan _ h x]
  exact SquareKit.FiniteSums.derivative_geom_eval x n

/-- The weighted sum is the input times that genuine scan evaluation. -/
theorem shaped_weighted_evaluation (plan : ScanPlan) (n : Nat)
    (h : (Polynomial.derivative
      (∑ k ∈ range (n + 1), (Polynomial.X : Polynomial R) ^ k)).natDegree <
        plan.shape.size) (x : R) :
    x * evaluatePolynomial plan
        (JetScan.coefficients plan.shape
          (Polynomial.derivative
            (∑ k ∈ range (n + 1), (Polynomial.X : Polynomial R) ^ k)) 0) x =
      ∑ k ∈ Ico 1 (n + 1), (k : R) * x ^ k := by
  rw [JetScan.shaped_evaluation_correct plan _ h x]
  exact (SquareKit.FiniteSums.weighted_derivative x n).symm

/-- Preparation supplies the strict shape premise, even at degree zero. -/
theorem prepared_derivative_adequate (n : Nat) :
    let q : Polynomial R := Polynomial.derivative
      (∑ k ∈ range (n + 1), (Polynomial.X : Polynomial R) ^ k);
    q.natDegree < (JetScan.prepare q).plan.shape.size := by
  dsimp only [JetScan.prepare]
  rw [JetScan.planForLength_size]
  exact Nat.lt_succ_self _

/-- Run the existing evaluator on its actual prepared derivative coefficients. -/
theorem prepared_derivative_evaluation (n : Nat) (x : R) :
    let q : Polynomial R := Polynomial.derivative
      (∑ k ∈ range (n + 1), (Polynomial.X : Polynomial R) ^ k);
    evaluatePolynomial (JetScan.prepare q).plan (JetScan.prepare q).data x =
      ∑ j ∈ range n, (j + 1 : R) * x ^ j := by
  let q : Polynomial R := Polynomial.derivative
    (∑ k ∈ range (n + 1), (Polynomial.X : Polynomial R) ^ k)
  change evaluatePolynomial (JetScan.planForLength (q.natDegree + 1))
    (JetScan.coefficients (JetScan.planForLength (q.natDegree + 1)).shape q 0) x = _
  rw [JetScan.shaped_evaluation_correct _ q
    (by simpa only [JetScan.planForLength_size] using Nat.lt_succ_self q.natDegree) x]
  exact SquareKit.FiniteSums.derivative_geom_eval x n

theorem prepared_weighted_evaluation (n : Nat) (x : R) :
    let q : Polynomial R := Polynomial.derivative
      (∑ k ∈ range (n + 1), (Polynomial.X : Polynomial R) ^ k);
    x * evaluatePolynomial (JetScan.prepare q).plan (JetScan.prepare q).data x =
      ∑ k ∈ Ico 1 (n + 1), (k : R) * x ^ k := by
  let q : Polynomial R := Polynomial.derivative
    (∑ k ∈ range (n + 1), (Polynomial.X : Polynomial R) ^ k)
  change x * evaluatePolynomial (JetScan.prepare q).plan (JetScan.prepare q).data x = _
  have hv := prepared_derivative_evaluation (R := R) n x
  change evaluatePolynomial (JetScan.prepare q).plan (JetScan.prepare q).data x = _ at hv
  rw [hv, ← SquareKit.FiniteSums.derivative_geom_eval x n]
  exact (SquareKit.FiniteSums.weighted_derivative x n).symm

/-- The derivative of 1+X+X²+X³ is 1+2X+3X², whose value at two is seventeen. -/
theorem geometric_three_derivative_at_two :
    let q : Polynomial ℚ := Polynomial.derivative
      (∑ k ∈ range 4, (Polynomial.X : Polynomial ℚ) ^ k);
    evaluatePolynomial (JetScan.prepare q).plan (JetScan.prepare q).data (2 : ℚ) =
      17 := by
  calc
    _ = ∑ j ∈ range 3, (j + 1 : ℚ) * (2 : ℚ) ^ j :=
      prepared_derivative_evaluation 3 2
    _ = 17 := by norm_num [Finset.sum_range_succ]

/-- The canonical source value consumes the universal weighted quotient identity. -/
theorem geometric_three_weighted_at_two :
    (∑ k ∈ Ico (1 : Nat) 4, (k : ℚ) * (2 : ℚ) ^ k) = 34 := by
  have h := SquareKit.FiniteSums.weighted_geom_closed (2 : ℚ) 3 (by norm_num)
  norm_num at h
  exact h

/-- The existing scan independently supplies the weighted value through its derivative. -/
theorem geometric_three_scan_weighted_at_two :
    let q : Polynomial ℚ := Polynomial.derivative
      (∑ k ∈ range 4, (Polynomial.X : Polynomial ℚ) ^ k);
    ((2 : ℚ) * evaluatePolynomial (JetScan.prepare q).plan
        (JetScan.prepare q).data 2 = ∑ k ∈ Ico (1 : Nat) 4, (k : ℚ) * (2 : ℚ) ^ k) ∧
      (2 : ℚ) * evaluatePolynomial (JetScan.prepare q).plan
        (JetScan.prepare q).data 2 = 34 := by
  let q : Polynomial ℚ := Polynomial.derivative
    (∑ k ∈ range 4, (Polynomial.X : Polynomial ℚ) ^ k)
  have hd : evaluatePolynomial (JetScan.prepare q).plan (JetScan.prepare q).data
      (2 : ℚ) = 17 := geometric_three_derivative_at_two
  constructor
  · exact prepared_weighted_evaluation 3 (2 : ℚ)
  · change (2 : ℚ) * evaluatePolynomial (JetScan.prepare q).plan
      (JetScan.prepare q).data 2 = 34
    rw [hd]
    norm_num

/-- A constant source polynomial has zero derivative at every rational input. -/
theorem geometric_zero_derivative (x : ℚ) :
    let q : Polynomial ℚ := Polynomial.derivative
      (∑ k ∈ range 1, (Polynomial.X : Polynomial ℚ) ^ k);
    evaluatePolynomial (JetScan.prepare q).plan (JetScan.prepare q).data x = 0 := by
  simpa using prepared_derivative_evaluation (R := ℚ) 0 x

/-- The zero derivative still has natural degree zero and is prepared with one slot. -/
theorem geometric_zero_prepared_size :
    let q : Polynomial ℚ := Polynomial.derivative
      (∑ k ∈ range 1, (Polynomial.X : Polynomial ℚ) ^ k);
    (JetScan.prepare q).plan.shape.size = 1 := by
  simp [JetScan.prepare, JetScan.planForLength_size]

/-- An empty shape cannot satisfy the strict degree condition. -/
theorem geometric_zero_empty_shape_inadequate :
    ¬ (Polynomial.derivative
      (∑ k ∈ range 1, (Polynomial.X : Polynomial ℚ) ^ k)).natDegree <
        ScanPlan.empty.shape.size := by
  change ¬ _ < 0
  exact Nat.not_lt_zero _

/-- At zero, every nonconstant finite geometric polynomial has derivative one. -/
theorem geometric_successor_derivative_at_zero (n : Nat) :
    let q : Polynomial ℚ := Polynomial.derivative
      (∑ k ∈ range (n + 1 + 1), (Polynomial.X : Polynomial ℚ) ^ k);
    evaluatePolynomial (JetScan.prepare q).plan (JetScan.prepare q).data (0 : ℚ) =
      1 := by
  calc
    _ = ∑ j ∈ range (n + 1), (j + 1 : ℚ) * (0 : ℚ) ^ j :=
      prepared_derivative_evaluation (n + 1) 0
    _ = 1 := by
      rw [Finset.sum_range_succ']
      simp

/-- Evaluation at one uses the derivative identity without an invalid quotient. -/
theorem geometric_derivative_at_one (n : Nat) :
    let q : Polynomial ℚ := Polynomial.derivative
      (∑ k ∈ range (n + 1), (Polynomial.X : Polynomial ℚ) ^ k);
    evaluatePolynomial (JetScan.prepare q).plan (JetScan.prepare q).data (1 : ℚ) =
      ∑ k ∈ Ico 1 (n + 1), (k : ℚ) := by
  simpa using prepared_weighted_evaluation (R := ℚ) n 1

/-- The zero-index polynomial and all three scalar expressions retain their endpoints. -/
theorem geometric_zero_endpoints (x : ℚ) :
    (∑ k ∈ range 1, (Polynomial.X : Polynomial ℚ) ^ k) = 1 ∧
      Polynomial.derivative (∑ k ∈ range 1, (Polynomial.X : Polynomial ℚ) ^ k) = 0 ∧
      (∑ k ∈ range 1, x ^ k) = 1 ∧
      (∑ j ∈ range 0, (j + 1 : ℚ) * x ^ j) = 0 ∧
      (∑ k ∈ Ico (1 : Nat) 1, (k : ℚ) * x ^ k) = 0 := by
  have hp : (∑ k ∈ range 1, (Polynomial.X : Polynomial ℚ) ^ k) = 1 := by simp
  have hd : Polynomial.derivative
      (∑ k ∈ range 1, (Polynomial.X : Polynomial ℚ) ^ k) = 0 := by
    rw [hp, Polynomial.derivative_one]
  refine ⟨hp, hd, ?_, ?_, ?_⟩
  · have h := SquareKit.FiniteSums.geom_eval x 0
    rw [hp] at h
    simpa only [Polynomial.eval_one] using h.symm
  · have h := SquareKit.FiniteSums.derivative_geom_eval x 0
    rw [hd] at h
    simpa only [Polynomial.eval_zero] using h.symm
  · rw [SquareKit.FiniteSums.weighted_derivative x 0, hd, Polynomial.eval_zero, mul_zero]

/-- At input zero the constant geometric term remains, while weighting removes it. -/
theorem geometric_at_zero (n : Nat) :
    (∑ k ∈ range (n + 1), (0 : ℚ) ^ k) = 1 ∧
      (∑ k ∈ Ico 1 (n + 1), (k : ℚ) * (0 : ℚ) ^ k) = 0 := by
  constructor
  · rw [← SquareKit.FiniteSums.geom_eval]
    simp [Finset.sum_range_succ', Polynomial.eval_finsetSum]
  · rw [SquareKit.FiniteSums.weighted_derivative, zero_mul]

/-- At input one the two derivative-related sums equal the positive triangular sum. -/
theorem geometric_at_one (n : Nat) :
    (∑ k ∈ range (n + 1), (1 : ℚ) ^ k) = (n + 1 : ℚ) ∧
      (∑ j ∈ range n, (j + 1 : ℚ) * (1 : ℚ) ^ j) =
        ((∑ k ∈ Ico 1 (n + 1), k : Nat) : ℚ) ∧
      (∑ k ∈ Ico 1 (n + 1), (k : ℚ) * (1 : ℚ) ^ k) =
        ((∑ k ∈ Ico 1 (n + 1), k : Nat) : ℚ) := by
  have hd : (∑ j ∈ range n, (j + 1 : ℚ) * (1 : ℚ) ^ j) =
      ((∑ k ∈ Ico 1 (n + 1), k : Nat) : ℚ) := by
    have h := SquareKit.FiniteSums.weighted_derivative (1 : ℚ) n
    rw [SquareKit.FiniteSums.derivative_geom_eval] at h
    simpa only [one_pow, mul_one, one_mul, Nat.cast_sum] using h.symm
  refine ⟨?_, hd, ?_⟩
  · rw [← SquareKit.FiniteSums.geom_eval]
    simp
  · rw [SquareKit.FiniteSums.weighted_derivative,
      SquareKit.FiniteSums.derivative_geom_eval, one_mul]
    exact hd

/-- Totalized field division at one cannot replace the excluded quotient premise. -/
theorem geometric_at_one_quotient_obstruction (n : Nat) :
    (1 - (1 : ℚ) ^ (n + 1)) / (1 - (1 : ℚ)) = 0 ∧
      (∑ k ∈ range (n + 1), (1 : ℚ) ^ k) ≠
        (1 - (1 : ℚ) ^ (n + 1)) / (1 - (1 : ℚ)) := by
  constructor
  · norm_num
  · rw [(geometric_at_one n).1]
    norm_num
    positivity

-- Each scaled universal identity is usable at the excluded quotient point.
example (n : Nat) :
    (1 - (1 : ℚ)) * (∑ k ∈ range (n + 1), (1 : ℚ) ^ k) =
      1 - (1 : ℚ) ^ (n + 1) :=
  SquareKit.FiniteSums.geom_scaled 1 n

example (n : Nat) :
    (1 - (1 : ℚ)) ^ 2 * (∑ j ∈ range n, (j + 1 : ℚ) * (1 : ℚ) ^ j) =
      1 - (n + 1 : ℚ) * (1 : ℚ) ^ n + (n : ℚ) * (1 : ℚ) ^ (n + 1) :=
  SquareKit.FiniteSums.derivative_geom_scaled 1 n

example (n : Nat) :
    (1 - (1 : ℚ)) ^ 2 * (∑ k ∈ Ico 1 (n + 1), (k : ℚ) * (1 : ℚ) ^ k) =
      (1 : ℚ) * (1 - (n + 1 : ℚ) * (1 : ℚ) ^ n +
        (n : ℚ) * (1 : ℚ) ^ (n + 1)) :=
  SquareKit.FiniteSums.weighted_geom_scaled 1 n

end Examples.GeometricSumScan

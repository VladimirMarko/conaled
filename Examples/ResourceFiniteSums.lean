import SquareKit.FiniteSums
import Applications.Resources.Growth
import Applications.Resources.ListExecution

/-!
# Finite sums, standard growth, and actual fold observations

The sum and tail examples are mathematical quantities, without an execution-cost
attribution. The fold comparisons separately consume the existing measured
programs and their public value/work theorems. The combining price is fixed;
the model does not price the combiner's internals or construction of the input.

Source accounting and model boundaries: `docs/research/adwh-finite-sums.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.ResourceFiniteSums

open Finset SquareKit.FiniteSums
open scoped BigOperators

universe u v
variable {α : Type u} {β : Type v}

/-- The positive sum uses the standard pointwise finite-sum order theorem. -/
example {f g : Nat → Nat} (n : Nat) (h : ∀ k, k ≤ n → f k ≤ g k) :
    (∑ k ∈ Ico 1 (n + 1), f k) ≤ ∑ k ∈ Ico 1 (n + 1), g k := by
  apply Finset.sum_le_sum
  intro k hk
  exact h k (Nat.lt_succ_iff.mp (Finset.mem_Ico.mp hk).2)

/-- An arbitrary zero term cannot be inserted into the positive interval. -/
example (n : Nat) :
    (∑ _k ∈ Ico 1 (n + 1), (1 : Nat)) = n ∧
      (∑ _k ∈ range (n + 1), (1 : Nat)) = n + 1 := by
  simp

/-- Upper coefficient one and reverse coefficient two both work from zero. -/
theorem triangle_isTheta_square :
    Asymptotics.IsTheta Filter.atTop
      (fun n : Nat => ((∑ k ∈ Ico 1 (n + 1), k : Nat) : ℝ))
      (fun n : Nat => ((n * n : Nat) : ℝ)) := by
  constructor
  · apply Resources.isBigO_of_nat_bound
      (fun n => ∑ k ∈ Ico 1 (n + 1), k) (fun n => n * n) 1 0
    intro n _
    simpa only [Nat.one_mul] using (triangle_bounds n).2
  · apply Resources.isBigO_of_nat_bound
      (fun n => n * n) (fun n => ∑ k ∈ Ico 1 (n + 1), k) 2 0
    intro n _
    exact (triangle_bounds n).1

/-- Upper coefficient one and reverse coefficient six include the empty sum. -/
theorem squares_isTheta_cube :
    Asymptotics.IsTheta Filter.atTop
      (fun n : Nat => ((∑ k ∈ Ico 1 (n + 1), k * k : Nat) : ℝ))
      (fun n : Nat => ((n * n * n : Nat) : ℝ)) := by
  constructor
  · apply Resources.isBigO_of_nat_bound
      (fun n => ∑ k ∈ Ico 1 (n + 1), k * k) (fun n => n * n * n) 1 0
    intro n _
    simpa only [Nat.one_mul] using (squares_bounds n).2
  · apply Resources.isBigO_of_nat_bound
      (fun n => n * n * n) (fun n => ∑ k ∈ Ico 1 (n + 1), k * k) 6 0
    intro n _
    exact (squares_bounds n).1

/-- All-index bounds retain the exact natural polynomial from the source. -/
theorem quadratic_linear_bounds (n : Nat) :
    n * n ≤ 2 * n * n + 3 * n ∧
      2 * n * n + 3 * n ≤ 5 * (n * n) := by
  have h := Nat.le_mul_self n
  constructor <;> nlinarith

theorem quadratic_linear_isTheta_square :
    Asymptotics.IsTheta Filter.atTop
      (fun n : Nat => ((2 * n * n + 3 * n : Nat) : ℝ))
      (fun n : Nat => ((n * n : Nat) : ℝ)) := by
  constructor
  · apply Resources.isBigO_of_nat_bound
      (fun n => 2 * n * n + 3 * n) (fun n => n * n) 5 0
    intro n _
    exact (quadratic_linear_bounds n).2
  · apply Resources.isBigO_of_nat_bound
      (fun n => n * n) (fun n => 2 * n * n + 3 * n) 1 0
    intro n _
    simpa only [Nat.one_mul] using (quadratic_linear_bounds n).1

theorem quadratic_linear_cube_bound (n : Nat) :
    2 * n * n + 3 * n ≤ 5 * (n * n * n) := by
  have hs : n * n ≤ n * n * n := by
    simpa only [Nat.mul_assoc] using
      (Nat.mul_le_mul_left n (Nat.le_mul_self n))
  exact (quadratic_linear_bounds n).2.trans (Nat.mul_le_mul_left 5 hs)

theorem quadratic_linear_isBigO_cube :
    Asymptotics.IsBigO Filter.atTop
      (fun n : Nat => ((2 * n * n + 3 * n : Nat) : ℝ))
      (fun n : Nat => ((n * n * n : Nat) : ℝ)) := by
  apply Resources.isBigO_of_nat_bound
    (fun n => 2 * n * n + 3 * n) (fun n => n * n * n) 5 0
  intro n _
  exact quadratic_linear_cube_bound n

/-- The twice-weighted sum has upper coefficient two and reverse coefficient one. -/
theorem weighted_two_isTheta :
    Asymptotics.IsTheta Filter.atTop
      (fun n : Nat => ((∑ k ∈ Ico 1 (n + 1), k * 2 ^ k : Nat) : ℝ))
      (fun n : Nat => ((n * 2 ^ n : Nat) : ℝ)) := by
  constructor
  · apply Resources.isBigO_of_nat_bound
      (fun n => ∑ k ∈ Ico 1 (n + 1), k * 2 ^ k) (fun n => n * 2 ^ n) 2 0
    intro n _
    exact (weighted_two_bounds n).2
  · apply Resources.isBigO_of_nat_bound
      (fun n => n * 2 ^ n) (fun n => ∑ k ∈ Ico 1 (n + 1), k * 2 ^ k) 1 0
    intro n _
    simpa only [Nat.one_mul] using (weighted_two_bounds n).1

/-- The actual executions agree in value for every list and combiner. -/
theorem fold_values_agree (c : Nat) (f : β → α → β) (e : β) (xs : List α) :
    (Resources.ListExecution.foldlViaInit c f e xs).1 =
      (Resources.ListExecution.foldl c f e xs).1 :=
  (Resources.ListExecution.foldlViaInit_value c f e xs).trans
    (Resources.ListExecution.foldl_value c f e xs).symm

/-- Gauss' shared formula closes the public work equation of the actual selector fold. -/
theorem foldlViaInit_work_double (c : Nat) (f : β → α → β) (e : β) (xs : List α) :
    2 * (Resources.ListExecution.foldlViaInit c f e xs).2 =
      3 * xs.length * (xs.length + 1) + 2 * c * xs.length + 2 := by
  rw [Resources.ListExecution.foldlViaInit_work, list_range_sum_eq_triangle]
  have h := triangle_double xs.length
  nlinarith

/-- Exact overhead of two existing executions with the same denotation. -/
theorem foldlViaInit_work_overhead (c : Nat) (f : β → α → β) (e : β) (xs : List α) :
    2 * (Resources.ListExecution.foldlViaInit c f e xs).2 =
      2 * (Resources.ListExecution.foldl c f e xs).2 +
        3 * xs.length * xs.length + xs.length := by
  have h := foldlViaInit_work_double c f e xs
  rw [Resources.ListExecution.foldl_work]
  nlinarith

/-- The empty selector fold preserves the seed and its one terminal charge. -/
theorem recursive_fold_empty (c : Nat) (f : β → α → β) (e : β) :
    Resources.ListExecution.foldlViaInit c f e ([] : List α) = (e, 1) := by
  apply Prod.ext
  · simpa only [List.foldl_nil] using
      (Resources.ListExecution.foldlViaInit_value c f e ([] : List α))
  · have h := foldlViaInit_work_double c f e ([] : List α)
    simp only [List.length_nil] at h
    change (Resources.ListExecution.foldlViaInit c f e ([] : List α)).2 = 1
    omega

theorem direct_fold_empty (c : Nat) (f : β → α → β) (e : β) :
    Resources.ListExecution.foldl c f e ([] : List α) = (e, 1) := by
  apply Prod.ext
  · simpa only [List.foldl_nil] using
      (Resources.ListExecution.foldl_value c f e ([] : List α))
  · have h := Resources.ListExecution.foldl_work c f e ([] : List α)
    simp only [List.length_nil] at h
    change (Resources.ListExecution.foldl c f e ([] : List α)).2 = 1
    omega

/-- The element and accumulator types remain independent in the singleton case. -/
theorem recursive_fold_singleton (c : Nat) (f : β → α → β) (e : β) (x : α) :
    Resources.ListExecution.foldlViaInit c f e [x] = (f e x, c + 4) := by
  apply Prod.ext
  · simpa only [List.foldl_cons, List.foldl_nil] using
      (Resources.ListExecution.foldlViaInit_value c f e [x])
  · have h := foldlViaInit_work_double c f e [x]
    simp only [List.length_cons, List.length_nil] at h
    change (Resources.ListExecution.foldlViaInit c f e [x]).2 = c + 4
    omega

theorem direct_fold_singleton (c : Nat) (f : β → α → β) (e : β) (x : α) :
    Resources.ListExecution.foldl c f e [x] = (f e x, c + 2) := by
  apply Prod.ext
  · simpa only [List.foldl_cons, List.foldl_nil] using
      (Resources.ListExecution.foldl_value c f e [x])
  · have h := Resources.ListExecution.foldl_work c f e [x]
    simp only [List.length_cons, List.length_nil] at h
    change (Resources.ListExecution.foldl c f e [x]).2 = c + 2
    omega

theorem recursive_fold_add_two :
    Resources.ListExecution.foldlViaInit 1 Nat.add 0 [1, 2] = (3, 12) := by
  apply Prod.ext
  · simpa only [List.foldl_cons, List.foldl_nil] using
      (Resources.ListExecution.foldlViaInit_value 1 Nat.add 0 [1, 2])
  · have h := foldlViaInit_work_double 1 Nat.add 0 [1, 2]
    simp only [List.length_cons, List.length_nil] at h
    change (Resources.ListExecution.foldlViaInit 1 Nat.add 0 [1, 2]).2 = 12
    omega

theorem direct_fold_add_two :
    Resources.ListExecution.foldl 1 Nat.add 0 [1, 2] = (3, 5) := by
  apply Prod.ext
  · simpa only [List.foldl_cons, List.foldl_nil] using
      (Resources.ListExecution.foldl_value 1 Nat.add 0 [1, 2])
  · have h := Resources.ListExecution.foldl_work 1 Nat.add 0 [1, 2]
    simp only [List.length_cons, List.length_nil] at h
    change (Resources.ListExecution.foldl 1 Nat.add 0 [1, 2]).2 = 5
    omega

/-- Canonical arithmetic cases consume the shared exact formulas. -/
theorem triangle_five : (∑ k ∈ Ico 1 (5 + 1), k : Nat) = 15 :=
  (triangle_exact 5).trans (by norm_num)

theorem squares_five : (∑ k ∈ Ico 1 (5 + 1), k * k : Nat) = 55 :=
  (squares_exact 5).trans (by norm_num)

theorem half_sum_one :
    (∑ k ∈ Ico (1 : Nat) (1 + 1), (k : ℚ) / (2 : ℚ) ^ k) = 1 / 2 :=
  (half_sum_closed 1).trans (by norm_num)

theorem half_sum_two :
    (∑ k ∈ Ico (1 : Nat) (2 + 1), (k : ℚ) / (2 : ℚ) ^ k) = 1 :=
  (half_sum_closed 2).trans (by norm_num)

theorem half_sum_three :
    (∑ k ∈ Ico (1 : Nat) (3 + 1), (k : ℚ) / (2 : ℚ) ^ k) = 11 / 8 :=
  (half_sum_closed 3).trans (by norm_num)

/-- The half-sum and remainder examples have no resource-cost attribution. -/
theorem half_sum_zero :
    (∑ k ∈ Ico (1 : Nat) (0 + 1), (k : ℚ) / (2 : ℚ) ^ k) = 0 :=
  (half_sum_closed 0).trans (by norm_num)

theorem half_remainder_zero : (0 + 2 : ℚ) / (2 : ℚ) ^ 0 = 2 := by
  norm_num

theorem half_remainder_six : (6 + 2 : ℚ) / (2 : ℚ) ^ 6 = 1 / 8 := by
  norm_num

/-- Equality with the target error does not satisfy the required strict bound. -/
theorem half_remainder_six_not_strict :
    ¬ (6 + 2 : ℚ) / (2 : ℚ) ^ 6 < 1 / 8 :=
  not_lt_of_ge (le_of_eq half_remainder_six.symm)

theorem half_remainder_seven : (7 + 2 : ℚ) / (2 : ℚ) ^ 7 = 9 / 128 := by
  norm_num

theorem half_remainder_seven_strict :
    (7 + 2 : ℚ) / (2 : ℚ) ^ 7 < 1 / 8 :=
  lt_of_eq_of_lt half_remainder_seven (by norm_num)

end Examples.ResourceFiniteSums

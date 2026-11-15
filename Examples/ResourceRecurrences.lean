import Applications.Resources.Recurrences
import Applications.Resources.ListExecution
import Mathlib.Order.Filter.AtTopBot.Prod

/-!
# Recurrence correspondences and growth boundaries

The universal examples connect source recurrence equations and comparisons to
native folds. Separate growth clients retain independent bases, inclusive
thresholds, rational coefficients, and the distinction from function equality.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.ResourceRecurrences

open Filter Asymptotics Resources SquareKit.FiniteRecurrences
open scoped BigOperators

/-! ## Native definition correspondences -/

example (b c : Nat) :
    (List.range' 1 0).foldl (fun x k => x + c * k) b = b := by
  simpa only [one_mul] using affine_fold_zero (fun _ => 1) (fun k => c * k) b

example (b c n : Nat) :
    (List.range' 1 (n + 1)).foldl (fun x k => x + c * k) b =
      (List.range' 1 n).foldl (fun x k => x + c * k) b + c * (n + 1) := by
  simpa only [one_mul] using affine_fold_succ (fun _ => 1) (fun k => c * k) b n

example (b c : Nat) :
    (List.range' 1 0).foldl (fun x k => 2 * x + c * k) b = b :=
  affine_fold_zero (fun _ => 2) (fun k => c * k) b

example (b c n : Nat) :
    (List.range' 1 (n + 1)).foldl (fun x k => 2 * x + c * k) b =
      2 * (List.range' 1 n).foldl (fun x k => 2 * x + c * k) b + c * (n + 1) :=
  affine_fold_succ (fun _ => 2) (fun k => c * k) b n

example (b c : Nat) :
    (List.range' 1 0).foldl (fun x k => k * x + c * k) b = b :=
  affine_fold_zero id (fun k => c * k) b

example (b c n : Nat) :
    (List.range' 1 (n + 1)).foldl (fun x k => k * x + c * k) b =
      (n + 1) * (List.range' 1 n).foldl (fun x k => k * x + c * k) b + c * (n + 1) :=
  affine_fold_succ id (fun k => c * k) b n

example : (∑ k ∈ Finset.range 0, 1 / (Nat.factorial k : ℚ)) = 0 := by simp

example (n : Nat) :
    (∑ k ∈ Finset.range (n + 1), 1 / (Nat.factorial k : ℚ)) =
      (∑ k ∈ Finset.range n, 1 / (Nat.factorial k : ℚ)) + 1 / (Nat.factorial n : ℚ) := by
  rw [Finset.sum_range_succ]

-- The native factorial already owns the source positivity obligation.
example (n : Nat) : 0 < Nat.factorial n := Nat.factorial_pos n

/-! ## Six universal comparison specializations -/

example (T : Nat → Nat) (b c : Nat) (hb : T 0 ≤ b)
    (hstep : ∀ n, T (n + 1) ≤ T n + c * (n + 1)) :
    ∀ n, T n ≤ (List.range' 1 n).foldl (fun x k => x + c * k) b := by
  intro n
  simpa only [one_mul] using
    le_affine_fold (fun _ => 1) (fun k => c * k) T b hb
      (fun j => by simpa only [one_mul] using hstep j) n

example (T : Nat → Nat) (b c : Nat) (hb : b ≤ T 0)
    (hstep : ∀ n, T n + c * (n + 1) ≤ T (n + 1)) :
    ∀ n, (List.range' 1 n).foldl (fun x k => x + c * k) b ≤ T n := by
  intro n
  simpa only [one_mul] using
    affine_fold_le (fun _ => 1) (fun k => c * k) T b hb
      (fun j => by simpa only [one_mul] using hstep j) n

example (T : Nat → Nat) (b c : Nat) (hb : T 0 ≤ b)
    (hstep : ∀ n, T (n + 1) ≤ 2 * T n + c * (n + 1)) :
    ∀ n, T n ≤ (List.range' 1 n).foldl (fun x k => 2 * x + c * k) b :=
  le_affine_fold (fun _ => 2) (fun k => c * k) T b hb hstep

example (T : Nat → Nat) (b c : Nat) (hb : b ≤ T 0)
    (hstep : ∀ n, 2 * T n + c * (n + 1) ≤ T (n + 1)) :
    ∀ n, (List.range' 1 n).foldl (fun x k => 2 * x + c * k) b ≤ T n :=
  affine_fold_le (fun _ => 2) (fun k => c * k) T b hb hstep

example (T : Nat → Nat) (b c : Nat) (hb : T 0 ≤ b)
    (hstep : ∀ n, T (n + 1) ≤ (n + 1) * T n + c * (n + 1)) :
    ∀ n, T n ≤ (List.range' 1 n).foldl (fun x k => k * x + c * k) b :=
  le_affine_fold id (fun k => c * k) T b hb hstep

example (T : Nat → Nat) (b c : Nat) (hb : b ≤ T 0)
    (hstep : ∀ n, (n + 1) * T n + c * (n + 1) ≤ T (n + 1)) :
    ∀ n, (List.range' 1 n).foldl (fun x k => k * x + c * k) b ≤ T n :=
  affine_fold_le id (fun k => c * k) T b hb hstep

/-! ## Theta does not assert equality of functions -/

theorem theta_is_not_function_equality :
    ((fun n : Nat => ((n * n : Nat) : ℝ)) =Θ[atTop]
      (fun n : Nat => ((n * n + n : Nat) : ℝ))) ∧
      (fun n : Nat => n * n) ≠ (fun n : Nat => n * n + n) := by
  constructor
  · constructor
    · apply isBigO_of_nat_bound _ _ 1 0
      intro n _
      omega
    · apply isBigO_of_nat_bound _ _ 2 0
      intro n _
      have hn := Nat.le_mul_self n
      omega
  · intro h
    have hvalue := congrFun h 1
    norm_num at hvalue

/-! ## Natural and rational coefficient discriminators -/

theorem half_coefficient_bound (n : Nat) :
    (n : ℚ) ≤ (1 / 2 : ℚ) * ((2 * n : Nat) : ℚ) := by
  apply le_of_eq
  push_cast
  ring

example : ∃ C N : Nat, 0 < C ∧ ∀ n, N ≤ n → n ≤ C * (2 * n) := by
  apply (nat_bound_iff_rat_bound (fun n => n) (fun n => 2 * n)).mpr
  exact ⟨1 / 2, by norm_num, 0, fun n _ => half_coefficient_bound n⟩

example (n : Nat) : n ≤ 1 * (2 * n) := by omega

-- A vanishing comparator is permitted by the coefficient equivalence.
example : ∃ C N : Nat, 0 < C ∧ ∀ n : Nat, N ≤ n → 0 ≤ C * 0 := by
  apply (nat_bound_iff_rat_bound (fun _ => 0) (fun _ => 0)).mpr
  refine ⟨1 / 2, by norm_num, 0, ?_⟩
  intro _ _
  norm_num

/-! ## Independent bases and exact boundary conditions -/

example (c : Nat) (hc : 0 < c) :
    (fun n => (((List.range' 1 n).foldl (fun x k => x + c * k) 0 : Nat) : ℝ)) =Θ[atTop]
      (fun n : Nat => ((n * n : Nat) : ℝ)) := additive_recurrence_isTheta 0 c hc

example (c : Nat) (hc : 0 < c) :
    (fun n => (((List.range' 1 n).foldl (fun x k => 2 * x + c * k) 0 : Nat) : ℝ)) =Θ[atTop]
      (fun n : Nat => ((2 ^ n : Nat) : ℝ)) := doubling_recurrence_isTheta 0 c hc

example (c : Nat) (hc : 0 < c) :
    (fun n => (((List.range' 1 n).foldl (fun x k => k * x + c * k) 0 : Nat) : ℝ)) =Θ[atTop]
      (fun n : Nat => (Nat.factorial n : ℝ)) := factorial_recurrence_isTheta 0 c hc

example :
    (List.range' 1 5).foldl (fun x k => x + 0 * k) 3 = 3 ∧
    (List.range' 1 5).foldl (fun x k => 2 * x + 0 * k) 3 = 96 ∧
    (List.range' 1 5).foldl (fun x k => k * x + 0 * k) 3 = 360 := by
  exact ⟨rfl, rfl, rfl⟩

/-- With zero toll, the additive fold stays at its independent constant base.
It cannot satisfy the reverse eventual quadratic bound. -/
theorem zero_toll_additive_not_isTheta :
    ¬ ((fun n => (((List.range' 1 n).foldl (fun x k => x + 0 * k) 3 : Nat) : ℝ)) =Θ[atTop]
      (fun n : Nat => ((n * n : Nat) : ℝ))) := by
  intro htheta
  obtain ⟨C, _hC, hbound⟩ :=
    (isBigO_natCast_iff (l := (atTop : Filter Nat))
      (fun n => n * n)
      (fun n => (List.range' 1 n).foldl (fun x k => x + 0 * k) 3)).mp htheta.2
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
  let n := N + 3 * C + 1
  have hnN : N ≤ n := by dsimp [n]; omega
  have hconstant : (List.range' 1 n).foldl (fun x k => x + 0 * k) 3 = 3 := by
    exact (additive_exact 3 0 n).trans (by simp)
  have hupper := hN n hnN
  rw [hconstant] at hupper
  have hsquare := Nat.le_mul_self n
  have hn : 3 * C < n := by dsimp [n]; omega
  omega

-- Every weight family has zero states when both base and toll are zero.
example (weight : Nat → Nat) (n : Nat) :
    (List.range' 1 n).foldl (fun x k => weight k * x + 0) 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [affine_fold_succ weight (fun _ => 0) 0 n, ih]
    simp

-- Changing only weight/toll at zero cannot affect a positive-index fold.
example (weight toll : Nat → Nat) (weightZero tollZero b n : Nat) :
    (List.range' 1 n).foldl (fun x k =>
      (if k = 0 then weightZero else weight k) * x +
        (if k = 0 then tollZero else toll k)) b =
      (List.range' 1 n).foldl (fun x k => weight k * x + toll k) b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [affine_fold_succ (fun k => if k = 0 then weightZero else weight k)
      (fun k => if k = 0 then tollZero else toll k) b n,
      affine_fold_succ weight toll b n, ih]
    simp

-- The n>=1 premises cannot be deleted from these three finite inequalities.
example : ¬ (List.range' 1 0).foldl (fun x k => x + 1 * k) 1 ≤ (1 + 1) * (0 * 0) := by
  decide

example : ¬ 1 * 2 ^ 0 ≤ 2 * (List.range' 1 0).foldl (fun x k => 2 * x + 1 * k) 0 := by
  decide

example : ¬ 1 * Nat.factorial 0 ≤
    (List.range' 1 0).foldl (fun x k => k * x + 1 * k) 0 := by
  decide

-- The reserve itself is valid at zero, unlike the factorial lower inequality.
example (b c : Nat) :
    (List.range' 1 0).foldl (fun x k => k * x + c * k) b + 2 * c ≤
      (b + 3 * c) * Nat.factorial 0 := by
  simp only [List.range'_zero, List.foldl_nil, Nat.factorial_zero, Nat.mul_one]
  omega


/-! ## Arbitrary tolls and positive-index boundaries -/

-- These source rows use the standard sum APIs directly, without project wrappers.
example (f : Nat → Nat) {n m : Nat} (hnm : n ≤ m) :
    (∑ k ∈ Finset.Ico 1 (n + 1), f k) ≤ ∑ k ∈ Finset.Ico 1 (m + 1), f k := by
  apply Finset.sum_le_sum_of_subset
  intro k hk
  obtain ⟨hk, hkn⟩ := Finset.mem_Ico.mp hk
  exact Finset.mem_Ico.mpr ⟨hk, by omega⟩

example (f : Nat → Nat) {k n : Nat} (hk : 1 ≤ k) (hkn : k ≤ n) :
    f k ≤ ∑ j ∈ Finset.Ico 1 (n + 1), f j :=
  Finset.single_le_sum_of_canonicallyOrdered (Finset.mem_Ico.mpr ⟨hk, by omega⟩)

/-- A finite exceptional prefix is retained by both globalization and the exact
positive-index sum. The reserve applies to every index, before and after its tail. -/
theorem finite_prefix_toll_contract :
    let toll : Nat → Nat := fun k => if k = 0 then 999 else if k = 1 then 100 else k
    (∃ C : Nat, 0 < C ∧ ∀ n : Nat, toll (n + 1) ≤ C * (n + 1)) ∧
      (∀ n : Nat, toll (n + 1) ≤ 100 * (n + 1)) ∧
      (∀ C : Nat, ¬ toll 0 ≤ C * 0) ∧
      (List.range 5).map (fun n =>
        (List.range' 1 n).foldl (fun x k => x + toll k) 0) = [0, 100, 102, 105, 109] ∧
      (∀ n : Nat, 1 ≤ n →
        (List.range' 1 n).foldl (fun x k => x + toll k) 0 =
          (∑ k ∈ Finset.Ico 1 (n + 1), k) + 99) ∧
      (∀ n : Nat, (∑ k ∈ Finset.Ico 1 (n + 1), k) ≤
        1 * (∑ k ∈ Finset.Ico 1 (n + 1), toll k) + ∑ k ∈ Finset.Ico 1 (2 + 1), k) ∧
      ((fun n : Nat =>
        (((List.range' 1 n).foldl (fun x k => x + toll k) 0 : Nat) : ℝ)) =Θ[atTop]
          (fun n : Nat => ((n * n : Nat) : ℝ))) ∧
      (∀ n : Nat, 1 ≤ n →
        (List.range' 1 n).foldl (fun x k => x + toll k) 0 ≤ 100 * (n * n)) ∧
      (∀ n : Nat, 4 ≤ n →
        n * n ≤ 4 * (List.range' 1 n).foldl (fun x k => x + toll k) 0) := by
  let toll : Nat → Nat := fun k => if k = 0 then 999 else if k = 1 then 100 else k
  have htail (k : Nat) (hk : 2 ≤ k) : toll k = k := by
    simp [toll, show k ≠ 0 by omega, show k ≠ 1 by omega]
  have hupper (k : Nat) (hk : 1 ≤ k) : toll k ≤ 100 * k := by
    by_cases h : k = 1
    · subst k
      norm_num [toll]
    · rw [htail k (by omega)]
      omega
  have htoll : (fun n : Nat => (toll n : ℝ)) =Θ[atTop]
      (fun n : Nat => (n : ℝ)) := by
    constructor
    · apply isBigO_of_nat_bound _ _ 1 2
      intro n hn
      simp [htail n hn]
    · apply isBigO_of_nat_bound _ _ 1 2
      intro n hn
      simp [htail n hn]
  have hsum : ∀ n : Nat, 1 ≤ n →
      (∑ k ∈ Finset.Ico 1 (n + 1), toll k) =
        (∑ k ∈ Finset.Ico 1 (n + 1), k) + 99 := by
    intro n
    induction n with
    | zero => intro hn; omega
    | succ n ih =>
        intro _
        by_cases hz : n = 0
        · subst n
          norm_num [toll]
        · rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1),
            Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1),
            ih (by omega), htail (n + 1) (by omega)]
          omega
  have hexact (n : Nat) (hn : 1 ≤ n) :
      (List.range' 1 n).foldl (fun x k => x + toll k) 0 =
        (∑ k ∈ Finset.Ico 1 (n + 1), k) + 99 := by
    rw [additive_toll_exact, zero_add]
    exact hsum n hn
  have hreserve := triangle_le_scaled_toll_sum toll 1 2
    (fun k hk => by rw [htail k hk]; omega)
  refine ⟨positive_linear_bound_of_isBigO toll htoll.1,
    (fun n => hupper (n + 1) (by omega)), ?_, ?_, hexact, hreserve,
    additive_toll_recurrence_isTheta toll 0 htoll, ?_, ?_⟩
  · intro C
    norm_num [toll]
  · rfl
  · intro n _
    rw [additive_toll_exact, zero_add]
    calc
      (∑ k ∈ Finset.Ico 1 (n + 1), toll k) ≤
          ∑ k ∈ Finset.Ico 1 (n + 1), 100 * k := by
        apply Finset.sum_le_sum
        intro k hk
        exact hupper k (Finset.mem_Ico.mp hk).1
      _ = 100 * (∑ k ∈ Finset.Ico 1 (n + 1), k) := by rw [Finset.mul_sum]
      _ ≤ 100 * (n * n) :=
        Nat.mul_le_mul_left 100 (SquareKit.FiniteSums.triangle_bounds n).2
  · intro n hn
    rw [hexact n (by omega)]
    have h := (SquareKit.FiniteSums.triangle_bounds n).1
    omega

/-- Every positive prefix excludes the arbitrary term at zero. Hence the
single-term inequality cannot drop its positive-index premise. -/
theorem positive_sum_zero_index_boundary :
    let f : Nat → Nat := fun k => if k = 0 then 999 else 0
    (∀ n : Nat, (∑ k ∈ Finset.Ico 1 (n + 1), f k) = 0) ∧
      (∀ n : Nat, ¬ f 0 ≤ ∑ k ∈ Finset.Ico 1 (n + 1), f k) := by
  let f : Nat → Nat := fun k => if k = 0 then 999 else 0
  have hsum (n : Nat) : (∑ k ∈ Finset.Ico 1 (n + 1), f k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkpos := (Finset.mem_Ico.mp hk).1
    simp [f, show k ≠ 0 by omega]
  refine ⟨hsum, ?_⟩
  intro n
  rw [hsum n]
  norm_num [f]

/-! ## Positive and zero bases with zero toll -/

/-- Zero toll is admissible for the new positive-base theorems. With base zero,
the same two growth conclusions fail at every possible eventual threshold. -/
theorem zero_toll_base_boundary :
    (∀ n : Nat,
      (List.range' 1 n).foldl (fun x _ => 2 * x + 0) 1 = 2 ^ n ∧
      (List.range' 1 n).foldl (fun x k => k * x + 0) 1 = Nat.factorial n ∧
      (List.range' 1 n).foldl (fun x _ => 2 * x + 0) 0 = 0 ∧
      (List.range' 1 n).foldl (fun x k => k * x + 0) 0 = 0) ∧
      ((fun n : Nat =>
        (((List.range' 1 n).foldl (fun x _ => 2 * x + 0) 1 : Nat) : ℝ)) =Θ[atTop]
          (fun n : Nat => ((2 ^ n : Nat) : ℝ))) ∧
      ((fun n : Nat =>
        (((List.range' 1 n).foldl (fun x k => k * x + 0) 1 : Nat) : ℝ)) =Θ[atTop]
          (fun n : Nat => (Nat.factorial n : ℝ))) ∧
      (¬ ((fun n : Nat =>
        (((List.range' 1 n).foldl (fun x _ => 2 * x + 0) 0 : Nat) : ℝ)) =Θ[atTop]
          (fun n : Nat => ((2 ^ n : Nat) : ℝ)))) ∧
      (¬ ((fun n : Nat =>
        (((List.range' 1 n).foldl (fun x k => k * x + 0) 0 : Nat) : ℝ)) =Θ[atTop]
          (fun n : Nat => (Nat.factorial n : ℝ)))) := by
  have hdouble (n : Nat) :
      (List.range' 1 n).foldl (fun x _ => 2 * x + 0) 1 = 2 ^ n := by
    simpa only [zero_mul, mul_zero, add_zero, mul_one] using doubling_exact 1 0 n
  have hfactorial (n : Nat) :
      (List.range' 1 n).foldl (fun x k => k * x + 0) 1 = Nat.factorial n := by
    induction n with
    | zero => rfl
    | succ n ih =>
        have hstep := affine_fold_succ (fun k => k) (fun _ => 0) 1 n
        rw [ih] at hstep
        simpa only [Nat.factorial_succ, add_zero] using hstep
  have hzero (weight : Nat → Nat) (n : Nat) :
      (List.range' 1 n).foldl (fun x k => weight k * x + 0) 0 = 0 := by
    exact Nat.eq_zero_of_le_zero
      (affine_fold_le weight (fun _ => 0) (fun _ => 0) 0 le_rfl
        (fun _ => by simp) n)
  have htoll : (fun _ : Nat => ((0 : Nat) : ℝ)) =O[atTop]
      (fun n : Nat => (n : ℝ)) :=
    isBigO_of_nat_bound (fun _ => 0) id 1 0 (fun _ _ => by simp)
  refine ⟨(fun n => ⟨hdouble n, hfactorial n, hzero (fun _ => 2) n, hzero id n⟩),
    doubling_toll_recurrence_isTheta (fun _ => 0) 1 (by decide) htoll,
    factorial_toll_recurrence_isTheta (fun _ => 0) 1 (by decide) htoll, ?_, ?_⟩
  · intro htheta
    obtain ⟨C, _hC, hbound⟩ :=
      (isBigO_natCast_iff (l := (atTop : Filter Nat)) (fun n => 2 ^ n)
        (fun n => (List.range' 1 n).foldl (fun x _ => 2 * x + 0) 0)).mp htheta.2
    obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
    have h := hN N le_rfl
    rw [hzero (fun _ => 2) N] at h
    have hp : 0 < (2 : Nat) ^ N := pow_pos (by decide) N
    omega
  · intro htheta
    obtain ⟨C, _hC, hbound⟩ :=
      (isBigO_natCast_iff (l := (atTop : Filter Nat)) Nat.factorial
        (fun n => (List.range' 1 n).foldl (fun x k => k * x + 0) 0)).mp htheta.2
    obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
    have h := hN N le_rfl
    rw [hzero (fun k => k) N] at h
    have hp := Nat.factorial_pos N
    omega

-- Supplied C=1 gives the source upper/reverse witnesses (3,0)/(1,0).
example (n : Nat) :
    (List.range' 1 n).foldl (fun x _ => 2 * x + 0) 1 ≤ 3 * 2 ^ n ∧
      2 ^ n ≤ 1 * (List.range' 1 n).foldl (fun x _ => 2 * x + 0) 1 := by
  rw [(zero_toll_base_boundary.1 n).1]
  omega

-- The factorial upper threshold remains one; its reverse threshold is zero.
example (n : Nat) (_hn : 1 ≤ n) :
    (List.range' 1 n).foldl (fun x k => k * x + 0) 1 ≤ 4 * Nat.factorial n := by
  rw [(zero_toll_base_boundary.1 n).2.1]
  omega

example (n : Nat) :
    Nat.factorial n ≤ 1 * (List.range' 1 n).foldl (fun x k => k * x + 0) 1 := by
  rw [(zero_toll_base_boundary.1 n).2.1]
  omega

/-- A coefficient chosen separately for each summand is insufficient for a
uniform eventual quadratic bound on their positive-prefix sums. -/
theorem pointwise_bounds_do_not_control_sum :
    (∀ k : Nat, 1 ≤ k → ∃ C : Nat, 0 < C ∧ k * k ≤ C * k) ∧
      ¬ ((fun n : Nat =>
        ((∑ k ∈ Finset.Ico 1 (n + 1), k * k : Nat) : ℝ)) =O[atTop]
          (fun n : Nat => ((n * n : Nat) : ℝ))) := by
  constructor
  · intro k hk
    exact ⟨k, by omega, le_rfl⟩
  · intro hO
    obtain ⟨C, _hC, hbound⟩ :=
      (isBigO_natCast_iff (l := (atTop : Filter Nat))
        (fun n => ∑ k ∈ Finset.Ico 1 (n + 1), k * k) (fun n => n * n)).mp hO
    obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
    let n := N + 6 * C + 1
    have hnN : N ≤ n := by dsimp [n]; omega
    have hnC : 6 * C < n := by dsimp [n]; omega
    have hnpos : 0 < n := by dsimp [n]; omega
    have hupper := hN n hnN
    have hscaled := Nat.mul_le_mul_left 6 hupper
    have hcubic := (SquareKit.FiniteSums.squares_bounds n).1
    have hstrict : 6 * C * (n * n) < n * n * n := by
      calc
        6 * C * (n * n) < n * (n * n) :=
          Nat.mul_lt_mul_of_pos_right hnC (Nat.mul_pos hnpos hnpos)
        _ = n * n * n := by ring
    have hbad : n * n * n ≤ 6 * C * (n * n) :=
      hcubic.trans (by simpa only [Nat.mul_assoc] using hscaled)
    exact (not_le_of_gt hstrict) hbad

/-! ## Actual measured init/last folding -/

universe u v

/-- The arbitrary-toll native fold matches the existing exact work formula;
the positive interval contributes exactly n copies of the fixed combine price. -/
private theorem init_toll_fold (c n : Nat) :
    (List.range' 1 n).foldl (fun x k => x + (3 * k + c)) 1 =
      3 * (List.range (n + 1)).sum + c * n + 1 := by
  rw [additive_toll_exact, SquareKit.FiniteSums.list_range_sum_eq_triangle]
  simp [Finset.sum_add_distrib, Finset.mul_sum, Nat.mul_comm,
    Nat.add_comm, Nat.add_left_comm]

/-- For every length-indexed input family, the actual executor retains its value
law and has quadratic charged work with a fixed combine price, including zero. -/
theorem foldlViaInit_value_and_isTheta {α : Type u} {β : Type v}
    (c : Nat) (f : β → α → β) (e : β)
    (xs : Nat → List α) (hlen : ∀ n : Nat, (xs n).length = n) :
    (∀ n : Nat, (Resources.ListExecution.foldlViaInit c f e (xs n)).1 =
      (xs n).foldl f e) ∧
      ((fun n : Nat => ((Resources.ListExecution.foldlViaInit c f e (xs n)).2 : ℝ)) =Θ[atTop]
        (fun n : Nat => ((n * n : Nat) : ℝ))) := by
  have hwork (n : Nat) : (Resources.ListExecution.foldlViaInit c f e (xs n)).2 =
      (List.range' 1 n).foldl (fun x k => x + (3 * k + c)) 1 := by
    rw [Resources.ListExecution.foldlViaInit_work, hlen n]
    exact (init_toll_fold c n).symm
  have htoll : (fun n : Nat => ((3 * n + c : Nat) : ℝ)) =Θ[atTop]
      (fun n : Nat => (n : ℝ)) := by
    constructor
    · apply isBigO_of_nat_bound _ _ (3 + c) 1
      intro n hn
      have hc : c ≤ c * n := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left c hn
      nlinarith
    · apply isBigO_of_nat_bound _ _ 1 0
      intro n _
      omega
  refine ⟨(fun n => Resources.ListExecution.foldlViaInit_value c f e (xs n)), ?_⟩
  simpa only [hwork] using additive_toll_recurrence_isTheta (fun k => 3 * k + c) 1 htoll

-- The concrete witnesses are (4+c,1) and (4,0), with no c>0 requirement.
example {α : Type u} {β : Type v} (c : Nat) (f : β → α → β) (e : β)
    (xs : List α) (hn : 1 ≤ xs.length) :
    (Resources.ListExecution.foldlViaInit c f e xs).2 ≤ (4 + c) * (xs.length * xs.length) := by
  rw [Resources.ListExecution.foldlViaInit_work, SquareKit.FiniteSums.list_range_sum_eq_triangle]
  have htriangle := (SquareKit.FiniteSums.triangle_bounds xs.length).2
  have hsq : 1 ≤ xs.length * xs.length := Nat.mul_le_mul hn hn
  have hprice := Nat.mul_le_mul_left c (Nat.le_mul_self xs.length)
  nlinarith

example {α : Type u} {β : Type v} (c : Nat) (f : β → α → β) (e : β) (xs : List α) :
    xs.length * xs.length ≤ 4 * (Resources.ListExecution.foldlViaInit c f e xs).2 := by
  have h := Resources.ListExecution.foldlViaInit_quadratic_lower c f e xs
  omega

example :
    (List.range 4).map (fun n =>
      (Resources.ListExecution.foldlViaInit 1 Nat.add 0 (List.range' 1 n)).2) = [1, 5, 12, 22] := by
  simp only [Resources.ListExecution.foldlViaInit_work, List.length_range']
  rfl

example : Resources.ListExecution.foldlViaInit 1 Nat.add 0 [1, 2] = (3, 12) := by
  apply Prod.ext
  · exact (Resources.ListExecution.foldlViaInit_value 1 Nat.add 0 [1, 2]).trans rfl
  · exact (Resources.ListExecution.foldlViaInit_work 1 Nat.add 0 [1, 2]).trans rfl

/-! ## Actual measured repeated folds

The setup and every pass are existing list executors. The outer runner adds
only their declared observations, in order, and feeds each returned value into
the next pass. The command index starts at zero.
-/

section MeasuredRepeatedFolds

open Resources.ListExecution

/-- Actual returned values and the sum of the actual state-independent pass
observations, for any input list and any number of passes. -/
theorem repeated_fold_value_and_work {α : Type u} {β : Type v}
    (f : β → α → β) (e : β) (xs : List α) (m : Nat) :
    (bind (foldlViaInit 1 f e xs)
      (fun s => run (fun i s => foldl (1 + i % 2) f s xs) (List.range m) s)).1 =
        (List.range m).foldl (fun s _ => xs.foldl f s) (xs.foldl f e) ∧
    (bind (foldlViaInit 1 f e xs)
      (fun s => run (fun i s => foldl (1 + i % 2) f s xs) (List.range m) s)).2 =
        1 + 3 * (∑ k ∈ Finset.Ico 1 (xs.length + 1), k) + xs.length +
          ((List.range m).map (fun i => (2 + i % 2) * xs.length + 1)).sum := by
  constructor
  · simp only [bind_value, run_state, foldlViaInit_value, foldl_value]
  · change (foldlViaInit 1 f e xs).2 +
        (run (fun i s => foldl (1 + i % 2) f s xs) (List.range m)
          (foldlViaInit 1 f e xs).1).2 = _
    rw [run_observation _ (fun i => (2 + i % 2) * xs.length + 1)
      (fun i s => by rw [foldl_work]; ring)]
    rw [foldlViaInit_work, SquareKit.FiniteSums.list_range_sum_eq_triangle]
    omega

/-- Extending the actual command list adds command m, with price 1+m%2,
using the value returned by the whole preceding computation. -/
theorem repeated_fold_succ {α : Type u} {β : Type v}
    (f : β → α → β) (e : β) (xs : List α) (m : Nat) :
    bind (foldlViaInit 1 f e xs)
      (fun s => run (fun i s => foldl (1 + i % 2) f s xs) (List.range (m + 1)) s) =
    bind (bind (foldlViaInit 1 f e xs)
      (fun s => run (fun i s => foldl (1 + i % 2) f s xs) (List.range m) s))
      (fun s => foldl (1 + m % 2) f s xs) := by
  rw [List.range_succ]
  simp only [run_append, run, Resources.bind_pure, Resources.bind_assoc]

/-- The exact witnesses needed by both the finite theorem and the uniform
Theta theorem. This local fact exposes the actual measured observation as T. -/
private theorem repeated_fold_hypotheses {α : Type u} {β : Type v}
    (f : β → α → β) (e : β) (xs : Nat → List α)
    (hlen : ∀ n : Nat, (xs n).length = n) :
    let T := fun m n : Nat =>
      (bind (foldlViaInit 1 f e (xs n))
        (fun s => run (fun i s => foldl (1 + i % 2) f s (xs n)) (List.range m) s)).2
    (∀ n : Nat, 1 ≤ n → n * n ≤ 1 * T 0 n ∧ T 0 n ≤ 5 * (n * n)) ∧
      (∀ m n : Nat, 1 ≤ n → 1 * T m n + n ≤ 1 * T (m + 1) n ∧
        T (m + 1) n ≤ T m n + 4 * n) := by
  let T := fun m n : Nat =>
    (bind (foldlViaInit 1 f e (xs n))
      (fun s => run (fun i s => foldl (1 + i % 2) f s (xs n)) (List.range m) s)).2
  change (∀ n : Nat, 1 ≤ n → n * n ≤ 1 * T 0 n ∧ T 0 n ≤ 5 * (n * n)) ∧
    (∀ m n : Nat, 1 ≤ n → 1 * T m n + n ≤ 1 * T (m + 1) n ∧
      T (m + 1) n ≤ T m n + 4 * n)
  have hzero (n : Nat) : T 0 n = (foldlViaInit 1 f e (xs n)).2 := by
    change (foldlViaInit 1 f e (xs n)).2 + 0 = _
    exact Nat.add_zero _
  have hstep (m n : Nat) : T (m + 1) n = T m n + ((2 + m % 2) * n + 1) := by
    change (bind (foldlViaInit 1 f e (xs n))
      (fun s => run (fun i s => foldl (1 + i % 2) f s (xs n))
        (List.range (m + 1)) s)).2 = _
    rw [repeated_fold_succ]
    change T m n + (foldl (1 + m % 2) f
      (bind (foldlViaInit 1 f e (xs n))
        (fun s => run (fun i s => foldl (1 + i % 2) f s (xs n)) (List.range m) s)).1
      (xs n)).2 = _
    rw [foldl_work, hlen n]
    ring
  constructor
  · intro n hn
    rw [hzero]
    simp only [Nat.one_mul]
    constructor
    · simpa only [hlen n] using foldlViaInit_quadratic_lower 1 f e (xs n)
    · rw [foldlViaInit_work, hlen n, SquareKit.FiniteSums.list_range_sum_eq_triangle]
      have htriangle := (SquareKit.FiniteSums.triangle_bounds n).2
      have hsq : 1 ≤ n * n := Nat.mul_le_mul hn hn
      have hlinear := Nat.le_mul_self n
      nlinarith
  · intro m n hn
    have hmod : m % 2 < 2 := Nat.mod_lt m (by decide)
    have hprice : 2 + m % 2 ≤ 3 := by omega
    have hupper : (2 + m % 2) * n ≤ 3 * n := Nat.mul_le_mul_right n hprice
    have hlower : n ≤ (2 + m % 2) * n := by
      have h := Nat.mul_le_mul_right n (show 1 ≤ 2 + m % 2 by omega)
      simpa only [Nat.one_mul] using h
    rw [hstep]
    simp only [Nat.one_mul]
    constructor <;> omega

/-- Uniform growth of the actual repeated-fold pipeline on every length-indexed
input family. The threshold applies only to n, and includes every m, even zero. -/
theorem repeated_fold_value_and_isTheta {α : Type u} {β : Type v}
    (f : β → α → β) (e : β) (xs : Nat → List α)
    (hlen : ∀ n : Nat, (xs n).length = n) :
    (∀ m n : Nat,
      (bind (foldlViaInit 1 f e (xs n))
        (fun s => run (fun i s => foldl (1 + i % 2) f s (xs n)) (List.range m) s)).1 =
          (List.range m).foldl (fun s _ => (xs n).foldl f s) ((xs n).foldl f e)) ∧
    (∀ m n : Nat, 1 ≤ n →
      m * n + n * n ≤ 2 *
        (bind (foldlViaInit 1 f e (xs n))
          (fun s => run (fun i s => foldl (1 + i % 2) f s (xs n)) (List.range m) s)).2 ∧
      (bind (foldlViaInit 1 f e (xs n))
        (fun s => run (fun i s => foldl (1 + i % 2) f s (xs n)) (List.range m) s)).2 ≤
          9 * (m * n + n * n)) ∧
    Asymptotics.IsTheta (Filter.comap Prod.snd Filter.atTop)
      (fun q : Nat × Nat =>
        ((bind (foldlViaInit 1 f e (xs q.2))
          (fun s => run (fun i s => foldl (1 + i % 2) f s (xs q.2))
            (List.range q.1) s)).2 : ℝ))
      (fun q : Nat × Nat => ((q.1 * q.2 + q.2 * q.2 : Nat) : ℝ)) := by
  let T := fun m n : Nat =>
    (bind (foldlViaInit 1 f e (xs n))
      (fun s => run (fun i s => foldl (1 + i % 2) f s (xs n)) (List.range m) s)).2
  obtain ⟨hb, hs⟩ := repeated_fold_hypotheses f e xs hlen
  refine ⟨?_, ?_, ?_⟩
  · intro m n
    exact (repeated_fold_value_and_work f e (xs n) m).1
  · intro m n hn
    have h := two_param_eventual_bounds T 5 1 4 1 1 (by decide) hb hs m n hn
    simpa only [Nat.add_comm] using h
  · exact Resources.two_param_recurrence_isTheta T 5 1 4 1 1
      (by decide) (by decide) (by decide) hb hs

/-- With constant price one, the same setup and runner have exactly the narrower
n-only toll formula A(n)+m*(2*n+1), without any added runner charge. -/
theorem repeated_fold_constant_price_work {α : Type u} {β : Type v}
    (f : β → α → β) (e : β) (xs : List α) (m : Nat) :
    (bind (foldlViaInit 1 f e xs)
      (fun s => run (fun (_ : Nat) s => foldl 1 f s xs) (List.range m) s)).2 =
        1 + 3 * (∑ k ∈ Finset.Ico 1 (xs.length + 1), k) + xs.length +
          m * (2 * xs.length + 1) := by
  change (foldlViaInit 1 f e xs).2 +
    (run (fun (_ : Nat) s => foldl 1 f s xs) (List.range m)
      (foldlViaInit 1 f e xs).1).2 = _
  rw [run_observation _ (fun _ : Nat => 2 * xs.length + 1)
    (fun _ s => foldl_work 1 f s xs)]
  rw [List.map_const', List.length_range, List.sum_replicate_nat]
  rw [foldlViaInit_work, SquareKit.FiniteSums.list_range_sum_eq_triangle]
  omega

/-- Empty inputs still incur the called executors' terminal work: one for setup
and one for every pass. Their actual returned state remains the supplied seed. -/
theorem repeated_fold_empty {α : Type u} {β : Type v}
    (f : β → α → β) (e : β) (m : Nat) :
    bind (foldlViaInit 1 f e [])
      (fun s => run (fun i s => foldl (1 + i % 2) f s []) (List.range m) s) =
        (e, 1 + m) := by
  apply Prod.ext
  · rw [(repeated_fold_value_and_work f e [] m).1]
    change (List.range m).foldl (fun s _ => s) e = e
    have h (is : List Nat) : is.foldl (fun s _ => s) e = e := by
      induction is with
      | nil => rfl
      | cons i is ih => exact ih
    exact h _
  · rw [(repeated_fold_value_and_work f e [] m).2]
    simp [List.map_const']

-- These are the actual pass calls, using each preceding pipeline's returned state.
example :
    (List.range 3).map (fun i =>
      (foldl (1 + i % 2) Nat.add
        (bind (foldlViaInit 1 Nat.add 0 [1, 2])
          (fun s => run (fun j s => foldl (1 + j % 2) Nat.add s [1, 2])
            (List.range i) s)).1 [1, 2]).2) = [5, 7, 5] := by
  simp only [foldl_work]
  rfl

example :
    (List.range 4).map (fun m =>
      (bind (foldlViaInit 1 Nat.add 0 [1, 2])
        (fun s => run (fun i s => foldl (1 + i % 2) Nat.add s [1, 2])
          (List.range m) s)).1) = [3, 6, 9, 12] := by
  have h (m : Nat) := (repeated_fold_value_and_work Nat.add 0 [1, 2] m).1
  simp only [h]
  rfl

example :
    bind (foldlViaInit 1 Nat.add 0 [1, 2])
      (fun s => run (fun i s => foldl (1 + i % 2) Nat.add s [1, 2]) (List.range 3) s) =
        (12, 29) := by
  apply Prod.ext
  · exact (repeated_fold_value_and_work Nat.add 0 [1, 2] 3).1.trans rfl
  · rw [(repeated_fold_value_and_work Nat.add 0 [1, 2] 3).2]
    change 1 + 3 * (∑ k ∈ Finset.Ico 1 (2 + 1 : Nat), k) + 2 +
      ((List.range 3).map (fun i => (2 + i % 2) * 2 + 1)).sum = 29
    rw [SquareKit.FiniteSums.triangle_exact 2]
    rfl

example :
    bind (foldlViaInit 1 Nat.add 0 [])
      (fun s => run (fun i s => foldl (1 + i % 2) Nat.add s []) (List.range 3) s) =
        (0, 4) :=
  repeated_fold_empty Nat.add 0 3

end MeasuredRepeatedFolds

end Examples.ResourceRecurrences

namespace Examples.ResourceRecurrences

open SquareKit.FiniteRecurrences
open scoped BigOperators

/-- Natural half-tolls satisfy the scaled lower step from length two onward. -/
theorem fractional_two_param_hypotheses :
    let T : Nat → Nat → Nat := fun m n => n * n + m * (n / 2)
    (∀ n, 2 ≤ n → n * n ≤ 1 * T 0 n ∧ T 0 n ≤ 1 * (n * n)) ∧
      (∀ m n, 2 ≤ n → 3 * T m n + n ≤ 3 * T (m + 1) n ∧
        T (m + 1) n ≤ T m n + 1 * n) := by
  dsimp only
  constructor
  · intro n _
    simp
  · intro m n hn
    have hl : n ≤ 3 * (n / 2) := by omega
    have hu : n / 2 ≤ n := Nat.div_le_self n 2
    constructor <;> nlinarith only [hl, hu]

/-- The actual native half-toll fold instantiates the arbitrary-family theorem. -/
theorem fractional_two_param_bounds (m n : Nat) (hn : 2 ≤ n) :
    m * n + n * n ≤ 4 * (List.range' 1 m).foldl (fun x _ => x + n / 2) (n * n) ∧
      (List.range' 1 m).foldl (fun x _ => x + n / 2) (n * n) ≤
        2 * (m * n + n * n) := by
  rw [constant_toll_exact]
  have h := two_param_eventual_bounds (fun m n => n * n + m * (n / 2))
    1 1 1 3 2 (by decide) fractional_two_param_hypotheses.1
    fractional_two_param_hypotheses.2 m n hn
  simpa only [Nat.reduceAdd, Nat.add_comm] using h

-- Source twoRun uses arbitrary functions, including their values at zero.
example (base toll : Nat → Nat) (n : Nat) :
    (List.range' 1 0).foldl (fun x _ => x + toll n) (base n) = base n := rfl

example (base toll : Nat → Nat) (m n : Nat) :
    (List.range' 1 (m + 1)).foldl (fun x _ => x + toll n) (base n) =
      (List.range' 1 m).foldl (fun x _ => x + toll n) (base n) + toll n := by
  simpa only [one_mul] using affine_fold_succ (fun _ => 1) (fun _ => toll n) (base n) m

example (base toll : Nat → Nat) (m n : Nat) :
    (List.range' 1 m).foldl (fun x _ => x + toll n) (base n) = base n + m * toll n :=
  constant_toll_exact (base n) (toll n) m

-- The corrected source model keeps independent b and c at every natural pair.
example (b c n : Nat) :
    (List.range' 1 0).foldl (fun x _ => x + c * n) (b * n * n) = b * n * n := rfl

example (b c m n : Nat) :
    (List.range' 1 (m + 1)).foldl (fun x _ => x + c * n) (b * n * n) =
      (List.range' 1 m).foldl (fun x _ => x + c * n) (b * n * n) + c * n := by
  simpa only [one_mul] using affine_fold_succ (fun _ => 1) (fun _ => c * n) (b * n * n) m

example (b c m n : Nat) :
    (List.range' 1 m).foldl (fun x _ => x + c * n) (b * n * n) =
      b * n * n + c * m * n := by
  rw [constant_toll_exact]
  ring

-- Printed m-tolls have their own all-parameter exact solution.
example (b c m n : Nat) :
    (List.range' 1 m).foldl (fun x k => x + c * k) (b * n * n) =
      b * n * n + c * ∑ k ∈ Finset.Ico 1 (m + 1), k := additive_exact _ _ _

example (b c m : Nat) :
    (List.range' 1 m).foldl (fun x _ => x + c * 0) (b * 0 * 0) = 0 := by
  rw [constant_toll_exact]
  simp

example (base toll : Nat → Nat) (m : Nat) :
    (List.range' 1 m).foldl (fun x _ => x + toll 0) (base 0) = base 0 + m * toll 0 :=
  constant_toll_exact _ _ _

example : ¬ (0 * 1 + 1 * 1 ≤
    (List.range' 1 0).foldl (fun x _ => x + 1 * 1) (0 * 1 * 1)) := by decide

example : ¬ (4 * 1 + 1 * 1 ≤
    (List.range' 1 4).foldl (fun x _ => x + 0 * 1) (1 * 1 * 1)) := by decide

example : 3 * (3 * 3 + 0 * (3 / 2)) + 3 = 30 ∧
    3 * (3 * 3 + 1 * (3 / 2)) = 30 ∧
    ¬ (3 * 3 + 0 * (3 / 2) + 3 ≤ 3 * 3 + 1 * (3 / 2)) := by decide

example : (List.range' 1 3).foldl (fun x _ => x + 4 / 2) (4 * 4) = 22 ∧
    3 * 4 + 4 * 4 = 28 := by decide

example : (List.range' 1 4).foldl (fun x k => x + 1 * k) (1 * 1 * 1) = 11 ∧
    (List.range' 1 4).foldl (fun x _ => x + 1 * 1) (1 * 1 * 1) = 5 ∧
    (11 : Nat) ≠ 5 := by decide

end Examples.ResourceRecurrences

namespace Examples.ResourceRecurrences

open Filter Asymptotics Resources
open scoped BigOperators

/-- Each fixed first parameter admits witnesses m+1 and one at threshold one.
The upper coefficient is allowed to depend on that fixed parameter. -/
theorem fixed_m_polynomial_isTheta (m : Nat) :
    Asymptotics.IsTheta Filter.atTop
      (fun n : Nat => (((m + 1) * n * n : Nat) : ℝ))
      (fun n : Nat => ((m * n + n * n : Nat) : ℝ)) := by
  constructor
  · apply isBigO_of_nat_bound _ _ (m + 1) 1
    intro n _hn
    calc
      (m + 1) * n * n = (m + 1) * (n * n) := by ring
      _ ≤ (m + 1) * (m * n + n * n) :=
        Nat.mul_le_mul_left (m + 1) (Nat.le_add_left _ _)
  · apply isBigO_of_nat_bound _ _ 1 1
    intro n _hn
    calc
      m * n + n * n ≤ m * (n * n) + n * n :=
        Nat.add_le_add_right (Nat.mul_le_mul_left m (Nat.le_mul_self n)) _
      _ = 1 * ((m + 1) * n * n) := by ring

/-- Fixed-parameter comparison constants cannot be chosen uniformly.
For any proposed C,N, use n=N+C+1 and m=n*n. -/
theorem fixed_m_polynomial_not_uniform_isBigO :
    ¬ Asymptotics.IsBigO (Filter.comap Prod.snd Filter.atTop)
      (fun q : Nat × Nat => (((q.1 + 1) * q.2 * q.2 : Nat) : ℝ))
      (fun q : Nat × Nat => ((q.1 * q.2 + q.2 * q.2 : Nat) : ℝ)) := by
  intro hO
  obtain ⟨C, N, _hC, hbound⟩ :=
    (isBigO_natCast_comap_snd_iff
      (fun m n => (m + 1) * n * n) (fun m n => m * n + n * n)).mp hO
  let n := N + C + 1
  let m := n * n
  have hnN : N ≤ n := by dsimp [n]; omega
  have hnpos : 0 < n := by dsimp [n]; omega
  have hCn : C + 1 ≤ n := by dsimp [n]; omega
  have hC_le_n : C ≤ n := by omega
  have hcoef_le : C * (n + 1) ≤ n * n := by
    calc
      C * (n + 1) = C * n + C := by ring
      _ ≤ C * n + n := Nat.add_le_add_left hC_le_n _
      _ = (C + 1) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul_right n hCn
  have hcoef : C * (n + 1) < n * n + 1 := Nat.lt_succ_of_le hcoef_le
  have hbad := hbound m n hnN
  change (n * n + 1) * n * n ≤ C * (n * n * n + n * n) at hbad
  have hstrict : C * (n * n * n + n * n) < (n * n + 1) * n * n := by
    calc
      C * (n * n * n + n * n) = (C * (n + 1)) * (n * n) := by ring
      _ < (n * n + 1) * (n * n) :=
        Nat.mul_lt_mul_of_pos_right hcoef (Nat.mul_pos hnpos hnpos)
      _ = (n * n + 1) * n * n := by ring
  exact (not_le_of_gt hstrict) hbad

/-- Product-atTop can discard the zero first-coordinate fiber, whereas the
second-projection filter retains it and detects its cubic growth. -/
theorem zero_fiber_filter_distinction :
    Asymptotics.IsTheta (Filter.atTop : Filter (Nat × Nat))
      (fun q : Nat × Nat =>
        ((if q.1 = 0 then q.2 * q.2 * q.2 else q.1 * q.2 + q.2 * q.2 : Nat) : ℝ))
      (fun q : Nat × Nat => ((q.1 * q.2 + q.2 * q.2 : Nat) : ℝ)) ∧
      ¬ Asymptotics.IsBigO (Filter.comap Prod.snd Filter.atTop)
        (fun q : Nat × Nat =>
          ((if q.1 = 0 then q.2 * q.2 * q.2 else q.1 * q.2 + q.2 * q.2 : Nat) : ℝ))
        (fun q : Nat × Nat => ((q.1 * q.2 + q.2 * q.2 : Nat) : ℝ)) := by
  have heq : ∀ᶠ q : Nat × Nat in Filter.atTop,
      (if q.1 = 0 then q.2 * q.2 * q.2 else q.1 * q.2 + q.2 * q.2) =
        q.1 * q.2 + q.2 * q.2 := by
    refine Filter.eventually_atTop.mpr ⟨(1, 0), ?_⟩
    intro q hq
    have hfirst : 1 ≤ q.1 := hq.1
    have hm : q.1 ≠ 0 := by omega
    simp only [ite_eq_right hm]
  constructor
  · constructor
    · apply (isBigO_natCast_iff (l := (Filter.atTop : Filter (Nat × Nat)))
        (fun q : Nat × Nat =>
          if q.1 = 0 then q.2 * q.2 * q.2 else q.1 * q.2 + q.2 * q.2)
        (fun q : Nat × Nat => q.1 * q.2 + q.2 * q.2)).mpr
      refine ⟨1, by decide, ?_⟩
      exact heq.mono fun q hq => by
        simpa only [one_mul] using le_of_eq hq
    · apply (isBigO_natCast_iff (l := (Filter.atTop : Filter (Nat × Nat)))
        (fun q : Nat × Nat => q.1 * q.2 + q.2 * q.2)
        (fun q : Nat × Nat =>
          if q.1 = 0 then q.2 * q.2 * q.2 else q.1 * q.2 + q.2 * q.2)).mpr
      refine ⟨1, by decide, ?_⟩
      exact heq.mono fun q hq => by
        simpa only [one_mul] using le_of_eq hq.symm
  · intro hO
    obtain ⟨C, N, _hC, hbound⟩ :=
      (isBigO_natCast_comap_snd_iff
        (fun m n => if m = 0 then n * n * n else m * n + n * n)
        (fun m n => m * n + n * n)).mp hO
    let n := N + C + 1
    have hnN : N ≤ n := by dsimp [n]; omega
    have hnC : C < n := by dsimp [n]; omega
    have hnpos : 0 < n := by dsimp [n]; omega
    have hbad := hbound 0 n hnN
    simp only [Nat.zero_mul, Nat.zero_add] at hbad
    have hstrict : C * (n * n) < n * n * n := by
      calc
        C * (n * n) < n * (n * n) :=
          Nat.mul_lt_mul_of_pos_right hnC (Nat.mul_pos hnpos hnpos)
        _ = n * n * n := by ring
    exact (not_le_of_gt hstrict) hbad

/-- The printed unit m-toll is not uniformly bounded by the corrected model.
For each proposed C,N, use n=N+1 and m=4*C*n+n+1. -/
theorem printed_m_toll_not_uniform_isBigO :
    ¬ Asymptotics.IsBigO (Filter.comap Prod.snd Filter.atTop)
      (fun q : Nat × Nat =>
        ((q.2 * q.2 + ∑ k ∈ Finset.Ico 1 (q.1 + 1), k : Nat) : ℝ))
      (fun q : Nat × Nat => ((q.1 * q.2 + q.2 * q.2 : Nat) : ℝ)) := by
  intro hO
  obtain ⟨C, N, _hC, hbound⟩ :=
    (isBigO_natCast_comap_snd_iff
      (fun m n => n * n + ∑ k ∈ Finset.Ico 1 (m + 1), k)
      (fun m n => m * n + n * n)).mp hO
  let n := N + 1
  let m := 4 * C * n + n + 1
  let Q := ∑ k ∈ Finset.Ico 1 (m + 1), k
  have hnN : N ≤ n := by dsimp [n]; omega
  have hnm : n ≤ m := by dsimp [m]; omega
  have hmpos : 0 < m := by dsimp [m]; omega
  have hlarge : 4 * C * n < m := by dsimp [m]; omega
  have hbad := hbound m n hnN
  change n * n + Q ≤ C * (m * n + n * n) at hbad
  have hQ : Q ≤ C * (m * n + n * n) :=
    (Nat.le_add_left _ _).trans hbad
  have hsquare : n * n ≤ m * n := Nat.mul_le_mul_right n hnm
  have htriangle : m * m ≤ 2 * Q :=
    (SquareKit.FiniteSums.triangle_bounds m).1
  have hupper : m * m ≤ 4 * C * n * m := by
    calc
      m * m ≤ 2 * Q := htriangle
      _ ≤ 2 * (C * (m * n + n * n)) := Nat.mul_le_mul_left 2 hQ
      _ ≤ 2 * (C * (m * n + m * n)) :=
        Nat.mul_le_mul_left 2
          (Nat.mul_le_mul_left C (Nat.add_le_add_left hsquare _))
      _ = 4 * C * n * m := by ring
  have hstrict : 4 * C * n * m < m * m :=
    Nat.mul_lt_mul_of_pos_right hlarge hmpos
  exact (not_le_of_gt hstrict) hupper

end Examples.ResourceRecurrences

import Applications.Resources.RoundedRecurrenceBounds
import Applications.Resources.Growth

/-! The exact scalar majorant for FDSA's median-of-medians selector.

The total natural recurrence has base 483 through size 20, children
ceil(n/5) and ceil(7n/10+3), and toll 19n+54. Child decrease establishes
its definition before any bound is proved. Its monotonicity justifies later
replacement of actual child lengths by the balance theorem's upper bounds.

This scalar is not an implementation or an execution count. The measured
selector must separately prove that its actual cost is bounded by this F.
Mathematical source: FDSA, July 27, 2026, Chapter 3, printed pp. 39–44.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.SelectionRecurrence

/-- The number of chunks of size five, retaining a final short chunk. -/
def pivotSize (n : Nat) : Nat := (n + 4) / 5

/-- The rounded upper bound for either strict selected side. -/
def sideSize (n : Nat) : Nat := (7 * n + 39) / 10

/-- The median list strictly decreases exactly above singleton size. -/
theorem pivotSize_lt_iff (n : Nat) : pivotSize n < n ↔ 1 < n := by
  unfold pivotSize
  omega

/-- The coarse strict-side scalar first decreases at size fourteen. -/
theorem sideSize_lt_iff (n : Nat) : sideSize n < n ↔ 13 < n := by
  unfold sideSize
  omega

theorem pivotSize_monotone : Monotone pivotSize := by
  intro m n h
  unfold pivotSize
  omega

theorem sideSize_monotone : Monotone sideSize := by
  intro m n h
  unfold sideSize
  omega

/-- FDSA's source majorant, including its deliberately coarse finite base. -/
def F (n : Nat) : Nat :=
  if h : n ≤ 20 then 483 else
    F (pivotSize n) + F (sideSize n) + 19 * n + 54
termination_by n
decreasing_by
  · exact (pivotSize_lt_iff n).mpr
      (lt_trans (by decide : 1 < 20) (Nat.lt_of_not_ge h))
  · exact (sideSize_lt_iff n).mpr
      (lt_trans (by decide : 13 < 20) (Nat.lt_of_not_ge h))

theorem F_of_le_twenty (n : Nat) (small : n ≤ 20) : F n = 483 := by
  rw [F]
  split
  · rfl
  · rename_i not_small
    exact (not_small small).elim

theorem F_of_twenty_lt (n : Nat) (large : 20 < n) :
    F n = F (pivotSize n) + F (sideSize n) + 19 * n + 54 := by
  rw [F]
  split
  · rename_i small
    exact ((not_le_of_gt large) small).elim
  · rfl

/-- Every recursive value still dominates the whole finite base. -/
theorem base_le_F (n : Nat) : 483 ≤ F n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      by_cases small : n ≤ 20
      · rw [F_of_le_twenty n small]
      · have large : 20 < n := Nat.lt_of_not_ge small
        have child := ih (pivotSize n) ((pivotSize_lt_iff n).mpr (by omega))
        rw [F_of_twenty_lt n large]
        omega

/-- Increasing the input size cannot decrease the actual scalar recurrence.
The recursive argument uses both child maps' monotonicity and strict decrease. -/
theorem F_monotone : Monotone F := by
  have comparison : ∀ n m : Nat, m ≤ n → F m ≤ F n := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro m hmn
        by_cases small_n : n ≤ 20
        · rw [F_of_le_twenty m (hmn.trans small_n), F_of_le_twenty n small_n]
        · by_cases small_m : m ≤ 20
          · rw [F_of_le_twenty m small_m]
            exact base_le_F n
          · have large_n : 20 < n := Nat.lt_of_not_ge small_n
            have large_m : 20 < m := Nat.lt_of_not_ge small_m
            have left := ih (pivotSize n) ((pivotSize_lt_iff n).mpr (by omega))
              (pivotSize m) (pivotSize_monotone hmn)
            have right := ih (sideSize n) ((sideSize_lt_iff n).mpr (by omega))
              (sideSize m) (sideSize_monotone hmn)
            rw [F_of_twenty_lt m large_m, F_of_twenty_lt n large_n]
            omega
  intro m n hmn
  exact comparison n m hmn

/-- The integer formula agrees with real ceiling also at zero. -/
theorem pivotSize_eq_ceil (n : Nat) :
    pivotSize n = ⌈(1 / 5 : ℝ) * (n : ℝ)⌉₊ := by
  apply Nat.le_antisymm
  · have bound := Nat.le_ceil ((1 / 5 : ℝ) * (n : ℝ))
    have cast_bound : (n : ℝ) ≤ 5 * (⌈(1 / 5 : ℝ) * (n : ℝ)⌉₊ : ℝ) := by
      linarith
    have natural_bound : n ≤ 5 * ⌈(1 / 5 : ℝ) * (n : ℝ)⌉₊ := by
      exact_mod_cast cast_bound
    unfold pivotSize
    omega
  · apply Nat.ceil_le.mpr
    have natural_bound : n ≤ 5 * pivotSize n := by unfold pivotSize; omega
    have cast_bound : (n : ℝ) ≤ 5 * (pivotSize n : ℝ) := by
      exact_mod_cast natural_bound
    linarith

/-- The additive three belongs inside the source ceiling. The integer formula
retains it even for small inputs where F instead takes its base branch. -/
theorem sideSize_eq_ceil (n : Nat) :
    sideSize n = ⌈(7 / 10 : ℝ) * (n : ℝ) + 3⌉₊ := by
  apply Nat.le_antisymm
  · have bound := Nat.le_ceil ((7 / 10 : ℝ) * (n : ℝ) + 3)
    have cast_bound : 7 * (n : ℝ) + 30 ≤
        10 * (⌈(7 / 10 : ℝ) * (n : ℝ) + 3⌉₊ : ℝ) := by linarith
    have natural_bound : 7 * n + 30 ≤ 10 * ⌈(7 / 10 : ℝ) * (n : ℝ) + 3⌉₊ := by
      exact_mod_cast cast_bound
    unfold sideSize
    omega
  · apply Nat.ceil_le.mpr
    have natural_bound : 7 * n + 30 ≤ 10 * sideSize n := by unfold sideSize; omega
    have cast_bound : 7 * (n : ℝ) + 30 ≤ 10 * (sideSize n : ℝ) := by
      exact_mod_cast natural_bound
    linarith

/-- Exact input to the general two-branch rounded-recurrence theorem. -/
theorem F_rounded (n : Nat) (large : 20 < n) :
    F n = F ⌈(1 / 5 : ℝ) * (n : ℝ) + 0⌉₊ +
      F ⌈(7 / 10 : ℝ) * (n : ℝ) + 3⌉₊ + 19 * n + 54 := by
  simpa only [pivotSize_eq_ceil, sideSize_eq_ceil, add_zero] using F_of_twenty_lt n large

/-- One pair of natural constants bounds every input, including the base and
zero. The actual F recurrence supplies the premise; no growth is assumed. -/
theorem exists_affine_bound : ∃ A B : Nat, ∀ n : Nat, F n ≤ A * n + B :=
  RoundedRecurrence.exists_affine_bound_nat F (1 / 5) 0 (7 / 10) 3 19 54 20
    (by norm_num) (by norm_num) (by norm_num) F_rounded

/-- The exact natural scalar has ordinary linear asymptotic growth after casting. -/
theorem F_isBigO :
    Asymptotics.IsBigO Filter.atTop (fun n : Nat => (F n : ℝ)) (fun n => (n : ℝ)) := by
  obtain ⟨A, B, bound⟩ := exists_affine_bound
  apply isBigO_of_nat_bound F (fun n => n) (A + B) 1
  intro n hn
  have constant : B ≤ B * n := by nlinarith
  calc
    F n ≤ A * n + B := bound n
    _ ≤ (A + B) * n := by nlinarith

end Resources.SelectionRecurrence

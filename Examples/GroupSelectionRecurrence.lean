import Applications.Resources.GroupSelectionRecurrence
import Applications.Resources.SelectionRecurrence

/-! Connected group-size boundaries and actual scalar recurrence instances.
These examples concern the declared scalar majorants. They do not identify
them with measured selection costs or infer impossibility from a coefficient.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.GroupSelectionRecurrence
open Resources.GroupSelectionRecurrence

theorem zero_requires_positive_domain : pivotFraction 0 + sideFraction 0 = 0 := by
  norm_num [pivotFraction, sideFraction]

theorem singleton_group : pivotFraction 1 + sideFraction 1 = (3 : ℝ) / 2 ∧
    ∀ n : Nat, pivotChild 1 n = n := by
  constructor
  · norm_num [pivotFraction, sideFraction]
  · exact pivotChild_one

theorem group_two : pivotFraction 2 + sideFraction 2 = (5 : ℝ) / 4 := by
  norm_num [pivotFraction, sideFraction]

/-- Equality only marks the boundary of this sufficient recurrence argument. -/
theorem groups_three_four :
    pivotFraction 3 + sideFraction 3 = 1 ∧ pivotFraction 4 + sideFraction 4 = 1 := by
  norm_num [pivotFraction, sideFraction]

theorem groups_five_six :
    pivotFraction 5 + sideFraction 5 = (9 : ℝ) / 10 ∧
      pivotFraction 6 + sideFraction 6 = (11 : ℝ) / 12 := by
  norm_num [pivotFraction, sideFraction]

theorem all_odd_even_thresholds (r : Nat) (hr : 0 < r) :
    (pivotFraction (2 * r + 1) + sideFraction (2 * r + 1) < 1 ↔ 2 ≤ r) ∧
      (pivotFraction (2 * r) + sideFraction (2 * r) < 1 ↔ 3 ≤ r) :=
  ⟨odd_contracts_iff r, even_contracts_iff r hr⟩

theorem explicit_cutoffs : cutoff 5 = 71 ∧ cutoff 6 = 97 ∧
    cutoff 7 = 64 ∧ cutoff 8 = 81 := by
  norm_num [cutoff, pivotFraction, sideFraction]

theorem first_five_children : pivotChild 5 72 = 15 ∧ sideChild 5 72 = 56 := by
  constructor
  · unfold pivotChild
    apply (Nat.ceil_eq_iff (by decide : (15 : Nat) ≠ 0)).mpr
    norm_num [pivotFraction]
  · unfold sideChild
    apply (Nat.ceil_eq_iff (by decide : (56 : Nat) ≠ 0)).mpr
    norm_num [sideFraction]

theorem first_six_children : pivotChild 6 98 = 17 ∧ sideChild 6 98 = 80 := by
  constructor
  · unfold pivotChild
    apply (Nat.ceil_eq_iff (by decide : (17 : Nat) ≠ 0)).mpr
    norm_num [pivotFraction]
  · unfold sideChild
    apply (Nat.ceil_eq_iff (by decide : (80 : Nat) ≠ 0)).mpr
    norm_num [sideFraction]

/-- Zero still uses the same finite base; an asymptotic conclusion need not
discard the base case from the stronger all-input affine bound. -/
theorem zero_base_value (d base slope constant : Nat) (hd : 5 ≤ d) :
    majorant d base slope constant hd 0 = base :=
  majorant_small d base slope constant hd 0 (Nat.zero_le _)

theorem last_five_base : majorant 5 1 2 3 (by decide) 71 = 1 :=
  majorant_small 5 1 2 3 (by decide) 71 (by norm_num [cutoff, pivotFraction, sideFraction])

/-- Both recursive children are actual base calls: 1+1+2*72+3=149. -/
theorem first_five_recurrence : majorant 5 1 2 3 (by decide) 72 = 149 := by
  rw [majorant_large 5 1 2 3 (by decide) 72
    (by norm_num [cutoff, pivotFraction, sideFraction])]
  rw [first_five_children.1, first_five_children.2]
  rw [majorant_small 5 1 2 3 (by decide) 15
      (by norm_num [cutoff, pivotFraction, sideFraction]),
    majorant_small 5 1 2 3 (by decide) 56
      (by norm_num [cutoff, pivotFraction, sideFraction])]

theorem first_six_recurrence : majorant 6 1 2 3 (by decide) 98 = 201 := by
  rw [majorant_large 6 1 2 3 (by decide) 98
    (by norm_num [cutoff, pivotFraction, sideFraction])]
  rw [first_six_children.1, first_six_children.2]
  rw [majorant_small 6 1 2 3 (by decide) 17
      (by norm_num [cutoff, pivotFraction, sideFraction]),
    majorant_small 6 1 2 3 (by decide) 80
      (by norm_num [cutoff, pivotFraction, sideFraction])]

/-- The generic two-group inequality also covers a short final chunk. -/
theorem short_final_group_bound (s : Nat)
    (h : s ≤ (5 / 2) * pivotChild 5 7 + (5 - 5 / 2) * (pivotChild 5 7 / 2)) :
    s ≤ sideChild 5 7 := two_group_bound_le_child 5 7 s (by decide) h

theorem zero_group_count_bound (d s : Nat) (hd : 0 < d)
    (h : s ≤ (d / 2) * pivotChild d 0 + (d - d / 2) * (pivotChild d 0 / 2)) :
    s ≤ sideChild d 0 := two_group_bound_le_child d 0 s hd h

/-- One fixed pair of constants also bounds every resized smaller input. -/
theorem uniform_resizing (d base slope constant : Nat) (hd : 5 ≤ d) :
    ∃ A B : Nat, ∀ m n : Nat, m ≤ n →
      majorant d base slope constant hd m ≤ A * n + B := by
  obtain ⟨A, B, bound⟩ := majorant_affine_bound d base slope constant hd
  exact ⟨A, B, fun m n h => (majorant_monotone d base slope constant hd h).trans (bound n)⟩

theorem positive_base_ne_all_input_linear (d base slope constant : Nat)
    (hd : 5 ≤ d) (hb : 0 < base) :
    ¬ ∃ C : Nat, ∀ n : Nat, majorant d base slope constant hd n ≤ C * n := by
  rintro ⟨C, h⟩
  have hzero := h 0
  rw [zero_base_value] at hzero
  omega

/-- Reuse the actual previously defined book recurrence, whose offset is
three; the conditional interface retains that exact offset. -/
theorem exact_book_F_specialization :
    ∃ A B : Nat, ∀ n : Nat, Resources.SelectionRecurrence.F n ≤ A * n + B := by
  apply rounded_group_affine_bound Resources.SelectionRecurrence.F 5 (by decide)
    0 3 19 54 20
  intro n large
  have left : pivotFraction 5 = (1 / 5 : ℝ) := rfl
  have right : sideFraction 5 = (7 / 10 : ℝ) := by norm_num [sideFraction]
  simpa only [left, right] using Resources.SelectionRecurrence.F_rounded n large

end Examples.GroupSelectionRecurrence

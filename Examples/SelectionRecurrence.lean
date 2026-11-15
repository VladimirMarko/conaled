import Applications.Resources.SelectionRecurrence

/-! Source constants, cutoff boundaries and uniform uses of the actual F.
These are scalar cases; no measured selector cost is asserted here. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SelectionRecurrence

open Resources.SelectionRecurrence

theorem zero_children : pivotSize 0 = 0 ∧ sideSize 0 = 3 := by
  decide +kernel

theorem scalar_cutoff_obstruction : sideSize 13 = 13 ∧ ¬ sideSize 13 < 13 := by
  norm_num [sideSize]

theorem scalar_cutoff_fourteen : pivotSize 14 < 14 ∧ sideSize 14 < 14 :=
  ⟨(pivotSize_lt_iff 14).mpr (by decide), (sideSize_lt_iff 14).mpr (by decide)⟩

theorem first_recursive_children : pivotSize 21 = 5 ∧ sideSize 21 = 18 := by
  decide +kernel

theorem F_zero : F 0 = 483 := F_of_le_twenty 0 (by decide)

theorem F_twenty : F 20 = 483 := F_of_le_twenty 20 (by decide)

/-- Both children remain in the base: 483+483+399+54=1419. -/
theorem F_twenty_one : F 21 = 1419 := by
  rw [F_of_twenty_lt 21 (by decide)]
  change F 5 + F 18 + 399 + 54 = 1419
  rw [F_of_le_twenty 5 (by decide), F_of_le_twenty 18 (by decide)]

/-- A changed rounded size still uses the same coarse finite base. -/
theorem F_twenty_two : F 22 = 1438 := by
  rw [F_of_twenty_lt 22 (by decide)]
  change F 5 + F 19 + 418 + 54 = 1438
  rw [F_of_le_twenty 5 (by decide), F_of_le_twenty 19 (by decide)]

theorem first_recursive_is_not_base : F 21 ≠ 483 := by
  rw [F_twenty_one]
  decide

/-- The symbolic monotonicity law crosses the base/recursive boundary. -/
theorem resize_across_cutoff : F 17 ≤ F 29 := F_monotone (by decide)

/-- One pair of constants works uniformly for every smaller child size.
This is the composition later needed by balance-based cost arguments. -/
theorem all_smaller_children_uniform :
    ∃ A B : Nat, ∀ n m : Nat, m ≤ n → F m ≤ A * n + B := by
  obtain ⟨A, B, bound⟩ := exists_affine_bound
  exact ⟨A, B, fun n m h => (F_monotone h).trans (bound n)⟩

/-- An all-input bound cannot discard the intercept because F(0)=483. -/
theorem zero_requires_intercept (A : Nat) : ¬ ∀ n : Nat, F n ≤ A * n := by
  intro bound
  have impossible := bound 0
  rw [F_zero] at impossible
  omega

end Examples.SelectionRecurrence

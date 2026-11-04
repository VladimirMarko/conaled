import Applications.Selection.CountRank

/-! Duplicate-aware selection, source-error witnesses, and rank transport. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SelectionCountRank
open Applications.Selection

/-- In [1,2,2,3], both middle occurrences have value 2. Strict counts are one
on either side, although the two occurrence indices differ. -/
theorem duplicate_lower_rank : RankedAt ([1, 2, 2, 3] : List Nat) 1 2 :=
  ranked_iff_count_bounds.mpr (by decide)

theorem duplicate_upper_rank : RankedAt ([1, 2, 2, 3] : List Nat) 2 2 :=
  ranked_iff_count_bounds.mpr (by decide)

theorem duplicate_bounds :
    ([1, 2, 2, 3] : List Nat).countP (fun x => decide (x < 2)) ≤ 2 ∧
      ([1, 2, 2, 3] : List Nat).countP (fun x => decide (2 < x)) < 4 - 2 :=
  duplicate_upper_rank.count_bounds

theorem duplicate_public_selection : selectWith lastPivot 3 [1, 2, 2, 3] = some 2 :=
  (selectWith_succ_some_iff_count_bounds _ last_pivot_valid _ 2 2).mpr
    duplicate_bounds

/-- Replacing the strict upper count by a weak bound admits a value absent
from the input. This is the source p31 prose error, not an alternate contract. -/
theorem weak_upper_count_is_insufficient :
    ([0, 2] : List Nat).countP (fun x => decide (x < 1)) ≤ 1 ∧
    ([0, 2] : List Nat).countP (fun x => decide (1 < x)) ≤ 2 - 1 ∧
    ¬RankedAt ([0, 2] : List Nat) 1 1 := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  exact (by decide : ¬(([0, 2] : List Nat).countP (fun x => decide (1 < x)) < 2 - 1))
    h.count_bounds.2

theorem zero_book_rank_is_public_one : selectWith List.head? 1 [3, 1, 2] = some 1 := by
  rw [selectWith_succ_value _ head_pivot_valid _ 0, ordered_getElem?_zero_iff_min]
  decide

theorem smallest_is_not_largest : selectWith List.head? 1 [1, 3] = some 1 := by
  rw [selectWith_succ_value _ head_pivot_valid _ 0, ordered_getElem?_zero_iff_min]
  decide

theorem invalid_count_bounds {a : Nat} : ¬RankedAt [] 0 a := by
  intro h
  have := h.lt_length
  simp at this

/-- A pivot outside the input need not have an equal block, although its
semantic selection recurrence is still valid. -/
theorem outside_pivot_equal_block : (partition3 2 ([1] : List Nat)).2.1 = [] := by
  rw [partition3_eq_filters]
  rfl

theorem outside_pivot_value :
    (ordered ([1] : List Nat))[0]? = (ordered (partition3 2 [1]).1)[0]? := by
  rw [ordered_getElem?_partition 2 [1] 0]
  have h : 0 < (partition3 2 ([1] : List Nat)).1.length := by
    rw [partition3_eq_filters]
    decide
  rw [ite_eq_left h]

theorem equal_occurrence_branch :
    (ordered ([3, 2, 2, 1] : List Nat))[2]? = some 2 := by
  rw [ordered_getElem?_partition 2 [3, 2, 2, 1] 2]
  have hl : ¬2 < (partition3 2 ([3, 2, 2, 1] : List Nat)).1.length := by
    rw [partition3_eq_filters]
    decide
  have he : 2 < (partition3 2 ([3, 2, 2, 1] : List Nat)).1.length +
      (partition3 2 ([3, 2, 2, 1] : List Nat)).2.1.length := by
    rw [partition3_eq_filters]
    decide
  rw [ite_eq_right hl, ite_eq_left he]

theorem ordered_blocks :
    ordered ([2, 1] ++ [4, 3] : List Nat) = ordered [2, 1] ++ ordered [4, 3] :=
  ordered_append _ _ (by decide)

theorem ordered_blocks_invalid_index :
    (ordered ([2, 1] ++ [4, 3] : List Nat))[7]? = (ordered [4, 3])[5]? := by
  rw [ordered_getElem?_append _ _ (by decide) 7]
  rfl

theorem duplicate_lower_median : lowerMedianWith List.head? ([1, 1] : List Nat) = some 1 := by
  rw [lowerMedian_value _ head_pivot_valid]
  apply ranked_iff_index.mp
  exact ranked_iff_count_bounds.mpr (by decide)

theorem duplicate_median_counts :
    ([1, 1] : List Nat).countP (fun x => decide (x < 1)) ≤ 0 ∧
      ([1, 1] : List Nat).countP (fun x => decide (1 < x)) ≤ 1 :=
  lowerMedian_count_bounds _ head_pivot_valid _ _ duplicate_lower_median

/-- A monotone relabeling can create ties and still preserves the count
specification through the existing occurrence-rank transport law. -/
theorem monotone_count_transport {α β : Type} [LinearOrder α] [LinearOrder β]
    (f : α → β) (hf : Monotone f) (xs : List α) (k : Nat) (a : α)
    (h : xs.countP (fun x => decide (x < a)) ≤ k ∧
      xs.countP (fun x => decide (a < x)) < xs.length - k) :
    (xs.map f).countP (fun y => decide (y < f a)) ≤ k ∧
      (xs.map f).countP (fun y => decide (f a < y)) < (xs.map f).length - k :=
  ((ranked_iff_count_bounds.mpr h).map f hf).count_bounds

end Examples.SelectionCountRank

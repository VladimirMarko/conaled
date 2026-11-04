import Applications.Resources.SelectionAuxiliary

/-! Connected insertion-selection cases for the Chapter 3 source tariff.
Counts are calculated from recursive insertion, valid lookup and length calls.
In particular, equal returned order statistics need not have equal work.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SelectionAuxiliary
open Resources.SelectionAuxiliary
open Applications.Selection
universe u

theorem empty_payload_selection : slowSelectRun 17 ([] : List (Fin 0)) = (none, 2) := by
  apply Prod.ext
  · exact (slowSelectRun_none 17 ([] : List (Fin 0))).mpr (by decide)
  · rw [slowSelectRun_cost]
    rfl

theorem singleton_selection : slowSelectRun 0 [7] = (some 7, 4) := by
  apply Prod.ext
  · rw [slowSelectRun_value]
    simpa only [ordered, Applications.Sorting.sortOn_eq_insertionOn] using
      (show (Applications.Sorting.insertionOn id ([7] : List Nat))[0]? = some 7 by
        decide +kernel)
  · rw [slowSelectRun_cost_of_lt 0 [7] (by decide)]
    rfl

theorem singleton_invalid : slowSelectRun 1 [7] = (none, 5) ∧
    slowSelectRun 17 [7] = (none, 5) := by
  constructor <;> apply Prod.ext
  · exact (slowSelectRun_none 1 [7]).mpr (by decide)
  · rw [slowSelectRun_cost]
    rfl
  · exact (slowSelectRun_none 17 [7]).mpr (by decide)
  · rw [slowSelectRun_cost]
    rfl

theorem public_rank_bridge {α : Type u} [LinearOrder α] (k : Nat) (xs : List α) :
    (slowSelectRun k xs).1 = sortSelect (k + 1) xs := slowSelectRun_public k xs

theorem duplicate_occurrence_rank : RankedAt [3, 1, 3, 2] 2 3 := by
  apply (slowSelectRun_some_iff 2 [3, 1, 3, 2] 3).mp
  rw [slowSelectRun_value]
  simpa only [ordered, Applications.Sorting.sortOn_eq_insertionOn] using
    (show (Applications.Sorting.insertionOn id ([3, 1, 3, 2] : List Nat))[2]? = some 3 by
      decide +kernel)

/-- A relabeling can merge all keys; this makes no claim about cost transport. -/
theorem collapsed_occurrence_rank : RankedAt [0, 0, 0, 0] 2 0 := by
  exact duplicate_occurrence_rank.map (fun _ : Nat => (0 : Nat)) (fun _ _ _ => le_rfl)

theorem valid_selection_budget {α : Type u} [LinearOrder α]
    (xs : List α) (k : Nat) (hk : k < xs.length) :
    (slowSelectRun k xs).2 ≤ xs.length ^ 2 + 3 * xs.length + 1 :=
  slowSelectRun_cost_bound k xs hk

theorem empty_payload_median : slowMedianRun ([] : List (Fin 0)) = (none, 3) := by
  apply Prod.ext
  · exact (slowMedianRun_none _).mpr rfl
  · rw [slowMedianRun_cost, Resources.SymmetricCosts.lengthRun_exact, slowSelectRun_cost]
    rfl

theorem singleton_median : slowMedianRun [7] = (some 7, 6) := by
  apply Prod.ext
  · rw [slowMedianRun_value, lowerMedian_value List.head? head_pivot_valid]
    simpa only [ordered, Applications.Sorting.sortOn_eq_insertionOn] using
      (show (Applications.Sorting.insertionOn id ([7] : List Nat))[0]? = some 7 by
        decide +kernel)
  · rw [slowMedianRun_cost, Resources.SymmetricCosts.lengthRun_exact, slowSelectRun_cost]
    rfl

theorem lower_even_median : slowMedianRun [7, 2] = (some 2, 10) := by
  apply Prod.ext
  · rw [slowMedianRun_value, lowerMedian_value List.head? head_pivot_valid]
    simpa only [ordered, Applications.Sorting.sortOn_eq_insertionOn] using
      (show (Applications.Sorting.insertionOn id ([7, 2] : List Nat))[0]? = some 2 by
        decide +kernel)
  · rw [slowMedianRun_cost, Resources.SymmetricCosts.lengthRun_exact, slowSelectRun_cost]
    rfl

theorem repeated_central_values : slowMedianRun [4, 4] = (some 4, 9) := by
  apply Prod.ext
  · rw [slowMedianRun_value, lowerMedian_value List.head? head_pivot_valid]
    simpa only [ordered, Applications.Sorting.sortOn_eq_insertionOn] using
      (show (Applications.Sorting.insertionOn id ([4, 4] : List Nat))[0]? = some 4 by
        decide +kernel)
  · rw [slowMedianRun_cost, Resources.SymmetricCosts.lengthRun_exact, slowSelectRun_cost]
    rfl

theorem ascending_five_median : slowMedianRun (List.range 5) = (some 2, 20) := by
  apply Prod.ext
  · rw [slowMedianRun_value, lowerMedian_value List.head? head_pivot_valid]
    simpa only [ordered, Applications.Sorting.sortOn_eq_insertionOn] using
      (show (Applications.Sorting.insertionOn id (List.range 5))[2]? = some 2 by
        decide +kernel)
  · rw [slowMedianRun_cost, Resources.SymmetricCosts.lengthRun_exact,
      slowSelectRun_cost_of_pairwise _ _ (by decide) (by decide)]
    rfl

theorem descending_five_median : slowMedianRun (List.range 5).reverse = (some 2, 30) := by
  apply Prod.ext
  · rw [slowMedianRun_value, lowerMedian_value List.head? head_pivot_valid]
    simpa only [ordered, Applications.Sorting.sortOn_eq_insertionOn] using
      (show (Applications.Sorting.insertionOn id (List.range 5).reverse)[2]? = some 2 by
        decide +kernel)
  · rw [slowMedianRun_cost, Resources.SymmetricCosts.lengthRun_exact,
      slowSelectRun_cost_reverse_range 5 _ (by decide)]
    rfl

theorem same_median_different_work :
    (slowMedianRun (List.range 5)).1 = (slowMedianRun (List.range 5).reverse).1 ∧
      (slowMedianRun (List.range 5)).2 < (slowMedianRun (List.range 5).reverse).2 := by
  rw [ascending_five_median, descending_five_median]
  decide

theorem arbitrary_short_chunk {α : Type u} [LinearOrder α]
    (xs : List α) (hx : xs ≠ []) (hn : xs.length ≤ 5) :
    (slowMedianRun xs).2 ≤ 47 := slowMedianRun_small_bound xs hx hn

theorem singleton_short_chunk : (slowMedianRun [9]).2 ≤ 47 :=
  arbitrary_short_chunk [9] (by decide) (by decide)

theorem median_value_and_budget {α : Type u} [LinearOrder α]
    (xs : List α) (a : α) (ha : (slowMedianRun xs).1 = some a) :
    RankedAt xs ((xs.length - 1) / 2) a ∧ a ∈ xs ∧
      (slowMedianRun xs).2 ≤ xs.length ^ 2 + 4 * xs.length + 2 := by
  have hx : xs ≠ [] := by
    intro he
    have hnone := (slowMedianRun_none xs).mpr he
    rw [hnone] at ha
    contradiction
  exact ⟨(slowMedianRun_some_iff xs a).mp ha, slowMedianRun_mem xs a ha,
    slowMedianRun_cost_bound xs hx⟩

theorem cutoff_sorted_last :
    1 + (Resources.SymmetricCosts.lengthRun (List.range 20)).2 +
      (slowSelectRun 19 (List.range 20)).2 = 83 := by
  rw [Resources.SymmetricCosts.lengthRun_exact,
    slowSelectRun_cost_of_pairwise 19 _ (by decide) (by decide)]
  rfl

theorem cutoff_descending_last :
    1 + (Resources.SymmetricCosts.lengthRun (List.range 20).reverse).2 +
      (slowSelectRun 19 (List.range 20).reverse).2 = 273 := by
  rw [Resources.SymmetricCosts.lengthRun_exact,
    slowSelectRun_cost_reverse_range 20 19 (by decide)]
  rfl

theorem cutoff_uniform_budget {α : Type u} [LinearOrder α]
    (xs : List α) (k : Nat) (hk : k < xs.length) (hn : xs.length ≤ 20) :
    1 + (Resources.SymmetricCosts.lengthRun xs).2 + (slowSelectRun k xs).2 ≤ 483 :=
  slowSelectRun_cutoff_bound k xs hk hn

end Examples.SelectionAuxiliary

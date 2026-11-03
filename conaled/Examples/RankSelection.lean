import Applications.Selection.Consumers

/-! Public rank, adequacy, policy and consumer contracts on checked inputs. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.RankSelection
open Applications.Selection

-- Empty-input behavior is independent of what a valid policy does on [].
def eccentricHead (xs : List Nat) : Option Nat :=
  if xs = [] then some 99 else xs.head?

theorem eccentric_valid : PivotValid eccentricHead := by
  intro xs hn
  simpa [eccentricHead, hn] using head_pivot_valid xs hn

example : selectWith eccentricHead 1 [] = none :=
  (selectWith_none eccentricHead eccentric_valid [] 1).mpr (by simp)

example : runWith eccentricHead 1 0 [] = none := rfl

example : selectWith List.head? 1 [7] = some 7 := by
  rw [selectWith_eq_sortSelect _ head_pivot_valid]
  simp only [sortSelect, ordered, Applications.Sorting.sortOn_eq_insertionOn]
  decide +kernel

example : selectWith List.head? 0 [1, 2, 3] = none :=
  (selectWith_none _ head_pivot_valid _ _).mpr (Or.inl rfl)

example : selectWith lastPivot 5 [1, 2, 2, 3] = none :=
  (selectWith_none _ last_pivot_valid _ _).mpr (Or.inr (by decide))

example : selectWith List.head? 1 [4, 1, 3, 2] = some 1 := by
  rw [selectWith_eq_sortSelect _ head_pivot_valid]
  simp only [sortSelect, ordered, Applications.Sorting.sortOn_eq_insertionOn]
  decide +kernel

example : selectWith lastPivot 4 [4, 1, 3, 2] = some 4 := by
  rw [selectWith_eq_sortSelect _ last_pivot_valid]
  simp only [sortSelect, ordered, Applications.Sorting.sortOn_eq_insertionOn]
  decide +kernel

example : selectWith lastPivot 3 [5, 5, 5, 5] = some 5 := by
  rw [selectWith_eq_sortSelect _ last_pivot_valid]
  simp only [sortSelect, ordered, Applications.Sorting.sortOn_eq_insertionOn]
  decide +kernel

theorem duplicate_rank : RankedAt ([1, 2, 2, 3] : List Nat) 2 2 :=
  ranked_iff_index.mpr (by
    simp only [ordered, Applications.Sorting.sortOn_eq_insertionOn]
    decide +kernel)

theorem duplicate_selection : selectWith List.head? 3 [1, 2, 2, 3] = some 2 :=
  (selectWith_some_iff _ head_pivot_valid _ _ _).mpr ⟨by decide, duplicate_rank⟩

-- Positional rank counts occurrences; the strict count needs the Nodup premise.
example : selectWith List.head? 3 [1, 2, 2, 3] = some 2 ∧
    ([1, 2, 2, 3] : List Nat).countP (fun x => decide (x < 2)) = 1 ∧
    ([1, 2, 2, 3] : List Nat).countP (fun x => decide (x < 2)) ≠ 3 - 1 :=
  ⟨duplicate_selection, by decide, by decide⟩

example : selectWith lastPivot 3 [1, 2, 2, 3] = some 2 := by
  rw [selectWith_policy _ List.head? last_pivot_valid head_pivot_valid]
  exact duplicate_selection

example : selectWith List.head? 2 [true, false, true] = some true := by
  rw [selectWith_eq_sortSelect _ head_pivot_valid]
  simp only [sortSelect, ordered, Applications.Sorting.sortOn_eq_insertionOn]
  decide +kernel

-- Inadequate administrative fuel can fail even when the public rank exists.
example : runWith List.head? 0 2 ([1, 2, 2, 3] : List Nat) = none ∧
    selectWith List.head? 3 [1, 2, 2, 3] = some 2 := ⟨rfl, duplicate_selection⟩

example : runWith lastPivot 4 2 ([1, 2, 2, 3] : List Nat) = some 2 := by
  rw [runWith_value _ last_pivot_valid _ _ (by decide)]
  exact ranked_iff_index.mp duplicate_rank

theorem even_median : lowerMedianWith lastPivot ([8, 1, 7, 2] : List Nat) = some 2 := by
  rw [lowerMedian_even_index _ last_pivot_valid _ 2 (by decide) (by decide)]
  simp only [ordered, Applications.Sorting.sortOn_eq_insertionOn]
  decide +kernel

example : ([8, 1, 7, 2] : List Nat).countP (fun x => decide (x < 2)) = 1 ∧
    ([8, 1, 7, 2] : List Nat).countP (fun x => decide (2 < x)) = 2 :=
  lowerMedian_even_counts _ last_pivot_valid _ _ 2 (by decide) (by decide) even_median

theorem odd_median : lowerMedianWith List.head? ([7, 2, 4] : List Nat) = some 4 := by
  rw [lowerMedian_odd_index _ head_pivot_valid _ 1 (by decide)]
  simp only [ordered, Applications.Sorting.sortOn_eq_insertionOn]
  decide +kernel

example : ([7, 2, 4] : List Nat).countP (fun x => decide (x < 4)) = 1 ∧
    ([7, 2, 4] : List Nat).countP (fun x => decide (4 < x)) = 1 :=
  lowerMedian_odd_counts _ head_pivot_valid _ _ 1 (by decide) (by decide) odd_median

example : lowerMedianWith lastPivot ([] : List Nat) = none :=
  (lowerMedian_none _ last_pivot_valid []).mpr rfl

-- Division by two identifies adjacent values but preserves order and rank values.
theorem halve_monotone : Monotone (fun x : Nat => x / 2) :=
  fun _ _ h => Nat.div_le_div_right h

example : ¬Function.Injective (fun x : Nat => x / 2) := by
  intro h
  have := h (a₁ := 0) (a₂ := 1) (by decide)
  omega

example : RankedAt (([1, 2, 2, 3] : List Nat).map (· / 2)) 2 1 :=
  duplicate_rank.map (fun x => x / 2) halve_monotone

example : selectWith lastPivot 3 (([1, 2, 2, 3] : List Nat).map (· / 2)) = some 1 := by
  rw [selectWith_map List.head? lastPivot head_pivot_valid last_pivot_valid
    (fun x => x / 2) halve_monotone, duplicate_selection]
  rfl

example {a : Nat} (h : RankedAt [1, 2, 2, 3] 2 a) : a = 2 :=
  h.unique duplicate_rank

end Examples.RankSelection

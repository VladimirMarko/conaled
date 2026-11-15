import Applications.Resources.SelectionGenericBounds
import Examples.SelectionGenericEnvelope
import Examples.GroupSelectionRecurrence

/-! Connected generic selection bounds at both cutoff orderings.

The scalar budgets are computed independently from the two rounded children
and the actual local tariff. They remain upper budgets, not exact execution
counts. Values are connected through the checked worker correspondence; the
previously checked count 269 and the invalid/empty equations are retained.
The groups three/four equality case concerns the sufficient recurrence only.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SelectionGenericBounds
open Applications.Selection
open Resources.Selection Resources.SelectionEnvelope
universe u

private theorem range_value (d cutoff : Nat) (hd : 2 ≤ d) (hc : 1 ≤ cutoff)
    (n k : Nat) (hk : k < n) :
    (selectRunWith d cutoff hd hc k (List.range n)).1 = some k := by
  have sorted : ordered (List.range n) = List.range n :=
    ordered_eq_of_pairwise_perm List.pairwise_le_range (List.Perm.refl _)
  rw [selectRunWith_value, sorted]
  exact List.getElem?_range hk

private theorem first_five_scalar :
    genericSelectionMajorant 5 1 (by decide) 72 = 2 * envelope 5 71 + 4111 := by
  have cut : Resources.GroupSelectionRecurrence.cutoff 5 = 71 :=
    Examples.GroupSelectionRecurrence.explicit_cutoffs.1
  have base : genericSelectionBase 5 1 = envelope 5 71 := by
    simp only [genericSelectionBase, cut, show max (1 : Nat) 71 = 71 from by decide]
  rw [genericSelectionMajorant_large 5 1 (by decide) 72 (by omega),
    Examples.GroupSelectionRecurrence.first_five_children.1,
    Examples.GroupSelectionRecurrence.first_five_children.2,
    genericSelectionMajorant_small 5 1 (by decide) 15 (by omega),
    genericSelectionMajorant_small 5 1 (by decide) 56 (by omega), base]
  norm_num [tollCoefficient]; omega

private theorem first_six_scalar :
    genericSelectionMajorant 6 1 (by decide) 98 = 2 * envelope 6 97 + 7063 := by
  have cut : Resources.GroupSelectionRecurrence.cutoff 6 = 97 :=
    Examples.GroupSelectionRecurrence.explicit_cutoffs.2.1
  have base : genericSelectionBase 6 1 = envelope 6 97 := by
    simp only [genericSelectionBase, cut, show max (1 : Nat) 97 = 97 from by decide]
  rw [genericSelectionMajorant_large 6 1 (by decide) 98 (by omega),
    Examples.GroupSelectionRecurrence.first_six_children.1,
    Examples.GroupSelectionRecurrence.first_six_children.2,
    genericSelectionMajorant_small 6 1 (by decide) 17 (by omega),
    genericSelectionMajorant_small 6 1 (by decide) 80 (by omega), base]
  norm_num [tollCoefficient]; omega

/-- Empty inputs need the affine or scalar statement: their actual cost is two. -/
theorem empty_every_sufficient_group (d cutoff : Nat) (hd : 2 ≤ d)
    (hc : 1 ≤ cutoff) (hgroup : 5 ≤ d) (k : Nat) :
    selectRunWith d cutoff hd hc k ([] : List (Fin 0)) = (none, 2) ∧
      (selectRunWith d cutoff hd hc k ([] : List (Fin 0))).2 ≤
        genericSelectionMajorant d cutoff hgroup 0 := by
  constructor
  · exact selectRunWith_nil d cutoff hd hc k
  · simpa only [List.length_nil] using
      selectRunWith_cost_le_groupMajorant d cutoff hd hc hgroup k ([] : List (Fin 0))

theorem five_repeated_prefix :
    (selectRunWith 5 1 (by decide) (by decide) 2 ([3, 1, 2, 2] : List Nat)).1 = some 2 ∧
      genericSelectionMajorant 5 1 (by decide) 4 = envelope 5 71 ∧
      (selectRunWith 5 1 (by decide) (by decide) 2 ([3, 1, 2, 2] : List Nat)).2 ≤
        genericSelectionMajorant 5 1 (by decide) 4 := by
  have cut : Resources.GroupSelectionRecurrence.cutoff 5 = 71 :=
    Examples.GroupSelectionRecurrence.explicit_cutoffs.1
  refine ⟨Examples.SelectionGenericEnvelope.group_five_budget.1, ?_, ?_⟩
  · rw [genericSelectionMajorant_small 5 1 (by decide) 4 (by omega)]
    simp only [genericSelectionBase, cut, show max (1 : Nat) 71 = 71 from by decide]
  · simpa only [List.length_cons, List.length_nil] using
      selectRunWith_cost_le_groupMajorant 5 1 (by decide) (by decide) (by decide)
        2 ([3, 1, 2, 2] : List Nat)

theorem six_repeated_prefix :
    (selectRunWith 6 1 (by decide) (by decide) 2 ([3, 1, 2, 2] : List Nat)).1 = some 2 ∧
      genericSelectionMajorant 6 1 (by decide) 4 = envelope 6 97 ∧
      (selectRunWith 6 1 (by decide) (by decide) 2 ([3, 1, 2, 2] : List Nat)).2 ≤
        genericSelectionMajorant 6 1 (by decide) 4 := by
  have cut : Resources.GroupSelectionRecurrence.cutoff 6 = 97 :=
    Examples.GroupSelectionRecurrence.explicit_cutoffs.2.1
  refine ⟨Examples.SelectionGenericEnvelope.group_six_budget.1, ?_, ?_⟩
  · rw [genericSelectionMajorant_small 6 1 (by decide) 4 (by omega)]
    simp only [genericSelectionBase, cut, show max (1 : Nat) 97 = 97 from by decide]
  · simpa only [List.length_cons, List.length_nil] using
      selectRunWith_cost_le_groupMajorant 6 1 (by decide) (by decide) (by decide)
        2 ([3, 1, 2, 2] : List Nat)

/-- The book selector already recurses at 21, while this generic scalar is
still in its finite prefix. Its exact checked cost remains 269. -/
theorem book_recurses_inside_scalar_prefix :
    selectRun 0 (List.range 21) = (some 0, 269) ∧
      genericSelectionMajorant 5 20 (by decide) 21 = envelope 5 71 ∧
      (selectRun 0 (List.range 21)).2 ≤ genericSelectionMajorant 5 20 (by decide) 21 := by
  have cut : Resources.GroupSelectionRecurrence.cutoff 5 = 71 :=
    Examples.GroupSelectionRecurrence.explicit_cutoffs.1
  refine ⟨Examples.SelectionCosts.first_recursive_left, ?_, ?_⟩
  · rw [genericSelectionMajorant_small 5 20 (by decide) 21 (by omega)]
    simp only [genericSelectionBase, cut, show max (20 : Nat) 71 = 71 from by decide]
  · simpa only [selectRun, List.length_range] using
      selectRunWith_cost_le_groupMajorant 5 20 (by decide) (by decide) (by decide)
        0 (List.range 21)

/-- Children 15 and 56 use the base; the actual local budget is 57*72+7. -/
theorem first_five_recursive_budget :
    (selectRunWith 5 1 (by decide) (by decide) 0 (List.range 72)).1 = some 0 ∧
      (selectRunWith 5 1 (by decide) (by decide) 0 (List.range 72)).2 ≤
        2 * envelope 5 71 + 4111 := by
  constructor
  · exact range_value 5 1 (by decide) (by decide) 72 0 (by decide)
  · simpa only [List.length_range, first_five_scalar] using
      selectRunWith_cost_le_groupMajorant 5 1 (by decide) (by decide) (by decide)
        0 (List.range 72)

/-- The first even sufficient size has children 17 and 80, and toll 72*98+7. -/
theorem first_six_recursive_budget :
    (selectRunWith 6 1 (by decide) (by decide) 97 (List.range 98)).1 = some 97 ∧
      (selectRunWith 6 1 (by decide) (by decide) 97 (List.range 98)).2 ≤
        2 * envelope 6 97 + 7063 := by
  constructor
  · exact range_value 6 1 (by decide) (by decide) 98 97 (by decide)
  · simpa only [List.length_range, first_six_scalar] using
      selectRunWith_cost_le_groupMajorant 6 1 (by decide) (by decide) (by decide)
        97 (List.range 98)

/-- At size 80 the actual cutoff 100 gives a small branch, while the scalar
cutoff 71 is already exceeded. The finite base must use the larger cutoff. -/
theorem actual_cutoff_above_scalar :
    Resources.GroupSelectionRecurrence.cutoff 5 < 80 ∧
      (selectRunWith 5 100 (by decide) (by decide) 0 (List.range 80)).1 = some 0 ∧
      (selectRunWith 5 100 (by decide) (by decide) 0 (List.range 80)).2 ≤ envelope 5 100 ∧
      (selectRunWith 5 100 (by decide) (by decide) 0 (List.range 80)).2 ≤
        genericSelectionMajorant 5 100 (by decide) 80 := by
  have cut : Resources.GroupSelectionRecurrence.cutoff 5 = 71 :=
    Examples.GroupSelectionRecurrence.explicit_cutoffs.1
  refine ⟨by omega, range_value 5 100 (by decide) (by decide) 80 0 (by decide), ?_, ?_⟩
  · have hprefix := selectRunWith_cost_le_groupBase_of_prefix 5 100 (by decide) (by decide)
      0 (List.range 80) (Or.inl (by
        simpa only [List.length_range] using (show (80 : Nat) ≤ 100 from by decide)))
    simpa only [genericSelectionBase, cut, show max (100 : Nat) 71 = 100 from by decide]
      using hprefix
  · simpa only [List.length_range] using
      selectRunWith_cost_le_groupMajorant 5 100 (by decide) (by decide) (by decide)
        0 (List.range 80)

theorem invalid_above_scalar :
    selectRunWith 5 1 (by decide) (by decide) 72 (List.range 72) = (none, 74) ∧
      (selectRunWith 5 1 (by decide) (by decide) 72 (List.range 72)).2 ≤
        2 * envelope 5 71 + 4111 := by
  constructor
  · simpa only [List.length_range] using
      selectRunWith_of_invalid 5 1 (by decide) (by decide) 72 (List.range 72)
        (by simp only [List.length_range, Nat.le_refl])
  · simpa only [List.length_range, first_five_scalar] using
      selectRunWith_cost_le_groupMajorant 5 1 (by decide) (by decide) (by decide)
        72 (List.range 72)

/-- Coefficient equality at three/four leaves their checked value correctness
intact. It supplies no impossibility theorem about running time. -/
theorem three_four_threshold_semantics :
    Resources.GroupSelectionRecurrence.pivotFraction 3 +
        Resources.GroupSelectionRecurrence.sideFraction 3 = 1 ∧
      Resources.GroupSelectionRecurrence.pivotFraction 4 +
        Resources.GroupSelectionRecurrence.sideFraction 4 = 1 ∧
      (selectRunWith 3 1 (by decide) (by decide) 2 ([3, 1, 2, 2] : List Nat)).1 = some 2 ∧
      (selectRunWith 4 1 (by decide) (by decide) 2 ([3, 1, 2, 2] : List Nat)).1 = some 2 :=
  ⟨Examples.GroupSelectionRecurrence.groups_three_four.1,
    Examples.GroupSelectionRecurrence.groups_three_four.2,
    Examples.SelectionGenericEnvelope.group_three_budget.1,
    Examples.SelectionGenericEnvelope.group_four_budget.1⟩

theorem odd_sufficient_uniform_family (r cutoff : Nat) (hr : 2 ≤ r) (hc : 1 ≤ cutoff) :
    ∃ C : Nat, ∀ (β : Type u) [LinearOrder β] (xs : List β) (k : Nat),
      0 < xs.length →
        (selectRunWith (2 * r + 1) cutoff (by omega) hc k xs).2 ≤ C * xs.length :=
  selectRunWith_exists_uniform_linear_bound (2 * r + 1) cutoff (by omega) hc (by omega)

theorem even_sufficient_uniform_family (r cutoff : Nat) (hr : 3 ≤ r) (hc : 1 ≤ cutoff) :
    ∃ C : Nat, ∀ (β : Type u) [LinearOrder β] (xs : List β) (k : Nat),
      0 < xs.length →
        (selectRunWith (2 * r) cutoff (by omega) hc k xs).2 ≤ C * xs.length :=
  selectRunWith_exists_uniform_linear_bound (2 * r) cutoff (by omega) hc (by omega)

theorem six_duplicate_integer_family (cutoff : Nat) (hc : 1 ≤ cutoff) :
    ∃ C : Nat, ∀ n k : Nat, 0 < n →
      (selectRunWith 6 cutoff (by decide) hc k (List.replicate n (4 : Int))).2 ≤ C * n := by
  obtain ⟨C, bound⟩ :=
    selectRunWith_exists_uniform_linear_bound 6 cutoff (by decide) hc (by decide)
  refine ⟨C, ?_⟩
  intro n k hn
  have h := bound Int (List.replicate n (4 : Int)) k
    (by simpa only [List.length_replicate] using hn)
  simpa only [List.length_replicate] using h

theorem five_descending_family (cutoff : Nat) (hc : 1 ≤ cutoff) :
    Asymptotics.IsBigO Filter.atTop
      (fun n : Nat =>
        ((selectRunWith 5 cutoff (by decide) hc (n - 1) (List.range n).reverse).2 : ℝ))
      (fun n => (n : ℝ)) :=
  selectRunWith_family_isBigO 5 cutoff (by decide) hc (by decide)
    (fun n => (List.range n).reverse) (fun n => n - 1)
    (by intro n; simp only [List.length_reverse, List.length_range])

end Examples.SelectionGenericBounds

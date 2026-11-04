import Applications.Resources.Selection
import Examples.SelectionMedians

/-! Checked applications of the nested selector's public execution equations.

The finite targets were calculated from the source phases before this module.
At size twenty-one, the left/equal/right cases cost 269/231/266. The left
branch omits the equal-length traversal; the equal branch omits the selected
child. These applications never unfold the private worker or its proof terms.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SelectionCosts
open Applications.Selection
open Resources.Selection Resources.SelectionAuxiliary Resources.SelectionMedians
universe u v

private theorem singleton_with (d cutoff : Nat) (hd : 2 ≤ d) (hc : 1 ≤ cutoff)
    (a : Nat) : selectRunWith d cutoff hd hc 0 [a] = (some a, 7) := by
  rw [selectRunWith_small d cutoff hd hc 0 [a] (by decide) hc]
  apply Prod.ext
  · rw [slowSelectRun_value]
    simpa only [ordered, Applications.Sorting.sortOn_eq_insertionOn] using
      (show (Applications.Sorting.insertionOn id [a])[0]? = some a from rfl)
  · rw [Resources.SymmetricCosts.lengthRun_exact, slowSelectRun_cost]
    rfl

private theorem sorted_base (k : Nat) (xs : List Nat) (a : Nat)
    (hk : k < xs.length) (hs : xs.length ≤ 20) (hp : xs.Pairwise (· ≤ ·))
    (ha : (Applications.Sorting.insertionOn id xs)[k]? = some a) :
    selectRun k xs = (some a, 3 * xs.length + k + 4) := by
  rw [selectRun_small k xs hk hs]
  apply Prod.ext
  · rw [slowSelectRun_value]
    simpa only [ordered, Applications.Sorting.sortOn_eq_insertionOn] using ha
  · rw [Resources.SymmetricCosts.lengthRun_exact, slowSelectRun_cost_of_pairwise k xs hk hp]
    omega

theorem empty_payload : selectRun 0 ([] : List (Fin 0)) = (none, 2) :=
  selectRun_nil 0

theorem empty_arbitrary_rank (k : Nat) : selectRun k ([] : List (Fin 0)) = (none, 2) :=
  selectRun_nil k

theorem singleton : selectRun 0 ([7] : List Nat) = (some 7, 7) :=
  singleton_with 5 20 (by decide) (by decide) 7

theorem singleton_invalid : selectRun 1 ([7] : List Nat) = (none, 3) :=
  selectRun_of_invalid 1 [7] (by decide)

theorem cutoff_ascending : selectRun 19 (List.range 20) = (some 19, 83) := by
  simpa only [List.length_range] using sorted_base 19 (List.range 20) 19
    (by decide) (by decide) (by decide) (by decide +kernel)

theorem cutoff_descending : selectRun 19 (List.range 20).reverse = (some 19, 273) := by
  rw [selectRun_small 19 _ (by decide) (by decide)]
  apply Prod.ext
  · rw [slowSelectRun_value]
    simpa only [ordered, Applications.Sorting.sortOn_eq_insertionOn] using
      (show (Applications.Sorting.insertionOn id (List.range 20).reverse)[19]? = some 19 by
        decide +kernel)
  · exact Examples.SelectionAuxiliary.cutoff_descending_last

theorem same_cutoff_value_different_work :
    (selectRun 19 (List.range 20)).1 = (selectRun 19 (List.range 20).reverse).1 ∧
      (selectRun 19 (List.range 20)).2 < (selectRun 19 (List.range 20).reverse).2 := by
  rw [cutoff_ascending, cutoff_descending]
  decide

theorem first_recursive_pivot :
    selectRun 2 ([2, 7, 12, 17, 20] : List Nat) = (some 12, 21) := by
  exact sorted_base 2 [2, 7, 12, 17, 20] 12
    (by decide) (by decide) (by decide) (by decide +kernel)

private theorem first_left_child : selectRun 0 (List.range 12) = (some 0, 40) := by
  simpa only [List.length_range] using sorted_base 0 (List.range 12) 0
    (by decide) (by decide) (by decide) (by decide +kernel)

private theorem first_right_child :
    selectRun 7 ([13, 14, 15, 16, 17, 18, 19, 20] : List Nat) = (some 20, 35) := by
  exact sorted_base 7 [13, 14, 15, 16, 17, 18, 19, 20] 20
    (by decide) (by decide) (by decide) (by decide +kernel)

private theorem first_partition :
    partition3 12 (List.range 21) =
      (List.range 12, [12], [13, 14, 15, 16, 17, 18, 19, 20]) := by
  rw [partition3_eq_filters]
  decide +kernel

private theorem first_pivot_observation :
    (selectRun ((((List.range 21).length ⌈/⌉ 5) - 1) / 2)
      (chunkMediansRun 5 (List.range 21)).1).1 = some 12 := by
  norm_num [Examples.SelectionMedians.first_recursive_size,
    Nat.ceilDiv_eq_add_pred_div, first_recursive_pivot]

/-- Entry/length 23, preparation 150, pivot 21, partition 22, lower length
13, selected child 40. The equal-bucket length is not evaluated. -/
theorem first_recursive_left : selectRun 0 (List.range 21) = (some 0, 269) := by
  apply Prod.ext
  · rw [selectRun_value]
    simpa only [ordered, Applications.Sorting.sortOn_eq_insertionOn] using
      (show (Applications.Sorting.insertionOn id (List.range 21))[0]? = some 0 by
        decide +kernel)
  · rw [selectRun_cost_step 0 _ (by decide) (by decide) 12 first_pivot_observation]
    norm_num [first_partition, Examples.SelectionMedians.first_recursive_size,
      Nat.ceilDiv_eq_add_pred_div, first_recursive_pivot, first_left_child,
      Resources.SymmetricCosts.lengthRun_exact, Resources.Partition.partitionRun_cost]

/-- The additional equal length costs two; no strict child is selected. -/
theorem first_recursive_equal : selectRun 12 (List.range 21) = (some 12, 231) := by
  rw [selectRun_step 12 _ (by decide) (by decide) 12 first_pivot_observation]
  norm_num [first_partition, Examples.SelectionMedians.first_recursive_size,
    Nat.ceilDiv_eq_add_pred_div, first_recursive_pivot,
    Resources.SymmetricCosts.lengthRun_exact, Resources.Partition.partitionRun_cost]

/-- The right child has adjusted rank seven and costs thirty-five. -/
theorem first_recursive_right : selectRun 20 (List.range 21) = (some 20, 266) := by
  rw [selectRun_step 20 _ (by decide) (by decide) 12 first_pivot_observation]
  norm_num [first_partition, Examples.SelectionMedians.first_recursive_size,
    Nat.ceilDiv_eq_add_pred_div, first_recursive_pivot, first_right_child,
    Resources.SymmetricCosts.lengthRun_exact, Resources.Partition.partitionRun_cost]

theorem first_recursive_invalid : selectRun 21 (List.range 21) = (none, 23) :=
  selectRun_of_invalid 21 _ (by decide)

private theorem equal_preparation :
    chunkMediansRun 5 (List.replicate 21 4) = (List.replicate 5 4, 150) := by
  apply Prod.ext
  · apply (List.map_inj_right
      (fun (a b : Nat) (h : some a = some b) => Option.some.inj h)).mp
    rw [chunkMediansRun_some_values]
    decide +kernel
  · rw [chunkMediansRun_cost_positive 5 _ (by decide)]
    decide +kernel

private theorem equal_pivot : selectRun 2 (List.replicate 5 4) = (some 4, 21) := by
  simpa only [List.length_replicate] using sorted_base 2 (List.replicate 5 4) 4
    (by decide) (by decide) (by decide) (by decide +kernel)

private theorem equal_partition :
    partition3 4 (List.replicate 21 4) = ([], List.replicate 21 4, []) := by
  rw [partition3_eq_filters]
  decide +kernel

private theorem equal_run (k : Nat) (hk : k < 21) :
    selectRun k (List.replicate 21 4) = (some 4, 239) := by
  have hp : (selectRun ((((List.replicate 21 4).length ⌈/⌉ 5) - 1) / 2)
      (chunkMediansRun 5 (List.replicate 21 4)).1).1 = some 4 := by
    norm_num [equal_preparation, Nat.ceilDiv_eq_add_pred_div, equal_pivot]
  rw [selectRun_step k _ (by simpa only [List.length_replicate] using hk)
    (by decide) 4 hp]
  norm_num [equal_partition, equal_preparation, Nat.ceilDiv_eq_add_pred_div,
    equal_pivot, Resources.SymmetricCosts.lengthRun_exact,
    Resources.Partition.partitionRun_cost, hk]

theorem all_equal_first : selectRun 0 (List.replicate 21 4) = (some 4, 239) :=
  equal_run 0 (by decide)

theorem all_equal_last : selectRun 20 (List.replicate 21 4) = (some 4, 239) :=
  equal_run 20 (by decide)

private theorem two_preparation_12 :
    chunkMediansRun 2 ([1, 2] : List Nat) = ([1], 19) := by
  apply Prod.ext
  · apply (List.map_inj_right
      (fun (a b : Nat) (h : some a = some b) => Option.some.inj h)).mp
    rw [chunkMediansRun_some_values]
    decide +kernel
  · rw [chunkMediansRun_cost_positive 2 _ (by decide)]
    decide +kernel

private theorem two_preparation_22 :
    chunkMediansRun 2 ([2, 2] : List Nat) = ([2], 19) := by
  apply Prod.ext
  · apply (List.map_inj_right
      (fun (a b : Nat) (h : some a = some b) => Option.some.inj h)).mp
    rw [chunkMediansRun_some_values]
    decide +kernel
  · rw [chunkMediansRun_cost_positive 2 _ (by decide)]
    decide +kernel

private theorem two_preparation_322 :
    chunkMediansRun 2 ([3, 2, 2] : List Nat) = ([2, 2], 32) := by
  apply Prod.ext
  · apply (List.map_inj_right
      (fun (a b : Nat) (h : some a = some b) => Option.some.inj h)).mp
    rw [chunkMediansRun_some_values]
    decide +kernel
  · rw [chunkMediansRun_cost_positive 2 _ (by decide)]
    decide +kernel

private theorem two_preparation_3122 :
    chunkMediansRun 2 ([3, 1, 2, 2] : List Nat) = ([1, 2], 37) := by
  apply Prod.ext
  · apply (List.map_inj_right
      (fun (a b : Nat) (h : some a = some b) => Option.some.inj h)).mp
    rw [chunkMediansRun_some_values]
    decide +kernel
  · rw [chunkMediansRun_cost_positive 2 _ (by decide)]
    decide +kernel

private theorem two_select_12 :
    selectRunWith 2 1 (by decide) (by decide) 0 ([1, 2] : List Nat) = (some 1, 36) := by
  have hp : (selectRunWith 2 1 (by decide) (by decide)
      (((([1, 2] : List Nat).length ⌈/⌉ 2) - 1) / 2)
      (chunkMediansRun 2 [1, 2]).1).1 = some 1 := by
    norm_num [two_preparation_12, Nat.ceilDiv_eq_add_pred_div, singleton_with]
  have ht : partition3 1 ([1, 2] : List Nat) = ([], [1], [2]) := by
    rw [partition3_eq_filters]
    decide +kernel
  rw [selectRunWith_step 2 1 (by decide) (by decide) 0 [1, 2]
    (by decide) (by decide) 1 hp]
  norm_num [ht, two_preparation_12, Nat.ceilDiv_eq_add_pred_div, singleton_with,
    Resources.SymmetricCosts.lengthRun_exact, Resources.Partition.partitionRun_cost]

private theorem two_select_22 :
    selectRunWith 2 1 (by decide) (by decide) 0 ([2, 2] : List Nat) = (some 2, 37) := by
  have hp : (selectRunWith 2 1 (by decide) (by decide)
      (((([2, 2] : List Nat).length ⌈/⌉ 2) - 1) / 2)
      (chunkMediansRun 2 [2, 2]).1).1 = some 2 := by
    norm_num [two_preparation_22, Nat.ceilDiv_eq_add_pred_div, singleton_with]
  have ht : partition3 2 ([2, 2] : List Nat) = ([], [2, 2], []) := by
    rw [partition3_eq_filters]
    decide +kernel
  rw [selectRunWith_step 2 1 (by decide) (by decide) 0 [2, 2]
    (by decide) (by decide) 2 hp]
  norm_num [ht, two_preparation_22, Nat.ceilDiv_eq_add_pred_div, singleton_with,
    Resources.SymmetricCosts.lengthRun_exact, Resources.Partition.partitionRun_cost]

private theorem two_select_322 :
    selectRunWith 2 1 (by decide) (by decide) 1 ([3, 2, 2] : List Nat) = (some 2, 82) := by
  have hp : (selectRunWith 2 1 (by decide) (by decide)
      (((([3, 2, 2] : List Nat).length ⌈/⌉ 2) - 1) / 2)
      (chunkMediansRun 2 [3, 2, 2]).1).1 = some 2 := by
    norm_num [two_preparation_322, Nat.ceilDiv_eq_add_pred_div, two_select_22]
  have ht : partition3 2 ([3, 2, 2] : List Nat) = ([], [2, 2], [3]) := by
    rw [partition3_eq_filters]
    decide +kernel
  rw [selectRunWith_step 2 1 (by decide) (by decide) 1 [3, 2, 2]
    (by decide) (by decide) 2 hp]
  norm_num [ht, two_preparation_322, Nat.ceilDiv_eq_add_pred_div, two_select_22,
    Resources.SymmetricCosts.lengthRun_exact, Resources.Partition.partitionRun_cost]

/-- Size-two groups terminate and select correctly, without asserting linear
growth for this noncontracting grouping regime. The cutoff is one. -/
theorem group_two_cutoff_one :
    selectRunWith 2 1 (by decide) (by decide) 2 ([3, 1, 2, 2] : List Nat) =
      (some 2, 169) := by
  have hp : (selectRunWith 2 1 (by decide) (by decide)
      (((([3, 1, 2, 2] : List Nat).length ⌈/⌉ 2) - 1) / 2)
      (chunkMediansRun 2 [3, 1, 2, 2]).1).1 = some 1 := by
    norm_num [two_preparation_3122, Nat.ceilDiv_eq_add_pred_div, two_select_12]
  have ht : partition3 1 ([3, 1, 2, 2] : List Nat) = ([], [1], [3, 2, 2]) := by
    rw [partition3_eq_filters]
    decide +kernel
  apply Prod.ext
  · rw [selectRunWith_value]
    simpa only [ordered, Applications.Sorting.sortOn_eq_insertionOn] using
      (show (Applications.Sorting.insertionOn id ([3, 1, 2, 2] : List Nat))[2]? = some 2 by
        decide +kernel)
  · rw [selectRunWith_cost_step 2 1 (by decide) (by decide) 2 [3, 1, 2, 2]
      (by decide) (by decide) 1 hp]
    norm_num [ht, two_preparation_3122, Nat.ceilDiv_eq_add_pred_div, two_select_12,
      two_select_322, Resources.SymmetricCosts.lengthRun_exact,
      Resources.Partition.partitionRun_cost]

theorem one_based_public_bridge {α : Type u} [LinearOrder α] (k : Nat) (xs : List α) :
    (selectRun k xs).1 = sortSelect (k + 1) xs :=
  selectRunWith_public 5 20 (by decide) (by decide) k xs

/-- Relabeling may merge distinct values; this transports the occurrence value,
without claiming that relabeling preserves the executed branch costs. -/
theorem monotone_payload_selection {α : Type u} {β : Type v}
    [LinearOrder α] [LinearOrder β] (f : α → β) (hf : Monotone f)
    (k : Nat) (xs : List α) (a : α) (ha : (selectRun k xs).1 = some a) :
    (selectRun k (xs.map f)).1 = some (f a) := by
  apply (selectRun_some_iff k (xs.map f) (f a)).mpr
  exact ((selectRun_some_iff k xs a).mp ha).map f hf

theorem collapsed_payload :
    (selectRun 20 ((List.range 21).map (fun _ : Nat => (0 : Nat)))).1 = some 0 :=
  monotone_payload_selection (fun _ : Nat => (0 : Nat)) (fun _ _ _ => le_rfl)
    20 (List.range 21) 20 (congrArg Prod.fst first_recursive_right)

end Examples.SelectionCosts

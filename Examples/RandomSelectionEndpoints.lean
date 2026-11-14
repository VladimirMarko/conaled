import Applications.Resources.RandomSelectionEndpoints
import Examples.RandomSelectionEqual

/-! Endpoint-step cases calculated before the universal proofs.
Unsorted and negative inputs exercise both directions; the middle-rank case
switches from a minimum step to a maximum step. Duplicate, singleton, empty
and invalid boundaries keep the distinctness and validity requirements visible.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.RandomSelectionEndpoints
open Resources.RandomSelection Applications.Selection
universe u
variable {α : Type u} [LinearOrder α]

theorem unsorted_minimum_step :
    stepRun 1 ([3, 1, 2] : List Int) 1 = (Sum.inl (0, [3, 2]), 14) := by
  norm_num [stepRun_eq, partition3_eq_filters]

theorem unsorted_maximum_step :
    stepRun 0 ([3, 1, 2] : List Int) 0 = (Sum.inl (0, [1, 2]), 13) := by
  norm_num [stepRun_eq, partition3_eq_filters]

theorem middle_rank_switch :
    EndpointPivot 1 ([3, 1, 2] : List Int) 1 ∧
      EndpointPivot 0 ([3, 2] : List Int) 0 ∧
      stepRun 0 ([3, 2] : List Int) 0 = (Sum.inl (0, [2]), 10) := by
  norm_num [EndpointPivot, stepRun_eq, partition3_eq_filters]

theorem negative_minimum_step :
    stepRun 3 ([3, -2, 8, 0, 5] : List Int) 1 =
      (Sum.inl (2, [3, 8, 0, 5]), 18) := by
  norm_num [stepRun_eq, partition3_eq_filters]

theorem negative_maximum_step :
    stepRun 0 ([3, -2, 8, 0, 5] : List Int) 2 =
      (Sum.inl (0, [3, -2, 0, 5]), 21) := by
  norm_num [stepRun_eq, partition3_eq_filters]

theorem singleton_terminal (x : α) :
    EndpointPivot 0 [x] 0 ∧ stepRun 0 [x] 0 = (Sum.inr x, 9) := by
  simp [EndpointPivot, stepRun_eq, partition3_eq_filters]

theorem duplicate_countercase :
    ¬ ([4, 4, 4] : List Nat).Nodup ∧
      stepRun 1 ([4, 4, 4] : List Nat) 0 = (Sum.inr 4, 15) := by
  norm_num [stepRun_eq, partition3_eq_filters]

theorem invalid_singleton_step :
    stepRun 1 ([7] : List Nat) 0 = (Sum.inl (0, []), 9) := by
  norm_num [stepRun_eq, partition3_eq_filters]

omit [LinearOrder α] in
theorem empty_has_no_valid_rank (k : Nat) : ¬ k < ([] : List α).length := by
  simp

theorem arbitrary_endpoint_occurrence (k : Nat) (xs : List α) (hne : xs ≠ []) :
    ∃ i : Fin xs.length, EndpointPivot k xs i := exists_endpointPivot k xs hne

theorem arbitrary_distinct_target (k : Nat) (xs : List α) (hxs : xs.Nodup)
    (hk : k < xs.length) (hn : 1 < xs.length) :
    ∃ (i : Fin xs.length) (ys : List α),
      EndpointPivot k xs i ∧ (stepRun k xs i).1 = Sum.inl (k - 1, ys) ∧
      ys.Nodup ∧ ys.length + 1 = xs.length ∧ k - 1 < ys.length ∧
      (ordered ys)[k - 1]? = (ordered xs)[k]? :=
  exists_endpoint_child k xs hxs hk hn

theorem endpoint_occurrence_is_unique (k : Nat) (xs : List α) (hxs : xs.Nodup)
    (i j : Fin xs.length) (hi : EndpointPivot k xs i) (hj : EndpointPivot k xs j) :
    i = j := endpointPivot_unique k xs hxs i j hi hj

end Examples.RandomSelectionEndpoints

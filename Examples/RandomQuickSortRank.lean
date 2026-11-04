import Applications.Resources.RandomQuickSortRank
import Examples.RandomQuickSortMean
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Consequential clients of the actual occurrence/rank and mean bridge.
Nontrivial input orders exercise the original-index rank permutation. Actual
child order is retained. The four-key mean 109/3 was calculated independently
from extreme-rank means 119/3 and internal-rank means 33. Distinct payload tags
with repeated keys demonstrate why mapped-key Nodup is required.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.RandomQuickSortRank
open Resources.RandomQuickSort
open scoped BigOperators ENNReal
universe u v w z

noncomputable section

local notation "natLt" => (fun a b : Nat => decide (a < b))

/-- An empty rank permutation uses no default payload or actual pivot. -/
theorem empty_rank {α : Type u} {κ : Type v} [LinearOrder κ] (key : α → κ) :
    occurrenceRank key [] = Equiv.refl (Fin 0) := by
  apply Equiv.ext
  intro i
  exact Fin.elim0 i

theorem empty_uninhabited_mean :
    exerciseMean (fun _ _ : Empty => false) [] = sizeMean 0 := by
  simp

theorem singleton_rank {α : Type u} {κ : Type v} [LinearOrder κ]
    (key : α → κ) (x : α) : occurrenceRank key [x] 0 = 0 := by
  exact Fin.fin_one_eq_zero _

theorem sizeMean_one : sizeMean 1 = 5 := by
  have h := exerciseMean_eq_sizeMean (id : Nat → Nat) [0] (by decide)
  exact h.symm.trans (exerciseMean_singleton natLt 0)

theorem sizeMean_two : sizeMean 2 = 13 := by
  have h := exerciseMean_eq_sizeMean (id : Nat → Nat) [0, 1] (by decide)
  exact h.symm.trans Examples.RandomQuickSortMean.two_key_exercise_mean

theorem sizeMean_three : sizeMean 3 = (71 : ℝ) / 3 := by
  have h := exerciseMean_eq_sizeMean (id : Nat → Nat) [0, 1, 2] (by decide)
  exact h.symm.trans Examples.RandomQuickSortMean.three_key_exercise_mean

/-- Read back ranks through the actual strict child, without evaluating the
abstract tuple-sort permutation or replacing the occurrence sampler.
-/
theorem three_occurrence_ranks (i : Fin 3) :
    (occurrenceRank (id : Nat → Nat) [2, 0, 1] i).val =
      ([2, 0, 1] : List Nat)[i.val] := by
  have h := left_length_eq_rank (id : Nat → Nat) [2, 0, 1] (by decide) i
  fin_cases i <;> simpa using h.symm

theorem three_middle_children :
    (([2, 0, 1] : List Nat).eraseIdx 2).filter
        (fun x => decide (x < ([2, 0, 1] : List Nat)[2])) = [0] ∧
      (([2, 0, 1] : List Nat).eraseIdx 2).filter
        (fun x => !(decide (x < ([2, 0, 1] : List Nat)[2]))) = [2] := by
  decide

/-- The actual nonidentity occurrence permutation still gives a uniform rank. -/
theorem three_left_size_law :
    PMF.map (fun i : Fin 3 =>
      ((([2, 0, 1] : List Nat).eraseIdx i.val).filter
        (fun x => decide (x < ([2, 0, 1] : List Nat)[i.val]))).length)
      (uniformIndex 2) = PMF.map (fun i : Fin 3 => i.val) (uniformIndex 2) := by
  exact left_length_law (id : Nat → Nat) 2 [0, 1] (by decide)

theorem three_reordered_exercise_mean : exerciseMean natLt [2, 0, 1] = (71 : ℝ) / 3 := by
  have h := exerciseMean_eq_sizeMean (id : Nat → Nat) [2, 0, 1] (by decide)
  exact h.trans sizeMean_three

/-- The positive-size range interface is checked against the independently
calculated four-key value, using earlier actual-execution means as inputs.
-/
theorem sizeMean_four : sizeMean 4 = (109 : ℝ) / 3 := by
  have h := sizeMean_recurrence 4 (by decide)
  norm_num [Finset.sum_range_succ, sizeMean_one, sizeMean_two, sizeMean_three] at h
  exact h

theorem four_occurrence_ranks (i : Fin 4) :
    (occurrenceRank (id : Nat → Nat) [3, 1, 0, 2] i).val =
      ([3, 1, 0, 2] : List Nat)[i.val] := by
  have h := left_length_eq_rank (id : Nat → Nat) [3, 1, 0, 2] (by decide) i
  fin_cases i <;> simpa using h.symm

/-- Pivot 2 leaves the actual left input [1,0], preserving its unsorted order. -/
theorem four_selected_children :
    (([3, 1, 0, 2] : List Nat).eraseIdx 3).filter
        (fun x => decide (x < ([3, 1, 0, 2] : List Nat)[3])) = [1, 0] ∧
      (([3, 1, 0, 2] : List Nat).eraseIdx 3).filter
        (fun x => !(decide (x < ([3, 1, 0, 2] : List Nat)[3]))) = [3] := by
  decide

theorem four_reordered_exercise_mean :
    exerciseMean natLt [3, 1, 0, 2] = (109 : ℝ) / 3 := by
  have h := exerciseMean_eq_sizeMean (id : Nat → Nat) [3, 1, 0, 2] (by decide)
  exact h.trans sizeMean_four

/-- Different tags do not imply the recursive key-distinctness hypothesis. -/
theorem distinct_tags_repeated_keys :
    ([(1, false), (1, true), (2, false)] : List (Nat × Bool)).Nodup ∧
      ¬ (([(1, false), (1, true), (2, false)] : List (Nat × Bool)).map Prod.fst).Nodup := by
  decide

/-- With a repeated key the second tie position is 1, but the actual left
child has length 0. Thus a permutation position alone cannot prove the size law.
-/
theorem repeated_key_rank_is_not_left_size :
    (occurrenceRank (Prod.fst : Nat × Bool → Nat)
      [(1, false), (1, true), (2, false)] (1 : Fin 3)).val = 1 ∧
    ((([(1, false), (1, true), (2, false)] : List (Nat × Bool)).eraseIdx 1).filter
      (fun x => decide (x.1 < 1))).length = 0 := by
  let f : Fin 3 → Nat := fun i =>
    ([(1, false), (1, true), (2, false)] : List (Nat × Bool))[i.val].1
  have hm : Monotone f := by decide
  have hs : Tuple.sort f = Equiv.refl (Fin 3) := Tuple.sort_eq_refl_iff_monotone.mpr hm
  constructor
  · change ((Tuple.sort f).symm (1 : Fin 3)).val = 1
    rw [hs]
    rfl
  · decide

theorem equal_keys_keep_quadratic_mean :
    exerciseMean natLt [2, 2, 2] = 25 ∧
      exerciseMean natLt [2, 2, 2] ≠ sizeMean 3 := by
  have h := Examples.RandomQuickSortMean.all_equal_three_means
  constructor
  · exact h.1
  · rw [h.1, sizeMean_three]
    norm_num

/-- The client uses unrelated key types and unrestricted tag universes. -/
theorem tagged_inputs_equal_mean {τ : Type u} {κ : Type v} {υ : Type w} {ν : Type z}
    [LinearOrder κ] [LinearOrder ν] (xs : List (κ × τ)) (ys : List (ν × υ))
    (hx : (xs.map Prod.fst).Nodup) (hy : (ys.map Prod.fst).Nodup)
    (hlen : xs.length = ys.length) :
    exerciseMean (fun a b : κ × τ => decide (a.1 < b.1)) xs =
      exerciseMean (fun a b : ν × υ => decide (a.1 < b.1)) ys :=
  exerciseMean_eq_of_length_eq Prod.fst Prod.fst xs ys hx hy hlen

end
end Examples.RandomQuickSortRank

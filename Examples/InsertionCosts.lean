import Applications.Resources.InsertionSort
import Applications.Selection.Rank

/-! Checked clients of shared insertion costs: empty input, ties, attained best
and worst cases, and key sorting without an order on payloads.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.InsertionCosts
open Resources.InsertionSort
universe u

theorem empty_cost : (sortRun (α := Nat) (· ≤ ·) []).2 = 1 := rfl

theorem singleton_cost {α : Type u} (r : α → α → Prop) [DecidableRel r] (x : α) :
    (sortRun r [x]).2 = 3 := rfl

theorem sorted_with_duplicates :
    (sortRun (α := Nat) (· ≤ ·) [1, 1, 2]).2 = 7 := by
  simpa using sortRun_cost_of_pairwise (α := Nat) (· ≤ ·) [1, 1, 2] (by decide)

theorem descending_worst :
    (sortRun (α := Nat) (· ≤ ·) [2, 1, 0]).2 = 10 := by
  change (sortRun (α := Nat) (· ≤ ·) (List.range 3).reverse).2 =
    (3 + 1) * (3 + 2) / 2
  exact sortRun_cost_reverse_range 3

theorem best_is_global (xs : List Nat) :
    2 * xs.length + 1 ≤ (sortRun (· ≤ ·) xs).2 := sortRun_cost_lower _ xs

theorem worst_is_global (xs : List Nat) :
    (sortRun (· ≤ ·) xs).2 ≤ (xs.length + 1) * (xs.length + 2) / 2 :=
  sortRun_cost_le _ xs

theorem source_quadratic (xs : List Nat) :
    (sortRun (· ≤ ·) xs).2 ≤ (xs.length + 1) ^ 2 := sortRun_quadratic _ xs

theorem immediate_insertion :
    insertRun (α := Nat) (· ≤ ·) 2 [2, 3] = ([2, 2, 3], 1) := by
  apply Prod.ext
  · rw [insertRun_value]
    rfl
  · exact insertRun_cost_of_all _ _ _ (by decide)

theorem full_traversal :
    insertRun (α := Nat) (· ≤ ·) 4 [1, 2, 3] = ([1, 2, 3, 4], 4) := by
  apply Prod.ext
  · rw [insertRun_value]
    rfl
  · exact insertRun_cost_of_all_not _ _ _ (by decide)

theorem tied_head_ignores_tail :
    insertRun (α := Nat) (· ≤ ·) 2 [2, 0] = ([2, 2, 0], 1) := by
  apply Prod.ext
  · rw [insertRun_value]
    rfl
  · exact insertRun_cost_of_head _ _ _ _ (by decide)

/-- This contract requires no order or equality decision on payloads. -/
theorem key_contract {payload : Type u} (xs : List (Nat × payload)) :
    Applications.Sorting.StableSort Prod.fst xs
      (sortRun (fun x y => x.1 ≤ y.1) xs).1 := sortRun_stable Prod.fst xs

theorem key_tie_observation :
    ((sortRun (fun x y : Nat × String => x.1 ≤ y.1)
      [(2, "first"), (1, "middle"), (2, "last")]).1).filter
        (fun x => decide (x.1 = 2)) = [(2, "first"), (2, "last")] := by
  have h := (key_contract [(2, "first"), (1, "middle"), (2, "last")]).stable 2
  simpa using h

/-- The measured sort supplies the existing occurrence-rank contract. The
count above is for sorting; this observation adds no claim about indexing cost.
-/
theorem sorted_result_has_rank {α : Type u} [LinearOrder α]
    (xs : List α) (k : Nat) (a : α)
    (h : (sortRun (· ≤ ·) xs).1[k]? = some a) :
    Applications.Selection.RankedAt xs k a := by
  have hs := sortRun_stable id xs
  exact Applications.Selection.pairwise_ranked hs.sorted hs.perm h

theorem repeated_value_rank :
    Applications.Selection.RankedAt [3, 1, 3, 2] 2 3 := by
  apply sorted_result_has_rank
  rw [sortRun_value]
  rfl

/-- A bounded-size sorting budget for selection clients, before indexing. -/
theorem small_sort_budget {α : Type u} (r : α → α → Prop) [DecidableRel r]
    (xs : List α) (h : xs.length ≤ 5) : (sortRun r xs).2 ≤ 21 := by
  have ht := sortRun_double_cost_le r xs
  have hp : (xs.length + 1) * (xs.length + 2) ≤ 6 * 7 :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

theorem small_rank_with_sort_budget (xs : List Nat) (k a : Nat)
    (hn : xs.length ≤ 5) (ha : (sortRun (· ≤ ·) xs).1[k]? = some a) :
    Applications.Selection.RankedAt xs k a ∧ (sortRun (· ≤ ·) xs).2 ≤ 21 :=
  ⟨sorted_result_has_rank xs k a ha, small_sort_budget _ xs hn⟩

end Examples.InsertionCosts

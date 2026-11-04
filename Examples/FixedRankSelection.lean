import Applications.Resources.FixedRank

/-!
Connected uses of the streaming fixed-rank algorithms and their source costs.
The expected cases retain duplicate occurrences, distinguish book index zero
from public rank one, and pay for traversal of a bounded accumulator. Concrete
source executions supplement the general erasure and cost theorems; they are
kernel-checked propositions, not native execution or wall-clock measurements.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.FixedRankSelection
open Applications.Selection Applications.Selection.FixedRank
open Resources.FixedRank

theorem minimum_example : select0 ([8, 1, 5] : List Nat) = some 1 :=
  (select0_some_iff_min _ _).mpr (by decide)

theorem minimum_duplicate : select0 ([4, 1, 1] : List Nat) = some 1 :=
  (select0_some_iff_min _ _).mpr (by decide)

theorem minimum_empty : select0 ([] : List Nat) = none :=
  (select0_none_iff _).mpr rfl

/-- Three input occurrences require the wrapper plus three tail-loop entries. -/
theorem minimum_execution : select0Run ([8, 1, 5] : List Nat) = (some 1, 4) := by
  rw [select0Run_exact, minimum_example]
  rfl

theorem minimum_empty_execution : select0Run ([] : List Nat) = (none, 1) := by
  rw [select0Run_exact, minimum_empty]
  rfl

/-- Sorted-prefix observation includes both occurrences of the minimum. -/
theorem duplicate_prefix : takeSort 3 ([4, 1, 7, 1] : List Nat) = [1, 1, 4] := by
  have hs : ordered ([4, 1, 7, 1] : List Nat) = [1, 1, 4, 7] :=
    ordered_eq_of_pairwise_perm (by decide) (by decide)
  rw [takeSort_value, hs]
  rfl

theorem zero_width_prefix (xs : List Nat) : takeSort 0 xs = [] := by
  rw [takeSort_value, List.take_zero]

/-- A nonempty previous history exercises the accumulator invariant. The new
input is read in the order 4,1, and the retained two occurrences become 1,2. -/
theorem prefix_with_history : prefixLoop 2 ([2, 5] : List Nat) [4, 1] = [1, 2] := by
  have hs : ordered ([5, 2] : List Nat) = [2, 5] :=
    ordered_eq_of_pairwise_perm (by decide) (by decide)
  have hout : ordered (([4, 1] : List Nat).reverse ++ [5, 2]) = [1, 2, 4, 5] :=
    ordered_eq_of_pairwise_perm (by decide) (by decide)
  have h := prefixLoop_prefix 2 ([5, 2] : List Nat) [4, 1]
  rw [hs, hout] at h
  exact h

/-- The exact width-two loop relation exposes the duplicate-sensitive update. -/
theorem two_loop_correspondence :
    (prefixLoop 2 ([1, 4] : List Nat) [1])[1]? = some (secondLoop 1 4 [1]) :=
  prefixLoop_two 1 4 [1]

theorem second_duplicate : select1 ([4, 1, 1] : List Nat) = some 1 := by
  rw [select1_eq_selectFixed]
  exact (selectFixed_some_iff_count_bounds _ _ _).mpr (by decide)

theorem second_distinct : select1 ([3, 1, 2] : List Nat) = some 2 := by
  rw [select1_eq_selectFixed]
  exact (selectFixed_some_iff_count_bounds _ _ _).mpr (by decide)

theorem second_singleton : select1 ([7] : List Nat) = none :=
  (select1_none_iff _).mpr (by decide)

theorem second_exists {α : Type} [LinearOrder α] (x y : α) (xs : List α) :
    ∃ a, select1 (x :: y :: xs) = some a ∧ RankedAt (x :: y :: xs) 1 a :=
  select1_spec _ (by simp)

theorem fixed_zero_is_minimum : selectFixed 0 ([8, 1, 5] : List Nat) = some 1 := by
  rw [← select0_eq_selectFixed]
  exact minimum_example

theorem fixed_last_occurrence : selectFixed 3 ([4, 1, 7, 1] : List Nat) = some 7 :=
  (selectFixed_some_iff_count_bounds _ _ _).mpr (by decide)

theorem fixed_invalid_rank : selectFixed 4 ([4, 1, 7, 1] : List Nat) = none :=
  (selectFixed_none_iff _ _).mpr (by decide)

theorem book_index_two_is_public_rank_three :
    selectWith List.head? 3 ([4, 1, 7, 1] : List Nat) = some 4 := by
  calc
    selectWith List.head? 3 ([4, 1, 7, 1] : List Nat) = selectFixed 2 [4, 1, 7, 1] :=
      (selectFixed_eq_selectWith _ head_pivot_valid 2 _).symm
    _ = some 4 := (selectFixed_some_iff_count_bounds _ _ _).mpr (by decide)

/-- Insertion before the head costs one; taking two entries costs three;
the bounded-insertion wrapper costs one, for a total of five. -/
theorem bounded_insert_at_head :
    boundedInsertRun 2 (0 : Nat) [1, 2] = ([0, 1], 5) := by
  apply Prod.ext
  · rw [boundedInsertRun_value]
    rfl
  · rw [boundedInsertRun_cost,
      Resources.InsertionSort.insertRun_cost_of_head (· ≤ ·) 0 1 [2] (by decide)]
    rfl

/-- Traversing both accumulator entries before insertion adds two calls. -/
theorem bounded_insert_after_accumulator :
    boundedInsertRun 2 (3 : Nat) [1, 2] = ([1, 2], 7) := by
  apply Prod.ext
  · rw [boundedInsertRun_value]
    rfl
  · rw [boundedInsertRun_cost,
      Resources.InsertionSort.insertRun_cost_of_all_not (· ≤ ·) 3 [1, 2] (by decide)]
    rfl

theorem bounded_step_for_rank (k x : Nat) (acc : List Nat)
    (hacc : acc.length ≤ k + 1) : (boundedInsertRun (k + 1) x acc).2 ≤ 2 * k + 5 := by
  have h := boundedInsertRun_cost_le (k + 1) x acc hacc
  omega

/-- Semantic rank and source cost compose for arbitrary values, with no
distinctness requirement and no assumptions about order-comparison outcomes. -/
theorem measured_rank_and_bound {α : Type} [LinearOrder α]
    (k : Nat) (xs : List α) (a : α)
    (h : xs.countP (fun x => decide (x < a)) ≤ k ∧
      xs.countP (fun x => decide (a < x)) < xs.length - k) :
    (selectFixedRun k xs).1 = some a ∧
      (selectFixedRun k xs).2 ≤ 2 * k * xs.length + 6 * xs.length + k + 4 := by
  refine ⟨?_, selectFixedRun_cost_le k xs⟩
  rw [selectFixedRun_value]
  exact (selectFixed_some_iff_count_bounds k xs a).mpr h

/-- Each width-one step costs four plus its outer entry. Three steps,
two wrapper/base entries, final lookup and selector entry total nineteen. -/
theorem fixed_zero_execution : selectFixedRun 0 ([4, 1, 1] : List Nat) = (some 1, 19) := by
  apply Prod.ext
  · rw [selectFixedRun_value, ← select0_eq_selectFixed]
    exact minimum_duplicate
  · decide

theorem fixed_zero_bound : (selectFixedRun 0 ([4, 1, 1] : List Nat)).2 ≤ 22 := by
  exact selectFixedRun_cost_le 0 [4, 1, 1]

/-- The actual minimum algorithm and the general rank-zero algorithm agree
on values but have different source costs; cost is never inferred from value. -/
theorem minimum_and_fixed_costs_differ :
    (select0Run ([4, 1, 1] : List Nat)).1 = (selectFixedRun 0 [4, 1, 1]).1 ∧
      (select0Run ([4, 1, 1] : List Nat)).2 = 4 ∧
      (selectFixedRun 0 ([4, 1, 1] : List Nat)).2 = 19 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [select0Run_value, selectFixedRun_value, select0_eq_selectFixed]
  · exact select0Run_cost [4, 1, 1]
  · rw [fixed_zero_execution]

theorem fixed_second_execution : selectFixedRun 1 ([4, 1, 1] : List Nat) = (some 1, 22) := by
  apply Prod.ext
  · rw [selectFixedRun_value, ← select1_eq_selectFixed]
    exact second_duplicate
  · decide

theorem duplicate_second_with_bound :
    (selectFixedRun 1 ([4, 1, 1] : List Nat)).1 = some 1 ∧
      (selectFixedRun 1 ([4, 1, 1] : List Nat)).2 ≤ 29 :=
  measured_rank_and_bound 1 [4, 1, 1] 1 (by decide)

theorem uniform_constants_include_minimum :
    ∃ C1 C2 C3 C4 : Nat, ∀ (k : Nat) (xs : List Nat), k < xs.length →
      (selectFixedRun k xs).2 ≤
        C1 * k * xs.length + C2 * xs.length + C3 * k + C4 :=
  selectFixedRun_uniform_bound

end Examples.FixedRankSelection

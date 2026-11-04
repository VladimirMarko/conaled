import Applications.Sorting.BottomUp
import Examples.StableSorting

/-! Adjacent-run, odd-leftover, accumulator and occurrence-order clients for the
source bottom-up variants. Expected values use public recurrence equations;
correctness clients use independent sortedness and permutation observations.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.BottomUpSorting
open Applications.Sorting
universe u

def natCompare (a b : Nat) : Bool := decide (a ≤ b)

/-- Unequal run lengths, an empty inner run, a duplicate and an odd final run. -/
def raggedRuns : List (List Nat) := [[1, 3], [2], [], [0, 4], [2, 5]]

theorem ragged_pass_value :
    mergePairsBy natCompare raggedRuns = [[1, 2, 3], [0, 4], [2, 5]] := by
  rw [raggedRuns, mergePairsBy_step, mergePairsBy_step, mergePairsBy_singleton]
  rfl

theorem ragged_run_count : (mergePairsBy natCompare raggedRuns).length = 3 := by
  calc
    _ = (raggedRuns.length + 1) / 2 := mergePairsBy_length _ _
    _ = 3 := rfl

theorem ragged_total_length : (mergePairsBy natCompare raggedRuns).flatten.length = 7 := by
  calc
    _ = raggedRuns.flatten.length := mergePairsBy_flatten_length _ _
    _ = 7 := rfl

theorem ragged_sum_lengths : ((mergePairsBy natCompare raggedRuns).map List.length).sum = 7 := by
  calc
    _ = (raggedRuns.map List.length).sum := mergePairsBy_sum_lengths _ _
    _ = 7 := rfl

/-- Multiset observations retain both occurrences of 2, rather than just support. -/
theorem ragged_duplicate_occurrences :
    ((mergePairsBy natCompare raggedRuns).flatten : Multiset Nat).count 2 = 2 := by
  rw [mergePairsBy_multiset]
  rfl

theorem ragged_multiset_as_sum :
    ((mergePairsBy natCompare raggedRuns).flatten : Multiset Nat) =
      (raggedRuns.map (fun xs => (xs : Multiset Nat))).sum :=
  (mergePairsBy_multiset _ _).trans (multiset_flatten_eq_sum _)

theorem even_uniform_runs_double :
    ∀ ys ∈ mergePairsBy natCompare [[0, 2], [1, 3], [4, 6], [5, 7]], ys.length = 4 := by
  apply mergePairsBy_uniform_length natCompare _ 2
  · exact ⟨2, rfl⟩
  · intro xs hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> rfl

/-- Three singleton runs leave the last singleton unchanged; evenness is necessary. -/
theorem odd_runs_do_not_all_double :
    ¬ (∀ ys ∈ mergePairsBy natCompare [[1], [2], [3]], ys.length = 2) := by
  intro h
  have wrong := h [3] (by rw [mergePairsBy_step, mergePairsBy_singleton]; simp)
  contradiction

theorem empty_inner_runs_are_counted :
    (mergePairsBy natCompare [[], [], [], []]).length = 2 ∧
      (mergePairsBy natCompare [[], [], [], []]).flatten.length = 0 := by
  constructor
  · calc
      _ = (([[], [], [], []] : List (List Nat)).length + 1) / 2 := mergePairsBy_length _ _
      _ = 2 := rfl
  · calc
      _ = ([[], [], [], []] : List (List Nat)).flatten.length := mergePairsBy_flatten_length _ _
      _ = 0 := rfl

/-- The sorted-run premise cannot be dropped even for the one-run base case. -/
theorem singleton_unsorted_run :
    ¬ KeySorted id (mergeAllBy natCompare [[2, 1]]) := by
  rw [mergeAllBy_singleton]
  decide

theorem ordinary_duplicate_sort :
    sortBottomUpOn id ([3, 1, 2, 1, 0] : List Nat) = [0, 1, 1, 2, 3] := by
  have h := sortBottomUpOn_correct id ([3, 1, 2, 1, 0] : List Nat)
  exact List.Perm.eq_of_pairwise' (r := fun a b : Nat => a ≤ b) h.1 (by decide)
    (h.2.trans (by decide : ([3, 1, 2, 1, 0] : List Nat).Perm [0, 1, 1, 2, 3]))

theorem tail_duplicate_sort :
    sortBottomUpRevOn id ([3, 1, 2, 1, 0] : List Nat) = [0, 1, 1, 2, 3] := by
  have h := sortBottomUpRevOn_correct id ([3, 1, 2, 1, 0] : List Nat)
  exact List.Perm.eq_of_pairwise' (r := fun a b : Nat => a ≤ b) h.1 (by decide)
    (h.2.trans (by decide : ([3, 1, 2, 1, 0] : List Nat).Perm [0, 1, 1, 2, 3]))

/-- Existing nonnegative-domain evidence exercises the input-local law. -/
theorem local_comparator_ordinary :
    KeySorted Prod.fst
      (sortBottomUpBy StableSorting.nonnegativeCompare StableSorting.nonnegativeInput) :=
  sortBottomUpBy_sorted_compatible_on Prod.fst _ _ StableSorting.nonnegative_compatible

theorem local_comparator_tail :
    KeySorted Prod.fst
      (sortBottomUpRevBy StableSorting.nonnegativeCompare StableSorting.nonnegativeInput) :=
  sortBottomUpRevBy_sorted_compatible_on Prod.fst _ _ StableSorting.nonnegative_compatible

/-- Signed keys and payloads use the key order alone. -/
theorem signed_record_correct :
    KeySorted Prod.fst (sortBottomUpRevOn Prod.fst StableSorting.input) ∧
      (sortBottomUpRevOn Prod.fst StableSorting.input).Perm StableSorting.input :=
  sortBottomUpRevOn_correct Prod.fst StableSorting.input

theorem arbitrary_comparator_preserves_occurrences {α : Type u} (xs : List α) :
    (sortBottomUpBy (fun _ _ => false) xs).Perm xs ∧
      (sortBottomUpRevBy (fun _ _ => false) xs).Perm xs ∧
      (sortBottomUpRevBy (fun _ _ => false) xs).length = xs.length :=
  ⟨sortBottomUpBy_perm _ _, sortBottomUpRevBy_perm _ _, sortBottomUpRevBy_length _ _⟩

/-- A nonempty accumulator is retained verbatim after the reversed completed runs. -/
theorem arbitrary_accumulator_value :
    mergePairsRevBy natCompare [[99], [], [42, 43]] raggedRuns =
      [[2, 5], [0, 4], [1, 2, 3], [99], [], [42, 43]] := by
  rw [mergePairsRevBy_eq_reverse_append, ragged_pass_value]
  rfl

theorem arbitrary_accumulator_run_count :
    (mergePairsRevBy natCompare [[99], [], [42, 43]] raggedRuns).length = 6 := by
  calc
    _ = ([[99], [], [42, 43]] : List (List Nat)).length + (raggedRuns.length + 1) / 2 :=
      mergePairsRevBy_length _ _ _
    _ = 6 := rfl

theorem arbitrary_accumulator_total_length :
    (mergePairsRevBy natCompare [[99], [], [42, 43]] raggedRuns).flatten.length = 10 := by
  calc
    _ = ([[99], [], [42, 43]] : List (List Nat)).flatten.length + raggedRuns.flatten.length :=
      mergePairsRevBy_flatten_length _ _ _
    _ = 10 := rfl

/-- The accumulator need not be sorted for the exact value or multiset equation. -/
theorem unsorted_accumulator_multiset :
    ((mergePairsRevBy natCompare [[9, 0], [], [7]] raggedRuns).flatten : Multiset Nat) =
      (([9, 0, 7] : List Nat) : Multiset Nat) + (raggedRuns.flatten : Multiset Nat) :=
  mergePairsRevBy_multiset _ _ _

theorem ordinary_equal_keys {α : Type u} (first middle last : α) :
    sortBottomUpOn Prod.fst ([(0, first), (0, middle), (0, last)] : List (Nat × α)) =
      [(0, first), (0, middle), (0, last)] := by
  simp only [sortBottomUpOn, sortBottomUpBy, List.map_cons, List.map_nil]
  rw [mergeAllBy_step, mergePairsBy_step, mergePairsBy_singleton]
  change mergeAllBy _ [[(0, first), (0, middle)], [(0, last)]] = _
  rw [mergeAllBy_step, mergePairsBy_step, mergePairsBy_nil, mergeAllBy_singleton]
  rfl

/-- Reversing the completed runs can move a later equal-key occurrence first. -/
theorem tail_equal_keys {α : Type u} (first middle last : α) :
    sortBottomUpRevOn Prod.fst ([(0, first), (0, middle), (0, last)] : List (Nat × α)) =
      [(0, last), (0, first), (0, middle)] := by
  simp only [sortBottomUpRevOn, sortBottomUpRevBy, List.map_cons, List.map_nil]
  rw [mergeAllRevBy_step, mergePairsRevBy_step, mergePairsRevBy_singleton]
  change mergeAllRevBy _ [[(0, last)], [(0, first), (0, middle)]] = _
  rw [mergeAllRevBy_step, mergePairsRevBy_step, mergePairsRevBy_nil, mergeAllRevBy_singleton]
  rfl

theorem tail_pass_need_not_equal_ordinary_pass :
    mergePairsRevBy natCompare [] [[1], [2], [3]] ≠
      mergePairsBy natCompare [[1], [2], [3]] := by
  rw [mergePairsRevBy_eq_reverse_append, mergePairsBy_step, mergePairsBy_singleton]
  decide

theorem tail_sort_need_not_be_stable :
    ¬ Stable Prod.fst ([(0, "first"), (0, "middle"), (0, "last")] : List (Nat × String))
      (sortBottomUpRevOn Prod.fst [(0, "first"), (0, "middle"), (0, "last")]) := by
  rw [tail_equal_keys]
  intro h
  have wrong := h 0
  simp at wrong

theorem empty_payload :
    sortBottomUpBy (fun x _ : Empty => nomatch x) [] = [] ∧
      sortBottomUpRevBy (fun x _ : Empty => nomatch x) [] = [] :=
  ⟨sortBottomUpBy_nil _, sortBottomUpRevBy_nil _⟩

theorem singleton_payload {α : Type u} (x : α) :
    sortBottomUpOn (fun _ : α => (0 : Nat)) [x] = [x] ∧
      sortBottomUpRevOn (fun _ : α => (0 : Nat)) [x] = [x] :=
  ⟨sortBottomUpBy_singleton _ _, sortBottomUpRevBy_singleton _ _⟩

end Examples.BottomUpSorting

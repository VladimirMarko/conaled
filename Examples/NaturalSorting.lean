import Applications.Sorting.Natural
import Examples.NaturalRuns

/-!
# Connected natural-sort values

The cases distinguish detecting runs from sorting their concatenation, retain
duplicate occurrences and arbitrary payloads, and exercise a comparator that
is compatible only on the input. Concrete equal-key orders are observations
of these inputs, not a general stability theorem.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.NaturalSorting

open Applications.Sorting
open Examples.NaturalRuns (natLT Record mixedRecords mixedRuns)
universe u
variable {α : Type u}

def natCompare (a b : Nat) : Bool := decide (a ≤ b)

theorem empty_payload :
    sortNaturalBy (fun a _ : Empty => nomatch a)
      (fun a _ : Empty => nomatch a) [] = [] := sortNaturalBy_nil _ _

theorem singleton_payload (a : α) :
    sortNaturalOn (fun _ : α => (0 : Nat)) [a] = [a] :=
  sortNaturalBy_singleton _ _ a

theorem ascending : sortNaturalBy natLT natCompare [0, 1, 2] = [0, 1, 2] :=
  sortNaturalOn_of_sorted id [0, 1, 2] (by decide)

theorem descending : sortNaturalBy natLT natCompare [2, 1, 0] = [0, 1, 2] := by
  simpa using sortNaturalOn_of_strictly_descending id [2, 1, 0] (by decide)

/-- The strict descending prefix stops before 2, which starts the next run. -/
theorem three_boundary_runs : runsBy natLT [3, 1, 2] = [[1, 3], [2]] := by
  simp [natLT, runsBy_cons_cons, descBy_cons]

theorem three_boundary : sortNaturalBy natLT natCompare [3, 1, 2] = [1, 2, 3] := by
  rw [sortNaturalBy_eq_mergeAll, three_boundary_runs, mergeAllBy_step,
    mergePairsBy_step, mergePairsBy_nil]
  simp [natCompare]

theorem restart_boundary :
    sortNaturalBy natLT natCompare [1, 3, 2, 4] = [1, 2, 3, 4] := by
  rw [sortNaturalBy_eq_mergeAll, NaturalRuns.restart_boundary, mergeAllBy_step,
    mergePairsBy_step, mergePairsBy_nil]
  simp [natCompare]

/-- Three runs of lengths two, two and one exercise an odd leftover and a second pass. -/
theorem odd_runs : runsBy natLT [1, 3, 2, 4, 0] = [[1, 3], [2, 4], [0]] := by
  simp [natLT, runsBy_cons_cons, ascBy_cons, Batteries.DList.singleton]

theorem odd_runs_value :
    sortNaturalBy natLT natCompare [1, 3, 2, 4, 0] = [0, 1, 2, 3, 4] := by
  have h := sortNaturalOn_correct id ([1, 3, 2, 4, 0] : List Nat)
  exact List.Perm.eq_of_pairwise' (r := fun a b : Nat => a ≤ b) h.1 (by decide)
    (h.2.trans (by decide : ([1, 3, 2, 4, 0] : List Nat).Perm [0, 1, 2, 3, 4]))

theorem duplicate_occurrences :
    (sortNaturalOn id ([2, 1, 2, 0] : List Nat) : Multiset Nat).count 2 = 2 := by
  rw [sortNaturalBy_multiset]
  rfl

/-- Full tagged records cross the detected-run boundary; equal keys select the left one. -/
theorem tagged_exact (first middle last : α) :
    sortNaturalOn Prod.fst ([(1, first), (0, middle), (1, last)] : List (Nat × α)) =
      [(0, middle), (1, first), (1, last)] := by
  simp [sortNaturalOn, sortNaturalBy, runsBy_cons_cons, descBy_cons,
    mergeAllBy_step, mergePairsBy_step]

theorem tagged_correct (xs : List (Nat × α)) :
    KeySorted Prod.fst (sortNaturalOn Prod.fst xs) ∧
      (sortNaturalOn Prod.fst xs).Perm xs := sortNaturalOn_correct Prod.fst xs

theorem mixed_records :
    sortNaturalOn Prod.fst mixedRecords =
      [(1, "D"), (2, "B"), (2, "C"), (3, "A")] := by
  change mergeAllBy (fun a b : Record => decide (a.1 ≤ b.1))
    (runsOn Prod.fst mixedRecords) = _
  rw [NaturalRuns.mixed_records]
  simp [mixedRuns, mergeAllBy_step, mergePairsBy_step]

theorem weak_descent_with_ties :
    sortNaturalOn Prod.fst ([(3, "A"), (3, "B"), (2, "C")] : List Record) =
      [(2, "C"), (3, "A"), (3, "B")] := by
  change mergeAllBy (fun a b : Record => decide (a.1 ≤ b.1))
    (runsOn Prod.fst [(3, "A"), (3, "B"), (2, "C")]) = _
  rw [NaturalRuns.weak_descent_with_ties]
  simp [mergeAllBy_step, mergePairsBy_step]

/-- Reversing the entire weakly descending input would reverse the tied payloads. -/
theorem weak_descent_is_not_reversal :
    sortNaturalOn Prod.fst ([(3, "A"), (3, "B"), (2, "C")] : List Record) ≠
      [(2, "C"), (3, "B"), (3, "A")] := by
  rw [weak_descent_with_ties]
  decide

def nonnegativeCompare (a b : Record) : Bool :=
  if 0 ≤ a.1 ∧ 0 ≤ b.1 then decide (a.1 ≤ b.1) else false

theorem nonnegative_merge_compatible :
    ∀ a ∈ mixedRecords, ∀ b ∈ mixedRecords,
      (nonnegativeCompare a b = true → a.1 ≤ b.1) ∧
      (nonnegativeCompare a b = false → b.1 ≤ a.1) := by
  intro a ha b hb
  simp only [mixedRecords, List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl <;> decide

/-- The scanner's retained negative-key counterexample rules out a global-law shortcut. -/
theorem input_local_correct :
    KeySorted Prod.fst
      (sortNaturalBy NaturalRuns.nonnegativeLT nonnegativeCompare mixedRecords) :=
  sortNaturalBy_sorted_compatible_on Prod.fst _ _ mixedRecords
    NaturalRuns.nonnegative_compatible nonnegative_merge_compatible

theorem arbitrary_operations_preserve_occurrences (lt cmp : α → α → Bool)
    (xs : List α) :
    (sortNaturalBy lt cmp xs).Perm xs ∧
      (sortNaturalBy lt cmp xs).length = xs.length ∧
      ∀ a, a ∈ sortNaturalBy lt cmp xs ↔ a ∈ xs :=
  ⟨sortNaturalBy_perm lt cmp xs, sortNaturalBy_length lt cmp xs,
    mem_sortNaturalBy lt cmp xs⟩

/-- Any list of arbitrary payloads is already sorted for a constant key. -/
theorem constant_key_fixed_point (xs : List α) :
    sortNaturalOn (fun _ : α => (0 : Nat)) xs = xs := by
  apply sortNaturalOn_of_sorted
  simp [KeySorted]

theorem range_fixed_point (n : Nat) :
    sortNaturalBy natLT natCompare (List.range n) = List.range n := by
  apply sortNaturalOn_of_sorted id
  exact List.pairwise_lt_range.imp (fun _ _ h => Nat.le_of_lt h)

end Examples.NaturalSorting

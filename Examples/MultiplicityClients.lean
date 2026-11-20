import Applications.Sequences.Multiplicity
import Applications.Sequences.Occurrences
import Applications.Sorting.Multiplicity
import Applications.Sorting.QuickSort
import Applications.Sorting.TopDown
import Applications.Search.ExactPriority
import Examples.StableSorting

/-!
Multiplicity observations connect occurrence selection, ordinary sorting and
exact priority queues. The cases retain repeated values and distinguish this
observation from membership, stable tie order and arbitrary Boolean tests.
The queue statements use ExactQueue: the weaker keyed interface permits
replacement and does not promise to retain every inserted occurrence.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.MultiplicityClients

open Sequences.Multiplicity
open Applications.Sorting
open Applications.Sorting.Specification
open Search.PriorityInterface

universe u v w
variable {α : Type u} {π : Type v}

section Occurrences
variable [BEq α] [LawfulBEq α]

/-- The existing positional selector removes one occurrence, including when
equal values occur at several distinct positions. -/
theorem picks_contents (xs : List α) (x : α) (rest : List α)
    (h : (x, rest) ∈ Sequences.Occurrences.picks xs) :
    contents xs = union (singleton x) (contents rest) := by
  rcases (Sequences.Occurrences.mem_picks_iff xs x rest).mp h with
    ⟨front, back, rfl, rfl⟩
  exact (perm_contents List.perm_middle).trans
    (contents_cons_union x (front ++ back))

/-- The selected value's residual multiplicity is exactly one smaller. -/
theorem picks_selected_count (xs : List α) (x : α) (rest : List α)
    (h : (x, rest) ∈ Sequences.Occurrences.picks xs) :
    contents xs x = contents rest x + 1 := by
  simpa [union, Sequences.Multiplicity.singleton, Nat.add_comm] using
    congrFun (picks_contents xs x rest h) x

/-- Deleting a selected occurrence leaves every different value's count intact. -/
theorem picks_other_count (xs : List α) (x : α) (rest : List α)
    (h : (x, rest) ∈ Sequences.Occurrences.picks xs) (y : α) (hne : y ≠ x) :
    contents xs y = contents rest y := by
  rcases (Sequences.Occurrences.mem_picks_iff xs x rest).mp h with
    ⟨front, back, rfl, rfl⟩
  exact count_insert_other front back x y hne

end Occurrences

/-- Selecting the first 2 retains the other 2 and the unrelated 1. -/
theorem selected_duplicate :
    contents ([2, 1, 2, 3] : List Nat) 2 = contents [1, 2, 3] 2 + 1 ∧
      contents ([2, 1, 2, 3] : List Nat) 1 = contents [1, 2, 3] 1 := by
  have h : (2, [1, 2, 3]) ∈ Sequences.Occurrences.picks ([2, 1, 2, 3] : List Nat) :=
    by decide
  exact ⟨picks_selected_count _ _ _ h, picks_other_count _ _ _ h 1 (by decide)⟩

/-- A caller may change both its ordering and occurrence observations through
the public bridges, while retaining its proposed implementation unchanged. -/
theorem recover_pairwise_spec (f : List Int → List Int)
    (h : ∀ xs, contents xs = contents (f xs) ∧ Indexed (· ≤ ·) (f xs)) :
    ∀ xs, xs.Perm (f xs) ∧ (f xs).Pairwise (· ≤ ·) :=
  (Applications.Sorting.Multiplicity.indexed_contract_equivalent
    (fun a b : Int => a ≤ b) f).mpr h

/-- Independent first-pivot quicksort and floor-left merge sort become
interchangeable by their contents contracts. This does not identify their
recursion, comparison costs or stable-record guarantees. -/
theorem quick_and_floor_from_contents [LinearOrder α] [BEq α] [LawfulBEq α] :
    quickSortOn (id : α → α) = sortFloorOn (id : α → α) := by
  apply Applications.Sorting.Multiplicity.sorters_eq_of_contents (fun a b : α => a ≤ b)
    (quickSortOn id) (sortFloorOn id)
  · intro xs
    exact ⟨(quickSortOn_correct id xs).1, perm_contents (quickSortOn_correct id xs).2⟩
  · intro xs
    exact ⟨(sortFloorOn_correct id xs).1, perm_contents (sortFloorOn_correct id xs).2⟩

section Queues
variable [LE π] [BEq (α × π)] [LawfulBEq (α × π)]

omit [LawfulBEq (α × π)] in
/-- Exact insertion adds occurrence functions for the new and old entries.
The interface's insertion law applies even before a validity premise is used. -/
theorem exact_add_contents (Q : ExactQueue.{u,v,w} α π)
    (xs : List (α × π)) (q : Q.Carrier) :
    contents (Q.entries (Q.add xs q)) = union (contents xs) (contents (Q.entries q)) :=
  (perm_contents (Q.add_exact xs q)).trans (contents_append xs (Q.entries q))

/-- Successful deletion from a valid queue removes exactly the selected pair.
The minimum-priority claim remains available separately in remove_spec. -/
theorem exact_remove_contents (Q : ExactQueue.{u,v,w} α π)
    (q : Q.Carrier) (e : α × π) (rest : Q.Carrier)
    (hq : Q.Valid q) (hr : Q.remove q = some (e, rest)) :
    contents (Q.entries q) = union (singleton e) (contents (Q.entries rest)) :=
  (perm_contents (Q.remove_spec q e rest hq hr).2.1).trans
    (contents_cons_union e (Q.entries rest))

theorem exact_remove_selected_count (Q : ExactQueue.{u,v,w} α π)
    (q : Q.Carrier) (e : α × π) (rest : Q.Carrier)
    (hq : Q.Valid q) (hr : Q.remove q = some (e, rest)) :
    contents (Q.entries q) e = contents (Q.entries rest) e + 1 := by
  simpa [union, Sequences.Multiplicity.singleton, Nat.add_comm] using
    congrFun (exact_remove_contents Q q e rest hq hr) e

theorem exact_remove_other_count (Q : ExactQueue.{u,v,w} α π)
    (q : Q.Carrier) (e : α × π) (rest : Q.Carrier)
    (hq : Q.Valid q) (hr : Q.remove q = some (e, rest))
    (other : α × π) (hne : other ≠ e) :
    contents (Q.entries q) other = contents (Q.entries rest) other := by
  simpa [union, Sequences.Multiplicity.singleton, hne] using
    congrFun (exact_remove_contents Q q e rest hq hr) other

end Queues

/-- The actual leftist insertion retains both equal pairs, rather than replacing
one by a keyed representative. -/
theorem exact_leftist_duplicates :
    let Q : ExactQueue Nat Nat := exactLeftist
    contents (Q.entries (Q.add [(7, 2), (4, 1), (7, 2)] Q.empty)) (7, 2) = 2 := by
  let Q : ExactQueue Nat Nat := exactLeftist
  change contents (Q.entries (Q.add [(7, 2), (4, 1), (7, 2)] Q.empty)) (7, 2) = 2
  calc
    _ = union (contents [(7, 2), (4, 1), (7, 2)]) (contents (Q.entries Q.empty))
        (7, 2) := congrFun (exact_add_contents Q _ Q.empty) (7, 2)
    _ = 2 := by rw [Q.empty_entries]; rfl

/-- The list realization actually removes the unique lowest-priority pair;
the generic removal theorems preserve both duplicates at the other priority. -/
theorem exact_list_duplicate_removal :
    (exactList (α := Nat) (π := Nat)).remove [(7, 2), (4, 1), (7, 2)] =
        some ((4, 1), [(7, 2), (7, 2)]) ∧
      contents ([(7, 2), (4, 1), (7, 2)] : List (Nat × Nat)) (7, 2) =
        contents [(7, 2), (7, 2)] (7, 2) ∧
      contents ([(7, 2), (4, 1), (7, 2)] : List (Nat × Nat)) (4, 1) =
        contents [(7, 2), (7, 2)] (4, 1) + 1 := by
  let Q : ExactQueue Nat Nat := exactList
  have hr : Q.remove [(7, 2), (4, 1), (7, 2)] =
      some ((4, 1), [(7, 2), (7, 2)]) := by
    change listRemove ([(7, 2), (4, 1), (7, 2)] : List (Nat × Nat)) =
      some ((4, 1), [(7, 2), (7, 2)])
    simp [listRemove, List.mergeSort, List.MergeSort.Internal.splitInTwo_fst,
      List.MergeSort.Internal.splitInTwo_snd]
  exact ⟨hr,
    exact_remove_other_count Q _ _ _ trivial hr (7, 2) (by decide),
    exact_remove_selected_count Q _ _ _ trivial hr⟩

/-- Membership cannot tell one occurrence from two, while contents can. -/
theorem multiplicities_matter :
    (∀ n : Nat, n ∈ [1, 1] ↔ n ∈ [1]) ∧
      contents ([1, 1] : List Nat) ≠ contents [1] := by
  refine ⟨by simp, ?_⟩
  intro h
  have hlen := ((contents_eq_iff_perm _ _).mp h).length_eq
  contradiction

/-- Reordering a list keeps its function-valued observation and its duplicates. -/
theorem reordered_contents :
    contents ([2, 1, 1] : List Nat) = contents [1, 2, 1] :=
  perm_contents (List.Perm.swap _ _ _)

theorem concatenated_occurrences : contents ([1, 2] ++ [1] : List Nat) 1 = 2 := by
  rw [contents_append]
  rfl

/-- Counts for an arbitrary Boolean test need not characterize true permutation.
LawfulBEq is a sufficient assumption for the bridge, not a claimed necessary
characterization of every possible admissible Boolean test. -/
theorem lawful_equality_matters :
    (letI : BEq Nat := ⟨fun _ _ => false⟩
     contents ([1] : List Nat) = contents []) ∧
      ¬ ([1] : List Nat).Perm [] := by
  constructor
  · funext n
    rfl
  · intro h
    have wrong := h.length_eq
    contradiction

/-- The existing equal-key counterexample remains a counterexample after
switching from permutation to contents and from pairwise to indexed ordering. -/
theorem sorted_contents_do_not_imply_stability :
    Indexed (fun a b : StableSorting.Record => a.1 ≤ b.1)
      [(2, "last"), (2, "first")] ∧
      contents ([(2, "first"), (2, "last")] : List StableSorting.Record) =
        contents [(2, "last"), (2, "first")] ∧
      ¬ Stable Prod.fst ([(2, "first"), (2, "last")] : List StableSorting.Record)
        [(2, "last"), (2, "first")] := by
  obtain ⟨hs, hp, hn⟩ := StableSorting.sorted_permutation_not_stable
  exact ⟨(keySorted_iff_indexed Prod.fst _).mp hs, perm_contents hp.symm, hn⟩

end Examples.MultiplicityClients

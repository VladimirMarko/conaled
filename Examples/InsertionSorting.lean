import Applications.Sorting.InsertionObservations
import Applications.Resources.InsertionSort
import Examples.StableSorting

/-!
VFA 2.1 Sort: the exact Nat insertion recurrence, all three sortedness
specifications, and both correctness routes. The optional indexed route uses
the independent positional proofs in InsertionObservations. Stable records and
the FDSA measured implementation are clients of the same shared algorithms.
The source's comparison, allocation and garbage-collection prose has separate
obligations; the measured observations below count declared recursive calls.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.InsertionSorting
open Applications.Sorting
open Applications.Sorting.Specification

/-- The pinned operation uses the source's non-strict, left-on-ties branch. -/
abbrev insert := List.orderedInsert (α := Nat) (· ≤ ·)

/-- The tail is sorted before inserting its former head. -/
abbrev sort := List.insertionSort (α := Nat) (· ≤ ·)

/-- IsChain supplies the source's empty, singleton and adjacent-cons rules. -/
abbrev Sorted (xs : List Nat) : Prop := xs.IsChain (· ≤ ·)

abbrev IndexedSorted := Indexed (α := Nat) (· ≤ ·)

def GetDSorted (xs : List Nat) : Prop :=
  ∀ i j : Nat, i < j → j < xs.length → xs.getD i 0 ≤ xs.getD j 0

/-- Occurrence-sensitive permutation and adjacent ordering, for every input. -/
def IsSortingAlgorithm (f : List Nat → List Nat) : Prop :=
  ∀ xs, xs.Perm (f xs) ∧ Sorted (f xs)

theorem insert_nil (a : Nat) : insert a [] = [a] := rfl

theorem insert_cons (a b : Nat) (xs : List Nat) :
    insert a (b :: xs) = if a ≤ b then a :: b :: xs else b :: insert a xs := rfl

theorem sort_nil : sort [] = [] := rfl

theorem sort_cons (a : Nat) (xs : List Nat) :
    sort (a :: xs) = insert a (sort xs) := rfl

theorem sorted_nil : Sorted [] := by decide

theorem sorted_1 (a : Nat) : Sorted [a] := by simp [Sorted]

theorem sorted_cons (a b : Nat) (xs : List Nat)
    (hab : a ≤ b) (h : Sorted (b :: xs)) : Sorted (a :: b :: xs) :=
  List.isChain_cons_cons.mpr ⟨hab, h⟩

/-- Ordinary route: reuse the library's branch proof of ordered insertion. -/
theorem insert_sorted (a : Nat) (xs : List Nat) (h : Sorted xs) :
    Sorted (insert a xs) :=
  List.isChain_iff_pairwise.mpr
    (List.Pairwise.orderedInsert a xs (List.isChain_iff_pairwise.mp h))

theorem sort_sorted (xs : List Nat) : Sorted (sort xs) := by
  induction xs with
  | nil => exact sorted_nil
  | cons a xs ih => exact insert_sorted a (sort xs) ih

theorem insert_perm (a : Nat) (xs : List Nat) : (a :: xs).Perm (insert a xs) :=
  (List.perm_orderedInsert (· ≤ ·) a xs).symm

theorem sort_perm (xs : List Nat) : xs.Perm (sort xs) := by
  induction xs with
  | nil => exact List.Perm.refl []
  | cons a xs ih => exact (ih.cons a).trans (insert_perm a (sort xs))

theorem insertion_sort_correct : IsSortingAlgorithm sort :=
  fun xs => ⟨sort_perm xs, sort_sorted xs⟩

theorem sorted_indexedSorted (xs : List Nat) : Sorted xs → IndexedSorted xs :=
  (adjacent_iff_indexed (· ≤ ·) xs).mp

theorem indexedSorted_sorted (xs : List Nat) : IndexedSorted xs → Sorted xs :=
  (adjacent_iff_indexed (· ≤ ·) xs).mpr

theorem getDSorted_iff_indexedSorted (xs : List Nat) : GetDSorted xs ↔ IndexedSorted xs :=
  (boundedIndexed_iff_getD (· ≤ ·) 0 xs).symm.trans
    (indexed_iff_boundedIndexed (· ≤ ·) 0 xs).symm

/-- Optional route: no ordinary sortedness result or equivalence is used. -/
theorem nth_error_insert (xs : List Nat) (a i iv : Nat)
    (h : (insert a xs)[i]? = some iv) :
    a = iv ∨ ∃ j : Nat, xs[j]? = some iv :=
  getElem?_orderedInsert_origin (· ≤ ·) a xs i iv h

theorem insert_indexedSorted (a : Nat) (xs : List Nat) (h : IndexedSorted xs) :
    IndexedSorted (insert a xs) := indexed_orderedInsert (· ≤ ·) a xs h

theorem sort_indexedSorted (xs : List Nat) : IndexedSorted (sort xs) :=
  indexed_insertionSort (· ≤ ·) xs

/-- Independent calculation from the source, retaining all repeated entries. -/
theorem sort_pi :
    sort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] = [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9] := rfl

theorem pi_contract :
    ([3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] : List Nat).Perm
      [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9] ∧
      Sorted [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9] := by
  simpa only [sort_pi] using insertion_sort_correct [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]

theorem pi_indexed : IndexedSorted [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9] := by
  simpa only [sort_pi] using sort_indexedSorted [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]

/-- Stopping preserves the arbitrary suffix value, without a sorted-tail premise. -/
theorem insert_suffix (tail : List Nat) :
    insert 7 ([1, 3, 4, 8] ++ tail) = [1, 3, 4, 7, 8] ++ tail := rfl

theorem insert_source_tail :
    insert 7 [1, 3, 4, 8, 12, 14, 18] = [1, 3, 4, 7, 8, 12, 14, 18] :=
  insert_suffix [12, 14, 18]

theorem source_ties : insert 2 [2, 0] = [2, 2, 0] := rfl

/-- Insertion preserves occurrences on unsorted input but need not sort it. -/
theorem unsorted_insertion :
    ([1, 2, 0] : List Nat).Perm (insert 1 [2, 0]) ∧ ¬ Sorted (insert 1 [2, 0]) :=
  ⟨insert_perm 1 [2, 0], by decide⟩

theorem sorted_fixed (xs : List Nat) (h : Sorted xs) : sort xs = xs :=
  (List.isChain_iff_pairwise.mp h).insertionSort_eq

theorem sort_idempotent (xs : List Nat) : sort (sort xs) = sort xs :=
  sorted_fixed (sort xs) (sort_sorted xs)

theorem signed_indexed : Indexed (fun a b : Int => a ≤ b) [-3, -1, 2] :=
  (pairwise_iff_indexed _ _).mp (by decide)

/-- Valid-index bounds make two very different defaults interchangeable. -/
theorem signed_defaults :
    BoundedIndexed (fun a b : Int => a ≤ b) (-999) [-3, -1, 2] ∧
      BoundedIndexed (fun a b : Int => a ≤ b) 999 [-3, -1, 2] := by
  have h := (indexed_iff_boundedIndexed _ (-999) _).mp signed_indexed
  exact ⟨h, (boundedIndexed_default_irrelevant _ (-999) 999 _).mp h⟩

theorem nontransitive_boundary :
    ([0, 1, 2] : List Nat).IsChain (fun a b => b = a + 1) ∧
      ¬ Indexed (fun a b : Nat => b = a + 1) [0, 1, 2] := by
  refine ⟨by decide, ?_⟩
  intro h
  have wrong := h 0 2 0 2 (by decide) rfl rfl
  contradiction

theorem index_bound_matters :
    ([1] : List Nat).Pairwise (· ≤ ·) ∧
      ¬ (∀ i j : Nat, i < j → (([1] : List Nat)[i]?).getD 0 ≤
        (([1] : List Nat)[j]?).getD 0) := by
  refine ⟨by decide, ?_⟩
  intro h
  have wrong := h 0 1 (by decide)
  contradiction

/-- The direct positional theorem orders keys without ordering record payloads. -/
theorem records_indexed :
    Indexed (fun a b : StableSorting.Record => a.1 ≤ b.1)
      (insertionOn Prod.fst StableSorting.input) := by
  let r := fun a b : StableSorting.Record => a.1 ≤ b.1
  let : Std.Total r := ⟨fun a b => le_total a.1 b.1⟩
  let : IsTrans StableSorting.Record r := ⟨fun _ _ _ hab hbc => le_trans hab hbc⟩
  exact indexed_insertionSort r StableSorting.input

theorem records_expected_indexed :
    Indexed (fun a b : StableSorting.Record => a.1 ≤ b.1) StableSorting.expected := by
  simpa only [StableSorting.insertion_sort_records] using records_indexed

/-- The independent stable merge realization carries the new observation too. -/
theorem merge_records_indexed :
    Indexed (fun a b : StableSorting.Record => a.1 ≤ b.1)
      (sortOn Prod.fst StableSorting.input) := by
  rw [sortOn_eq_insertionOn]
  exact records_indexed

/-- Indexed ordering and permutation still do not imply equal-key stability. -/
theorem sorted_indexed_permutation_not_stable :
    Indexed (fun a b : StableSorting.Record => a.1 ≤ b.1)
      [(2, "last"), (2, "first")] ∧
      ([(2, "last"), (2, "first")] : List StableSorting.Record).Perm
        [(2, "first"), (2, "last")] ∧
      ¬ Stable Prod.fst ([(2, "first"), (2, "last")] : List StableSorting.Record)
        [(2, "last"), (2, "first")] := by
  obtain ⟨hs, hp, hn⟩ := StableSorting.sorted_permutation_not_stable
  exact ⟨(keySorted_iff_indexed Prod.fst _).mp hs, hp, hn⟩

/-- Reuse FDSA's executed value and recursive-call tariff through the new contract.
This is not the distinct n*(n-1)/2 comparison tariff. -/
theorem measured_sort_spec (xs : List Nat) :
    IndexedSorted (Resources.InsertionSort.sortRun (· ≤ ·) xs).1 ∧
      xs.Perm (Resources.InsertionSort.sortRun (· ≤ ·) xs).1 ∧
      2 * (Resources.InsertionSort.sortRun (· ≤ ·) xs).2 ≤
        (xs.length + 1) * (xs.length + 2) := by
  rw [Resources.InsertionSort.sortRun_value]
  exact ⟨sort_indexedSorted xs, sort_perm xs,
    Resources.InsertionSort.sortRun_double_cost_le (· ≤ ·) xs⟩

/-- This stopping branch has four declared recursive calls, independent of the tail.
The suffix equality is a value fact; it certifies no physical allocation/sharing. -/
theorem measured_insert_stopping (tail : List Nat) :
    (Resources.InsertionSort.insertRun (· ≤ ·) 7 ([1, 3, 4, 8] ++ tail)).1 =
      [1, 3, 4, 7, 8] ++ tail ∧
      (Resources.InsertionSort.insertRun (· ≤ ·) 7 ([1, 3, 4, 8] ++ tail)).2 = 4 := by
  constructor
  · rw [Resources.InsertionSort.insertRun_value]
    exact insert_suffix tail
  · rfl

end Examples.InsertionSorting

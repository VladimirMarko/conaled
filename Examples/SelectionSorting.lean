import Applications.Sorting.SourceSelection
import Applications.Sorting.Uniqueness
import Applications.Resources.SelectionSort
import Applications.Resources.InsertionWork
import Applications.Selection.FixedRank
import Examples.MultisetSorting

/-!
VFA 2.1 Selection: all source statements, both executable recursion accounts,
and the direct multiset route. The actual source remainder is retained. Ordinary
sorting correctness is separated from stability and unit comparison counts.
The exact source inventory and prose dispositions are in vfa-coverage.md.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SelectionSorting

open Applications.Sorting Resources

abbrev select := SourceSelection.select (α := Nat) (· ≤ ·)
abbrev selsort := SourceSelection.sortFuel (α := Nat) (· ≤ ·)
abbrev selectionSort := SourceSelection.sort (α := Nat) (· ≤ ·)
abbrev selsort' := SourceSelection.sortWF (α := Nat) (· ≤ ·)

/-- Both source chapters use the same adjacent empty/singleton/cons relation. -/
abbrev Sorted := InsertionSorting.Sorted
abbrev IsSortingAlgorithm := InsertionSorting.IsSortingAlgorithm

theorem select_nil (x : Nat) : select x [] = (x, []) := SourceSelection.select_nil _ x

/-- Nat's Boolean test reflects the decidable relation in both source branches. -/
theorem select_cons (x h : Nat) (t : List Nat) :
    select x (h :: t) = if decide (x ≤ h) then
      ((select x t).1, h :: (select x t).2)
    else ((select h t).1, x :: (select h t).2) := by
  by_cases hx : x ≤ h <;> simp [SourceSelection.select_cons, hx]

theorem selsort_zero (xs : List Nat) : selsort xs 0 = [] := SourceSelection.sortFuel_zero _ xs
theorem selsort_nil (n : Nat) : selsort [] n = [] := SourceSelection.sortFuel_nil _ n
theorem selsort_cons (x : Nat) (xs : List Nat) (n : Nat) :
    selsort (x :: xs) (n + 1) = (select x xs).1 :: selsort (select x xs).2 n :=
  SourceSelection.sortFuel_cons _ x xs n

theorem selectionSort_eq (xs : List Nat) : selectionSort xs = selsort xs xs.length := rfl

theorem sorted_nil : Sorted [] := InsertionSorting.sorted_nil
theorem sorted_1 (x : Nat) : Sorted [x] := InsertionSorting.sorted_1 x
theorem sorted_cons (x y : Nat) (xs : List Nat) (hxy : x ≤ y)
    (hs : Sorted (y :: xs)) : Sorted (x :: y :: xs) :=
  InsertionSorting.sorted_cons x y xs hxy hs

/-- The source quantifies two unused pair components; they remain parameters. -/
theorem pairs_example (a _c x : Nat) (b _d l : List Nat)
    (h : (a, b) = (let (c, d) := select x l; (c, d))) : (a, b) = select x l := by
  cases hp : select x l with
  | mk c d => simpa only [hp] using h

theorem select_perm (x : Nat) (l : List Nat) (y : Nat) (rest : List Nat)
    (h : select x l = (y, rest)) : (x :: l).Perm (y :: rest) := by
  simpa only [h] using (SourceSelection.select_perm (· ≤ ·) x l).symm

theorem select_rest_length (x : Nat) (l : List Nat) (y : Nat) (rest : List Nat)
    (h : select x l = (y, rest)) : l.length = rest.length := by
  have hp := (select_perm x l y rest h).length_eq
  exact Nat.succ.inj hp

theorem selsort_perm (n : Nat) (l : List Nat) (hn : l.length = n) :
    l.Perm (selsort l n) := (SourceSelection.sortFuel_perm (· ≤ ·) l n hn.le).symm

theorem selectionSort_perm (l : List Nat) : l.Perm (selectionSort l) :=
  (SourceSelection.sort_perm (· ≤ ·) l).symm

theorem select_fst_leq (al bl : List Nat) (x y : Nat)
    (h : select x al = (y, bl)) : y ≤ x := by
  simpa only [h] using SourceSelection.select_le_seed (· ≤ ·) x al

/-- The source's Forall lower bound, with the membership observation exposed. -/
def IsLowerBound (x : Nat) (xs : List Nat) : Prop := List.Forall (fun y => x ≤ y) xs

theorem isLowerBound_iff (x : Nat) (xs : List Nat) : IsLowerBound x xs ↔ ∀ y ∈ xs, x ≤ y :=
  List.forall_iff_forall_mem

theorem isLowerBound_le_one (lst : List Nat) (y n : Nat)
    (h : IsLowerBound y lst) (hn : n ∈ lst) : y ≤ n := (isLowerBound_iff y lst).mp h n hn

theorem select_smallest (al bl : List Nat) (x y : Nat)
    (h : select x al = (y, bl)) : IsLowerBound y bl := by
  apply (isLowerBound_iff y bl).mpr
  simpa only [h] using SourceSelection.select_smallest (· ≤ ·) x al

theorem select_in (al bl : List Nat) (x y : Nat)
    (h : select x al = (y, bl)) : y ∈ x :: al := by
  simpa only [h] using SourceSelection.select_mem (· ≤ ·) x al

theorem cons_of_small_maintains_sort (bl : List Nat) (y n : Nat)
    (hn : n = bl.length) (hb : IsLowerBound y bl) (hs : Sorted (selsort bl n)) :
    Sorted (y :: selsort bl n) := by
  apply List.isChain_iff_pairwise.mpr
  refine List.pairwise_cons.mpr ⟨?_, List.isChain_iff_pairwise.mp hs⟩
  intro a ha
  exact isLowerBound_le_one bl y a hb ((selsort_perm n bl hn.symm).mem_iff.mpr ha)

theorem selsort_sorted (n : Nat) (al : List Nat) (_hn : al.length = n) :
    Sorted (selsort al n) := List.isChain_iff_pairwise.mpr (SourceSelection.sortFuel_pairwise (· ≤ ·) al n)

theorem selectionSort_sorted (al : List Nat) : Sorted (selectionSort al) :=
  List.isChain_iff_pairwise.mpr (SourceSelection.sort_pairwise (· ≤ ·) al)

theorem selectionSort_is_correct : IsSortingAlgorithm selectionSort :=
  fun xs => ⟨selectionSort_perm xs, selectionSort_sorted xs⟩

theorem selsort'_nil : selsort' [] = [] := SourceSelection.sortWF_nil _
theorem selsort'_cons (x : Nat) (xs : List Nat) :
    selsort' (x :: xs) = (select x xs).1 :: selsort' (select x xs).2 :=
  SourceSelection.sortWF_cons _ x xs

theorem selsort'_perm (n : Nat) (l : List Nat) (_hn : l.length = n) :
    l.Perm (selsort' l) := (SourceSelection.sortWF_perm (· ≤ ·) l).symm

theorem cons_of_small_maintains_sort' (bl : List Nat) (y : Nat)
    (hb : IsLowerBound y bl) (hs : Sorted (selsort' bl)) : Sorted (y :: selsort' bl) := by
  apply List.isChain_iff_pairwise.mpr
  refine List.pairwise_cons.mpr ⟨?_, List.isChain_iff_pairwise.mp hs⟩
  intro a ha
  exact isLowerBound_le_one bl y a hb ((SourceSelection.sortWF_perm (· ≤ ·) bl).mem_iff.mp ha)

theorem selsort'_sorted (n : Nat) (al : List Nat) (_hn : al.length = n) :
    Sorted (selsort' al) := List.isChain_iff_pairwise.mpr (SourceSelection.sortWF_pairwise (· ≤ ·) al)

theorem selsort'_is_correct : IsSortingAlgorithm selsort' :=
  fun xs => ⟨selsort'_perm xs.length xs rfl, selsort'_sorted xs.length xs rfl⟩

/-- This uses the direct contents recurrence, not the ordinary Perm theorem. -/
theorem select_contents (al bl : List Nat) (x y : Nat)
    (h : select x al = (y, bl)) :
    Sequences.Multiplicity.union (Sequences.Multiplicity.singleton x) (Sequences.Multiplicity.contents al) =
      Sequences.Multiplicity.union (Sequences.Multiplicity.singleton y) (Sequences.Multiplicity.contents bl) := by
  have hc := (SourceSelection.select_contents (· ≤ ·) x al).symm
  simpa only [h, Sequences.Multiplicity.contents_cons_union] using hc

/-- The source's redundant n refers to the input; the output is the full sort. -/
theorem selectionSort_contents (n : Nat) (l : List Nat) (_hn : l.length = n) :
    Sequences.Multiplicity.contents l = Sequences.Multiplicity.contents (selectionSort l) := (SourceSelection.sort_contents (· ≤ ·) l).symm

theorem sorted_iff_sorted (l : List Nat) : Sorted l ↔ InsertionSorting.Sorted l := Iff.rfl

theorem selection_sort_correct' : MultisetSorting.IsSortingAlgorithm selectionSort :=
  fun xs => ⟨selectionSort_contents xs.length xs rfl,
    (sorted_iff_sorted _).mp (selectionSort_sorted xs)⟩

/-! Source calculations and connected fuel/termination clients. -/

/-- The returned remainder is not a structural tail of the input tail. -/
theorem reconstructed_remainder : select 1 [0, 2] = (0, [1, 2]) := rfl
theorem select_true_branch : select 1 [3, 2] = (1, [3, 2]) := rfl
theorem select_false_branch : select 3 [1, 2] = (1, [3, 2]) := rfl
theorem select_tie_branch : select 2 [2, 0] = (0, [2, 2]) := rfl

theorem returned_remainder_length : (select 1 [0, 2]).2.length = 2 :=
  SourceSelection.select_length (· ≤ ·) 1 [0, 2]

theorem partial_output : selsort [3, 1, 4, 1, 5] 3 = [1, 1, 3] := rfl

theorem out_of_fuel : selsort [3, 1, 4, 1, 5] 3 ≠ [1, 1, 3, 4, 5] := by
  intro h
  have hl : (selsort [3, 1, 4, 1, 5] 3).length = 3 :=
    SourceSelection.sortFuel_length (· ≤ ·) [3, 1, 4, 1, 5] 3
  rw [h] at hl
  contradiction

theorem extra_fuel : selsort [3, 1, 4, 1, 5] 10 = [1, 1, 3, 4, 5] := by
  change SourceSelection.sortFuel (α := Nat) (· ≤ ·) [3, 1, 4, 1, 5] 10 = _
  rw [SourceSelection.sortFuel_saturated (α := Nat) (· ≤ ·) [3, 1, 4, 1, 5] 10 (by decide)]
  rfl

theorem sort_pi : selectionSort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] =
    [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9] := rfl

theorem pi_contract :
    ([3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] : List Nat).Perm
      [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9] ∧ Sorted [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9] := by
  simpa only [sort_pi] using selectionSort_is_correct [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]

/-- The independent well-founded equations are exercised directly. -/
theorem selsort'_example : selsort' [3, 1, 4, 1, 5, 9, 2, 6, 5] =
    [1, 1, 2, 3, 4, 5, 5, 6, 9] := by
  simp [selsort'_cons, select, SourceSelection.select, selsort'_nil]

theorem wf_example_contract :
    ([3, 1, 4, 1, 5, 9, 2, 6, 5] : List Nat).Perm [1, 1, 2, 3, 4, 5, 5, 6, 9] ∧
      Sorted [1, 1, 2, 3, 4, 5, 5, 6, 9] := by
  simpa only [selsort'_example] using selsort'_is_correct [3, 1, 4, 1, 5, 9, 2, 6, 5]

theorem boundary_values : selectionSort [] = [] ∧ selectionSort [7] = [7] ∧
    selsort [7] 0 = [] ∧ selsort [7] 1 = [7] ∧ selsort [] 5 = [] := by decide

theorem partial_ordered_but_not_permutation :
    Sorted (selsort [3, 1, 4, 1, 5] 3) ∧
      ¬ (selsort [3, 1, 4, 1, 5] 3).Perm [3, 1, 4, 1, 5] := by
  refine ⟨List.isChain_iff_pairwise.mpr (SourceSelection.sortFuel_pairwise (· ≤ ·) _ 3), ?_⟩
  rw [SourceSelection.sortFuel_perm_iff]
  decide

theorem sorted_fixed (xs : List Nat) (hs : Sorted xs) : selectionSort xs = xs :=
  SourceSelection.sort_of_pairwise (· ≤ ·) xs (List.isChain_iff_pairwise.mp hs)

theorem sort_idempotent (xs : List Nat) : selectionSort (selectionSort xs) = selectionSort xs :=
  SourceSelection.sort_idempotent (· ≤ ·) xs

/-! Reuse across ordinary sorting and minimum observations. -/

theorem agrees_with_insertion (xs : List Nat) : selectionSort xs = InsertionSorting.sort xs :=
  sorters_eq_at (· ≤ ·) selectionSort InsertionSorting.sort xs
    (SourceSelection.sort_correct (· ≤ ·) xs)
    ⟨List.isChain_iff_pairwise.mp (InsertionSorting.sort_sorted xs),
      (InsertionSorting.sort_perm xs).symm⟩

universe u v
theorem minimum_agrees {α : Type u} [LinearOrder α] (x : α) (xs : List α) :
    Applications.Selection.FixedRank.select0 (x :: xs) = some (SourceSelection.select (· ≤ ·) x xs).1 :=
  (Applications.Selection.FixedRank.select0_some_iff_min _ _).mpr
    ⟨SourceSelection.select_mem (· ≤ ·) x xs, SourceSelection.select_lower (· ≤ ·) x xs⟩

/-- Payloads carry no equality or order requirement. -/
theorem keyed_correct {α : Type u} {κ : Type v} [LE κ] [DecidableLE κ]
    [Std.IsLinearPreorder κ] (key : α → κ) (xs : List α) :
    KeySorted key (SourceSelection.sort (fun a b => key a ≤ key b) xs) ∧
      (SourceSelection.sort (fun a b => key a ≤ key b) xs).Perm xs := by
  let r := fun a b : α => key a ≤ key b
  let : Std.Total r := ⟨fun a b => Std.le_total (a := key a) (b := key b)⟩
  let : IsTrans α r := ⟨fun _ _ _ hab hbc => Std.le_trans hab hbc⟩
  exact SourceSelection.sort_correct r xs

abbrev Record := Nat × String
def records : List Record := [(2, "a"), (2, "b"), (1, "c")]
def RecordOrder (a b : Record) : Prop := a.1 ≤ b.1
instance : DecidableRel RecordOrder := fun a b => inferInstanceAs (Decidable (a.1 ≤ b.1))

/-- Equal keys retain the seed in the selected position, including its payload. -/
theorem tied_seed_retained : SourceSelection.select RecordOrder (2, "a") [(2, "b")] =
    ((2, "a"), [(2, "b")]) :=
  SourceSelection.select_of_lower RecordOrder (2, "a") [(2, "b")] (by simp [RecordOrder])

theorem record_output : SourceSelection.sort RecordOrder records = [(1, "c"), (2, "b"), (2, "a")] := rfl

theorem record_contract : KeySorted Prod.fst (SourceSelection.sort RecordOrder records) ∧
    (SourceSelection.sort RecordOrder records).Perm records := keyed_correct Prod.fst records

/-- The two equal-key records are reversed by this actual source execution. -/
theorem selection_not_stable : ¬ Stable Prod.fst records (SourceSelection.sort RecordOrder records) := by
  intro hs
  have h := hs 2
  rw [record_output] at h
  have bad : ([(2, "b"), (2, "a")] : List Record) = [(2, "a"), (2, "b")] := h
  contradiction

theorem selection_records_ne_insertion : SourceSelection.sort RecordOrder records ≠ insertionOn Prod.fst records := by
  intro h
  apply selection_not_stable
  rw [h]
  exact (insertionOn_spec Prod.fst records).stable

/-- Antisymmetry is on the observed keys; it is not assumed on records. -/
theorem key_lists_agree {α : Type u} {κ : Type v} [LinearOrder κ]
    (key : α → κ) (xs : List α) :
    (SourceSelection.sort (fun a b => key a ≤ key b) xs).map key = sortOn id (xs.map key) := by
  have hs := keyed_correct key xs
  have ht := sortOn_correct id (xs.map key)
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·))
  · simpa only [List.pairwise_map, Function.comp_def] using hs.1
  · exact ht.1
  · exact (hs.2.map key).trans ht.2.symm

theorem equality_relation_boundary :
    (SourceSelection.sort (α := Nat) (· = ·) [1, 2]).Perm [1, 2] ∧
      ¬ (SourceSelection.sort (α := Nat) (· = ·) [1, 2]).Pairwise (· = ·) :=
  ⟨SourceSelection.sort_perm (· = ·) [1, 2], by decide⟩

def Cyclic (a b : Fin 3) : Prop := a = b ∨ (a.val + 1) % 3 = b.val
instance : DecidableRel Cyclic := fun a b => inferInstanceAs (Decidable (a = b ∨ (a.val + 1) % 3 = b.val))

/-- Totality by itself does not make the source output pairwise ordered. -/
theorem transitivity_boundary :
    (∀ a b : Fin 3, Cyclic a b ∨ Cyclic b a) ∧
      ¬ (SourceSelection.sort Cyclic [0, 1, 2]).Pairwise Cyclic := by decide

/-! Executed comparison clients, under the same unit charge as CTB-80. -/

theorem measured_select : SelectionSort.selectRun (· ≤ ·) 1 [0, 2] = ((0, [1, 2]), 2) :=
  SelectionSort.selectRun_exact (· ≤ ·) 1 [0, 2]

theorem measured_partial : SelectionSort.sortFuelRun (· ≤ ·) [3, 1, 4, 1, 5] 3 = ([1, 1, 3], 9) :=
  SelectionSort.sortFuelRun_exact (· ≤ ·) [3, 1, 4, 1, 5] 3

theorem measured_full : SelectionSort.sortRun (· ≤ ·) [3, 1, 4, 1, 5] = ([1, 1, 3, 4, 5], 10) :=
  SelectionSort.sortFuelRun_exact (· ≤ ·) [3, 1, 4, 1, 5] 5

theorem measured_excess : SelectionSort.sortFuelRun (· ≤ ·) [3, 1, 4, 1, 5] 10 =
    ([1, 1, 3, 4, 5], 10) := by
  rw [SelectionSort.sortFuelRun_saturated (· ≤ ·) _ 10 (by decide)]
  exact measured_full

theorem measured_boundaries : SelectionSort.sortRun (α := Nat) (· ≤ ·) [] = ([], 0) ∧
    SelectionSort.sortRun (· ≤ ·) [7] = ([7], 0) ∧ SelectionSort.sortFuelRun (· ≤ ·) [7] 0 = ([], 0) := by decide

theorem insertion_comparisons_le_selection {α : Type u} (r : α → α → Prop)
    [DecidableRel r] (xs : List α) : InsertionSort.sortComparisons r xs ≤ (SelectionSort.sortRun r xs).2 := by
  rw [SelectionSort.sortRun_exact_comparisons]
  exact InsertionSort.sortComparisons_le r xs

theorem insertion_worst_matches_selection {α : Type u} (r : α → α → Prop)
    [DecidableRel r] (xs : List α) (hs : xs.Pairwise (fun a b => ¬ r a b)) :
    InsertionSort.sortComparisons r xs = (SelectionSort.sortRun r xs).2 := by
  rw [InsertionSort.sortComparisons_of_opposite r xs hs, SelectionSort.sortRun_exact_comparisons]

theorem insertion_best_strict {α : Type u} (r : α → α → Prop) [DecidableRel r]
    (xs : List α) (hs : xs.Pairwise r) (hn : 3 ≤ xs.length) :
    InsertionSort.sortComparisons r xs < (SelectionSort.sortRun r xs).2 := by
  rw [InsertionSort.sortComparisons_of_pairwise r xs hs]
  have hc := SelectionSort.sortRun_double r xs
  have hsub : xs.length - 1 + 1 = xs.length := Nat.sub_add_cancel (by omega)
  nlinarith

theorem ascending_comparison_advantage (n : Nat) (hn : 3 ≤ n) :
    InsertionSort.sortComparisons (· ≤ ·) (List.range n) < (SelectionSort.sortRun (· ≤ ·) (List.range n)).2 := by
  apply insertion_best_strict
  · exact List.pairwise_le_range
  · simpa only [List.length_range] using hn

theorem equal_comparison_advantage (a n : Nat) (hn : 3 ≤ n) :
    InsertionSort.sortComparisons (· ≤ ·) (List.replicate n a) <
      (SelectionSort.sortRun (· ≤ ·) (List.replicate n a)).2 := by
  apply insertion_best_strict
  · exact List.pairwise_of_forall_mem_list (fun _ hx _ hy => by
      have h₁ := (List.mem_replicate.mp hx).2
      have h₂ := (List.mem_replicate.mp hy).2
      omega)
  · simpa only [List.length_replicate] using hn

theorem descending_comparison_equality (n : Nat) :
    InsertionSort.sortComparisons (· ≤ ·) (List.range n).reverse =
      (SelectionSort.sortRun (· ≤ ·) (List.range n).reverse).2 := by
  rw [InsertionSort.sortComparisons_reverse_range, SelectionSort.sortRun_exact_comparisons,
    List.length_reverse, List.length_range]

theorem same_values_different_comparisons :
    (SelectionSort.sortRun (· ≤ ·) [1, 2, 3, 4]).1 = (InsertionSort.sortMeasured (· ≤ ·) [1, 2, 3, 4]).1 ∧
      (SelectionSort.sortRun (· ≤ ·) [1, 2, 3, 4]).2 ≠ InsertionSort.sortComparisons (· ≤ ·) [1, 2, 3, 4] := by
  constructor
  · rw [SelectionSort.sortRun_value, InsertionSort.sortMeasured_value]
    exact agrees_with_insertion _
  · decide

end Examples.SelectionSorting

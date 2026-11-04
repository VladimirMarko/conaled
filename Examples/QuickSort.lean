import Applications.Sorting.QuickSort
import Mathlib.Data.Multiset.Filter

/-! First-pivot source observations and the arbitrary-suffix accumulator law.
The expected mixed prefix is [0,1,2,2,3], while the unsorted overlapping suffix
[4,0,2] is retained verbatim. No count, allocation, or tail-recursion result is
inferred from these list equalities.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.QuickSort
open Applications.Sorting
universe u v
variable {α : Type u} {κ : Type v}

/-- The source list-filter/multiset-filter correspondence is the standard quotient law. -/
theorem source_filter_multiset (p : α → Prop) [DecidablePred p] (xs : List α) :
    ((xs.filter (fun x => decide (p x)) : List α) : Multiset α) =
      Multiset.filter p (xs : Multiset α) :=
  (Multiset.filter_coe p xs).symm

/-- Complementarity need hold only on the multiset being partitioned. -/
theorem source_complementary_multiset (p q : α → Prop) [DecidablePred p]
    [DecidablePred q] (s : Multiset α) (h : ∀ x ∈ s, p x ↔ ¬ q x) :
    Multiset.filter p s + Multiset.filter q s = s := by
  have hp : Multiset.filter p s = Multiset.filter (fun x => ¬ q x) s :=
    Multiset.filter_congr h
  rw [hp, add_comm]
  exact Multiset.filter_add_not q s

theorem source_key_partition [LinearOrder κ] (key : α → κ)
    (pivot : α) (xs : List α) :
    Multiset.filter (fun x => key x < key pivot) (xs : Multiset α) +
      Multiset.filter (fun x => key pivot ≤ key x) (xs : Multiset α) =
      (xs : Multiset α) := by
  apply source_complementary_multiset
  intro x _
  simp only [not_le]

/-- The concatenation characterization needs only the observed relation. -/
theorem source_sorted_append [LE κ] (key : α → κ) (xs ys : List α) :
    KeySorted key (xs ++ ys) ↔
      KeySorted key xs ∧ KeySorted key ys ∧ ∀ a ∈ xs, ∀ b ∈ ys, key a ≤ key b :=
  List.pairwise_append

theorem source_multiset (lt : α → α → Bool) (xs : List α) :
    ((quickSortBy lt xs : List α) : Multiset α) = (xs : Multiset α) :=
  Quot.sound (quickSortBy_perm lt xs)

theorem source_support (lt : α → α → Bool) (xs : List α) :
    {x | x ∈ quickSortBy lt xs} = {x | x ∈ xs} := by
  ext x
  exact mem_quickSortBy lt xs x

theorem mixed_source_equation :
    quickSortOn id ([2, 1, 2, 3, 0] : List Nat) =
      quickSortOn id [1, 0] ++ ([2] ++ quickSortOn id [2, 3]) := by
  simpa using quickSortOn_cons id (2 : Nat) [1, 2, 3, 0]

/-- The independently sorted permutation consumes both general correctness fields. -/
theorem mixed_source_value :
    quickSortOn id ([2, 1, 2, 3, 0] : List Nat) = [0, 1, 2, 2, 3] := by
  have h := quickSortOn_correct id ([2, 1, 2, 3, 0] : List Nat)
  exact List.Perm.eq_of_pairwise' (r := fun a b : Nat => a ≤ b) h.1 (by decide)
    (h.2.trans (by decide : ([2, 1, 2, 3, 0] : List Nat).Perm [0, 1, 2, 2, 3]))

theorem mixed_accumulator_equation :
    quickSortAccOn id ([2, 1, 2, 3, 0] : List Nat) [4, 0, 2] =
      quickSortAccOn id [1, 0] (2 :: quickSortAccOn id [2, 3] [4, 0, 2]) := by
  simpa using quickSortAccOn_cons id (2 : Nat) [1, 2, 3, 0] [4, 0, 2]

theorem mixed_accumulator_value :
    quickSortAccOn id ([2, 1, 2, 3, 0] : List Nat) [4, 0, 2] =
      [0, 1, 2, 2, 3, 4, 0, 2] := by
  rw [quickSortAccOn_eq_append, mixed_source_value]

theorem empty_first_input :
    quickSortAccOn id ([] : List Nat) [4, 0, 2] = [4, 0, 2] :=
  quickSortAccBy_nil _ _

theorem singleton_first_input :
    quickSortAccOn id ([2] : List Nat) [4, 0, 2] = [2, 4, 0, 2] :=
  quickSortAccBy_singleton _ _ _

theorem all_equal_right_recursion :
    quickSortOn id ([2, 2, 2] : List Nat) =
      quickSortOn id [] ++ ([2] ++ quickSortOn id [2, 2]) := by
  simpa using quickSortOn_cons id (2 : Nat) [2, 2]

theorem all_equal_accumulator :
    quickSortAccOn id ([2, 2, 2] : List Nat) [4, 0, 2] = [2, 2, 2, 4, 0, 2] := by
  rw [quickSortAccOn_eq_append]
  have he : quickSortOn id ([2, 2, 2] : List Nat) = [2, 2, 2] := by
    have h := quickSortOn_correct id ([2, 2, 2] : List Nat)
    exact List.Perm.eq_of_pairwise' (r := fun a b : Nat => a ≤ b) h.1 (by decide) h.2
  rw [he]

/-- Even a sorted suffix need not follow the sorted prefix in key order. -/
theorem sorted_suffix_is_not_enough :
    KeySorted id ([1] : List Nat) ∧
      ¬ KeySorted id (quickSortAccOn id ([2] : List Nat) [1]) := by
  rw [quickSortAccBy_singleton]
  decide

theorem empty_payload :
    quickSortBy (fun x _ : Empty => Empty.elim x) [] = [] := quickSortBy_nil _

theorem empty_payload_suffix :
    quickSortAccBy (fun x _ : Empty => Empty.elim x) [] [] = [] := quickSortAccBy_nil _ _

theorem arbitrary_comparator_occurrences (lt : α → α → Bool) (xs suffix : List α) :
    (quickSortBy lt xs).Perm xs ∧
      (quickSortBy lt xs).length = xs.length ∧
      (quickSortAccBy lt xs suffix).Perm (xs ++ suffix) :=
  ⟨quickSortBy_perm lt xs, quickSortBy_length lt xs, quickSortAccBy_perm lt xs suffix⟩

/-- Ties go right at the actual first pivot, retaining distinguishable payloads. -/
theorem payload_source_equation (first middle last : α) :
    quickSortOn Prod.fst ([(1, first), (0, middle), (1, last)] : List (Nat × α)) =
      quickSortOn Prod.fst [(0, middle)] ++
        ([(1, first)] ++ quickSortOn Prod.fst [(1, last)]) := by
  simpa using quickSortOn_cons Prod.fst ((1 : Nat), first) [(0, middle), (1, last)]

/-- This source calculation requires no typeclass on the arbitrary payload type. -/
theorem arbitrary_payload_order (first middle last : α) :
    quickSortOn Prod.fst ([(1, first), (0, middle), (1, last)] : List (Nat × α)) =
      [(0, middle), (1, first), (1, last)] := by
  simpa only [quickSortOn, quickSortBy_singleton, List.cons_append, List.nil_append]
    using payload_source_equation first middle last

theorem arbitrary_payload_suffix (first middle last : α) (suffix : List (Nat × α)) :
    quickSortAccOn Prod.fst [(1, first), (0, middle), (1, last)] suffix =
      [(0, middle), (1, first), (1, last)] ++ suffix := by
  rw [quickSortAccOn_eq_append, arbitrary_payload_order]

/-- Outside this concrete input the comparator deliberately reverses the key test. -/
def localLess (a b : Int) : Bool :=
  if 0 ≤ a ∧ 0 ≤ b then decide (a < b) else decide (b < a)

theorem localLess_compatible :
    ∀ a ∈ ([2, 0, 2, 1] : List Int), ∀ b ∈ ([2, 0, 2, 1] : List Int),
      (localLess a b = true → a ≤ b) ∧ (localLess a b = false → b ≤ a) := by
  intro a ha b hb
  have ha0 : 0 ≤ a := by simp only [List.mem_cons, List.mem_singleton] at ha; omega
  have hb0 : 0 ≤ b := by simp only [List.mem_cons, List.mem_singleton] at hb; omega
  simp only [localLess, if_pos ⟨ha0, hb0⟩]
  exact ⟨fun h => le_of_lt (of_decide_eq_true h),
    fun h => le_of_not_gt (of_decide_eq_false h)⟩

theorem local_comparator_sorted :
    KeySorted id (quickSortBy localLess ([2, 0, 2, 1] : List Int)) :=
  quickSortBy_sorted_compatible_on id _ _ localLess_compatible

theorem local_comparator_fails_globally :
    localLess (-1) 0 = false ∧ ¬ ((0 : Int) ≤ -1) := by decide

end Examples.QuickSort

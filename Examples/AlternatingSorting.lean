import Applications.Sorting.Alternating
import Examples.StableSorting
import Mathlib.Data.Multiset.Basic

/-! Exercise 2.5's actual accumulated pile order, occurrence correctness and
ordinary sortedness. Reversed alternating piles can reorder equal-key records,
so the source's ordinary correctness claim is kept separate from stability.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.AlternatingSorting
open Applications.Sorting
universe u
variable {α : Type u}

/-- The printed nonempty-accumulator example, using the actual public step equations. -/
theorem source_halve_example :
    halve ([2, 3, 4] : List Nat) ([0], [1]) = ([4, 2, 0], [3, 1]) := by
  simp only [halve_cons_cons, halve_singleton]

theorem source_halve_lengths :
    (halve ([2, 3, 4] : List Nat) ([0], [1])).1.length = 3 ∧
      (halve ([2, 3, 4] : List Nat) ([0], [1])).2.length = 2 := by
  simpa using halve_lengths ([2, 3, 4] : List Nat) [0] [1]

theorem even_halve_example :
    halve ([0, 1, 2, 3] : List Nat) ([], []) = ([2, 0], [3, 1]) := by
  simp only [halve_cons_cons, halve_nil]

theorem even_halve_lengths :
    (halve ([0, 1, 2, 3] : List Nat) ([], [])).1.length = 2 ∧
      (halve ([0, 1, 2, 3] : List Nat) ([], [])).2.length = 2 := by
  simpa using halve_lengths ([0, 1, 2, 3] : List Nat) [] []

/-- Arbitrary original pile contents remain in the combined multiset. -/
theorem accumulator_multiset (xs left right : List α) :
    (((halve xs (left, right)).1 ++ (halve xs (left, right)).2 : List α) : Multiset α) =
      ((xs ++ left ++ right : List α) : Multiset α) :=
  Quot.sound (halve_perm xs left right)

/-- Only the added lengths are balanced if the initial pile lengths differ. -/
theorem unbalanced_initial_piles :
    (halve ([] : List Nat) ([3, 2, 1], [])).1.length = 3 ∧
      (halve ([] : List Nat) ([3, 2, 1], [])).2.length = 0 := by
  simpa using halve_lengths ([] : List Nat) [3, 2, 1] []

theorem empty_halve_payload : halve ([] : List Empty) ([], []) = ([], []) := halve_nil _

theorem singleton_halve_payload (x : α) (left right : List α) :
    halve [x] (left, right) = (x :: left, right) := halve_singleton _ _ _

/-- Both balanced children of every nontrivial input satisfy the actual recursion measure. -/
theorem recursive_halves (xs : List α) (hn : 2 ≤ xs.length) :
    (halve xs ([], [])).2.length ≤ (halve xs ([], [])).1.length ∧
      (halve xs ([], [])).1.length ≤ (halve xs ([], [])).2.length + 1 ∧
      (halve xs ([], [])).1.length < xs.length ∧
      (halve xs ([], [])).2.length < xs.length :=
  ⟨(halve_empty_balance xs).1, (halve_empty_balance xs).2, halve_strict xs hn⟩

/-- Odd occurrences form the left pile in reverse order. -/
theorem source_sort_three_equation (cmp : α → α → Bool) (a b c : α) :
    sortAlternatingBy cmp [a, b, c] =
      List.merge (sortAlternatingBy cmp [c, a]) (sortAlternatingBy cmp [b]) cmp := by
  simpa only [halve_cons_cons, halve_singleton] using sortAlternatingBy_cons_cons cmp a b [c]

/-- The independent expected sorted permutation consumes both public correctness fields. -/
theorem duplicate_source_value :
    sortAlternatingOn id ([2, 1, 2, 3, 0] : List Nat) = [0, 1, 2, 2, 3] := by
  have h := sortAlternatingOn_correct id ([2, 1, 2, 3, 0] : List Nat)
  exact List.Perm.eq_of_pairwise' (r := fun a b : Nat => a ≤ b) h.1 (by decide)
    (h.2.trans (by decide : ([2, 1, 2, 3, 0] : List Nat).Perm [0, 1, 2, 2, 3]))

theorem source_multiset (cmp : α → α → Bool) (xs : List α) :
    ((sortAlternatingBy cmp xs : List α) : Multiset α) = (xs : Multiset α) :=
  Quot.sound (sortAlternatingBy_perm cmp xs)

theorem arbitrary_comparator_occurrences (cmp : α → α → Bool) (xs : List α) :
    (sortAlternatingBy cmp xs).Perm xs ∧ (sortAlternatingBy cmp xs).length = xs.length :=
  ⟨sortAlternatingBy_perm cmp xs, sortAlternatingBy_length cmp xs⟩

theorem empty_sort_payload :
    sortAlternatingOn (Empty.elim : Empty → Nat) [] = [] := sortAlternatingBy_nil _

theorem singleton_sort_payload (x : α) :
    sortAlternatingOn (fun _ : α => (0 : Nat)) [x] = [x] := sortAlternatingBy_singleton _ _

/-- Reuse the accepted comparator witness whose contract holds only on this input. -/
theorem local_comparator_sorted :
    KeySorted Prod.fst
      (sortAlternatingBy StableSorting.nonnegativeCompare StableSorting.nonnegativeInput) :=
  sortAlternatingBy_sorted_compatible_on Prod.fst _ _ StableSorting.nonnegative_compatible

/-- A source calculation on arbitrary payloads exposes the reversal of equal-key records. -/
theorem arbitrary_payload_order (first middle last : α) :
    sortAlternatingOn Prod.fst ([(1, first), (0, middle), (1, last)] : List (Nat × α)) =
      [(0, middle), (1, last), (1, first)] := by
  unfold sortAlternatingOn
  rw [source_sort_three_equation, sortAlternatingBy_pair, sortAlternatingBy_singleton]
  simp [List.cons_merge_cons]

/-- Ordinary sortedness and multiplicity preservation do not make this variant stable. -/
theorem source_variant_not_stable :
    ¬ Stable Prod.fst ([(1, 0), (0, 1), (1, 2)] : List (Nat × Nat))
      (sortAlternatingOn Prod.fst [(1, 0), (0, 1), (1, 2)]) := by
  rw [arbitrary_payload_order]
  intro h
  have hf := h 1
  simp at hf

end Examples.AlternatingSorting

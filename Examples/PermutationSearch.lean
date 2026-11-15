import Examples.Permutations
import SquareKit.FiniteSearch

/-!
# Positional permutations as exact-depth search

The state retains a reversed chosen prefix and the remaining input. Every
positional pick is a successor occurrence, even when equal values make two
successors equal. The ordered search leaves refine the selection generator
exactly; the shared counter therefore counts its factorial number of outputs.
This is an output-count theorem, not a runtime bound or a distinct-result count.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.PermutationSearch

open Sequences.Permutations FiniteSearch

universe u
variable {α : Type u}

/-- Choose the next input position, retaining its value in a reversed prefix. -/
def next (state : List α × List α) : List (List α × List α) :=
  (picks state.2).map (fun choice => (choice.1 :: state.1, choice.2))

/-- The complete leaf list preserves the selection generator's order and duplicates. -/
theorem enumerate_selection (remaining chosen : List α) :
    enumerate next remaining.length (chosen, remaining) =
      (bySelection remaining).map (fun result => (result.reverse ++ chosen, [])) := by
  cases remaining with
  | nil => simp [bySelection_eqn, enumerate]
  | cons x xs =>
      rw [bySelection_eqn]
      simp only [List.cons_ne_nil, ↓reduceIte, List.map_flatMap, List.map_map,
        Function.comp_def, List.length_cons, enumerate, next, List.flatMap_map]
      apply List.flatMap_congr
      intro choice hchoice
      have hlength : xs.length = choice.2.length := by
        have h := picks_remainder_length (x :: xs) choice hchoice
        simp only [List.length_cons] at h
        omega
      rw [hlength, enumerate_selection choice.2 (choice.1 :: chosen)]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
termination_by remaining.length
decreasing_by
  exact Nat.lt_of_lt_of_eq (Nat.lt_succ_self _)
    (picks_remainder_length _ _ hchoice)

/-- Readout restores chronological choice order after any existing prefix. -/
theorem enumerate_readout (remaining chosen : List α) :
    (enumerate next remaining.length (chosen, remaining)).map
        (fun state => state.1.reverse) =
      (bySelection remaining).map (chosen.reverse ++ ·) := by
  rw [enumerate_selection]
  simp only [List.map_map, Function.comp_def, List.reverse_append, List.reverse_reverse]

theorem enumerate_from_empty (remaining : List α) :
    (enumerate next remaining.length ([], remaining)).map
        (fun state => state.1.reverse) = bySelection remaining := by
  simpa using enumerate_readout remaining []

/-- The actual search is complete for the independent permutation relation. -/
theorem search_mem_iff (input result : List α) :
    result ∈ (enumerate next input.length ([], input)).map
        (fun state => state.1.reverse) ↔ result.Perm input := by
  rw [enumerate_from_empty, bySelection_mem_iff]

/-- The shared counter counts occurrences, including equal resulting permutations. -/
theorem count_factorial (remaining chosen : List α) :
    count next remaining.length (chosen, remaining) = Nat.factorial remaining.length := by
  rw [count_eq_length, enumerate_selection, List.length_map, bySelection_length]

theorem terminal_remaining (remaining chosen : List α) (state : List α × List α)
    (h : state ∈ enumerate next remaining.length (chosen, remaining)) : state.2 = [] := by
  rw [enumerate_selection] at h
  rcases List.mem_map.mp h with ⟨result, _, rfl⟩
  rfl

theorem empty_positive_depth (chosen : List α) (depth : Nat) :
    enumerate next (depth + 1) (chosen, []) = [] := rfl

/-- Once all positions have been chosen, no positive-depth successor remains. -/
theorem exhausted (remaining chosen : List α) (extra : Nat) :
    enumerate next (remaining.length + (extra + 1)) (chosen, remaining) = [] := by
  rw [enumerate_add, enumerate_selection, List.flatMap_map]
  apply List.flatMap_eq_nil_iff.mpr
  intro result _
  exact empty_positive_depth _ _

theorem exhausted_count (remaining chosen : List α) (extra : Nat) :
    count next (remaining.length + (extra + 1)) (chosen, remaining) = 0 := by
  rw [count_eq_length, exhausted]
  rfl

theorem empty_leaves :
    enumerate next 0 (([] : List Nat), []) = [([], [])] := rfl

theorem empty_count : count next 0 (([] : List Nat), []) = 1 :=
  count_factorial [] []

theorem repeated_count : count next 3 (([] : List Nat), [1, 1, 2]) = 6 :=
  count_factorial [1, 1, 2] []

/-- Six ordered occurrences survive, although there are only three distinct output lists. -/
theorem repeated_order :
    (enumerate next 3 (([] : List Nat), [1, 1, 2])).map
        (fun state => state.1.reverse) =
      [[1, 1, 2], [1, 2, 1], [1, 1, 2], [1, 2, 1], [2, 1, 1], [2, 1, 1]] := by
  simpa [Examples.Permutations.selection_triple] using
    enumerate_from_empty ([1, 1, 2] : List Nat)

/-- The stored prefix is reversed; readout restores it before the new choices. -/
theorem prefixed_order :
    (enumerate next 2 (([9, 8] : List Nat), [1, 2])).map
        (fun state => state.1.reverse) = [[8, 9, 1, 2], [8, 9, 2, 1]] := by
  simpa [Examples.Permutations.selection_pair] using
    enumerate_readout ([1, 2] : List Nat) [9, 8]

theorem prefixed_count : count next 2 (([9, 8] : List Nat), [1, 2]) = 2 :=
  count_factorial [1, 2] [9, 8]

/-- The two equal first choices remain separate frontier occurrences. -/
theorem repeated_partition :
    count next (1 + 2) (([] : List Nat), [1, 1, 2]) = ([2, 2, 2] : List Nat).sum := by
  rw [count_partition]
  rfl

theorem completed_state_has_no_successor :
    count next 1 (([2, 1, 1] : List Nat), []) = 0 := by
  rw [count_eq_length, empty_positive_depth ([2, 1, 1] : List Nat) 0]
  rfl

theorem no_fourth_choice : count next 4 (([] : List Nat), [1, 1, 2]) = 0 :=
  exhausted_count [1, 1, 2] [] 0

end Examples.PermutationSearch

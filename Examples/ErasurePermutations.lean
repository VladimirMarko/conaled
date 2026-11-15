import Applications.Resources.ErasurePermutationGrowth
import Examples.PositionalPermutations

/-! Ordered and priced erasure cases through the public execution contracts. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.ErasurePermutations
open Resources.ErasurePermutations

theorem empty : generate ([] : List Nat) = ([[]],1) := by
  rw [generate_eqn]
  rfl

theorem singleton : generate [1] = ([[1]],16) := by
  rw [← generateFuel_eq 1 [1] (by decide)]
  decide

theorem pair : generate [1,2] = ([[1,2],[2,1]],62) := by
  rw [← generateFuel_eq 2 [1,2] (by decide)]
  decide

theorem equal_pair : generate [1,1] = ([[1,1],[1,1]],59) := by
  rw [← generateFuel_eq 2 [1,1] (by decide)]
  decide

theorem triple : generate [1,2,3] = (PositionalPermutations.three,249) := by
  rw [← generateFuel_eq 3 [1,2,3] (by decide)]
  decide

theorem adjacent_duplicates : generate [1,1,2] = (PositionalPermutations.duplicates,243) := by
  rw [← generateFuel_eq 3 [1,1,2] (by decide)]
  decide

def separatedOutputs : List (List Nat) :=
  [[1,2,1],[1,1,2],[2,1,1],[2,1,1],[1,2,1],[1,1,2]]

theorem separated_duplicates : generate [1,2,1] = (separatedOutputs,240) := by
  rw [← generateFuel_eq 3 [1,2,1] (by decide)]
  decide

theorem repeated_triple : generate [1,1,1] = (List.replicate 6 [1,1,1],231) := by
  rw [← generateFuel_eq 3 [1,1,1] (by decide)]
  decide

theorem same_multiset_different_work :
    ([1,1,2] : List Nat).Perm [1,2,1] ∧
      (generate [1,1,2]).2 ≠ (generate [1,2,1]).2 := by
  constructor
  · exact List.Perm.cons 1 (List.Perm.swap 2 1 [])
  · rw [adjacent_duplicates, separated_duplicates]; decide

theorem positional_order_differs :
    (generate [1,2,1]).1 ≠ (Resources.PositionalPermutations.generate [1,2,1]).1 := by
  rw [separated_duplicates, Resources.PositionalPermutations.generate_value,
    Examples.Permutations.selection_triple]
  decide

theorem missing_base_is_not_generation :
    Sequences.Permutations.byErasureWithoutBase ([] : List Nat) ≠ (generate []).1 := by
  rw [Sequences.Permutations.byErasureWithoutBase_eq_nil, empty]
  decide

theorem first_match : removeRun 1 [2,1,1] = ([2,1],5) :=
  removeRun_first 1 [2] [1] (by decide)

theorem absent : removeRun 9 [2,1,1] = ([2,1,1],10) :=
  removeRun_absent 9 [2,1,1] (by decide)

theorem empty_removal : removeRun 1 [] = ([],1) := removeRun_absent 1 [] (by decide)

theorem head_hit : removeRun 1 [1,2,1] = ([2,1],2) :=
  removeRun_first 1 [] [2,1] (by decide)

theorem late_hit : removeRun 1 [2,3,1] = ([2,3],8) :=
  removeRun_first 1 [2,3] [] (by decide)

theorem excess_fuel : generateFuel 7 [1,2,1] = (separatedOutputs,240) := by
  rw [generateFuel_eq 7 [1,2,1] (by decide), separated_duplicates]

theorem short_fuel : generateFuel 0 [1] ≠ generate [1] := by
  rw [singleton]
  decide

theorem observation_empty : observed ([] : List Nat) = ([[]],5) := by
  rw [observed_eq, ← generate_value, empty]
  decide

theorem observation_duplicates : observed [1,2,1] = (separatedOutputs,277) := by
  rw [observed_eq, ← generate_value, separated_duplicates]
  decide

theorem factorial_duplicates : (Sequences.Permutations.byErasure [1,1,1]).length = 6 :=
  Sequences.Permutations.byErasure_length [1,1,1]

def repeated (n : Nat) : List Unit := List.replicate n ()

theorem repeated_growth : Asymptotics.IsTheta Filter.atTop
    (fun n => ((generate (repeated n)).2 : ℝ))
    (fun n : Nat => ((n*Nat.factorial n : Nat) : ℝ)) :=
  generate_theta repeated (fun _ => List.length_replicate)

theorem distinct_growth : Asymptotics.IsTheta Filter.atTop
    (fun n => ((observed (List.range n)).2 : ℝ))
    (fun n : Nat => ((n*Nat.factorial n : Nat) : ℝ)) :=
  observed_theta List.range (fun _ => List.length_range)

theorem repeated_observed_not_shifted : ¬ Asymptotics.IsBigO Filter.atTop
    (fun n : Nat => (Nat.factorial (n+2) : ℝ))
    (fun n => ((observed (repeated n)).2 : ℝ)) :=
  observed_not_shifted_lower repeated (fun _ => List.length_replicate)

end Examples.ErasurePermutations

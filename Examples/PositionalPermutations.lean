import Applications.Resources.PositionalPermutationGrowth
import Examples.Permutations

/-! Independent ordered fixtures through the measured public contracts. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.PositionalPermutations
open Resources.PositionalPermutations

def three : List (List Nat) :=
  [[1,2,3],[1,3,2],[2,1,3],[2,3,1],[3,1,2],[3,2,1]]
def duplicates : List (List Nat) :=
  [[1,1,2],[1,2,1],[1,1,2],[1,2,1],[2,1,1],[2,1,1]]

theorem empty : generate ([] : List Nat) = ([[]],1) := by
  rw [generate_eq]
  rw [Examples.Permutations.empty_selection]
  decide

theorem singleton : generate [1] = ([[1]],18) := by
  rw [generate_eq]
  rw [Examples.Permutations.selection_singleton]
  decide

theorem two : generate [1,2] = ([[1,2],[2,1]],69) := by
  rw [generate_eq]
  rw [Examples.Permutations.selection_pair]
  decide

theorem three_exact : generate [1,2,3] = (three,274) := by
  rw [generate_eq]
  rw [Examples.Permutations.selection_triple]
  decide

theorem duplicates_exact : generate [1,1,2] = (duplicates,274) := by
  rw [generate_eq]
  rw [Examples.Permutations.selection_triple]
  decide

theorem insertion_order_differs :
    (generate [1,2,3]).1 ≠ ([1,2,3] : List Nat).permutations' := by
  rw [three_exact]
  decide

theorem fuel_exact : generateFuel 3 [1,2,3] = (three,274) := by
  rw [generateFuel_eq 3 [1,2,3] (by decide), three_exact]

theorem fuel_excess : generateFuel 7 [1,2,3] = (three,274) := by
  rw [generateFuel_eq 7 [1,2,3] (by decide), three_exact]

theorem short_fuel : generateFuel 0 [1] ≠ generate [1] := by
  rw [singleton]
  decide

theorem mixed_empty_observation : observeSpines [[],[1,2],[]] = ([[],[1,2],[]],12) := by
  rw [observeSpines_eq]
  decide

theorem observed_empty : observed ([] : List Nat) = ([[]],5) := by
  rw [observed_eq]
  rw [Examples.Permutations.empty_selection]
  decide

theorem observed_two : observed [1,2] = ([[1,2],[2,1]],80) := by
  rw [observed_eq]
  rw [Examples.Permutations.selection_pair]
  decide

theorem observed_three : observed [1,2,3] = (three,311) := by
  rw [observed_eq]
  rw [Examples.Permutations.selection_triple]
  decide

-- Arbitrary function labels require no equality instance.
def functions : List (Bool → Bool) := [id, fun _ => true]

theorem functions_observed :
    (generate functions).1.map (List.map (fun f => f false)) = [[false,true],[true,false]] := by
  rw [generate_value]
  simp only [functions, Examples.Permutations.selection_pair]
  decide

theorem function_spine_work : (observed functions).2 = 80 := by
  rw [observed_eq]
  decide

theorem duplicate_picks : picksRun [1,1] = ([(1,[1]),(1,[1])],10) := by
  apply Prod.ext
  · rw [picksRun_value]; decide
  · rw [picksRun_work]; decide

-- Distinct callbacks preserve occurrences and varying bills under the local tariff.
theorem varying_callbacks : mapRun (fun n : Nat => (n+1,n*n)) [1,1,3] = ([2,2,4],18) := by
  rw [mapRun_eq]
  decide

theorem native_callback_bridge : mapRun (fun n : Nat => (n+1,n*n)) [1,1,3] =
    let r := StructuredLinear.Costs.traverse
      (fun n : Nat => (n+1,StructuredLinear.Costs.tick .outputWrite (n*n))) [1,1,3]
    (r.1,r.2 .outputWrite + 7) := mapRun_native _ _

def repeated (n : Nat) : List Unit := List.replicate n ()

theorem repeated_construction_growth : Asymptotics.IsTheta Filter.atTop
    (fun n => ((generate (repeated n)).2 : ℝ))
    (fun n : Nat => ((n * Nat.factorial n : Nat) : ℝ)) :=
  generate_theta repeated (fun _ => List.length_replicate)

theorem repeated_observation_growth : Asymptotics.IsTheta Filter.atTop
    (fun n => ((observed (repeated n)).2 : ℝ))
    (fun n : Nat => ((n * Nat.factorial n : Nat) : ℝ)) :=
  observed_theta repeated (fun _ => List.length_replicate)

theorem repeated_not_shifted : ¬ Asymptotics.IsBigO Filter.atTop
    (fun n : Nat => (Nat.factorial (n+2) : ℝ))
    (fun n => ((observed (repeated n)).2 : ℝ)) :=
  observed_not_shifted_lower repeated (fun _ => List.length_replicate)

end Examples.PositionalPermutations

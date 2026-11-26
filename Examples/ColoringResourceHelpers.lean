import Applications.Resources.ListExecution.MeasuredFold
import Applications.Resources.Coloring.Helpers
import Examples.ColoringSelection
import Examples.ColoringCorrectness
import Mathlib.Algebra.FreeMonoid.Basic

/-! Connected helper cases for the complete Color resource program. Expected
values and tariffs are fixed in checkpoint055 before implementation. -/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.ColoringResourceHelpers

open Resources Resources.ListExecution

def decimal (x state : Nat) : Measured Nat (FreeAddMonoid (Nat × Nat)) :=
  (10 * state + x, FreeAddMonoid.of (x, state))

theorem decimal_bridge :
    ((MeasuredFold.run decimal [1, 2, 3] 0).1, (MeasuredFold.run decimal [1, 2, 3] 0).2.2) =
      (321, FreeAddMonoid.of (3, 0) + FreeAddMonoid.of (2, 3) + FreeAddMonoid.of (1, 32)) := by
  rw [MeasuredFold.run_callback]
  rfl

theorem decimal_order : FreeAddMonoid.toList (MeasuredFold.run decimal [1, 2, 3] 0).2.2 =
    [(3, 0), (2, 3), (1, 32)] :=
  congrArg (fun result => FreeAddMonoid.toList result.2) decimal_bridge

theorem decimal_counts : (MeasuredFold.run decimal [1, 2, 3] 0).2.1 = (4, 3) :=
  MeasuredFold.run_counts decimal [1, 2, 3] 0

theorem decimal_left : (Resources.run decimal [1, 2, 3] 0).1 = 123 := rfl

theorem empty_seed (seed : Nat) : MeasuredFold.run decimal [] seed = (seed, ((1, 0), 0)) :=
  MeasuredFold.run_nil decimal seed

theorem old_fold_client (price : Nat) :
    reweight (fun cost => cost.1.1 + cost.2)
        (MeasuredFold.run (fun x state : Nat => (10 * state + x, price)) [1, 2, 3] 0) =
      ListExecution.foldr price (fun x state => 10 * state + x) 0 [1, 2, 3] :=
  MeasuredFold.pure_fold price (fun x state => 10 * state + x) [1, 2, 3] 0

abbrev Allowed (x : Nat) : Prop := x = 1 ∨ x = 2 ∨ x = 3

def saturated (x state : Nat) : Measured Nat Nat :=
  if x = 1 ∨ x = 2 ∨ x = 3 then (min (state + x) 10, state + 1) else (11, 100)

theorem saturated_closed (x state : Nat) (input : Allowed x) (_initial : state ≤ 10) :
    (saturated x state).1 ≤ 10 := by
  change (if Allowed x then (min (state + x) 10, state + 1) else (11, 100)).1 ≤ 10
  rw [ite_eq_left input]
  exact Nat.min_le_right _ _

theorem saturated_bounded (x state : Nat) (input : Allowed x) (initial : state ≤ 10) :
    (saturated x state).2 ≤ 11 := by
  change (if Allowed x then (min (state + x) 10, state + 1) else (11, 100)).2 ≤ 11
  rw [ite_eq_left input]
  dsimp only
  omega

theorem inputs_allowed : ∀ x ∈ ([1, 2, 3] : List Nat), Allowed x := by
  intro x member
  simpa only [Allowed, List.mem_cons, List.not_mem_nil, or_false] using member

theorem saturated_invariant : (MeasuredFold.run saturated [1, 2, 3] 0).1 ≤ 10 :=
  MeasuredFold.run_invariant_on saturated Allowed (· ≤ 10) saturated_closed [1, 2, 3]
    inputs_allowed 0 (by decide)

theorem saturated_work : (MeasuredFold.run saturated [1, 2, 3] 0).2.2 ≤ 33 :=
  MeasuredFold.run_callback_work_le saturated Allowed (· ≤ 10) 11 saturated_closed saturated_bounded
    [1, 2, 3] inputs_allowed 0 (by decide)

theorem saturated_result : MeasuredFold.run saturated [1, 2, 3] 0 = (6, ((4, 3), 11)) := by decide

theorem restricted_boundary :
    ¬ Allowed 0 ∧ saturated 0 0 = (11, 100) ∧ (saturated 1 11).2 = 12 := by decide

open Search.PositiveTrie Numerals.PositiveArithmetic Graphs.Coloring
open Resources.Coloring Examples.ColoringSelection
open scoped BigOperators

theorem source_valid : GraphValid 3 sourceGraph := by
  apply mkGraph_valid
  intro edge member
  simp only [sourceEdges, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem palette_valid : SetValid 2 palette :=
  (((SetValid.nil 2).add 3 (by decide)).add 2 (by decide)).add 1 (by decide)

theorem isolated_valid : GraphValid 1 isolated :=
  (GraphValid.nil 1).add 1 .nil (by decide) (SetValid.nil 1)

theorem source_mass : degreeMass sourceGraph = 14 := by
  rw [degreeMass_entries]
  decide

theorem source_degree_bound : ((select 3 sourceGraph).map (degree sourceGraph)).sum ≤ 14 := by
  simpa only [source_mass] using selected_degrees_le 3 sourceGraph

theorem arbitrary_removal_valid (key : Node) : GraphValid 3 (removeNode key sourceGraph) :=
  source_valid.remove key

theorem arbitrary_removal_mass (key : Node) : degreeMass (removeNode key sourceGraph) ≤ 14 := by
  simpa only [source_mass] using degreeMass_remove_le key sourceGraph

theorem source_adjacency_size_bound :
    (∑ key ∈ SparseMap.keys sourceGraph, (adj sourceGraph key).numNodes) ≤ 42 := by
  simpa only [source_mass] using source_valid.adjacency_nodes_le

theorem nodes_value_client : (nodesRun sourceGraph).1 = nodes sourceGraph := nodesRun_value sourceGraph

theorem nodes_work : work (nodesRun sourceGraph).2 = 87 := by decide

theorem source_lowDegree :
    (lowDegreeRun unitPrices 3 1 (adj sourceGraph 1)).1 = false ∧
      work (lowDegreeRun unitPrices 3 1 (adj sourceGraph 1)).2 = 21 := by
  rw [lowDegreeRun_value, lowDegreeRun_unit_work]
  decide

theorem residual_lowDegree :
    (lowDegreeRun unitPrices 3 1 (adj (removeNode 4 sourceGraph) 1)).1 = true ∧
      work (lowDegreeRun unitPrices 3 1 (adj (removeNode 4 sourceGraph) 1)).2 = 17 := by
  rw [lowDegreeRun_value, lowDegreeRun_unit_work]
  decide

theorem source_eligible_value : (eligibleRun unitPrices 3 sourceGraph).1 = eligible 3 sourceGraph :=
  eligibleRun_value unitPrices 3 sourceGraph

theorem source_eligible_work : work (eligibleRun unitPrices 3 sourceGraph).2 = 165 := by decide

theorem isolated_eligible_work : work (eligibleRun unitPrices 1 isolated).2 = 13 := by decide

theorem source_first_removal : work (removeNodeRun 4 sourceGraph).2 = 59 := by decide

theorem source_first_erase_attempts : count .adjErase (removeNodeRun 4 sourceGraph).2 = 4 := by
  rw [removeNodeRun_count]
  decide

theorem failed_attempts_still_count :
    count .adjErase (removeNodeRun 4 sourceGraph).2 = 4 ∧
      KeySet.mem 4 (adj sourceGraph 5) = false ∧ KeySet.mem 4 (adj sourceGraph 6) = false := by
  exact ⟨source_first_erase_attempts, rfl, rfl⟩

theorem choice_seven : work (choose (KeySet.add 7 .nil)).2 = 7 ∧
    ¬ work (choose (KeySet.add 7 .nil)).2 ≤ 2 * bitLength 7 := by decide

theorem choice_bound_client : work (choose (KeySet.add 7 .nil)).2 ≤ 9 :=
  choose_work_le_of_some ((SetValid.nil 3).add 7 (by decide)) (key := 7) rfl

def operandPrices : Prices := ⟨fun a b => a + b + 1, fun degree bound => degree + bound + 1⟩

theorem operand_sensitive :
    (lowDegreeRun operandPrices 3 1 (KeySet.add 1 (KeySet.add 2 .nil))).1 = true ∧
      work (lowDegreeRun operandPrices 3 1 (KeySet.add 1 (KeySet.add 2 .nil))).2 = 20 ∧
      work (lowDegreeRun unitPrices 3 1 (KeySet.add 1 (KeySet.add 2 .nil))).2 = 11 := by
  rw [lowDegreeRun_value, lowDegreeRun_work, lowDegreeRun_unit_work]
  decide

end Examples.ColoringResourceHelpers

import Applications.Resources.BinomialQueue.Amortized

/-!
Connected source operations with independent expected shapes and primitive bills.
The numerical bills use the documented syntactic prices. Kernel reduction here
does not establish native timing or physical allocation.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.BinomialQueueWork

open Search.BinomialQueue Resources.BinomialQueue

def cmp : Nat → Nat → Resources.Measured Bool Nat := unitComparator natGreater

theorem cmp_correct (x y : Nat) : (cmp x y).1 = true ↔ ¬ x ≤ y := natGreater_eq x y

theorem cmp_bound (x y : Nat) : (cmp x y).2 ≤ 1 := Nat.le_refl _

def unitPrices : Cost := fun _ => 1

def singleton (key : Nat) : BinaryTree Nat := .node key .nil .nil

def rankOne : BinaryTree Nat := .node 5 (singleton 5) .nil

def rankTwo : BinaryTree Nat := .node 5 (.node 5 (singleton 5) (singleton 5)) .nil

def occupiedThree : Queue Nat := [singleton 5, rankOne, rankTwo]

theorem occupiedThree_valid : Valid occupiedThree := by
  simp [occupiedThree, rankOne, rankTwo, singleton, Valid, ValidFrom, Pow2Heap, Pow2HeapAux]

theorem empty_bills : weighted unitPrices (emptyRun : Resources.Measured (Queue Nat) Cost).2 = 1 ∧
    (findMaxRun cmp []).1 = none ∧ calls (findMaxRun cmp []).2 = 1 ∧
    (deleteMaxRun cmp []).1 = none ∧ calls (deleteMaxRun cmp []).2 = 2 ∧
    (insertionsRun cmp [] []).2 .comparisons = 0 := by decide

theorem equal_smash_bill :
    (smashRun cmp (.node 5 (singleton 1) .nil) (.node 5 (singleton 2) .nil)).1 =
      .node 5 (.node 5 (singleton 1) (singleton 2)) .nil ∧
    (smashRun cmp (singleton 5) (singleton 5)).2 .comparisons = 1 ∧
    (smashRun cmp (singleton 5) (singleton 5)).2 .nodes = 2 ∧
    calls (smashRun cmp (singleton 5) (singleton 5)).2 = 1 := by decide

theorem no_link_and_one_link :
    (carryRun cmp [.nil, rankOne] (singleton 5)).1 = [singleton 5, rankOne] ∧
    (carryRun cmp [.nil, rankOne] (singleton 5)).2 .comparisons = 0 ∧
    (carryRun cmp [.nil, rankOne] (singleton 5)).2 .carryCalls = 1 ∧
    (carryRun cmp [singleton 5, .nil, rankTwo] (singleton 5)).1 = [.nil, rankOne, rankTwo] ∧
    (carryRun cmp [singleton 5, .nil, rankTwo] (singleton 5)).2 .comparisons = 1 ∧
    (carryRun cmp [singleton 5, .nil, rankTwo] (singleton 5)).2 .carryCalls = 2 := by decide

theorem empty_carry_reuses_tail :
    (carryRun cmp occupiedThree .nil).1 = occupiedThree ∧
    (carryRun cmp occupiedThree .nil).2 .carryCalls = 1 ∧
    (carryRun cmp occupiedThree .nil).2 .cons = 1 ∧
    (carryRun cmp occupiedThree .nil).2 .smashCalls = 0 := by decide

theorem long_carry_and_counter_write :
    (insertRun cmp 5 occupiedThree).2 .comparisons = 3 ∧
    (insertRun cmp 5 occupiedThree).2 .carryCalls = 4 ∧
    (insertRun cmp 5 occupiedThree).2 .smashCalls = 3 ∧
    (insertRun cmp 5 occupiedThree).2 .cons = 4 ∧
    (insertRun cmp 5 occupiedThree).2 .nodes = 7 ∧
    Resources.BinaryCounter.flipCost (occupancy occupiedThree) = 4 ∧
    potential occupiedThree = 3 ∧ potential (insertRun cmp 5 occupiedThree).1 = 1 := by decide

theorem join_zero_and_single_occupied :
    (joinRun cmp [.nil] [.nil] .nil).1 = [.nil] ∧
    (joinRun cmp [.nil] [.nil] (singleton 7)).1 = [singleton 7] ∧
    (joinRun cmp [.nil] [singleton 5] .nil).1 = [singleton 5] ∧
    (joinRun cmp [singleton 3] [.nil] .nil).1 = [singleton 3] ∧
    (joinRun cmp [.nil] [.nil] .nil).2 .cons = 1 ∧
    (joinRun cmp [.nil] [.nil] .nil).2 .comparisons = 0 ∧
    (joinRun cmp [.nil] [.nil] .nil).2 .joinCalls = 2 ∧
    (joinRun cmp [.nil] [.nil] .nil).2 .carryCalls = 1 := by decide

theorem join_two_occupied :
    (joinRun cmp [.nil] [singleton 5] (singleton 7)).1 =
      [.nil, .node 7 (singleton 5) .nil] ∧
    (joinRun cmp [singleton 3] [.nil] (singleton 7)).1 =
      [.nil, .node 7 (singleton 3) .nil] ∧
    (joinRun cmp [singleton 3] [singleton 5] .nil).1 =
      [.nil, .node 5 (singleton 3) .nil] ∧
    (joinRun cmp [singleton 3] [singleton 5] .nil).2 .comparisons = 1 ∧
    (joinRun cmp [singleton 3] [singleton 5] .nil).2 .cons = 2 ∧
    (joinRun cmp [singleton 3] [singleton 5] .nil).2 .nodes = 2 := by decide

theorem join_three_occupied_and_bases :
    (joinRun cmp [singleton 3] [singleton 5] (singleton 7)).1 =
      [singleton 7, .node 5 (singleton 3) .nil] ∧
    (joinRun cmp [singleton 3] [singleton 5] (singleton 7)).2 .comparisons = 1 ∧
    (joinRun cmp [] [singleton 3] (singleton 7)).1 =
      [.nil, .node 7 (singleton 3) .nil] ∧
    (joinRun cmp [singleton 3] [] (singleton 7)).1 =
      [.nil, .node 7 (singleton 3) .nil] ∧
    (joinRun cmp [] [singleton 3] (singleton 7)).2 .joinCalls = 1 ∧
    (joinRun cmp [] [singleton 3] (singleton 7)).2 .carryCalls = 2 := by decide

def expensiveContinuation (q : Queue Nat) : Resources.Measured (Queue Nat) Cost :=
  (singleton 99 :: q, charge .applications 7 + charge .cons 1)

theorem continuation_argument_and_bill :
    (unzipRun (.node 5 .nil (singleton 3)) expensiveContinuation).1 =
      [singleton 3, singleton 5, singleton 99] ∧
    (unzipRun (.node 5 .nil (singleton 3)) expensiveContinuation).1 ≠
      (expensiveContinuation (unzip (.node 5 .nil (singleton 3)) id)).1 ∧
    (unzipRun (.node 5 .nil (singleton 3)) expensiveContinuation).2 .unzipCalls = 3 ∧
    (unzipRun (.node 5 .nil (singleton 3)) expensiveContinuation).2 .closures = 2 ∧
    (unzipRun (.node 5 .nil (singleton 3)) expensiveContinuation).2 .applications = 9 ∧
    (unzipRun (.node 5 .nil (singleton 3)) expensiveContinuation).2 .cons = 3 ∧
    (unzipRun (.node 5 .nil (singleton 3)) expensiveContinuation).2 .nodes = 2 := by decide

theorem ranked_heap_deletion_bill :
    (heapDeleteMaxRun rankTwo).1 = [singleton 5, rankOne] ∧
    (heapDeleteMaxRun rankTwo).2 .heapDeleteMaxCalls = 1 ∧
    (heapDeleteMaxRun rankTwo).2 .unzipCalls = 3 ∧
    (heapDeleteMaxRun rankTwo).2 .closures = 2 ∧
    (heapDeleteMaxRun rankTwo).2 .applications = 3 ∧
    (heapDeleteMaxRun rankTwo).2 .cons = 2 ∧
    (heapDeleteMaxRun rankTwo).2 .nodes = 2 ∧
    weighted unitPrices (heapDeleteMaxRun rankTwo).2 = 13 := by decide

theorem singleton_deletion_padding :
    (deleteMaxRun cmp [singleton 0]).1 = some (0, [.nil]) ∧
    (deleteMaxRun cmp [singleton 0]).2 .comparisons = 1 ∧
    (deleteMaxRun cmp [singleton 0]).2 .cons = 2 ∧
    (deleteMaxRun cmp [singleton 0]).2 .nodes = 1 ∧
    calls (deleteMaxRun cmp [singleton 0]).2 = 8 ∧
    weighted unitPrices (deleteMaxRun cmp [singleton 0]).2 = 14 := by decide

def costlyCmp (x y : Nat) : Resources.Measured Bool Nat :=
  (natGreater x y, if x = y then 7 else 3)

theorem costlyCmp_bound (x y : Nat) : (costlyCmp x y).2 ≤ 7 := by
  dsimp [costlyCmp]
  split <;> decide

theorem comparison_follows_actual_candidate :
    (findMaxRun costlyCmp [singleton 3, singleton 7, singleton 7, singleton 2]).1 = some 7 ∧
    (findMaxRun costlyCmp [singleton 3, singleton 7, singleton 7, singleton 2]).2 .comparisons = 3 ∧
    (findMaxRun costlyCmp [singleton 3, singleton 7, singleton 7, singleton 2]).2 .comparisonWork = 13 ∧
    calls (findMaxRun costlyCmp [singleton 3, singleton 7, singleton 7, singleton 2]).2 = 5 := by decide

theorem nonunit_bill_connected :
    (findMaxRun costlyCmp [singleton 3, singleton 7, singleton 7, singleton 2]).2 .comparisonWork ≤
      7 * (findMaxRun costlyCmp [singleton 3, singleton 7, singleton 7, singleton 2]).2 .comparisons :=
  findMaxRun_comparisonWork_le costlyCmp 7 costlyCmp_bound _

def firstMaximum : Queue Nat := [singleton 9, rankOne, rankTwo]
def middleMaximum : Queue Nat := [.nil, .node 9 (singleton 5) .nil, rankTwo]
def finalMaximum : Queue Nat := [.nil, .nil, .node 9 (.node 5 (singleton 5) (singleton 5)) .nil]

theorem selected_states_valid : Valid firstMaximum ∧ Valid middleMaximum ∧ Valid finalMaximum := by
  simp [firstMaximum, middleMaximum, finalMaximum, rankOne, rankTwo, singleton,
    Valid, ValidFrom, Pow2Heap, Pow2HeapAux]

theorem first_selected_bill :
    (deleteMaxRun cmp firstMaximum).1 = some (9, [.nil, rankOne, rankTwo]) ∧
    (deleteMaxRun cmp firstMaximum).2 .comparisons = 3 ∧
    (deleteMaxRun cmp firstMaximum).2 .deleteMaxAuxCalls = 1 ∧
    (deleteMaxRun cmp firstMaximum).2 .unzipCalls = 1 ∧
    (deleteMaxRun cmp firstMaximum).2 .cons = 2 ∧
    calls (deleteMaxRun cmp firstMaximum).2 = 10 := by decide

theorem middle_selected_bill :
    (deleteMaxRun cmp middleMaximum).1 = some (9, [singleton 5, .nil, rankTwo]) ∧
    (deleteMaxRun cmp middleMaximum).2 .comparisons = 2 ∧
    (deleteMaxRun cmp middleMaximum).2 .deleteMaxAuxCalls = 2 ∧
    (deleteMaxRun cmp middleMaximum).2 .unzipCalls = 2 ∧
    (deleteMaxRun cmp middleMaximum).2 .closures = 1 ∧
    (deleteMaxRun cmp middleMaximum).2 .applications = 2 ∧
    (deleteMaxRun cmp middleMaximum).2 .cons = 5 ∧
    calls (deleteMaxRun cmp middleMaximum).2 = 13 := by decide

theorem final_selected_bill :
    (deleteMaxRun cmp finalMaximum).1 = some (9, [singleton 5, rankOne, .nil]) ∧
    (deleteMaxRun cmp finalMaximum).2 .comparisons = 1 ∧
    (deleteMaxRun cmp finalMaximum).2 .deleteMaxAuxCalls = 3 ∧
    (deleteMaxRun cmp finalMaximum).2 .unzipCalls = 3 ∧
    (deleteMaxRun cmp finalMaximum).2 .closures = 2 ∧
    (deleteMaxRun cmp finalMaximum).2 .applications = 3 ∧
    (deleteMaxRun cmp finalMaximum).2 .cons = 8 ∧
    calls (deleteMaxRun cmp finalMaximum).2 = 16 := by decide

theorem selected_general_bound :
    (deleteMaxRun cmp finalMaximum).2 .comparisons ≤ 3 * finalMaximum.length :=
  deleteMaxRun_comparisons_le cmp cmp_correct finalMaximum selected_states_valid.2.2

def offsetMaximum : Queue Nat := [.node 9 (.node 5 (singleton 5) (singleton 5)) .nil]

theorem rank_offset_bill : ValidFrom 2 offsetMaximum ∧
    (deleteMaxAuxRun cmp 9 offsetMaximum).1 = ([.nil], [singleton 5, rankOne]) ∧
    (deleteMaxAuxRun cmp 9 offsetMaximum).2 .deleteMaxAuxCalls = 1 ∧
    (deleteMaxAuxRun cmp 9 offsetMaximum).2 .unzipCalls = 3 ∧
    (deleteMaxAuxRun cmp 9 offsetMaximum).2 .cons = 3 ∧
    (deleteMaxAuxRun cmp 9 offsetMaximum).2 .nodes = 3 := by
  refine ⟨?_, by decide⟩
  simp [offsetMaximum, singleton, ValidFrom, Pow2Heap, Pow2HeapAux]

theorem rank_offset_connected :
    (deleteMaxAuxRun cmp 9 offsetMaximum).2 .unzipCalls = 3 := by
  obtain ⟨j, small, _, _, _, _, unzipCost, _, _⟩ :=
    deleteMaxAuxRun_selected_counts cmp cmp_correct 2 offsetMaximum 9
      rank_offset_bill.1 (by decide)
  have zero : j = 0 := by
    change j < 1 at small
    omega
  simpa only [zero] using unzipCost

theorem malformed_fallback_bill :
    (smashRun cmp (.node 5 .nil (singleton 2)) (singleton 7)).1 = .nil ∧
    (smashRun cmp (.node 5 .nil (singleton 2)) (singleton 7)).2 .comparisons = 0 ∧
    (heapDeleteMaxRun (.node 5 .nil (singleton 2))).1 = [] ∧
    (heapDeleteMaxRun (.node 5 .nil (singleton 2))).2 .unzipCalls = 0 ∧
    (deleteMaxAuxRun cmp 5 [.nil, .node 5 .nil (singleton 2)]).1 = ([.nil], []) ∧
    (deleteMaxAuxRun cmp 5 [.nil, .node 5 .nil (singleton 2)]).2 .deleteMaxAuxCalls = 2 ∧
    (deleteMaxAuxRun cmp 5 [.nil, .node 5 .nil (singleton 2)]).2 .comparisons = 0 := by decide

theorem arbitrary_empty_padding (n : Nat) :
    Valid (List.replicate n (.nil : BinaryTree Nat)) ∧
    mass (List.replicate n (.nil : BinaryTree Nat)) = 0 ∧
    (findMaxRun cmp (List.replicate n .nil)).2 .findMaxCalls = n + 1 ∧
    calls (deleteMaxRun cmp (List.replicate n .nil)).2 = n + 2 := by
  refine ⟨replicate_nil_valid 0 n, replicate_nil_mass n, ?_, ?_⟩
  · rw [findMaxRun_padding]
    simp [charge]
  · rw [deleteMaxRun_padding]
    simp [calls, charge]

def sourceInputs : List Nat := [3, 1, 4, 1, 5, 9, 2, 3, 5]

theorem source_build_bill :
    occupancy (insertionsRun cmp sourceInputs []).1 = [true, false, false, true] ∧
    (insertionsRun cmp sourceInputs []).2 .comparisons = 7 ∧
    potential (insertionsRun cmp sourceInputs []).1 = 2 ∧
    weighted unitPrices (insertionsRun cmp sourceInputs []).2 = 85 := by decide

theorem source_build_potential_connected :
    (insertionsRun cmp sourceInputs []).2 .comparisons +
      potential (insertionsRun cmp sourceInputs []).1 = sourceInputs.length := by
  simpa [potential, occupancy, Resources.BinaryCounter.ones] using
    insertionsRun_potential cmp sourceInputs [] (by simp)

theorem source_build_weighted_connected :
    weighted unitPrices (insertionsRun cmp sourceInputs []).2 +
      7 * potential (insertionsRun cmp sourceInputs []).1 ≤ 11 * sourceInputs.length := by
  simpa [potential, occupancy, Resources.BinaryCounter.ones, insertionBasePrice,
    carryPrice, smashPrice, unitPrices] using
    insertionsRun_weighted_potential cmp unitPrices 1 cmp_bound sourceInputs [] (by simp)

/-- Reusing a saved value on two branches does not permit spending its credit once. -/
theorem persistent_branch_credit :
    (insertRun cmp 5 occupiedThree).2 .comparisons +
      (insertRun cmp 7 occupiedThree).2 .comparisons > potential occupiedThree + 2 := by decide

def mixedInstructions : List (Instruction Nat) :=
  [.insert 5, .insert 7, .merge [singleton 3], .deleteMax]

theorem mixed_admissible : AdmissibleHistory cmp 0 3 mixedInstructions [] := by
  simp only [mixedInstructions, admissibleHistory_cons, admissibleHistory_nil, and_true]
  simp only [Admissible, Capacity, Valid, ValidFrom, Pow2Heap, Pow2HeapAux, singleton]
  decide

theorem mixed_history_value_and_bill :
    (runCommands cmp mixedInstructions []).1 = [.nil, .node 5 (singleton 3) .nil] ∧
    weighted unitPrices (runCommands cmp mixedInstructions []).2 = 55 := by decide

theorem mixed_history_capacity_connected :
    Valid (runCommands cmp mixedInstructions []).1 ∧
      mass (runCommands cmp mixedInstructions []).1 ≤ 3 ∧
      Capacity 0 3 (runCommands cmp mixedInstructions []).1 :=
  runCommands_invariant cmp cmp_correct 0 3 mixedInstructions [] trivial (by decide)
    (by simp [Capacity]) mixed_admissible

theorem mixed_history_work_connected :
    weighted unitPrices (runCommands cmp mixedInstructions []).2 ≤ 1088 := by
  have bits : Nat.size 3 = 2 := by decide
  simpa [mixedInstructions, unitPrices, commandPrice, insertPrice, carryPrice,
    smashPrice, joinPrice, deletePrice, scanPrice, auxiliaryPrice, heapPrice, bits] using
    runCommands_weighted_le cmp cmp_correct unitPrices 1 cmp_bound 0 3 mixedInstructions []
      trivial (by decide) (by simp [Capacity]) mixed_admissible

theorem reachable_padding_four :
    (drainRun cmp 4 (insertionsRun cmp [5, 5, 5, 5] []).1).1 = [.nil, .nil, .nil] ∧
    calls (deleteMaxRun cmp (drainRun cmp 4 (insertionsRun cmp [5, 5, 5, 5] []).1).1).2 = 5 := by decide

theorem reachable_padding_power (r : Nat) :
    (drainRun cmp (2 ^ r) (insertionsRun cmp (List.replicate (2 ^ r) 5) []).1).1 =
      List.replicate (r + 1) .nil := build_drain_power_padding cmp cmp_correct 5 r

theorem repeated_build_linear :
    Asymptotics.IsBigO Filter.atTop
      (fun n : Nat => (weighted unitPrices (insertionsRun cmp (List.replicate n 5) []).2 : ℝ))
      (fun n => (n : ℝ)) :=
  insertionsRun_isBigO cmp unitPrices 1 cmp_bound (fun n => List.replicate n 5)
    (fun _ => List.length_replicate)

end Examples.BinomialQueueWork

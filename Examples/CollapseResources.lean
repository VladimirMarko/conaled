import Applications.Resources.CollapseMaterialization

/-! Demanded prefixes, full materialization, and a resource-preserving sum observation. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.CollapseResources
open Resources Resources.CollapseMaterialization

/-- Observe the actual materialized output while retaining the producer's work. -/
def measuredSum : Squares.Square
    ⟨Measured (List Int) Nat, List Int, Prod.fst⟩
    ⟨Measured Int Nat, Int, Prod.fst⟩ where
  impl result := bind result Steepness.sumRun
  spec := List.sum
  commutes result := Steepness.sumRun_value result.1

def observedDifference := Squares.compose measuredSum differenceSquare
def observedLeft := Squares.compose measuredSum leftSquare

theorem observed_value (blocks : List (List Int)) :
    (observedDifference.impl blocks).1 = (Sequences.Accumulation.collapse blocks).sum :=
  observedDifference.commutes blocks

theorem observed_values_agree (blocks : List (List Int)) :
    (observedDifference.impl blocks).1 = (observedLeft.impl blocks).1 := by
  calc
    (observedDifference.impl blocks).1 = (Sequences.Accumulation.collapse blocks).sum :=
      observed_value blocks
    _ = (observedLeft.impl blocks).1 := (observedLeft.commutes blocks).symm

theorem observed_cached_summary (blocks : List (List Int)) :
    (observedDifference.impl blocks).1 =
      Multiplicative.toAdd (α := Int) (Sequences.Accumulation.collapseSummary.impl blocks) := by
  rw [observed_value, Sequences.Accumulation.collapseSummary_correct]

theorem observed_work (blocks : List (List Int)) :
    (observedDifference.impl blocks).2 =
      (differenceCollapse blocks).2 +
        (2 * (Sequences.Accumulation.collapse blocks).length + 1) := by
  change (differenceCollapse blocks).2 + (Steepness.sumRun (differenceCollapse blocks).1).2 = _
  rw [Steepness.sumRun_work, differenceCollapse_value,
    (Sequences.Accumulation.differenceResult_refines blocks).2]

theorem observed_work_le (blocks : List (List Int)) :
    (observedDifference.impl blocks).2 ≤
      6 * blocks.flatten.length + 15 * blocks.length + 5 := by
  rw [observed_work]
  have hc := differenceCollapse_work_le blocks
  have hl := produced_length_le blocks
  omega

theorem first_positive_function :
    differenceCollapse [[1], [100, 200], [-10]] = ([1], 20) :=
  difference_first_positive [1] [[100, 200], [-10]] (by decide)

theorem first_positive_left :
    leftCollapse [[1], [100, 200], [-10]] = ([1], 18) :=
  left_first_positive [1] [[100, 200], [-10]] (by decide)

theorem no_unconditional_improvement :
    ¬ ∀ blocks : List (List Int),
      (differenceCollapse blocks).2 ≤ (leftCollapse blocks).2 := by
  intro h
  have hb := h [[1], [100, 200], [-10]]
  rw [first_positive_function, first_positive_left] at hb
  exact (by decide : ¬ 20 ≤ 18) hb

theorem one_label_demanded : (build [[1], [100, 200]]).labelWork = 7 :=
  congrArg BuildRun.labelWork (build_first_positive [1] [[100, 200]] (by decide))

theorem empty_block_labels : (build [[], [], []]).labelWork = 23 := by
  simp [build, buildAux, labelStep_nil, labelStep_cons, Steepness.sumRun]

theorem empty_blocks_materialize : differenceCollapse [[], [], []] = ([], 49) := by
  simp [differenceCollapse, build, buildAux, labelStep_nil, labelStep_cons,
    Steepness.sumRun, applyFunction, appendRun_exact, overhead]

theorem left_zero_materialization :
    (leftMaterialize (build [[0], [0], [0]]).history).2 = 9 :=
  left_zeroBlocks_materialization 3

theorem function_zero_materialization :
    (applyFunction (build [[0], [0], [0]]).history []).2 = 9 := by
  rw [difference_materialization_work]
  change 2 * (build (List.replicate 3 [0])).used.flatten.length +
    (build (List.replicate 3 [0])).used.length = 9
  rw [build_zeroBlocks_used]
  decide

theorem arbitrary_tail (blocks : List (List Int)) :
    (applyFunction (build blocks).history [90, -3]).1 =
      Sequences.Accumulation.collapse blocks ++ [90, -3] := by
  rw [build_apply_difference, Sequences.Accumulation.differenceResult_apply]

theorem same_work_for_arbitrary_tail (blocks : List (List Int)) (tail : List Int) :
    (applyFunction (build blocks).history tail).2 =
      (applyFunction (build blocks).history []).2 := by
  rw [applyFunction_work, applyFunction_work]

theorem cached_selected_sums :
    (CollapseDemand.cached [[1], [100, 200], [-4]]).sumInputs = [[1]] :=
  congrArg CollapseDemand.Run.sumInputs
    (CollapseDemand.cached_first_positive [1] [[100, 200], [-4]] (by decide))

theorem plain_selected_sums :
    (CollapseDemand.plain [[1], [100, 200], [-4]]).sumInputs = [[], [1]] :=
  congrArg CollapseDemand.Run.sumInputs
    (CollapseDemand.plain_first_positive [1] [[100, 200], [-4]] (by decide))

theorem empty_blocks_keep_final_test :
    (CollapseDemand.cached [[], [], []]).tests = 4 := by decide

theorem empty_block_sums_cost :
    (CollapseDemand.cached [[], [], []]).sumWork = 3 := by decide

theorem signed_cached_sums :
    (CollapseDemand.cached [[-1], [-2], [10], [90]]).sumInputs = [[-1], [-2], [10]] := by
  decide

theorem signed_plain_sums :
    (CollapseDemand.plain [[-1], [-2], [10], [90]]).sumInputs =
      [[], [-1], [-1, -2], [-1, -2, 10]] := by decide

theorem signed_observation :
    observedDifference.impl [[-1], [-2], [10], [90]] = (7, 65) := by
  apply Prod.ext
  · rw [observed_value]; decide
  · rw [observed_work]
    simp [differenceCollapse, build, buildAux, labelStep_cons,
      Steepness.sumRun, applyFunction, appendRun_exact, overhead,
      Sequences.Accumulation.collapse, Sequences.Accumulation.collapseAux]

theorem empty_observation : observedDifference.impl [] = (0, 5) := by
  apply Prod.ext
  · rw [observed_value]; rfl
  · rw [observed_work]
    simp [differenceCollapse, build, buildAux, labelStep_nil, applyFunction,
      overhead, Sequences.Accumulation.collapse, Sequences.Accumulation.collapseAux]

/-- Empty blocks are selected even though the produced list has no elements. -/
theorem empty_blocks_selected : (build [[], [], []]).used = [[], [], []] := by
  simp [build, buildAux, labelStep_nil, labelStep_cons, Steepness.sumRun]

/-- Flattened equality alone would not distinguish the two empty blocks. -/
theorem selected_empty_prefix :
    (build [[], [1], [], [90]]).used = [[], [1]] ∧
      Sequences.Accumulation.NonpositiveBefore 0 [[], [1]] ∧
      0 < (historyValue (build [[], [1], [], [90]]).history).sum := by
  have hu : (build [[], [1], [], [90]]).used = [[], [1]] := by
    simp [build, buildAux, labelStep_cons, Steepness.sumRun]
  obtain ⟨remaining, hb, hn, hs⟩ := build_selected [[], [1], [], [90]]
  refine ⟨hu, by simpa only [hu] using hn, ?_⟩
  rcases hs with rfl | hpos
  · have hl := congrArg List.length hb
    simp [hu] at hl
  · exact hpos

end Examples.CollapseResources

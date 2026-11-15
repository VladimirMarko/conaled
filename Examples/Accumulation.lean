import Applications.Sequences.Accumulation
import Applications.Sequences.Steepness

/-! Checked Chapter 1 clients: first-positive block prefixes, cached observations,
arbitrary difference-list tails, and strict suffix-sum comparisons. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.Accumulation
open Sequences.Accumulation

/-- The first source case stops at the first block; both refinements use that result. -/
theorem source_first_positive :
    collapse [[1], [-3], [2, 4]] = [1] ∧
    collapseCached [[1], [-3], [2, 4]] = [1] ∧
    collapseDifference [[1], [-3], [2, 4]] = [1] ∧
    CollapseSpec [] [[1], [-3], [2, 4]] [1] := by
  have expected : collapse [[1], [-3], [2, 4]] = [1] := by decide
  refine ⟨expected, (cachedResult_refines _).2.trans expected,
    (differenceResult_refines _).2.trans expected, ?_⟩
  exact (collapse_spec_iff _ _).mpr expected.symm

/-- Nonpositive earlier boundaries force consumption of every block in order. -/
theorem source_exhaustion :
    collapse [[-2, 1], [-3], [2, 4]] = [-2, 1, -3, 2, 4] ∧
    collapseCached [[-2, 1], [-3], [2, 4]] = [-2, 1, -3, 2, 4] ∧
    collapseDifference [[-2, 1], [-3], [2, 4]] = [-2, 1, -3, 2, 4] ∧
    CollapseSpec [] [[-2, 1], [-3], [2, 4]] [-2, 1, -3, 2, 4] := by
  have expected : collapse [[-2, 1], [-3], [2, 4]] = [-2, 1, -3, 2, 4] := by decide
  refine ⟨expected, (cachedResult_refines _).2.trans expected,
    (differenceResult_refines _).2.trans expected, ?_⟩
  exact (collapse_spec_iff _ _).mpr expected.symm

/-- The first positive boundary occurs after the second block, before the final block. -/
theorem source_later_positive :
    collapse [[-2, 1], [3], [2, 4]] = [-2, 1, 3] ∧
    collapseCached [[-2, 1], [3], [2, 4]] = [-2, 1, 3] ∧
    collapseDifference [[-2, 1], [3], [2, 4]] = [-2, 1, 3] ∧
    CollapseSpec [] [[-2, 1], [3], [2, 4]] [-2, 1, 3] := by
  have expected : collapse [[-2, 1], [3], [2, 4]] = [-2, 1, 3] := by decide
  refine ⟨expected, (cachedResult_refines _).2.trans expected,
    (differenceResult_refines _).2.trans expected, ?_⟩
  exact (collapse_spec_iff _ _).mpr expected.symm

def blocks : List (List Int) := [[], [-2], [], [1], [3], [99]]

/-- Totals at whole-block boundaries are 0, 0, -2, -2, -1, 2; the last
block is not consumed. Empty blocks do not change the chosen output. -/
theorem cached_first_positive : collapseCached blocks = [-2, 1, 3] := by
  rw [(cachedResult_refines blocks).2]
  decide

theorem difference_first_positive : collapseDifference blocks = [-2, 1, 3] := by
  rw [(differenceResult_refines blocks).2]
  decide

theorem chosen_prefix_satisfies_spec : CollapseSpec [] blocks [-2, 1, 3] := by
  have h := collapseCached_correct blocks
  rw [cached_first_positive] at h
  exact h

/-- This is the actual composed cache observer, not a second summation of its
output list. Its correctness follows through the shared summary square. -/
theorem composed_sum : Multiplicative.toAdd (α := Int) (collapseSummary.impl blocks) = 2 := by
  rw [collapseSummary_correct]
  decide

/-- A nonempty, arbitrary tail checks the complete difference-function contract. -/
theorem every_tail (tail : List Int) :
    (differenceResult blocks).1.apply tail = [-2, 1, 3] ++ tail := by
  rw [differenceResult_apply]
  have h : collapse blocks = [-2, 1, 3] := by decide
  rw [h]

theorem ordered_tail : (differenceResult blocks).1.apply [7, 8] = [-2, 1, 3, 7, 8] :=
  every_tail [7, 8]

theorem negative_exhaustion :
    collapseDifference [[-5, 3], [-2], [-4], [-4, 1]] = [-5, 3, -2, -4, -4, 1] := by
  rw [(differenceResult_refines _).2]
  decide

theorem zero_continues : collapseCached [[0], [1], [99]] = [0, 1] := by
  rw [(cachedResult_refines _).2]
  decide

theorem empty_cached : collapseCached [] = [] := by
  rw [(cachedResult_refines []).2]
  rfl

theorem empty_difference (tail : List Int) : (differenceResult []).1.apply tail = tail := by
  simpa only [collapse, collapseAux, List.nil_append] using differenceResult_apply [] tail

theorem positive_seed_stops : collapseAux [5] [[99]] = [5] := by
  rw [collapseAux_eq_run]
  rfl

/-- The raw pair interface does not silently certify arbitrary cached sums. -/
theorem incorrect_cache_rejected :
    ¬ Sequences.OrderedSummary.listValid sumMeasure ([99], Multiplicative.ofAdd 0) := by
  intro h
  have bad := congrArg Multiplicative.toAdd h.2
  simp only [id_eq, summary_sum] at bad
  change (0 : Int) = 99 at bad
  omega

open Sequences.Steepness

/-- Each proper suffix sum is strictly below its preceding entry. -/
theorem tupled_steep : fastSteep [8, 4, 2, 1] = (15, true) := by
  rw [fastSteep_invariant]
  decide

theorem steep_mathematics : Steep [8, 4, 2, 1] := by
  apply (steepFast_correct _).mp
  change (fastSteep [8, 4, 2, 1]).2 = true
  rw [tupled_steep]

/-- Equality at the first boundary fails the strict condition. -/
theorem steep_tie_fails : steepFast [7, 4, 2, 1] = false := by
  rw [steepFast_eq_steep]
  decide

theorem steep_negative_fails : steepFast [-1, -2, -4] = false := by
  rw [steepFast_eq_steep]
  decide

theorem steep_empty : steepFast [] = true := by
  rw [steepFast_eq_steep]
  rfl

theorem steep_zero_fails : steepFast [0] = false := by
  rw [steepFast_eq_steep]
  decide

end Examples.Accumulation

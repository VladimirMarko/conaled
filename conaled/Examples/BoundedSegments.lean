import Applications.Segments.Observation

/-! Independent first-maximum certificates retain exact suffix-order choices.
Global-optimum and score consumers use the public realization theorems. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.BoundedSegments
open Segments

theorem empty (bound : Nat) : maxSegmentThinScan bound [] = [] ∧
    SegmentOptimal bound [] [] := by
  exact ⟨maxSegmentThinScan_nil bound, by simpa using maxSegmentThinScan_optimal bound []⟩

theorem zero_capacity (xs : List Int) : maxSegmentThinScan 0 xs = [] ∧
    (scoreSquare.impl (0, xs)).2 = 0 := by
  refine ⟨maxSegmentThinScan_zero xs, ?_⟩
  have optimal : SegmentOptimal 0 xs [] := by
    simpa only [maxSegmentThinScan_zero] using maxSegmentThinScan_optimal 0 xs
  exact selected_score_eq (0, xs) [] optimal

theorem negative_input : maxSegmentThinScan 3 [-5, -1, -2] = [] ∧
    SegmentOptimal 3 [-5, -1, -2] [] := by
  have h := maxSegmentThinScan_of_negative 3 [-5, -1, -2] (by decide)
  exact ⟨h, by simpa only [h] using maxSegmentThinScan_optimal 3 [-5, -1, -2]⟩

/-- Candidate scores are 7,9,5,0: the bound removes the full score-12 segment. -/
theorem binding_certificate :
    FirstMaximum List.sum ((tails [3, 4, 5]).map (msp1 2)) [4, 5] := by
  refine ⟨[[3, 4]], [[5], []], by decide, ?_, ?_⟩ <;> simp

theorem binding_capacity : maxSegmentThinScan 2 [3, 4, 5] = [4, 5] ∧
    maxSegmentThinScan 3 [3, 4, 5] = [3, 4, 5] := by
  refine ⟨maxSegmentThinScan_eq_of_firstMaximum _ _ _ binding_certificate, ?_⟩
  apply maxSegmentThinScan_eq_of_firstMaximum
  refine ⟨[], [[4, 5], [5], []], by decide, ?_, ?_⟩ <;> simp

/-- In suffix order, [1,1] appears before the equally good [2]. -/
theorem first_tie_certificate :
    FirstMaximum List.sum ((tails [1, 1, -10, 2]).map (msp1 2)) [1, 1] := by
  refine ⟨[], [[1], [], [2], []], by decide, ?_, ?_⟩ <;> simp

/-- Reversing the input moves [2] to the first suffix candidate. -/
theorem reversed_tie_certificate :
    FirstMaximum List.sum ((tails [2, -10, 1, 1]).map (msp1 2)) [2] := by
  refine ⟨[], [[], [1, 1], [1], []], by decide, ?_, ?_⟩ <;> simp

theorem distinct_tied_witnesses :
    maxSegmentThinScan 2 [1, 1, -10, 2] = [1, 1] ∧
      maxSegmentThinScan 2 [2, -10, 1, 1] = [2] :=
  ⟨maxSegmentThinScan_eq_of_firstMaximum _ _ _ first_tie_certificate,
    maxSegmentThinScan_eq_of_firstMaximum _ _ _ reversed_tie_certificate⟩

theorem first_tie_global : SegmentOptimal 2 [1, 1, -10, 2] [1, 1] := by
  have h := selected_witness_optimal (2, [1, 1, -10, 2])
  rw [distinct_tied_witnesses.1] at h
  exact h

theorem reversed_tie_global : SegmentOptimal 2 [2, -10, 1, 1] [2] := by
  have h := selected_witness_optimal (2, [2, -10, 1, 1])
  rw [distinct_tied_witnesses.2] at h
  exact h

/-- The score consumer forgets the distinct witnesses and reports the same optimum. -/
theorem tied_scores : (scoreSquare.impl (2, [1, 1, -10, 2])).2 = 2 ∧
    (scoreSquare.impl (2, [2, -10, 1, 1])).2 = 2 :=
  ⟨(selected_score_eq (2, [1, 1, -10, 2]) [1, 1] first_tie_global).trans (by decide),
    (selected_score_eq (2, [2, -10, 1, 1]) [2] reversed_tie_global).trans (by decide)⟩

/-- Three candidate occurrences survive; membership alone would not record them. -/
theorem repeated_all_optima : mss0 1 [0] = [[], [0], []] := by
  rw [← mss0Scan_eq]
  decide

theorem repeated_global_membership (p : List Int) :
    SegmentOptimal 1 [0] p ↔ p ∈ [[], [0], []] := by
  rw [← mem_mss0, repeated_all_optima]

theorem single_zero_witness : maxSegmentThinScan 1 [0] = [] := by
  apply maxSegmentThinScan_eq_of_firstMaximum
  refine ⟨[], [[]], by decide, ?_, ?_⟩ <;> simp

/-- The exact cut fold retains the ordered bounded prefixes, including the empty one. -/
theorem binding_prefixes : boundedPrefixes 2 ([3, 4, 5] : List Int) = [[], [3], [3, 4]] := by
  rw [boundedPrefixes_eq_filter]
  decide

theorem actual_frontier : Optimization.Thinning.IsThinning PrefixDominates
    [[], [-2], [-2, 4], [-2, 4, 4]] [[], [-2, 4], [-2, 4, 4]] := by
  simpa only [show boundedPrefixes 3 [-2, 4, 4] = [[], [-2], [-2, 4], [-2, 4, 4]] by decide,
    show thinnedPrefixes 3 [-2, 4, 4] = [[], [-2, 4], [-2, 4, 4]] by decide]
    using thinnedPrefixes_refinement 3 [-2, 4, 4]

/-- Without the invariant, source thinning stops at the first positive score. -/
theorem dropWhile_boundary : thin [[-1], [2], [-3]] = [[2], [-3]] := by decide

end Examples.BoundedSegments

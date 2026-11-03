import Applications.Subsequences.Observation

/-! Strict increasingness, occurrence order and the two public observations. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.IncreasingSubsequences
open Subsequences
open Optimization.Thinning (thinBy bump)

/-- Empty input has the empty optimum and observed length zero. -/
theorem empty : lus [] = [] ∧ LusOptimal [] [] ∧ (lengthSquare.impl []).2 = 0 := by
  have h : LusOptimal [] [] := by simpa only [lus_nil] using selected_witness_optimal []
  exact ⟨lus_nil, h, selected_length_eq [] [] h⟩

theorem singleton (x : Int) : lus [x] = [x] :=
  lus_of_increasing [x] (by simp [Increasing])

theorem increasing : lus [1, 2, 4] = [1, 2, 4] :=
  lus_of_increasing _ (by simp [Increasing])

theorem negative : lus [-4, -2, -1] = [-4, -2, -1] ∧
    (lengthSquare.impl [-4, -2, -1]).2 = 3 := by
  exact ⟨lus_of_increasing _ (by simp [Increasing]),
    selected_length_eq _ _ (lusOptimal_self [-4, -2, -1] (by simp [Increasing]))⟩

/-- The generators preserve different occurrence orders. -/
theorem generator_orders : subseqs [1, 2] = [[], [2], [1], [1, 2]] ∧
    subseqs1 [1, 2] = [[], [1], [2], [1, 2]] ∧
    (subseqs1 [1, 2]).Perm (subseqs [1, 2]) :=
  ⟨by decide, by decide, subseqs1_perm_subseqs _⟩

theorem duplicate_entries : subseqs [1, 1] = [[], [1], [1], [1, 1]] ∧
    (subseqs [1, 1]).length = 4 :=
  ⟨by decide, subseqs_length _⟩

theorem strict_boundary : ¬ Increasing [1, 1] ∧ Increasing [1, 2] := by
  constructor
  · intro h
    have htest := (up_correct [1, 1]).mpr h
    contradiction
  · exact (up_correct [1, 2]).mp (by decide)

/-- Filter fusion retains both occurrences of the repeated singleton. -/
theorem repeated_filter : upStates [1, 1] = [[], [1], [1]] := by
  rw [← filter_subseqs]
  decide

theorem repeated_all_optima : lus0 [1, 1, 2] = [[1, 2], [1, 2]] := by
  rw [lus0_eq_upStates]
  decide

theorem repeated_witness : lus [1, 1, 2] = [1, 2] ∧ LusOptimal [1, 1, 2] [1, 2] := by
  have he : lus [1, 1, 2] = [1, 2] := by
    simp [lus, lusStates, lusStep, sourceMergeBy, sourceMerge, thinBy, bump,
      UpDominates, lengthLE, canPrepend]
  exact ⟨he, by simpa only [he] using selected_witness_optimal [1, 1, 2]⟩

theorem repeated_membership (p : List Int) :
    LusOptimal [1, 1, 2] p ↔ p ∈ [[1, 2], [1, 2]] := by
  rw [← mem_lus0, repeated_all_optima]

/-- Length merge reorders the frontier, so only local merged thinning is a sublist. -/
theorem reordered_frontier : lusStates [4, 1, 3] = [[], [4], [1, 3]] := by
  simp [lusStates, lusStep, sourceMergeBy, sourceMerge, thinBy, bump,
    UpDominates, lengthLE, canPrepend]

theorem reordered_refinement : Optimization.Thinning.Represents UpDominates
    (upStates [4, 1, 3]) [[], [4], [1, 3]] := by
  simpa only [reordered_frontier] using lusStates_refinement [4, 1, 3]

theorem not_global_sublist : ¬ (lusStates [4, 1, 3]).Sublist (upStates [4, 1, 3]) := by
  rw [reordered_frontier]
  decide

theorem local_merged_refinement : Optimization.Thinning.IsThinning UpDominates
    [[], [3], [4], [1, 3]] [[], [4], [1, 3]] := by
  have h := lusStep_refinement 4 (lusStates [1, 3])
  convert h using 1 <;>
    simp [lusStates, lusStep, sourceMergeBy, sourceMerge, thinBy, bump,
      UpDominates, lengthLE, canPrepend]

/-- The adjacent bump cannot remove nonadjacent redundancies. -/
theorem actual_adjacent : Optimization.Thinning.thinBy UpDominates
    [[1, 2], [], [1]] = [[1, 2], [], [1]] := by decide

theorem frontier_order : ([[], [4], [1, 3]] : List (List Int)).Pairwise UpBefore := by
  simpa only [reordered_frontier] using lusStates_ordered [4, 1, 3]

theorem frontier_antichain : ([[], [4], [1, 3]] : List (List Int)).Pairwise
    (fun p q => ¬ UpDominates p q ∧ ¬ UpDominates q p) := by
  simpa only [reordered_frontier] using lusStates_antichain [4, 1, 3]

/-- Equal-length witnesses need not agree with the first all-optimum occurrence. -/
theorem tie_choices : lus [1, 3, 2] = [1, 3] ∧
    lus0 [1, 3, 2] = [[1, 2], [1, 3]] := by
  constructor
  · simp [lus, lusStates, lusStep, sourceMergeBy, sourceMerge, thinBy, bump,
      UpDominates, lengthLE, canPrepend]
  · decide

theorem tied_global : LusOptimal [1, 3, 2] [1, 3] := by
  have h := selected_witness_optimal [1, 3, 2]
  rw [tie_choices.1] at h
  exact h

theorem alternative_global : LusOptimal [1, 3, 2] [1, 2] := by
  apply (mem_lus0 _ _).mp
  rw [tie_choices.2]
  simp

theorem tied_length : (lengthSquare.impl [1, 3, 2]).2 = 2 :=
  selected_length_eq _ _ alternative_global

theorem decreasing : lus [3, 2, 1] = [3] ∧ LusOptimal [3, 2, 1] [3] := by
  have he : lus [3, 2, 1] = [3] := by
    simp [lus, lusStates, lusStep, sourceMergeBy, sourceMerge, thinBy, bump,
      UpDominates, lengthLE, canPrepend]
  exact ⟨he, by simpa only [he] using selected_witness_optimal [3, 2, 1]⟩

theorem frontier_bound : (lusStates [4, 1, 3]).length ≤ 3 := by
  have h := lusStates_count_le [4, 1, 3]
  have he : lus [4, 1, 3] = [1, 3] := by rw [lus, reordered_frontier]; rfl
  simpa only [he, List.length_cons, List.length_nil] using h

end Examples.IncreasingSubsequences

import Applications.EditAlignment.Observation

/-! Ordered edit witnesses, source tie policies, full rows and cache boundaries. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048

namespace Examples.EditAlignment
open _root_.EditAlignment

-- The first obligation is global alignment optimality, not just a reduced script.
theorem empty_minimum : MinimumEdit ([] : Script Nat) [] [] := by
  simpa [uncachedWitnessSquare, witnessSquare, Optimization.selectionSquare, mce2,
    editTable, firstrow] using (selected_witness (α := Nat) ([], [])).1

theorem delete_minimum : MinimumEdit ([.delete 1, .delete 2] : Script Nat) [1, 2] [] := by
  have h := mce2_spec ([1, 2] : List Nat) []
  simpa only [mce2_eq_mce, mce_nil_right, List.map_cons, List.map_nil] using h

theorem insert_minimum : MinimumEdit ([.insert 1, .insert 2] : Script Nat) [] [1, 2] := by
  have h := mce3_spec ([] : List Nat) [1, 2]
  simpa only [mce3_eq_mceIRD, mceIRD_nil_left, List.map_cons, List.map_nil] using h

theorem copies_minimum : MinimumEdit ([.copy 1, .copy 1] : Script Nat) [1, 1] [1, 1] := by
  have h := mce2_spec ([1, 1] : List Nat) [1, 1]
  simpa only [mce2_eq_mce, mce_equal_heads, mce_nil_right, List.map_nil] using h

theorem replacement_minimum : MinimumEdit ([.replace 0 1] : Script Nat) [0] [1] := by
  have h := mce2_spec ([0] : List Nat) [1]
  have he : mce2 ([0] : List Nat) [1] = [.replace 0 1] := by decide +kernel
  exact he ▸ h

example : costE ([.replace 0 1] : Script Nat) = 3 ∧
    costE ([.delete 0, .insert 1] : Script Nat) = 4 ∧
    (cachedCostSquare.impl ([0], [1])).2 = 3 :=
  ⟨rfl, rfl, cached_cost_eq_of_minimum ([0], [1]) [.replace 0 1] replacement_minimum⟩

-- Self-replacement remains an admissible competitor, but is strictly worse than copy.
example : Aligns ([.replace 0 0] : Script Nat) [0] [0] ∧
    costE ([.copy 0] : Script Nat) < costE [.replace 0 0] :=
  ⟨.replace 0 0 .nil, by decide⟩

def answerD : Script Char := [.delete 'a', .copy 'b', .delete 'c', .copy 'a', .insert 'c']
def answerI : Script Char := [.insert 'b', .copy 'a', .delete 'b', .copy 'c', .delete 'a']

theorem source_ties : mce2 "abca".toList "bac".toList = answerD ∧
    mce3 "abca".toList "bac".toList = answerI := by decide +kernel

theorem tied_minima : MinimumEdit answerD "abca".toList "bac".toList ∧
    MinimumEdit answerI "abca".toList "bac".toList := by
  have h := selected_witness ("abca".toList, "bac".toList)
  change MinimumEdit (mce2 "abca".toList "bac".toList) _ _ ∧
    MinimumEdit (mce3 "abca".toList "bac".toList) _ _ at h
  simpa only [source_ties.1, source_ties.2] using h

theorem source_cost_observations : answerD ≠ answerI ∧ costE answerD = 6 ∧ costE answerI = 6 ∧
    (uncachedCostSquare.impl ("abca".toList, "bac".toList)).2 = 6 ∧
    (cachedCostSquare.impl ("abca".toList, "bac".toList)).2 = 6 := by
  have hc := cached_cost_eq_of_minimum ("abca".toList, "bac".toList) answerD tied_minima.1
  refine ⟨by decide +kernel, rfl, rfl, ?_, hc⟩
  rw [observed_cost_agreement]
  exact hc

theorem solvers_can_differ : mce2 "abca".toList "bac".toList ≠
    mce3 "abca".toList "bac".toList := by
  rw [source_ties.1, source_ties.2]
  exact source_cost_observations.1

theorem uncached_source_cost : costE (mce2 "abca".toList "bac".toList) = 6 :=
  source_cost_observations.2.2.2.1

example : reconstruct answerD = ("abca".toList, "bac".toList) ∧
    reconstruct answerI = ("abca".toList, "bac".toList) :=
  ⟨tied_minima.1.1.reconstruct, tied_minima.2.1.reconstruct⟩

-- Every suffix entry is exposed, including the terminal insertion-only column.
theorem all_uncached_entries :
    (editTable ([0, 1] : List Nat) [1])[0]? = some [.delete 0, .copy 1] ∧
    (editTable ([0, 1] : List Nat) [1])[1]? = some [.copy 1] ∧
    (editTable ([0, 1] : List Nat) [1])[2]? = some [.insert 1] := by
  constructor
  · rw [editTable_entry _ _ _ (by decide)]
    decide +kernel
  constructor
  · rw [editTable_entry _ _ _ (by decide)]
    decide +kernel
  · rw [editTable_entry _ _ _ (by decide)]
    decide +kernel

theorem all_cached_entries :
    (editTable3 ([0, 1] : List Nat) [1])[0]? = some (2, [.delete 0, .copy 1]) ∧
    (editTable3 ([0, 1] : List Nat) [1])[1]? = some (0, [.copy 1]) ∧
    (editTable3 ([0, 1] : List Nat) [1])[2]? = some (2, [.insert 1]) := by
  constructor
  · rw [editTable3_entry _ _ _ (by decide)]
    decide +kernel
  constructor
  · rw [editTable3_entry _ _ _ (by decide)]
    decide +kernel
  · rw [editTable3_entry _ _ _ (by decide)]
    decide +kernel

example : (editTable3 ([0, 1] : List Nat) [1]).length = 3 ∧
    ∀ p ∈ editTable3 ([0, 1] : List Nat) [1], CacheValid p :=
  ⟨editTable3_length _ _, editTable3_cache_valid _ _⟩

-- Standard shared selection supplies the positional first-minimum observation.
example : Optimization.FirstMinimum costE [answerD, answerI] answerD := by
  have h := best_firstMinimum answerD answerI
  rw [best_tie_left _ _ (by decide +kernel)] at h
  exact h

example : (editTable3 ([0, 1] : List Nat) [1])[3]? = none := by
  rw [List.getElem?_eq_none_iff, editTable3_length]
  decide

-- Incorrect cached scores can choose the more expensive of two valid alignments.
def bad : Pair Nat := (0, [.delete 0, .insert 1])
def good : Pair Nat := cache [.replace 0 1]

example : Aligns bad.2 [0] [1] ∧ Aligns good.2 [0] [1] :=
  ⟨(aligns_iff_reconstruct _ _ _).mpr (by decide +kernel),
    (aligns_iff_reconstruct _ _ _).mpr (by decide +kernel)⟩

example : ¬CacheValid bad ∧ CacheValid good ∧
    (cachedBest bad good).2 = bad.2 ∧ best bad.2 good.2 = good.2 ∧
    costE good.2 < costE (cachedBest bad good).2 := by
  unfold CacheValid
  decide +kernel

example : CacheValid (cachedBest (cache answerD) (cache answerI)) :=
  cachedBest_valid _ _ (cache_valid _) (cache_valid _)

end Examples.EditAlignment

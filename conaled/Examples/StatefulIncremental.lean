import Applications.Incremental.VectorSumCost
import Applications.Incremental.PrefixSum

/-! Checked clients of retained-state composition. The repeated assignment at
index 1 reads 7 on its second visit, so the final vector is [-2,4,5], sum 7.
The consumer doubles that sum to 14. -/
namespace Examples.StatefulIncremental
open Incremental Incremental.VectorSum

def input : Values ℤ 3 := ![2, 3, 5]
def edits : Patch ℤ 3 := [(1, 7), (1, 4), (0, -2)]

theorem repeated_assignments :
    (realization ℤ 3).observe ((realization ℤ 3).repair ((realization ℤ 3).init input) edits).1 = 7 := by
  calc
    _ = total (applyPatch input edits) :=
      realization_laws.observe _ _ (realization_laws.repair _ _ _ (realization_laws.init input))
    _ = 7 := by decide

theorem retained_composition :
    (doubled ℤ 3).observe ((doubled ℤ 3).repair ((doubled ℤ 3).init input) edits).1 = 14 := by
  rw [doubled_after_patch]
  decide

theorem measured_composition :
    (Cost.composedRepair (Cost.composedInit input).1 edits).1.1.2 = 14 := by
  rw [Cost.composedInit_value, Cost.composedRepair_value]
  exact retained_composition

theorem boundary_change :
    ((realization ℤ 3).repair ((realization ℤ 3).init input) edits).2 = -3 := by decide

theorem workload_count : (Cost.workload input [edits, []]).2 = 35 := by
  rw [Cost.workload_cost]
  decide

theorem workload_observation : (Cost.workload input [edits, []]).1.2 = 14 := by
  have h := Cost.workload_valid input [edits, []]
  have ho := doubled_laws.observe _ _ h
  calc
    _ = total ([edits, []].foldl applyPatch input) + total ([edits, []].foldl applyPatch input) := ho
    _ = 14 := by decide

theorem empty_vector :
    (Cost.composedInit (Fin.elim0 : Values ℤ 0)).1.2 = 0 ∧
      (Cost.composedInit (Fin.elim0 : Values ℤ 0)).2 = 4 := by
  constructor
  · rw [Cost.composedInit_value]; rfl
  · exact Cost.composedInit_cost _

theorem empty_patch :
    (Cost.composedRepair (Cost.composedInit input).1 []).1.1.2 = 20 ∧
      (Cost.composedRepair (Cost.composedInit input).1 []).2 = 4 := by
  constructor
  · rw [Cost.composedInit_value, Cost.composedRepair_value]
    exact doubled_after_patch input [] |>.trans (by decide)
  · exact Cost.composedRepair_cost _ []

/-- A single input assignment forces three output writes in this observation. -/
theorem materialized_prefix_requires_three (writes : Patch ℤ 3)
    (h : applyPatch (prefixes input) writes = prefixes (assign input (0, 3))) :
    3 ≤ writes.length :=
  prefix_write_lower_bound input 1 (by decide) writes h

/-- The same ordinary theorem works for any exact additive commutative group,
without importing a cost model or requiring an executable scalar representation. -/
theorem arbitrary_group {G : Type} [AddCommGroup G] (v : Values G 4) (p : Patch G 4) :
    (doubled G 4).observe ((doubled G 4).repair ((doubled G 4).init v) p).1 =
      total (applyPatch v p) + total (applyPatch v p) := doubled_after_patch v p

end Examples.StatefulIncremental

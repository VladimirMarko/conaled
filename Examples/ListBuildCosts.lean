import Applications.Resources.ListBuildCosts

/-!
Independent calculations for the ordinary-list alternatives: appending three
elements costs 1+2+3=6 append calls, plus four loop entries and one wrapper;
prepending and reversing costs four calls for each traversal and one wrapper.
The unequal ordered inputs also check that both executions reconstruct order.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.ListBuildCosts
open Resources.ListBuildCosts
universe u

theorem empty_payload :
    appendSubRun ([] : List Empty) [] = ([], 0) ∧
    appendBuildRun ([] : List Empty) = ([], 2) ∧
    consReverseBuildRun ([] : List Empty) = ([], 3) := by
  refine ⟨appendSubRun_nil [], ?_, ?_⟩
  · exact appendBuildRun_exact []
  · exact consReverseBuildRun_exact []

/-- The fixed entry costs matter for small inputs, before the quadratic growth dominates. -/
theorem singleton :
    appendSubRun [7] [] = ([7], 1) ∧
    appendBuildRun [7] = ([7], 4) ∧ consReverseBuildRun [7] = ([7], 5) := by
  refine ⟨?_, appendBuildRun_exact [7], consReverseBuildRun_exact [7]⟩
  apply Prod.ext
  · exact appendSubRun_value [7] []
  · exact appendSubRun_empty_cost [7]

theorem ordered_duplicates :
    appendSubRun [3, 1, 3] [] = ([3, 1, 3], 6) ∧
    appendBuildRun [3, 1, 3] = ([3, 1, 3], 11) ∧
    consReverseBuildRun [3, 1, 3] = ([3, 1, 3], 9) := by
  refine ⟨?_, appendBuildRun_exact [3, 1, 3], consReverseBuildRun_exact [3, 1, 3]⟩
  apply Prod.ext
  · exact appendSubRun_value [3, 1, 3] []
  · exact appendSubRun_empty_cost [3, 1, 3]

/-- This nonpalindromic input distinguishes reconstruction from one reversal. -/
theorem order_is_restored :
    appendBuildRun [3, 1, 3, 2] = ([3, 1, 3, 2], 16) ∧
    consReverseBuildRun [3, 1, 3, 2] = ([3, 1, 3, 2], 11) :=
  ⟨appendBuildRun_exact [3, 1, 3, 2], consReverseBuildRun_exact [3, 1, 3, 2]⟩

/-- A supplied one-element seed makes the two actual append counts 2 and 3. -/
theorem nonempty_seed : appendSubRun [3, 1] [9] = ([9, 3, 1], 5) := by
  apply Prod.ext
  · exact appendSubRun_value [3, 1] [9]
  · exact appendSubRun_cost [3, 1] [9]

/-- Three loop entries, but no outer wrapper, are added for these two elements. -/
theorem nonempty_seed_full_loop : appendLoopRun [3, 1] [9] = ([9, 3, 1], 8) := by
  apply Prod.ext
  · exact appendLoopRun_value [3, 1] [9]
  · simp [appendLoopRun_cost, nonempty_seed]

/-- Abstract payloads and multiplicity are retained without any element instances. -/
theorem polymorphic_order {α : Type u} (a b : α) :
    appendBuildRun [a, b, a] = ([a, b, a], 11) ∧
    consReverseBuildRun [a, b, a] = ([a, b, a], 9) := by
  constructor
  · simpa using appendBuildRun_exact [a, b, a]
  · simpa using consReverseBuildRun_exact [a, b, a]

theorem same_value_different_cost :
    (appendBuildRun [3, 1, 3]).1 = (consReverseBuildRun [3, 1, 3]).1 ∧
    (appendBuildRun [3, 1, 3]).2 ≠ (consReverseBuildRun [3, 1, 3]).2 := by
  refine ⟨realizations_agree [3, 1, 3], ?_⟩
  rw [appendBuildRun_cost, consReverseBuildRun_cost]
  decide

/-- The exact laws imply uniform quadratic versus linear bounds for every payload type. -/
theorem uniform_bounds {α : Type u} (items : List α) (hn : 1 ≤ items.length) :
    items.length * items.length ≤ 2 * (appendBuildRun items).2 ∧
    (appendBuildRun items).2 ≤ 4 * items.length * items.length ∧
    (consReverseBuildRun items).2 ≤ 5 * items.length :=
  ⟨appendBuildRun_quadratic_lower items,
    appendBuildRun_quadratic_upper items hn, consReverseBuildRun_linear_upper items hn⟩

end Examples.ListBuildCosts

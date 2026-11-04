import Applications.Resources.NaturalRunComparisons
import Examples.NaturalRuns

/-!
The independently calculated runs from the value examples now carry the
source comparison observation. A four-element scan costs three comparisons,
whether it emits one run or restarts; a worker with two remaining elements
costs two, independently of the already supplied accumulator.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.NaturalRunComparisons
open Applications.Sorting Resources.NaturalRunComparisons Examples.NaturalRuns

theorem empty_payload :
    runsRunBy (fun a _ : Empty => nomatch a) [] = ([], 0) := runsRunBy_nil _

theorem singleton : runsRunBy natLT [7] = ([[7]], 0) := runsRunBy_singleton _ _

/-- A failed ascending boundary is charged once and its next element is retained. -/
theorem restart_boundary :
    runsRunBy natLT [1, 3, 2, 4] = ([[1, 3], [2, 4]], 3) := by
  apply Prod.ext
  · rw [runsRunBy_value]
    exact NaturalRuns.restart_boundary
  · exact runsRunBy_cost_exact natLT [1, 3, 2, 4]

theorem ascending_ties : runsRunBy natLT [1, 1, 2, 3] = ([[1, 1, 2, 3]], 3) := by
  exact runsRunBy_of_sorted id [1, 1, 2, 3] (by decide) (by simp)

theorem descending_reversal :
    runsRunBy natLT [4, 3, 2, 1] = ([[1, 2, 3, 4]], 3) := by
  exact runsRunBy_of_strictly_descending id [4, 3, 2, 1] (by decide) (by simp)

/-- No equality, default value or ordering instance is needed for the payloads. -/
theorem payloads_need_no_structure {β : Type} (p q : β) :
    runsRunBy (fun x y : Nat × β => decide (x.1 < y.1)) [(1, p), (1, q)] =
      ([[(1, p), (1, q)]], 1) := by
  apply Prod.ext
  · rw [runsRunBy_value]
    exact NaturalRuns.payloads_need_no_structure p q
  · exact runsRunBy_cost_exact _ [(1, p), (1, q)]

/-- The strict descending branch stops at equal keys; both occurrences survive. -/
theorem mixed_records :
    runsRunBy (fun x y : Record => decide (x.1 < y.1)) mixedRecords =
      (mixedRuns, 3) := by
  apply Prod.ext
  · rw [runsRunBy_value]
    exact NaturalRuns.mixed_records
  · exact runsRunBy_cost_exact _ mixedRecords

theorem weak_descent_with_ties :
    runsRunBy (fun x y : Record => decide (x.1 < y.1))
      [(3, "A"), (3, "B"), (2, "C")] =
      ([[(3, "A"), (3, "B")], [(2, "C")]], 2) := by
  apply Prod.ext
  · rw [runsRunBy_value]
    exact NaturalRuns.weak_descent_with_ties
  · exact runsRunBy_cost_exact _ [(3, "A"), (3, "B"), (2, "C")]

/-- Low comparison cost does not turn weak descent with ties into one reversed run. -/
theorem weak_descent_not_one_reversal :
    (runsRunBy (fun x y : Record => decide (x.1 < y.1))
      [(3, "A"), (3, "B"), (2, "C")]).1 ≠
        [[(2, "C"), (3, "B"), (3, "A")]] := by
  rw [runsRunBy_value]
  exact NaturalRuns.weak_descent_not_one_reversal

theorem arbitrary_builder_restart :
    ascSourceRunBy natLT 5 seededBuilder seededBuilder_law [4, 6] =
      ([[1, 3, 5], [4, 6]], 2) := by
  apply Prod.ext
  · rw [ascSourceRunBy_value]
    exact NaturalRuns.arbitrary_builder_restart
  · exact ascSourceRunBy_cost natLT 5 seededBuilder seededBuilder_law [4, 6]

/-- A lawful but unsorted supplied prefix needs no comparisons on an empty tail. -/
theorem unsorted_builder_zero_comparisons :
    ascSourceRunBy natLT 3 unsortedBuilder unsortedBuilder_law [] = ([[2, 1, 3]], 0) ∧
    ¬KeySorted id
      (ascSourceRunBy natLT 3 unsortedBuilder unsortedBuilder_law []).1.flatten := by
  constructor
  · apply Prod.ext
    · rw [ascSourceRunBy_value]
      exact NaturalRuns.unsorted_builder_value
    · exact ascSourceRunBy_cost natLT 3 unsortedBuilder unsortedBuilder_law []
  · rw [ascSourceRunBy_value]
    exact NaturalRuns.lawful_builder_does_not_imply_sorted.2

/-- The arbitrary weak descending state still reverses the two equal-key payloads. -/
theorem weak_descending_zero_comparisons :
    descRunBy (fun x y : Record => decide (x.1 < y.1))
      equalCurrent equalAccumulator [] = ([[(2, "later"), (2, "earlier")]], 0) ∧
    ¬Stable Prod.fst ([(2, "earlier"), (2, "later")] : List Record)
      (descRunBy (fun x y : Record => decide (x.1 < y.1))
        equalCurrent equalAccumulator []).1.flatten := by
  constructor
  · apply Prod.ext
    · rw [descRunBy_value]
      exact NaturalRuns.weak_descending_value
    · exact descRunBy_cost_exact _ equalCurrent equalAccumulator []
  · rw [descRunBy_value]
    exact NaturalRuns.weak_descending_not_stable

/-- The source counter ignores order laws, but the value theorem does not invent them. -/
theorem arbitrary_comparators_same_count {α : Type} (lt₁ lt₂ : α → α → Bool)
    (xs : List α) : (runsRunBy lt₁ xs).2 = (runsRunBy lt₂ xs).2 := by
  rw [runsRunBy_cost_exact, runsRunBy_cost_exact]

end Examples.NaturalRunComparisons

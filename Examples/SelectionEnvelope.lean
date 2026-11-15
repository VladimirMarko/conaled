import Applications.Resources.SelectionEnvelope

/-! Scalar cases with expectations recorded before implementation.
These are not measurements of a selection execution.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SelectionEnvelope
open Resources.SelectionEnvelope

theorem group_two_values :
    tollCoefficient 2 = 24 ∧ envelope 2 0 = 4 ∧ envelope 2 1 = 39 ∧
      envelope 2 2 = 133 ∧ envelope 2 3 = 345 := by decide

theorem group_five_values :
    tollCoefficient 5 = 57 ∧ envelope 5 0 = 4 ∧ envelope 5 1 = 72 ∧
      envelope 5 2 = 265 ∧ envelope 5 3 = 708 := by decide

theorem small_budget_values :
    smallBudget 0 = 3 ∧ smallBudget 1 = 8 ∧
      smallBudget 2 = 15 ∧ smallBudget 3 = 24 := by decide

theorem invalid_empty_bound (d : Nat) : 2 ≤ envelope d 0 :=
  invalid_budget_le d 0

theorem charged_two_child_example :
    envelope 2 1 + envelope 2 0 + (tollCoefficient 2 * 2 + 7) = 98 ∧
      98 ≤ envelope 2 2 := by
  constructor
  · decide
  · exact two_child_budget_le 2 2 1 0 39 4 55 98
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Equal-size recursive children are outside the transfer theorem's domain. -/
theorem nonshrinking_budget_exceeds :
    2 * envelope 2 1 + tollCoefficient 2 * 1 + 7 = 109 ∧
      envelope 2 1 < 109 := by decide

theorem actual_cutoff_prefix (d actualCutoff scalarCutoff n : Nat)
    (hn : n ≤ actualCutoff) :
    envelope d n ≤ envelope d (max actualCutoff scalarCutoff) :=
  prefix_max_bound d actualCutoff scalarCutoff n (Or.inl hn)

theorem scalar_cutoff_prefix (d actualCutoff scalarCutoff n : Nat)
    (hn : n ≤ scalarCutoff) :
    envelope d n ≤ envelope d (max actualCutoff scalarCutoff) :=
  prefix_max_bound d actualCutoff scalarCutoff n (Or.inr hn)

end Examples.SelectionEnvelope

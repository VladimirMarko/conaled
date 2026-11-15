import Applications.Resources.SelectionGenericEnvelope
import Examples.SelectionCosts
import Examples.SelectionEnvelope

/-! Actual generic values and finite-size call budgets.
The exact group-two count169 is reused from the checked worker example.
Other runtime assertions here are envelope bounds, with independently
prepared finite values; scalar envelopes are not identified with actual costs.
Groups three and four retain correctness without a linearity claim.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SelectionGenericEnvelope
open Applications.Selection
open Resources.Selection Resources.SelectionEnvelope

private theorem repeated_value_and_budget (d cutoff : Nat)
    (hd : 2 ≤ d) (hc : 1 ≤ cutoff) :
    (selectRunWith d cutoff hd hc 2 ([3, 1, 2, 2] : List Nat)).1 = some 2 ∧
      (selectRunWith d cutoff hd hc 2 ([3, 1, 2, 2] : List Nat)).2 ≤ envelope d 4 := by
  constructor
  · rw [selectRunWith_value]
    simpa only [ordered, Applications.Sorting.sortOn_eq_insertionOn] using
      (show (Applications.Sorting.insertionOn id ([3, 1, 2, 2] : List Nat))[2]? = some 2 by
        decide +kernel)
  · simpa only [List.length_cons, List.length_nil] using
      selectRunWith_cost_le_envelope d cutoff hd hc 2 ([3, 1, 2, 2] : List Nat)

theorem empty_any_group (d cutoff : Nat) (hd : 2 ≤ d) (hc : 1 ≤ cutoff) (k : Nat) :
    selectRunWith d cutoff hd hc k ([] : List (Fin 0)) = (none, 2) ∧
      (selectRunWith d cutoff hd hc k ([] : List (Fin 0))).2 ≤ 4 := by
  constructor
  · exact selectRunWith_nil d cutoff hd hc k
  · simpa only [List.length_nil, envelope_zero] using
      selectRunWith_cost_le_envelope d cutoff hd hc k ([] : List (Fin 0))

theorem group_two_budget :
    selectRunWith 2 1 (by decide) (by decide) 2 ([3, 1, 2, 2] : List Nat) = (some 2, 169) ∧
      (selectRunWith 2 1 (by decide) (by decide) 2 ([3, 1, 2, 2] : List Nat)).2 ≤ 793 := by
  constructor
  · exact Examples.SelectionCosts.group_two_cutoff_one
  · simpa only [show envelope 2 4 = 793 from by decide] using
      (repeated_value_and_budget 2 1 (by decide) (by decide)).2

theorem group_three_budget :
    (selectRunWith 3 1 (by decide) (by decide) 2 ([3, 1, 2, 2] : List Nat)).1 = some 2 ∧
      (selectRunWith 3 1 (by decide) (by decide) 2 ([3, 1, 2, 2] : List Nat)).2 ≤ 1027 := by
  simpa only [show envelope 3 4 = 1027 from by decide] using
    repeated_value_and_budget 3 1 (by decide) (by decide)

theorem group_four_budget :
    (selectRunWith 4 1 (by decide) (by decide) 2 ([3, 1, 2, 2] : List Nat)).1 = some 2 ∧
      (selectRunWith 4 1 (by decide) (by decide) 2 ([3, 1, 2, 2] : List Nat)).2 ≤ 1313 := by
  simpa only [show envelope 4 4 = 1313 from by decide] using
    repeated_value_and_budget 4 1 (by decide) (by decide)

theorem group_five_budget :
    (selectRunWith 5 1 (by decide) (by decide) 2 ([3, 1, 2, 2] : List Nat)).1 = some 2 ∧
      (selectRunWith 5 1 (by decide) (by decide) 2 ([3, 1, 2, 2] : List Nat)).2 ≤ 1651 := by
  simpa only [show envelope 5 4 = 1651 from by decide] using
    repeated_value_and_budget 5 1 (by decide) (by decide)

theorem group_six_budget :
    (selectRunWith 6 1 (by decide) (by decide) 2 ([3, 1, 2, 2] : List Nat)).1 = some 2 ∧
      (selectRunWith 6 1 (by decide) (by decide) 2 ([3, 1, 2, 2] : List Nat)).2 ≤ 2041 := by
  simpa only [show envelope 6 4 = 2041 from by decide] using
    repeated_value_and_budget 6 1 (by decide) (by decide)

theorem group_three_invalid :
    selectRunWith 3 1 (by decide) (by decide) 4 ([3, 1, 2, 2] : List Nat) = (none, 6) ∧
      (selectRunWith 3 1 (by decide) (by decide) 4 ([3, 1, 2, 2] : List Nat)).2 ≤ 1027 := by
  constructor
  · exact selectRunWith_of_invalid 3 1 (by decide) (by decide) 4 _ (by decide)
  · simpa only [List.length_cons, List.length_nil,
      show envelope 3 4 = 1027 from by decide] using
      selectRunWith_cost_le_envelope 3 1 (by decide) (by decide) 4 ([3, 1, 2, 2] : List Nat)

/-- Increasing the actual cutoff is also covered by the same size envelope. -/
theorem larger_cutoff_budget :
    (selectRunWith 2 10 (by decide) (by decide) 2 ([3, 1, 2, 2] : List Nat)).1 = some 2 ∧
      (selectRunWith 2 10 (by decide) (by decide) 2 ([3, 1, 2, 2] : List Nat)).2 ≤ 793 := by
  simpa only [show envelope 2 4 = 793 from by decide] using
    repeated_value_and_budget 2 10 (by decide) (by decide)

theorem group_three_left :
    (selectRunWith 3 1 (by decide) (by decide) 0 (List.range 7)).1 = some 0 ∧
      (selectRunWith 3 1 (by decide) (by decide) 0 (List.range 7)).2 ≤ 9552 := by
  constructor
  · rw [selectRunWith_value]
    simpa only [ordered, Applications.Sorting.sortOn_eq_insertionOn] using
      (show (Applications.Sorting.insertionOn id (List.range 7))[0]? = some 0 by decide +kernel)
  · simpa only [List.length_range, show envelope 3 7 = 9552 from by decide] using
      selectRunWith_cost_le_envelope 3 1 (by decide) (by decide) 0 (List.range 7)

theorem group_three_right :
    (selectRunWith 3 1 (by decide) (by decide) 6 (List.range 7)).1 = some 6 ∧
      (selectRunWith 3 1 (by decide) (by decide) 6 (List.range 7)).2 ≤ 9552 := by
  constructor
  · rw [selectRunWith_value]
    simpa only [ordered, Applications.Sorting.sortOn_eq_insertionOn] using
      (show (Applications.Sorting.insertionOn id (List.range 7))[6]? = some 6 by decide +kernel)
  · simpa only [List.length_range, show envelope 3 7 = 9552 from by decide] using
      selectRunWith_cost_le_envelope 3 1 (by decide) (by decide) 6 (List.range 7)

/-- The input domain is infinite; only the common length threshold is fixed. -/
theorem integer_prefix (d cutoff : Nat) (hd : 2 ≤ d) (hc : 1 ≤ cutoff) (N : Nat) :
    ∀ (xs : List Int) (k : Nat), xs.length ≤ N →
      (selectRunWith d cutoff hd hc k xs).2 ≤ envelope d N :=
  selectRunWith_uniform_prefix_bound d cutoff hd hc N Int

end Examples.SelectionGenericEnvelope

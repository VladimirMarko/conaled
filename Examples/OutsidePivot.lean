import Applications.Selection.OutsidePivot

/-! Connected cases for the exact outside-pivot recurrence.
Repeated entries, both endpoints, negative integers, a singleton and the empty
boundary distinguish the valid-state theorem from an unqualified pivot slogan.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.OutsidePivot
open Applications.Selection Applications.Selection.OutsidePivot

theorem below_partition :
    partition3 0 ([1, 3, 1] : List Nat) = ([], [], [1, 3, 1]) :=
  partition3_below 0 _ (by simp)

theorem above_partition :
    partition3 4 ([1, 3, 1] : List Nat) = ([1, 3, 1], [], []) :=
  partition3_above 4 _ (by simp)

theorem below_dispatch_same_state (recur : Nat → List Nat → Option Nat) (k : Nat) :
    dispatch recur 0 k [1, 3, 1] = recur k [1, 3, 1] :=
  dispatch_below recur 0 k _ (by simp)

theorem above_dispatch_same_state (recur : Nat → List Nat → Option Nat) :
    dispatch recur 4 2 [1, 3, 1] = recur 2 [1, 3, 1] :=
  dispatch_above recur 4 2 _ (by decide) (by simp)

/-- This is universally quantified fuel, not a finite sample of failed calls. -/
theorem below_both_endpoints (fuel : Nat) :
    runWith (fun _ => some 0) fuel 0 ([1, 3, 1] : List Nat) = none ∧
    runWith (fun _ => some 0) fuel 2 ([1, 3, 1] : List Nat) = none := by
  constructor
  · exact runWith_below_none _ 0 _ 0 fuel (by simp) rfl (by simp)
  · exact runWith_below_none _ 0 _ 2 fuel (by simp) rfl (by simp)

theorem above_both_endpoints (fuel : Nat) :
    runWith (fun _ => some 4) fuel 0 ([1, 3, 1] : List Nat) = none ∧
    runWith (fun _ => some 4) fuel 2 ([1, 3, 1] : List Nat) = none := by
  constructor
  · exact runWith_above_none _ 4 _ 0 fuel (by decide) rfl (by simp)
  · exact runWith_above_none _ 4 _ 2 fuel (by decide) rfl (by simp)

theorem negative_duplicate_input (fuel : Nat) :
    runWith (fun _ => some 0) fuel 2 ([-3, -1, -3] : List Int) = none :=
  runWith_above_none _ 0 _ 2 fuel (by decide) rfl (by simp)

theorem singleton_never_answers (fuel : Nat) :
    runWith (fun _ => some 0) fuel 0 ([1] : List Nat) = none :=
  runWith_below_none _ 0 _ 0 fuel (by simp) rfl (by simp)

theorem below_valid_answer_not_obtained (fuel : Nat) :
    runWith (fun _ => some 0) fuel 0 ([1, 3, 1] : List Nat) ≠
      (ordered [1, 3, 1])[0]? :=
  runWith_below_ne_spec _ 0 _ 0 fuel (by decide) rfl (by simp)

theorem above_valid_answer_not_obtained (fuel : Nat) :
    runWith (fun _ => some 4) fuel 2 ([1, 3, 1] : List Nat) ≠
      (ordered [1, 3, 1])[2]? :=
  runWith_above_ne_spec _ 4 _ 2 fuel (by decide) rfl (by simp)

/-- A local outside choice already violates the membership interface. -/
theorem below_policy_rejected (choose : List Nat → Option Nat)
    (hc : choose [1, 3, 1] = some 0) : ¬ PivotValid choose :=
  not_pivotValid_below choose 0 _ (by simp) hc (by simp)

theorem above_policy_rejected (choose : List Int → Option Int)
    (hc : choose [-3, -1, -3] = some 0) : ¬ PivotValid choose :=
  not_pivotValid_above choose 0 _ (by simp) hc (by simp)

theorem public_positive_boundary :
    selectWith (fun _ => some 0) 1 ([1, 3, 1] : List Nat) = none ∧
    selectWith (fun _ => some 4) 3 ([1, 3, 1] : List Nat) = none := by
  constructor
  · exact selectWith_below_none _ 0 _ 0 (by simp) rfl (by simp)
  · exact selectWith_above_none _ 4 _ 2 (by decide) rfl (by simp)

theorem empty_has_no_valid_rank (fuel k : Nat) :
    runWith (fun _ => some 0) fuel k ([] : List Nat) = none := by
  cases fuel <;> rfl

/-- Above-range self-recursion needs a valid rank: here length=3 and k=3. -/
theorem invalid_above_uses_empty_right (recur : Nat → List Nat → Option Nat) :
    dispatch recur 4 3 [1, 3, 1] = recur 0 [] := rfl

theorem in_range_policy_contrast :
    selectWith List.head? 3 ([1, 3, 1] : List Nat) = some 3 := by
  decide

end Examples.OutsidePivot

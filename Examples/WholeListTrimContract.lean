import Applications.Resources.WholeListTrim

/-! Independent ordinary-list longest-prefix answers and prices, frozen before
implementing the measured trim runner. These are not execution observations. -/

namespace Resources.WholeListTrimContract
open WholeListTrim

def nondecreasing (xs : List Nat) : Bool := decide (xs.Pairwise (· ≤ ·))
def distinct (xs : List Nat) : Bool := decide (xs.Pairwise (· ≠ ·))
def onlyOneTwo (xs : List Nat) : Bool := decide (xs = [1, 2])

theorem ordered_spec : Spec nondecreasing [3, 7, 8, 2, 3] [3, 7, 8] :=
  Spec.of_checks _ _ _ (by decide) (by decide) (by decide)

theorem distinct_spec : Spec distinct [1, 2, 1] [1, 2] :=
  Spec.of_checks _ _ _ (by decide) (by decide) (by decide)

theorem only_spec : Spec onlyOneTwo [1, 2, 3] [1, 2] :=
  Spec.of_checks _ _ _ (by decide) (by decide) (by decide)

-- Two rejected lengths, then one accepted guard; full fold charges 2*k+1.
example : 2 * 5 + 2 * 4 + 3 = 21 := rfl
example : 21 + (1 + 1) * 3 + 1 = 28 := rfl
example : 2 * 3 + 2 = 8 := rfl
example : 8 + (1 + 1) * 2 + 1 = 13 := rfl
example : ([1, 2, 1] : List Nat).Chain' (· ≠ ·) := by decide
example : distinct [1, 2, 1] = false := by decide
example : onlyOneTwo [1, 2] = true ∧ ¬ Accept onlyOneTwo [2] := by decide

end Resources.WholeListTrimContract

import Mathlib.Order.Monotone.Basic
import Lean.Elab.Tactic.Omega

/-! Uniform finite-prefix budgets supporting the generalized selection analysis.

This scalar is deliberately coarse. It bounds a quadratic small branch and
two strictly smaller child budgets with an explicit linear local toll. An
algorithmic application must prove that its actual execution obeys those
budgets. This module does not assume a finite payload type, define a runtime,
or replace the separate contracting recurrence and its linear bound.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.SelectionEnvelope

/-- A loose coefficient available for the later measured local-toll proof. -/
def tollCoefficient (d : Nat) : Nat := d * d + 4 * d + 12

/-- Length acquisition, the entry call and the quadratic small selector. -/
def smallBudget (n : Nat) : Nat := n * n + 4 * n + 3

/-- A size-only budget; both hypothetical children use the previous size. -/
def envelope (d : Nat) : Nat → Nat
  | 0 => 4
  | n + 1 => max (smallBudget (n + 1))
      (2 * envelope d n + tollCoefficient d * (n + 1) + 7)

@[simp] theorem envelope_zero (d : Nat) : envelope d 0 = 4 := rfl

theorem envelope_succ (d n : Nat) :
    envelope d (n + 1) = max (smallBudget (n + 1))
      (2 * envelope d n + tollCoefficient d * (n + 1) + 7) := rfl

theorem recursive_budget_le (d n : Nat) :
    2 * envelope d n + tollCoefficient d * (n + 1) + 7 ≤ envelope d (n + 1) :=
  le_max_right _ _

theorem le_succ (d n : Nat) : envelope d n ≤ envelope d (n + 1) := by
  have bound := recursive_budget_le d n
  omega

theorem envelope_mono (d : Nat) : Monotone (envelope d) :=
  monotone_nat_of_le_succ (le_succ d)

theorem small_budget_le (d n : Nat) : smallBudget n ≤ envelope d n := by
  cases n with
  | zero => decide
  | succ n => exact le_max_left _ _

theorem invalid_budget_le (d n : Nat) : n + 2 ≤ envelope d n := by
  have bound := small_budget_le d n
  unfold smallBudget at bound
  omega

/-- Two strict child bounds and the actual local toll can be transported to
the parent budget. The comparisons must be supplied by an execution proof. -/
theorem two_child_budget_le (d n m r pivotCost childCost localCost total : Nat)
    (hm : m < n) (hr : r < n)
    (hpivot : pivotCost ≤ envelope d m) (hchild : childCost ≤ envelope d r)
    (hlocal : localCost ≤ tollCoefficient d * n + 7)
    (htotal : total ≤ pivotCost + childCost + localCost) : total ≤ envelope d n := by
  cases n with
  | zero => omega
  | succ n =>
      have hp := envelope_mono d (by omega : m ≤ n)
      have hc := envelope_mono d (by omega : r ≤ n)
      have bound := recursive_budget_le d n
      omega

/-- The base is fixed by the two cutoffs before the varying size is supplied. -/
theorem prefix_max_bound (d actualCutoff scalarCutoff n : Nat)
    (hn : n ≤ actualCutoff ∨ n ≤ scalarCutoff) :
    envelope d n ≤ envelope d (max actualCutoff scalarCutoff) := by
  apply envelope_mono d
  rcases hn with hactual | hscalar
  · exact hactual.trans (le_max_left _ _)
  · exact hscalar.trans (le_max_right _ _)

end Resources.SelectionEnvelope

import Applications.Resources.SignedPotential
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Signed charges on the actual resource trajectory

Savings may fall enough to make one amortized charge negative. The run still
has its independently specified nonnegative modeled costs. Real fractions use
the same group theorem. Debt has the opposite sign and its exact identity does
not turn complete work into already realized work.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SignedPotential
open Resources

namespace IntSavings

/-- Save three potential units or release them; each modeled step costs one. -/
def step (save : Bool) (_ : Int) : Measured Int Int :=
  (if save then 3 else 0, 1)

theorem charges :
    potentialCharge step id true 0 = 4 ∧
      potentialCharge step id false 3 = -2 := by
  norm_num [potentialCharge, step]

theorem result : run step [true, false] 0 = (0, 2) := by
  norm_num [run, Resources.bind, Resources.pure, step]

/-- The total charge is obtained through the public exact telescope. -/
theorem total_charge : budget step (potentialCharge step id) [true, false] 0 = 2 := by
  have balance := run_potentialCharge_exact step id [true, false] 0
  change (2 : Int) + 0 = 0 + budget step (potentialCharge step id) [true, false] 0
    at balance
  simpa only [add_zero, zero_add] using balance.symm

/-- A prefix retains its positive final potential in the same identity. -/
theorem saved_prefix :
    (run step [true] 0).2 + (run step [true] 0).1 =
      budget step (potentialCharge step id) [true] 0 := by
  simpa only [id_eq, zero_add] using run_potentialCharge_exact step id [true] 0

theorem saved_prefix_numbers :
    run step [true] 0 = (3, 1) ∧ budget step (potentialCharge step id) [true] 0 = 4 := by
  constructor
  · norm_num [run, Resources.bind, Resources.pure, step]
  · have balance := saved_prefix
    change (1 : Int) + 3 = budget step (potentialCharge step id) [true] 0 at balance
    exact balance.symm

/-- Releasing saved potential may cost more than its negative new charge. -/
theorem release_boundary :
    (run step [false] 3).2 = 1 ∧
      budget step (potentialCharge step id) [false] 3 = -2 ∧
        (run step [false] 3).2 > budget step (potentialCharge step id) [false] 3 := by
  have balance := run_potentialCharge_exact step id [false] 3
  change (1 : Int) + 0 = 3 + budget step (potentialCharge step id) [false] 3 at balance
  have charged : budget step (potentialCharge step id) [false] 3 = -2 := by
    linarith [balance]
  constructor
  · norm_num [run, Resources.bind, Resources.pure, step]
  · refine ⟨charged, ?_⟩
    rw [charged]
    norm_num [run, Resources.bind, Resources.pure, step]

/-- Negative intermediate charges do not obstruct a valid final-potential bound. -/
theorem cost_bound :
    (run step [true, false] 0).2 ≤ budget step (potentialCharge step id) [true, false] 0 := by
  have bound := run_cost_le_of_nonneg_final step (potentialCharge step id) id
    (fun i s => le_of_eq (potentialCharge_balance step id i s)) [true, false] 0
    (by norm_num [run, Resources.bind, Resources.pure, step])
  simpa only [id_eq, zero_add] using bound

end IntSavings

namespace NegativeFinal

/-- This step has positive work but leaves a negative potential. -/
def step (_ : Unit) (_ : Int) : Measured Int Int := (-1, 1)

theorem charge_zero : potentialCharge step id () 0 = 0 := by
  norm_num [potentialCharge, step]

/-- The exact law still holds; it does not permit discarding a negative end. -/
theorem exact_balance :
    (run step [()] 0).2 + (run step [()] 0).1 =
      budget step (potentialCharge step id) [()] 0 := by
  simpa only [id_eq, zero_add] using run_potentialCharge_exact step id [()] 0

theorem final_potential_negative : ¬ 0 ≤ (run step [()] 0).1 := by
  norm_num [run, Resources.bind, Resources.pure, step]

theorem cost_not_bounded_by_charge :
    ¬ (run step [()] 0).2 ≤ budget step (potentialCharge step id) [()] 0 := by
  have balance := exact_balance
  change (1 : Int) + -1 = budget step (potentialCharge step id) [()] 0 at balance
  change ¬ (1 : Int) ≤ budget step (potentialCharge step id) [()] 0
  linarith [balance]

end NegativeFinal

namespace FractionalSavings

/-- Half a unit of modeled work, with three-halves saved or released. -/
noncomputable def step (save : Bool) (_ : ℝ) : Measured ℝ ℝ :=
  (if save then 3 / 2 else 0, 1 / 2)

theorem charges :
    potentialCharge step id true 0 = 2 ∧
      potentialCharge step id false (3 / 2) = -1 := by
  norm_num [potentialCharge, step]

theorem result : run step [true, false] 0 = (0, 1) := by
  norm_num [run, Resources.bind, Resources.pure, step]

theorem total_charge : budget step (potentialCharge step id) [true, false] 0 = 1 := by
  have balance := run_potentialCharge_exact step id [true, false] 0
  change ((1 / 2 : ℝ) + (1 / 2 + 0)) + 0 =
    0 + budget step (potentialCharge step id) [true, false] 0 at balance
  linarith [balance]

theorem cost_bound :
    (run step [true, false] 0).2 ≤ budget step (potentialCharge step id) [true, false] 0 := by
  have bound := run_cost_le_of_nonneg_final step (potentialCharge step id) id
    (fun i s => le_of_eq (potentialCharge_balance step id i s)) [true, false] 0
    (by norm_num [run, Resources.bind, Resources.pure, step])
  simpa only [id_eq, zero_add] using bound

end FractionalSavings

namespace DebtSign

/-- The second field models complete work, including work possibly deferred.
No forcing or persistent-payment law is asserted by this small algebra case. -/
noncomputable def step (grow : Bool) (_ : ℝ) : Measured ℝ ℝ :=
  (if grow then 1 / 4 else 0, 1 / 2)

theorem opposite_charges :
    potentialCharge step id true 0 = 3 / 4 ∧
      debtCharge step id true 0 = 1 / 4 ∧
        debtCharge step id false (1 / 4) = 3 / 4 := by
  norm_num [potentialCharge, debtCharge, step]

/-- The public debt law retains the positive outstanding final debt. -/
theorem growing_debt_balance :
    (run step [true] 0).2 =
      (run step [true] 0).1 + budget step (debtCharge step id) [true] 0 := by
  simpa only [id_eq, add_zero] using run_debtCharge_exact step id [true] 0

theorem growing_debt_charge : budget step (debtCharge step id) [true] 0 = 1 / 4 := by
  have balance := growing_debt_balance
  change (1 / 2 : ℝ) + 0 = 1 / 4 + budget step (debtCharge step id) [true] 0
    at balance
  linarith [balance]

/-- Complete work need not be bounded by this charge while debt remains. -/
theorem complete_work_exceeds_new_charge :
    (run step [true] 0).2 > budget step (debtCharge step id) [true] 0 := by
  rw [growing_debt_charge]
  norm_num [run, Resources.bind, Resources.pure, step]

theorem paid_pair_charge : budget step (debtCharge step id) [true, false] 0 = 1 := by
  have balance := run_debtCharge_exact step id [true, false] 0
  change ((1 / 2 : ℝ) + (1 / 2 + 0)) + 0 =
    0 + budget step (debtCharge step id) [true, false] 0 at balance
  linarith [balance]

end DebtSign
end Examples.SignedPotential

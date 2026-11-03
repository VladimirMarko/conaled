import Applications.Resources.Potential
import Mathlib.Algebra.Group.Basic

/-! Signed savings and debt charges on the existing measured state trajectory.

The savings charge is actual cost plus the change in potential. The debt charge
uses the opposite sign. Their exact identities are algebraic facts about the
given observations and states. A debt identity does not establish shared
consumable credit across persistent aliases, identify complete cost with actual
runtime, or prove that debt is paid before a suspension is forced. Those claims
require a separate work-allocation and forcing correspondence. -/
namespace Resources
universe u v w
variable {ι : Type u} {σ : Type v} {C : Type w}

/-- Signed savings charge: cost plus final potential minus initial potential. -/
def potentialCharge [Add C] [Sub C]
    (step : ι → σ → σ × C) (potential : σ → C) (i : ι) (s : σ) : C :=
  (step i s).2 + potential (step i s).1 - potential s

/-- The conventional signed charge satisfies the local exact balance. -/
theorem potentialCharge_balance [AddCommGroup C]
    (step : ι → σ → σ × C) (potential : σ → C) (i : ι) (s : σ) :
    (step i s).2 + potential (step i s).1 =
      potential s + potentialCharge step potential i s := by
  unfold potentialCharge
  rw [add_comm (potential s), sub_add_cancel]

/-- Savings charges telescope with both boundary potentials retained. No sign
condition is imposed on an individual charge or on either boundary potential. -/
theorem run_potentialCharge_exact [AddCommGroup C]
    (step : ι → σ → σ × C) (potential : σ → C) (is : List ι) (s : σ) :
    (run step is s).2 + potential (run step is s).1 =
      potential s + budget step (potentialCharge step potential) is s := by
  exact run_potential_exact step (potentialCharge step potential) potential
    (potentialCharge_balance step potential) is s

/-- Opposite-sign debt charge: complete cost plus initial debt minus final debt.
The caller supplies the observation called complete cost; this formula alone
does not identify that observation with actual work. -/
def debtCharge [Add C] [Sub C]
    (step : ι → σ → σ × C) (debt : σ → C) (i : ι) (s : σ) : C :=
  (step i s).2 + debt s - debt (step i s).1

/-- Debt accounting is savings accounting at the negative potential. -/
theorem debtCharge_eq_potentialCharge_neg [AddCommGroup C]
    (step : ι → σ → σ × C) (debt : σ → C) (i : ι) (s : σ) :
    debtCharge step debt i s = potentialCharge step (fun t => -debt t) i s := by
  simp only [debtCharge, potentialCharge, sub_eq_add_neg, neg_neg]
  exact add_right_comm _ _ _

/-- Exact debt identity on the supplied state trajectory. Its terminal debt
term is retained; it supplies no persistent actual-work bound by itself. -/
theorem run_debtCharge_exact [AddCommGroup C]
    (step : ι → σ → σ × C) (debt : σ → C) (is : List ι) (s : σ) :
    (run step is s).2 + debt s =
      debt (run step is s).1 + budget step (debtCharge step debt) is s := by
  have charge_eq : potentialCharge step (fun t => -debt t) = debtCharge step debt := by
    funext i t
    exact (debtCharge_eq_potentialCharge_neg step debt i t).symm
  have h := run_potentialCharge_exact step (fun t => -debt t) is s
  rw [charge_eq] at h
  have moved := congrArg (fun x : C => debt s + x + debt (run step is s).1) h
  simpa [add_assoc, add_left_comm, add_comm] using moved

end Resources

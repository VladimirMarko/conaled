import Applications.Resources.Workload
import Mathlib.Tactic

/-! Attempt and branch observations shared by two finite execution adapters.
These tariffs are logical prices, not physical running-time measurements. -/
namespace Resources

/-- Attempted transitions, accepted transitions, and rejected transitions. -/
abbrev AttemptCounts := Nat × (Nat × Nat)

def acceptedAttempt : AttemptCounts := (1,(1,0))
def rejectedAttempt : AttemptCounts := (1,(0,1))

def attemptTariff : AttemptCounts →+ Nat where
  toFun := Prod.fst
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Illustrative additive price: two per attempt, one per acceptance, three per rejection. -/
def branchTariff : AttemptCounts →+ Nat where
  toFun c := 2*c.1+c.2.1+3*c.2.2
  map_zero' := rfl
  map_add' a b := by simp only [Prod.fst_add, Prod.snd_add]; omega

theorem attemptTariff_mono : Monotone attemptTariff := fun _ _ h => h.1

theorem branchTariff_mono : Monotone branchTariff := by
  intro a b h
  have h₁ := h.1
  have h₂ := h.2.1
  have h₃ := h.2.2
  change 2*a.1+a.2.1+3*a.2.2 ≤ 2*b.1+b.2.1+3*b.2.2
  omega

end Resources

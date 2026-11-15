import SquareKit.Internal.DependentJudgments.TelescopeAuthoring

/-! Recover the selected interpreted value from an admitted source judgment. -/
noncomputable section
namespace SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
open GuardedTheory PathTransport.Typed
set_option backward.isDefEq.respectTransparency false
universe u
variable {V : Type} {Ω : List (Judgment V)} {Γ A t : Expression V}
namespace Tm
/-- Soundness returns the value of the actual source term at its identified
semantic type. No alternative target proof is substituted for that value. -/
theorem evaluates (ht : Tm (Ω := Ω) Γ A t) (M : PathTransport.Typed.Model.{u})
    (ρ : V → Value M.toStructuralModel)
    (hρ : ∀ a ∈ Ω, a.eval (model M).toAlgebra ρ)
    (G : M.Context) (B : M.Family G)
    (hg : Γ.eval (algebra M) ρ = .context G) (ha : A.eval (algebra M) ρ = .family G B) :
    ∃ selected : M.Section G B, t.eval (algebra M) ρ = .term G B selected := by
  have h := Derivation.sound (model M) ht ρ hρ
  change ∃ G B selected, Γ.eval (algebra M) ρ = Value.context G ∧
    A.eval (algebra M) ρ = Value.family G B ∧ t.eval (algebra M) ρ = Value.term G B selected at h
  obtain ⟨G', B', selected, hg', ha', ht'⟩ := h
  rw [hg] at hg'
  cases Value.context.inj hg'
  rw [ha] at ha'
  have e : B = B' := by cases ha'; rfl
  subst B'
  exact ⟨selected, ht'⟩
end Tm
end SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation

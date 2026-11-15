import SquareKit.Internal.PathTransport.ComparisonCompositionBinders

/-! Horizontal composition through finite dependent telescopes of the existing
comparison models. Each binder retains its full family comparison. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory Typed.StructuralModel
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

inductive TelescopeComposes (S T U : Signature.{u}) :
    {Γ Δ Θ : Context.{u}} → {n : Nat} → Telescope (structuralModel S) Γ n →
      Telescope (structuralModel T) Δ n → Telescope (structuralModel U) Θ n → Prop
  | nil {Γ Δ Θ} (h : Γ.Composes Δ Θ) : TelescopeComposes S T U
      (Telescope.nil : Telescope (structuralModel S) Γ 0)
      (Telescope.nil : Telescope (structuralModel T) Δ 0)
      (Telescope.nil : Telescope (structuralModel U) Θ 0)
  | cons {Γ Δ Θ n} {A : Family Γ} {B : Family Δ} {C : Family Θ}
      {Ts : Telescope (structuralModel S) A.extend n}
      {Tt : Telescope (structuralModel T) B.extend n}
      {Tu : Telescope (structuralModel U) C.extend n}
      (hA : A.Composes B C) (hT : TelescopeComposes S T U Ts Tt Tu) :
      TelescopeComposes S T U (Telescope.cons A Ts) (Telescope.cons B Tt) (Telescope.cons C Tu)

namespace TelescopeComposes
variable {S T U : Signature.{u}} {Γ Δ Θ : Context.{u}} {n : Nat}
variable {Ts : Telescope (structuralModel S) Γ n} {Tt : Telescope (structuralModel T) Δ n}
variable {Tu : Telescope (structuralModel U) Θ n}

theorem context (h : TelescopeComposes S T U Ts Tt Tu) : Γ.Composes Δ Θ := by
  cases h with
  | nil h => exact h
  | cons hA _ => exact hA.context

theorem total (h : TelescopeComposes S T U Ts Tt Tu) :
    Ts.total.Composes Tt.total Tu.total := by
  induction h with
  | nil h => exact h
  | cons _ _ ih => exact ih

theorem pullback (h : TelescopeComposes S T U Ts Tt Tu)
    {Γ' Δ' Θ' : Context.{u}} {σ : Substitution Γ' Γ} {τ : Substitution Δ' Δ}
    {ρ : Substitution Θ' Θ} (hσ : σ.Composes τ ρ) :
    TelescopeComposes S T U (Telescope.pullback (structuralModel S) Ts σ)
      (Telescope.pullback (structuralModel T) Tt τ) (Telescope.pullback (structuralModel U) Tu ρ) := by
  induction h generalizing Γ' Δ' Θ' with
  | nil _ => exact .nil hσ.source
  | cons hA hT ih =>
    apply TelescopeComposes.cons (hA.reindex hσ)
    apply ih
    simpa only [model_lift] using hA.lift hσ

theorem liftSub (h : TelescopeComposes S T U Ts Tt Tu)
    {Γ' Δ' Θ' : Context.{u}} {σ : Substitution Γ' Γ} {τ : Substitution Δ' Δ}
    {ρ : Substitution Θ' Θ} (hσ : σ.Composes τ ρ) :
    (Telescope.liftSub (structuralModel S) Ts σ).Composes
      (Telescope.liftSub (structuralModel T) Tt τ) (Telescope.liftSub (structuralModel U) Tu ρ) := by
  induction h generalizing Γ' Δ' Θ' with
  | nil _ => exact hσ
  | cons hA hT ih =>
    apply ih
    simpa only [model_lift] using hA.lift hσ

end TelescopeComposes
end SquareKit.Internal.PathTransport.GroupoidModel.Comparison

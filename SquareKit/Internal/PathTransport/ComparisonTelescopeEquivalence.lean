import SquareKit.Internal.PathTransport.ComparisonEquivalence

/-! Equivalence of arbitrary finite dependent comparison telescopes. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory Typed.StructuralModel
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

inductive TelescopeEquivalences (S : Signature.{u}) :
    {Γ : Context.{u}} → {n : Nat} → Telescope (structuralModel S) Γ n → Prop
  | nil {Γ} : TelescopeEquivalences S (Telescope.nil : Telescope (structuralModel S) Γ 0)
  | cons {Γ n} {A : Family Γ} {Ts : Telescope (structuralModel S) A.extend n}
      (hA : A.FiberEquivalences) (hT : TelescopeEquivalences S Ts) :
      TelescopeEquivalences S (Telescope.cons A Ts)

namespace TelescopeEquivalences
variable {S : Signature.{u}} {Γ : Context.{u}} {n : Nat}
variable {Ts : Telescope (structuralModel S) Γ n}

theorem total (h : TelescopeEquivalences S Ts) (hg : Γ.map.IsEquivalence) :
    Ts.total.map.IsEquivalence := by
  revert hg
  induction h with
  | nil => exact fun h => h
  | cons hA _ ih =>
    intro hg
    let := hg
    exact ih (Family.extend_equivalence _ hA)

theorem pullback (h : TelescopeEquivalences S Ts)
    {Δ : Context.{u}} (σ : Substitution Δ Γ) :
    TelescopeEquivalences S (Telescope.pullback (structuralModel S) Ts σ) := by
  induction h generalizing Δ with
  | nil => exact .nil
  | cons hA _ ih => exact .cons (Family.reindex_equivalences _ hA σ) (ih _)

end TelescopeEquivalences
end SquareKit.Internal.PathTransport.GroupoidModel.Comparison

import SquareKit.Internal.Cubical.IdentityComposition
import SquareKit.Internal.Cubical.PathFillingSubstitution

namespace SquareKit.Cubical.Presheaf
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
universe u
namespace IdentityComposition

theorem comp_reindex {Γ Δ E : Context.{u}} {A : Family Γ} {a₀ a₁ : Term A}
    (G : Composition (paths (A := A) (a₀ := a₀) (a₁ := a₁))) (hG : G.Lawful)
    (σ : E ⟶ Γ)
    (G' : Composition (paths (A := reindex A σ) (a₀ := a₀.reindex σ) (a₁ := a₁.reindex σ))) (hG' : G'.Lawful)
    (hmap : ∀ (p : total (interval Δ) ⟶ E) (φ : Cofibration Δ)
      (b : OpenBox (reindex (paths (A := A) (a₀ := a₀) (a₁ := a₁)) (p ≫ σ)) φ),
      G'.comp p φ (b.map (Functor.whiskerLeft p.mapElements
        (pathReindex (reindex A (projection (interval Γ))) a₀ a₁ σ))) =
        Term.map (Functor.whiskerLeft (endpointSub Δ true ≫ p).mapElements
          (pathReindex (reindex A (projection (interval Γ))) a₀ a₁ σ))
          (G.comp (p ≫ σ) φ b))
    (p : total (interval Δ) ⟶ E) (φ : Cofibration Δ)
    (b : OpenBox (reindex (identity A a₀ a₁) (p ≫ σ)) φ) :
    (composition G' hG').comp p φ
      (b.map (Functor.whiskerLeft p.mapElements (identityReindex A a₀ a₁ σ))) =
      Term.map (Functor.whiskerLeft (endpointSub Δ true ≫ p).mapElements (identityReindex A a₀ a₁ σ))
        ((composition G hG).comp (p ≫ σ) φ b) := by
  let b' := b.map (Functor.whiskerLeft p.mapElements (identityReindex A a₀ a₁ σ))
  apply Term.ext
  intro x
  apply IdentityElement.ext
  · have hl := congrArg (fun t => t.val x)
      (result_path p φ b' (G'.comp p φ (pathBox p φ b')) (hG'.boundary p φ (pathBox p φ b')))
    have hr := congrArg (fun t => t.val x)
      (result_path (p ≫ σ) φ b (G.comp (p ≫ σ) φ (pathBox (p ≫ σ) φ b))
        (hG.boundary (p ≫ σ) φ (pathBox (p ≫ σ) φ b)))
    exact hl.trans ((congrArg (fun t => t.val x) (hmap p φ (pathBox (p ≫ σ) φ b))).trans
      (congrArg ((pathReindex (reindex A (projection (interval Γ))) a₀ a₁ σ).app
        ((endpointSub Δ true ≫ p).mapElements.obj x)) hr).symm)
  · rfl

end IdentityComposition
end SquareKit.Cubical.Presheaf

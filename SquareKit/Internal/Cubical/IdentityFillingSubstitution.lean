import SquareKit.Internal.Cubical.IdentityFilling
import SquareKit.Internal.Cubical.IdentityCompositionSubstitution
import SquareKit.Internal.Cubical.CompositionMap

namespace SquareKit.Cubical.Presheaf
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
universe u

theorem identityComposition_reindex_family {Γ Δ E : Context.{u}} {A : Family Γ}
    (F : Filling A) (hF : F.Lawful) (a₀ a₁ : Term A) (σ : E ⟶ Γ)
    (p : total (interval Δ) ⟶ E) (φ : Cofibration Δ)
    (b : OpenBox (reindex (identity A a₀ a₁) (p ≫ σ)) φ) :
    (identityComposition (F.reindex σ) (hF.reindex σ) (a₀.reindex σ) (a₁.reindex σ)).comp p φ
      (b.map (Functor.whiskerLeft p.mapElements (identityReindex A a₀ a₁ σ))) =
      Term.map (Functor.whiskerLeft (endpointSub Δ true ≫ p).mapElements (identityReindex A a₀ a₁ σ))
        ((identityComposition F hF a₀ a₁).comp (p ≫ σ) φ b) := by
  apply IdentityComposition.comp_reindex
  intro q ψ c
  exact congrArg (fun t => t.reindex (endpointSub Δ true))
    (pathFilling_reindex_family (F.reindex (projection (interval Γ)))
      (hF.reindex (projection (interval Γ))) a₀ a₁ σ q ψ c)

theorem identityFilling_reindex_family {Γ Δ E : Context.{u}} {A : Family Γ}
    (F : Filling A) (hF : F.Lawful) (a₀ a₁ : Term A) (σ : E ⟶ Γ)
    (p : total (interval Δ) ⟶ E) (φ : Cofibration Δ)
    (b : OpenBox (reindex (identity A a₀ a₁) (p ≫ σ)) φ) :
    (identityFilling (F.reindex σ) (hF.reindex σ) (a₀.reindex σ) (a₁.reindex σ)).fill p φ
      (b.map (Functor.whiskerLeft p.mapElements (identityReindex A a₀ a₁ σ))) =
      Term.map (Functor.whiskerLeft p.mapElements (identityReindex A a₀ a₁ σ))
        ((identityFilling F hF a₀ a₁).fill (p ≫ σ) φ b) := by
  exact Composition.fill_map ((identityComposition F hF a₀ a₁).reindex σ)
    (identityComposition (F.reindex σ) (hF.reindex σ) (a₀.reindex σ) (a₁.reindex σ))
    (identityReindex A a₀ a₁ σ)
    (identityComposition_reindex_family F hF a₀ a₁ σ) p φ b

theorem identityFilling_reindex_iso {Γ Δ : Context.{u}} {A : Family Γ}
    (F : Filling A) (hF : F.Lawful) (a₀ a₁ : Term A) (σ : Δ ⟶ Γ) :
    ((identityFilling F hF a₀ a₁).reindex σ).transport (identityReindexIso A a₀ a₁ σ) =
      identityFilling (F.reindex σ) (hF.reindex σ) (a₀.reindex σ) (a₁.reindex σ) :=
  Filling.transport_eq _ _ _ (identityFilling_reindex_family F hF a₀ a₁ σ)

end SquareKit.Cubical.Presheaf

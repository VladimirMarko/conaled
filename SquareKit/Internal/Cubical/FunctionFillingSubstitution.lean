import SquareKit.Internal.Cubical.FunctionCompositionSubstitution
import SquareKit.Internal.Cubical.CompositionMap

/-! Substitution preserves the selected dependent function filler. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

theorem piFilling_reindex {Γ Δ E : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (F : Filling A) (hF : F.Lawful) (G : Filling B)
    (σ : E ⟶ Γ) (p : total (interval Δ) ⟶ E) (φ : Cofibration Δ)
    (b : OpenBox (reindex (pi A B) (p ≫ σ)) φ) :
    (piFilling (F.reindex σ) (hF.reindex σ) (G.reindex (liftSub A σ))).fill p φ
      (b.map (Functor.whiskerLeft p.mapElements (piReindex A B σ))) =
      Term.map (Functor.whiskerLeft p.mapElements (piReindex A B σ))
        ((piFilling F hF G).fill (p ≫ σ) φ b) :=
  Composition.fill_map ((piComposition F hF G.toComposition).reindex σ)
    (piComposition (F.reindex σ) (hF.reindex σ) (G.reindex (liftSub A σ)).toComposition)
    (piReindex A B σ) (FunctionComposition.comp_reindex F hF G.toComposition σ) p φ b

end SquareKit.Cubical.Presheaf

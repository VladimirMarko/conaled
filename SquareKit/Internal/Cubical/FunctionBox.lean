import SquareKit.Internal.Cubical.BackwardFilling
import SquareKit.Internal.Cubical.PartialFunctions

/-! Evaluate a function box along an actual moving argument. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

namespace OpenBox
variable {Γ Δ E : Context.{u}} {A : Family Γ} {B : Family (total A)}

def applyAlong (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (b : OpenBox (Presheaf.reindex (pi A B) p) φ) (σ : E ⟶ Δ)
    (v : Term (Presheaf.reindex A (liftSub (interval Δ) σ ≫ p))) :
    OpenBox (Presheaf.reindex B (pair (liftSub (interval Δ) σ ≫ p) v)) (φ.reindex σ) where
  tube :=
    (((b.tube.reindex (liftSub (interval Δ) σ)).map
      (piReindex A B (liftSub (interval Δ) σ ≫ p))).app).reindex (pair (𝟙 _) v)
  base :=
    (Presheaf.app (Term.map (piReindex A B (σ ≫ endpointSub Δ false ≫ p))
      (b.base.reindex σ))).reindex (pair (𝟙 _) (v.reindex (endpointSub E false)))
  boundary x h := by
    change ((b.tube.val ((endpointSub Δ false).mapElements.obj (σ.mapElements.obj x)) h).val
      (𝟙 _) (v.val ((endpointSub E false).mapElements.obj x))) =
      ((b.base.val (σ.mapElements.obj x)).val (𝟙 _) _)
    exact congrArg (fun f => f.val (𝟙 _) (v.val ((endpointSub E false).mapElements.obj x))) (b.boundary (σ.mapElements.obj x) h)

theorem applyAlong_reindex (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (b : OpenBox (Presheaf.reindex (pi A B) p) φ) (σ : E ⟶ Δ)
    (v : Term (Presheaf.reindex A (liftSub (interval Δ) σ ≫ p)))
    {K : Context.{u}} (τ : K ⟶ E) :
    (applyAlong p φ b σ v).reindex τ =
      applyAlong p φ b (τ ≫ σ) (v.reindex (liftSub (interval E) τ)) := rfl

end OpenBox
end SquareKit.Cubical.Presheaf

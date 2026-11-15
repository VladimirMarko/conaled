import SquareKit.Internal.Cubical.IntervalSquare

/-! The connection contracts the inner interval towards zero while retaining
its outer parameter. -/
namespace SquareKit.Cubical
open CategoryTheory
universe u

theorem Cube.zero_meet {I : Cube} (r : Hom I ⟨1⟩) :
    meet (endpoint I false) r = endpoint I false := by
  refine Quotient.inductionOn r ?_
  intro r
  exact Quotient.sound (fun i => (Expr.Conv.meet_comm _ _).trans (.meet_zero (r i)))

namespace Presheaf

def scaleInterval (Γ : Context.{u}) :
    total (interval (total (interval Γ))) ⟶ total (interval Γ) :=
  pair (projection (interval (total (interval Γ))) ≫ projection (interval Γ))
    (intervalMeet ((generic (interval Γ)).reindex (projection (interval (total (interval Γ)))))
      (generic (interval (total (interval Γ)))))

theorem scaleInterval_zero (Γ : Context.{u}) :
    endpointSub (total (interval Γ)) false ≫ scaleInterval Γ =
      projection (interval Γ) ≫ endpointSub Γ false := by
  ext I z
  exact congrArg (fun r => (⟨z.1,ULift.up r⟩ : (total (interval Γ)).obj I)) (Cube.meet_zero _)

theorem scaleInterval_one (Γ : Context.{u}) :
    endpointSub (total (interval Γ)) true ≫ scaleInterval Γ = 𝟙 _ := by
  ext I z
  exact congrArg (fun r => (⟨z.1,ULift.up r⟩ : (total (interval Γ)).obj I)) (Cube.meet_one _)

theorem scaleInterval_natural {Γ Δ : Context.{u}} (σ : Δ ⟶ Γ) :
    scaleInterval Δ ≫ liftSub (interval Γ) σ =
      liftSub (interval (total (interval Γ))) (liftSub (interval Γ) σ) ≫ scaleInterval Γ := rfl

end Presheaf
end SquareKit.Cubical

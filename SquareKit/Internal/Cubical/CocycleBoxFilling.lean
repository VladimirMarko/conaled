import SquareKit.Internal.Cubical.CocycleBoxPrimitive
import SquareKit.Internal.Cubical.CocycleSectionSubstitution
import SquareKit.Internal.Cubical.CocycleSectionBoundary

/-! A selected relative cocycle filler with its exact cap and tube boundaries. -/
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory Presheaf

variable {Γ : Context.{0}} {φ : Cofibration Γ}
variable (b : OpenBox (cocycleFamily (total (interval Γ))) φ)

theorem boxPrimitive_zeroCap {X Y : (total (interval Γ)).Elementsᵒᵖ} (f : X ⟶ Y) :
    extendZero (boxPrimitive b) ((intervalCap Γ false).mapElements.op.map f) = 0 := by
  classical
  unfold extendZero
  split
  · exact tubePrimitive_cap φ (boxDifference b) f _
  · rfl

theorem boxCocycle_cap :
    (boxCocycle b).pullback (intervalCap Γ false).mapElements.op =
      (boxBaseCocycle b).pullback (intervalCap Γ false).mapElements.op := by
  apply Cocycle2.ext
  funext X Y Z f g
  exact relativeExtension_zero _ _ _ _ (boxPrimitive_zeroCap b f)
    (boxPrimitive_zeroCap b g) (boxPrimitive_zeroCap b (f ≫ g))

noncomputable def boxFill : Term (cocycleFamily (total (interval Γ))) := cocycleSection (boxCocycle b)

private theorem cap_endpoint_pullback (z : Cocycle2 (total (interval Γ)).Elementsᵒᵖ) :
    (z.pullback (intervalCap Γ false).mapElements.op).pullback (endpointSub Γ false).mapElements.op =
      z.pullback (endpointSub Γ false).mapElements.op := by
  apply Cocycle2.ext
  rfl

private theorem base_endpoint_pullback (t : Term (cocycleFamily Γ)) :
    (termCocycle (t.reindex (projection (interval Γ)))).pullback (endpointSub Γ false).mapElements.op =
      termCocycle t := by
  apply Cocycle2.ext
  rfl

theorem boxFill_base : (boxFill b).reindex (endpointSub Γ false) = b.base := by
  have e := congrArg (fun z : Cocycle2 (total (interval Γ)).Elementsᵒᵖ =>
    z.pullback (endpointSub Γ false).mapElements.op) (boxCocycle_cap b)
  rw [cap_endpoint_pullback,cap_endpoint_pullback] at e
  have eb : (boxBaseCocycle b).pullback (endpointSub Γ false).mapElements.op = termCocycle b.base :=
    base_endpoint_pullback b.base
  have ee := e.trans eb
  exact (cocycleSection_reindex (boxCocycle b) (endpointSub Γ false)).trans
    ((congrArg (fun z : Cocycle2 Γ.Elementsᵒᵖ => cocycleSection z) ee).trans
      (cocycleSection_termCocycle b.base))

theorem boxFill_fills : b.Fills (boxFill b) := by
  constructor
  · exact boxFill_base b
  · exact cocycleSection_partial (boxCocycle b) b.tube (boxCocycle_tube b)

end SquareKit.Cubical.CategoryCocycles

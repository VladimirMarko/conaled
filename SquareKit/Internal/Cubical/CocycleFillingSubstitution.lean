import SquareKit.Internal.Cubical.CocycleBoxFilling
import SquareKit.Internal.Cubical.CocyclePrimitiveSubstitution

/-! The relative extension and its reconstructed filler are strictly uniform. -/
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory Presheaf

private theorem extendZero_congr {C : Type*} [Category C] {S : SieveObjects C}
    (b c : PartialCochain1 S) (h : ∀ {X Y : C} (f : X ⟶ Y) p, b f p = c f p)
    {X Y : C} (f : X ⟶ Y) : extendZero b f = extendZero c f := by
  classical
  unfold extendZero
  split
  · exact h f _
  · rfl

theorem boxPrimitive_extend_reindex {Γ Δ : Context.{0}} {φ : Cofibration Γ}
    (b : OpenBox (cocycleFamily (total (interval Γ))) φ) (σ : Δ ⟶ Γ)
    {X Y : (total (interval Δ)).Elementsᵒᵖ} (f : X ⟶ Y) :
    extendZero (boxPrimitive (b.reindex σ)) f =
      extendZero (boxPrimitive b) ((liftSub (interval Γ) σ).mapElements.op.map f) :=
  extendZero_congr _ (PartialCochain1.pullback (boxPrimitive b) (liftSub (interval Γ) σ).mapElements.op)
    (boxPrimitive_reindex b σ) f

theorem boxCocycle_reindex {Γ Δ : Context.{0}} {φ : Cofibration Γ}
    (b : OpenBox (cocycleFamily (total (interval Γ))) φ) (σ : Δ ⟶ Γ) :
    boxCocycle (b.reindex σ) = (boxCocycle b).pullback (liftSub (interval Γ) σ).mapElements.op := by
  apply Cocycle2.ext
  funext X Y Z f g
  let L := (liftSub (interval Γ) σ).mapElements.op
  have hf := boxPrimitive_extend_reindex b σ f
  have hg := boxPrimitive_extend_reindex b σ g
  have hfg := boxPrimitive_extend_reindex b σ (f ≫ g)
  have he : (boxBaseCocycle (b.reindex σ)).cochain f g = (boxBaseCocycle b).cochain (L.map f) (L.map g) := rfl
  change (boxBaseCocycle (b.reindex σ)).cochain f g +
    (extendZero (boxPrimitive (b.reindex σ)) g - extendZero (boxPrimitive (b.reindex σ)) (f ≫ g) +
      extendZero (boxPrimitive (b.reindex σ)) f) =
    (boxBaseCocycle b).cochain (L.map f) (L.map g) +
    (extendZero (boxPrimitive b) (L.map g) - extendZero (boxPrimitive b) (L.map (f ≫ g)) +
      extendZero (boxPrimitive b) (L.map f))
  exact congrArg₂ (fun a b : ℤ => a + b) he
    (congrArg₂ (fun a b : ℤ => a + b) (congrArg₂ (fun a b : ℤ => a - b) hg hfg) hf)

theorem boxFill_reindex {Γ Δ : Context.{0}} {φ : Cofibration Γ}
    (b : OpenBox (cocycleFamily (total (interval Γ))) φ) (σ : Δ ⟶ Γ) :
    boxFill (b.reindex σ) = (boxFill b).reindex (liftSub (interval Γ) σ) := by
  exact (congrArg (fun z : Cocycle2 (total (interval Δ)).Elementsᵒᵖ => cocycleSection z)
    (boxCocycle_reindex b σ)).trans
      (cocycleSection_reindex (boxCocycle b) (liftSub (interval Γ) σ)).symm

end SquareKit.Cubical.CategoryCocycles

import SquareKit.Internal.Cubical.CocyclePrimitiveValue
import SquareKit.Internal.Cubical.FreshExtensionSubstitution

/-! The selected relative primitive retains its exact value under parameter substitution. -/
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory Presheaf

theorem boxPrimitive_reindex {Γ Δ : Context.{0}} {φ : Cofibration Γ}
    (b : OpenBox (cocycleFamily (total (interval Γ))) φ) (σ : Δ ⟶ Γ)
    {X Y : (total (interval Δ)).Elementsᵒᵖ} (f : X ⟶ Y)
    (p : (tubeSieve (φ.reindex σ)).contains Y) :
    boxPrimitive (b.reindex σ) f p =
      boxPrimitive b ((liftSub (interval Γ) σ).mapElements.op.map f) p := by
  let L := liftSub (interval Γ) σ
  have e := freshExtension_substitution σ (intervalBaseElement Y.unop)
  have ht := b.tube.val_heq e (freshPreservesTube (φ.reindex σ) Y p)
    (freshPreservesTube φ (L.mapElements.op.obj Y) p)
  have hb := b.base.val_heq (congrArg (projection (interval Γ)).mapElements.obj e)
  have h₁ := boxPrimitive_value (b.reindex σ) f p
  have h₂ := boxPrimitive_value b (L.mapElements.op.map f) p
  apply h₁.trans
  apply Eq.trans _ h₂.symm
  exact congrArg₂ (fun q r =>
    primitiveValue f.unop.hom.unop X.unop.val.2.down Y.unop.val.2.down q -
      primitiveValue f.unop.hom.unop X.unop.val.2.down Y.unop.val.2.down r)
    (eq_of_heq ht) (eq_of_heq hb)

end SquareKit.Cubical.CategoryCocycles

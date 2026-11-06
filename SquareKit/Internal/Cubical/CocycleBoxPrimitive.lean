import SquareKit.Internal.Cubical.ElementPartialPrism
import SquareKit.Internal.Cubical.RelativeCocycleExtension
import SquareKit.Internal.Cubical.DependentFilling

/-! The compatible cap of an open box makes its relative tube cocycle vanish there. -/
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory Presheaf

variable {Γ : Context.{0}} {φ : Cofibration Γ}
variable (b : OpenBox (cocycleFamily (total (interval Γ))) φ)

def boxBaseCocycle : Cocycle2 (total (interval Γ)).Elementsᵒᵖ :=
  termCocycle (b.base.reindex (projection (interval Γ)))

def boxDifference : PartialCocycle2 (tubeSieve φ) :=
  partialDifference (partialSectionCocycle b.tube) (boxBaseCocycle b)

theorem boxDifference_cap {X Y Z : (total (interval Γ)).Elementsᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) (p : (tubeSieve φ).contains Z) :
    (boxDifference b).cochain ((intervalCap Γ false).mapElements.op.map f)
      ((intervalCap Γ false).mapElements.op.map g) p = 0 := by
  change CubeCocycle.eval (b.tube.val ((intervalCap Γ false).mapElements.obj Z.unop) p)
    f.unop.hom.unop g.unop.hom.unop (𝟙 _) -
    CubeCocycle.eval (b.base.val (intervalBaseElement Z.unop))
      f.unop.hom.unop g.unop.hom.unop (𝟙 _) = 0
  exact sub_eq_zero.mpr (congrArg (fun q => CubeCocycle.eval q
    f.unop.hom.unop g.unop.hom.unop (𝟙 Z.unop.obj.unop))
    (b.boundary (intervalBaseElement Z.unop) p))

def boxPrimitive : PartialCochain1 (tubeSieve φ) := tubePrimitive φ (boxDifference b)

theorem boxPrimitive_boundary {X Y Z : (total (interval Γ)).Elementsᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) (p : (tubeSieve φ).contains Z) :
    boxPrimitive b g p - boxPrimitive b (f ≫ g) p +
      boxPrimitive b f ((tubeSieve φ).downward g p) =
      (partialSectionCocycle b.tube).cochain f g p - (boxBaseCocycle b).cochain f g := by
  have e := tubePrimitive_boundary φ (boxDifference b) f g p
  have e' := congrArg (fun a : ℤ => (boxDifference b).cochain f g p - a) (boxDifference_cap b f g p)
  exact e.trans (e'.trans (sub_zero _))

noncomputable def boxCocycle : Cocycle2 (total (interval Γ)).Elementsᵒᵖ :=
  relativeExtension (boxBaseCocycle b) (boxPrimitive b)

theorem boxCocycle_tube {X Y Z : (total (interval Γ)).Elementsᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) (p : (tubeSieve φ).contains Z) :
    (boxCocycle b).cochain f g = (partialSectionCocycle b.tube).cochain f g p :=
  relativeExtension_inside _ _ _ (boxPrimitive_boundary b) f g p

end SquareKit.Cubical.CategoryCocycles

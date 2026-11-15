import SquareKit.Internal.Cubical.PartialCocycleSections
import SquareKit.Internal.Cubical.ElementPrism

/-! Relative prisms on a face pulled back from the parameter context. -/
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory Presheaf

abbrev tubeFace {Γ : Context.{0}} (φ : Cofibration Γ) := φ.reindex (projection (interval Γ))
abbrev tubeSieve {Γ : Context.{0}} (φ : Cofibration Γ) := faceSieve (tubeFace φ)

theorem freshPreservesTube {Γ : Context.{0}} (φ : Cofibration Γ)
    (X : (total (interval Γ)).Elementsᵒᵖ) (p : (tubeSieve φ).contains X) :
    (tubeSieve φ).contains ((freshenElements Γ).op.obj X) :=
  φ.full_natural (Functor.Elements.homMk (dropOpp X.unop.obj) rfl :
    intervalBaseElement X.unop ⟶ Γ.elementsMk _ (Γ.map (dropOpp X.unop.obj) X.unop.val.1)) p

def tubePrimitive {Γ : Context.{0}} (φ : Cofibration Γ) (z : PartialCocycle2 (tubeSieve φ)) :
    PartialCochain1 (tubeSieve φ) := fun f p =>
  partialPrism z (NatTrans.op (freshToCap Γ false)) (freshPreservesTube φ) f p -
    partialPrism z (NatTrans.op (freshToElement Γ)) (freshPreservesTube φ) f p

theorem tubePrimitive_boundary {Γ : Context.{0}} (φ : Cofibration Γ)
    (z : PartialCocycle2 (tubeSieve φ))
    {X Y Z : (total (interval Γ)).Elementsᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (p : (tubeSieve φ).contains Z) :
    tubePrimitive φ z g p - tubePrimitive φ z (f ≫ g) p +
      tubePrimitive φ z f ((tubeSieve φ).downward g p) =
      z.cochain f g p - z.cochain ((intervalCap Γ false).mapElements.op.map f)
        ((intervalCap Γ false).mapElements.op.map g) p := by
  have h₁ := partialPrism_boundary z (NatTrans.op (freshToCap Γ false)) (freshPreservesTube φ) f g p
  have h₂ := partialPrism_boundary z (NatTrans.op (freshToElement Γ)) (freshPreservesTube φ) f g p
  change _ = z.cochain ((freshenElements Γ).op.map f) ((freshenElements Γ).op.map g) _ -
    z.cochain f g p at h₂
  dsimp only [tubePrimitive]
  change _ = z.cochain f g p - _
  omega

/-- Both graph specializations coincide on the cap, including their selected cochain values. -/
theorem tubePrimitive_cap {Γ : Context.{0}} (φ : Cofibration Γ)
    (z : PartialCocycle2 (tubeSieve φ))
    {X Y : (total (interval Γ)).Elementsᵒᵖ} (f : X ⟶ Y) (p : (tubeSieve φ).contains Y) :
    tubePrimitive φ z ((intervalCap Γ false).mapElements.op.map f) p = 0 := by
  exact sub_self _

end SquareKit.Cubical.CategoryCocycles

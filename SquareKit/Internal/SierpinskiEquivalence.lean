import SquareKit.Internal.SierpinskiClassified
import SquareKit.Internal.ArrowTransformation

/-! The full relative Sierpiński classification equivalence for arbitrary
represented sheaf sources. Morphisms are unrestricted geometric transformations
and actual maps between subterminal carriers. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SquareKit.Internal.Sierpinski
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
universe v u vB uB
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {B : Type uB} [Category.{vB} B] [HasInitial B] [HasFiniteLimits B]
variable [HasStrictInitialObjects B]
variable (h : GeometricMorphism (Sheaf J (Type (max u v))) B)
variable (k : GeometricMorphism.Lift h (ArrowGeometry.projection B))

/-- Reconstruction respects the specified base comparison, not just the inverse image. -/
theorem reconstruction_over :
    whiskerLeft (ArrowGeometry.projection B).inverseImage
      (ArrowReconstruction.reconstruction k).hom ≫
        (classified J h ((liftInterpretation h).obj k)).comparison.hom = k.comparison.hom := by
  apply NatTrans.ext
  funext X
  have d : ArrowPresentation.domain ((ArrowGeometry.diagonal B).obj X) = 𝟙 _ := by
    apply Arrow.hom_ext <;> simp [ArrowPresentation.domain, ArrowGeometry.diagonal]
  have r := ArrowReconstruction.objectIso_domain k ((ArrowGeometry.diagonal B).obj X)
  rw [d, k.morphism.inverseImage.map_id, Category.id_comp] at r
  change (ArrowReconstruction.objectIso k ((ArrowGeometry.diagonal B).obj X)).hom ≫
    (classified J h ((liftInterpretation h).obj k)).comparison.hom.app X = _
  rw [r]
  dsimp [classified, ArrowGeometry.projection,
    ArrowSheaf.ofSubterminal, ArrowSheaf.geometric, GeometricMorphism.comp, ArrowTransport.geometric]
  simp only [Category.id_comp, Category.comp_id]
  simp [ArrowPushout.interpretation, ArrowTransport.diagonalIso,
    ArrowPushout.diagonalIso, ArrowPushout.diagonalObj, ArrowGeometry.diagonal,
    interpretation, interpret, liftInterpretation, GeometricMorphism.Lift.forget,
    Category.assoc]

/-- The reconstructed inverse image gives an isomorphism in the actual lift category. -/
def reconstructionIso : k ≅ (classify J h).obj ((liftInterpretation h).obj k) where
  hom := {
    transformation := (ArrowReconstruction.reconstruction k).hom
    over := reconstruction_over J h k }
  inv := {
    transformation := (ArrowReconstruction.reconstruction k).inv
    over := by
      rw [← reconstruction_over J h k]
      apply NatTrans.ext
      funext X
      change (ArrowReconstruction.reconstruction k).inv.app _ ≫
        ((ArrowReconstruction.reconstruction k).hom.app _ ≫ _) = _
      rw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
      rfl }
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

/-- Generic-model interpretation is an equivalence of full categories. -/
def classifier : GeometricMorphism.Lift h (ArrowGeometry.projection B) ≌
    MonoOver (⊤_ (Sheaf J (Type (max u v)))) where
  functor := liftInterpretation h
  inverse := classify J h
  unitIso := NatIso.ofComponents (reconstructionIso J h) (by intros; apply Subsingleton.elim)
  counitIso := classifyInterpretation J h
  functor_unitIso_comp _ := Subsingleton.elim _ _

end SquareKit.Internal.Sierpinski

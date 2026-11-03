import SquareKit.Internal.ArrowReconstruction

/-! A transformation over the base is determined by its generic-model component.
This is a consequence of the arrow presentation, not a restriction on geometric
transformations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SquareKit.Internal.Sierpinski
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
universe vF vB uF uB
variable {F : Type uF} {B : Type uB} [Category.{vF} F] [Category.{vB} B]
variable [HasInitial B] [HasFiniteLimits B] [HasStrictInitialObjects B]
variable {h : GeometricMorphism F B}
variable {k l : GeometricMorphism.Lift h (ArrowGeometry.projection B)}
variable (α β : k ⟶ l)

omit [HasInitial B] [HasFiniteLimits B] [HasStrictInitialObjects B] in
/-- The comparison over the base fixes the transformation on constant arrows. -/
theorem transformation_diagonal (X : B) :
    α.transformation.app ((ArrowGeometry.diagonal B).obj X) =
      β.transformation.app ((ArrowGeometry.diagonal B).obj X) := by
  apply (cancel_mono (l.comparison.hom.app X)).mp
  exact (congrArg (fun η => η.app X) α.over).trans
    (congrArg (fun η => η.app X) β.over).symm

/-- Agreement on the constant arrows and generic carrier determines a natural transformation. -/
theorem naturalTransformation_ext
    {h' : GeometricMorphism F B} {l' : GeometricMorphism.Lift h' (ArrowGeometry.projection B)}
    (α β : k.morphism.inverseImage ⟶ l'.morphism.inverseImage)
    (ed : ∀ X, α.app ((ArrowGeometry.diagonal B).obj X) =
      β.app ((ArrowGeometry.diagonal B).obj X))
    (e : α.app (generic B) = β.app (generic B)) : α = β := by
  have eb (X : B) : α.app ((ArrowGeometry.initialArrow B).obj X) =
      β.app ((ArrowGeometry.initialArrow B).obj X) := by
    apply (mapIsLimitOfPreservesOfIsLimit l'.morphism.inverseImage _ _
      (ArrowPresentation.boundaryIsProduct X)).hom_ext
    intro j
    rcases j with ⟨_ | _⟩
    · change _ ≫ l'.morphism.inverseImage.map (ArrowPresentation.toGeneric X) =
        _ ≫ l'.morphism.inverseImage.map (ArrowPresentation.toGeneric X)
      rw [← α.naturality, ← β.naturality, e]
    · change _ ≫ l'.morphism.inverseImage.map (ArrowPresentation.boundary X) =
        _ ≫ l'.morphism.inverseImage.map (ArrowPresentation.boundary X)
      rw [← α.naturality, ← β.naturality, ed X]
  apply NatTrans.ext
  funext a
  apply (ArrowReconstruction.presentationPushout k a).hom_ext
  · rw [α.naturality, β.naturality, ed a.left]
  · rw [α.naturality, β.naturality, eb a.right]

/-- Its component on the generic carrier determines the whole transformation over a fixed base. -/
theorem transformation_ext
    (e : α.transformation.app (generic B) = β.transformation.app (generic B)) : α = β :=
  GeometricMorphism.Lift.Hom.ext (naturalTransformation_ext α.transformation β.transformation
    (transformation_diagonal α β) e)

variable [HasFiniteLimits F]

/-- Actual generic-model evaluation is faithful on the full category of lifts. -/
instance : (liftInterpretation h).Faithful where
  map_injective eq := transformation_ext _ _ (congrArg (fun f => f.hom.left) eq)

/-- Thinness is derived for this theory alone, through its faithful interpretation. -/
instance : Quiver.IsThin (GeometricMorphism.Lift h (ArrowGeometry.projection B)) :=
  fun _ _ => ⟨fun _α _β => (liftInterpretation h).map_injective (Subsingleton.elim _ _)⟩

end SquareKit.Internal.Sierpinski

import SquareKit.Internal.SubterminalChange
import SquareKit.Internal.SliceSourceChange

/-! Generic-model evaluation commutes with source substitution on actual carriers. -/
noncomputable section
set_option autoImplicit false
namespace SquareKit.Internal.Sierpinski
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
universe vF vG vB uF uG uB
variable {F : Type uF} {G : Type uG} {B : Type uB}
variable [Category.{vF} F] [Category.{vG} G] [Category.{vB} B]
variable [HasFiniteLimits F] [HasFiniteLimits G]
variable [HasInitial B] [HasFiniteLimits B] [HasStrictInitialObjects B]
variable (h : GeometricMorphism F B) (f : GeometricMorphism G F)

/-- Both routes have carrier `f*(k*G)` and agree on all model maps. -/
def sourceComparison :
    GeometricMorphism.Lift.precompFunctor f ⋙ liftInterpretation (f.comp h) ≅
      liftInterpretation h ⋙ SubterminalChange.pull f :=
  NatIso.ofComponents (fun _ => MonoOver.isoMk (Iso.refl _) (terminal.hom_ext _ _))
    (by intros; apply Subsingleton.elim)

/-- The carrier map in the source comparison is the identity on the actual inverse image. -/
theorem sourceComparison_carrier (k : GeometricMorphism.Lift h (ArrowGeometry.projection B)) :
    ((sourceComparison h f).hom.app k).hom.left =
      𝟙 (f.inverseImage.obj (k.morphism.inverseImage.obj (generic B))) := rfl

/-- Source transformations retain their component at the actual generic carrier. -/
def sourceTransformation {f g : GeometricMorphism G F} (α : f ⟶ g) :
    liftInterpretation h ⋙ SubterminalChange.pull f ⟶
      liftInterpretation h ⋙ SubterminalChange.pull g :=
  whiskerLeft (liftInterpretation h) (SubterminalChange.transformation α)

/-- Evaluation of the source transformation has the expected direction and component. -/
theorem sourceTransformation_carrier {f g : GeometricMorphism G F} (α : f ⟶ g)
    (k : GeometricMorphism.Lift h (ArrowGeometry.projection B)) :
    ((sourceTransformation h α).app k).hom.left =
      α.app (k.morphism.inverseImage.obj (generic B)) := rfl

end SquareKit.Internal.Sierpinski

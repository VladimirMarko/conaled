import SquareKit.SierpinskiClassifier
import Examples.SheafBaseChange
import Mathlib.CategoryTheory.Sites.LeftExact

/-! Specialization to the existing finite diamond site. Its sheaf category
has genuine local gluing; the relative classifier applies without replacing
models or geometric transformations by their isomorphism classes. -/
noncomputable section
set_option autoImplicit false
namespace Examples.SierpinskiSheaf
open CategoryTheory CategoryTheory.Limits SquareKit.Internal
open Examples.SheafImage

abbrev S := Sheaf topology Type

def classification :
    GeometricMorphism.Lift (GeometricMorphism.identity S) (ArrowGeometry.projection S) ≌
      MonoOver (⊤_ S) :=
  Sierpinski.classifier topology (GeometricMorphism.identity S)

/-- Evaluation keeps the actual carrier of the generic model at the true point. -/
example : (classification.functor.obj (ArrowGeometry.trueLift S)).obj.left = ⊤_ S := rfl

/-- Every actual subterminal on the site is recovered by the explicit inverse. -/
def recover (P : MonoOver (⊤_ S)) :
    classification.functor.obj (classification.inverse.obj P) ≅ P :=
  classification.counitIso.app P

/-- The full cone equivalence specializes to this site, with varying geometric
base legs and their transformations. -/
def varyingBase : GeometricMorphism S (Arrow S) ≌
    GeometricMorphism.Cone (GeometricMorphism.postcompose (F := S) (GeometricMorphism.identity S))
      (ArrowGeometry.projection S) :=
  Sierpinski.pseudopullback topology (GeometricMorphism.identity S)

/-- The true point preserves both Boolean sections; no witness is collapsed. -/
example : (ArrowGeometry.truePoint S).inverseImage.obj
    (Arrow.mk (𝟙 Examples.SheafBaseChange.D)) = Examples.SheafBaseChange.D := rfl

end Examples.SierpinskiSheaf

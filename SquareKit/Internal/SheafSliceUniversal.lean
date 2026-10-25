import SquareKit.Internal.SliceUniversal
import SquareKit.SheafSliceFunction

/-! Arbitrary sheaf sources discharge the slice-closure requirement of the
geometric slice universal property. Site objects lie in `Type u`, arrows in
`Type v`, and section types in `Type (max u v)`. -/
noncomputable section
set_option autoImplicit false
namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe u v uB vB
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {B : Type uB} [Category.{vB} B] [CartesianMonoidalCategory B] [HasPullbacks B]
variable (h : GeometricMorphism (Sheaf J (Type (max u v))) B) (a : B) [Closed a]
local instance sheafSliceUniversalLocal1 : CartesianMonoidalCategory (Over (h.inverseImage.obj a)) :=
  Over.cartesianMonoidalCategory _
local instance sheafSliceUniversalLocal2 : MonoidalClosed (Over (h.inverseImage.obj a)) :=
  SquareKit.SheafSliceFunction.closed _

/-- No dependent-product or classifier conclusion is assumed of the source. -/
def sheafSectionEquivalence :
    Lift h (slice a) ≌ Discrete (⊤_ (Sheaf J (Type (max u v))) ⟶ h.inverseImage.obj a) :=
  sectionEquivalence h a
end SquareKit.Internal.GeometricMorphism

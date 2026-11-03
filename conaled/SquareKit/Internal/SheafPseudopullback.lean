import SquareKit.Internal.SlicePseudopullback
import SquareKit.SheafSliceFunction

/-! Arbitrary sheaf sources satisfy the structural closure used by the full
geometric pseudopullback theorem. -/
noncomputable section
set_option autoImplicit false
namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe u v uF vF uB vB
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {F : Type uF} [Category.{vF} F] [CartesianMonoidalCategory F] [HasPullbacks F]
variable {B : Type uB} [Category.{vB} B] [CartesianMonoidalCategory B] [HasPullbacks B]
variable (f : GeometricMorphism F B) (a : B) [Closed a] [Closed (f.inverseImage.obj a)]
local instance sheafPseudopullbackLocal1 : ∀ h : GeometricMorphism (Sheaf J (Type (max u v))) F,
    @MonoidalClosed (Over (h.inverseImage.obj (f.inverseImage.obj a))) inferInstance
      (Over.cartesianMonoidalCategory _).toMonoidalCategory :=
  fun h => SquareKit.SheafSliceFunction.closed _

/-- Full cone classification, including both noninvertible transformation legs. -/
def sheafPseudopullback : GeometricMorphism (Sheaf J (Type (max u v))) (Over (f.inverseImage.obj a)) ≌
    Cone (postcompose (F := Sheaf J (Type (max u v))) f) (slice a) :=
  slicePseudopullback f a
end SquareKit.Internal.GeometricMorphism

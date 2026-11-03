import SquareKit.Internal.FiniteClassifier
import SquareKit.SheafCartesianClosed

/-! The classifier equivalence for arbitrary sheaf sources. Local Cartesian
closedness is supplied by the sheaf constructions, rather than assumed of each lift. -/
noncomputable section
set_option autoImplicit false
namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe u v uB vB
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {B : Type uB} [Category.{vB} B] [CartesianMonoidalCategory B]
variable [HasPullbacks B] [HasBinaryCoproducts B]
variable (h : GeometricMorphism (Sheaf J (Type (max u v))) B)
variable {U : B} (u : U ⟶ ⊤_ B) [Mono u] [Closed (U ⨿ ⊤_ B)]
local instance sheafFiniteClassifierLocal1 : CartesianMonoidalCategory (Over (h.inverseImage.obj (U ⨿ ⊤_ B))) :=
  Over.cartesianMonoidalCategory _
local instance sheafFiniteClassifierLocal2 : MonoidalClosed (Over (h.inverseImage.obj (U ⨿ ⊤_ B))) :=
  SquareKit.SheafSliceFunction.closed _

/-- The full hom-category classifier for every geometric morphism from a sheaf topos. -/
def sheafFiniteClassifier : Lift h (slice (U ⨿ ⊤_ B)) ≌
    PartitionSection.Model (parameterPullback h u) := finiteClassifier h u
end SquareKit.Internal.GeometricMorphism

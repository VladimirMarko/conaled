import SquareKit.Internal.GeometricMorphism
import SquareKit.SliceDependentProduct
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import Mathlib.CategoryTheory.Adjunction.Limits

/-! Actual geometric morphisms for slicing and section pullback. Right adjoints
are constructed from internal sections using the repository's ordinary
pullback choices. These constructions are inputs to the slice universal
property; this module does not yet prove that universal property. -/
noncomputable section
set_option autoImplicit false
namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe v₁ v₂ u₁ u₂
variable {F : Type u₁} {B : Type u₂}
variable [Category.{v₁} F] [Category.{v₂} B]

/-- A finite-limit-preserving functor together with its actual adjunction. -/
def ofAdjunction {L : B ⥤ F} {R : F ⥤ B} (adj : L ⊣ R)
    [PreservesFiniteLimits L] : GeometricMorphism F B := ⟨L, R, adj, inferInstance⟩

/-- A geometric inverse image acts on slice categories, with explicit right adjoint. -/
def onSlices (h : GeometricMorphism F B) [HasPullbacks B] (a : B) :
    GeometricMorphism (Over (h.inverseImage.obj a)) (Over a) :=
  ofAdjunction (Over.postAdjunctionLeft h.adjunction)

section Slice
variable [CartesianMonoidalCategory B] [HasPullbacks B] (a : B) [Closed a]
local instance geometricSliceLocal1 : BraidedCategory B := BraidedCategory.ofCartesianMonoidalCategory
local instance geometricSliceLocal2 : ChosenPullbacksAlong (curryRightUnitorHom a) :=
  ChosenPullbacksAlong.ofHasPullbacksAlong _

/-- Compare the product-based inverse image with the ordinary slice functor. -/
def toOverStar : toOver a ≅ Over.star a :=
  (forgetAdjToOver a).rightAdjointUniq (Over.forgetAdjStar a)

/-- The slice projection has inverse image `Over.star` and internal sections as direct image. -/
def slice : GeometricMorphism (Over a) B :=
  ofAdjunction ((Over.toOverSectionsAdj a).ofNatIsoLeft (toOverStar a))
end Slice

section Pullback
variable [HasPullbacks F] {x y : F} (s : x ⟶ y)
local instance geometricSliceLocal3 : CartesianMonoidalCategory (Over y) := Over.cartesianMonoidalCategory y
variable [Closed (Over.mk s)]

/-- Pullback along an exponentiable map is an actual geometric inverse image. -/
def along : GeometricMorphism (Over x) (Over y) :=
  ofAdjunction (SquareKit.SliceDependentProduct.adjunction s)
end Pullback

/-- An equivalence supplies a geometric morphism in the direction of its direct image. -/
def ofEquivalence (e : B ≌ F) : GeometricMorphism F B :=
  ofAdjunction e.toAdjunction

section Section
variable [HasPullbacks B] [HasPullbacks F] [HasTerminal F]
variable (h : GeometricMorphism F B) (a : B) (s : ⊤_ F ⟶ h.inverseImage.obj a)
local instance geometricSliceLocal4 : CartesianMonoidalCategory (Over (h.inverseImage.obj a)) :=
  Over.cartesianMonoidalCategory _
variable [Closed (Over.mk s)]

/-- The section construction retains its right adjoint and finite-limit preservation.
The remaining comparison over the base is a separate obligation. -/
def fromSection : GeometricMorphism F (Over a) :=
  (ofEquivalence (Over.equivalenceOfIsTerminal (terminalIsTerminal (C := F)))).comp
    ((along s).comp (h.onSlices a))
end Section
end SquareKit.Internal.GeometricMorphism

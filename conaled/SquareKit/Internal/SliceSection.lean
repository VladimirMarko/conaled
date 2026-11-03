import SquareKit.Internal.GeometricSlice
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-! The comparison over the base for the geometric morphism constructed from
an actual section. All comparisons are natural isomorphisms of inverse images. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
universe v₁ v₂ u₁ u₂
variable {F : Type u₁} {B : Type u₂}
variable [Category.{v₁} F] [Category.{v₂} B]
section Products
variable [HasBinaryProducts F] [HasBinaryProducts B]

/-- Left exactness compares the actual products in the two categories. -/
def starPost (h : GeometricMorphism F B) (a : B) :
    Over.star a ⋙ Over.post h.inverseImage ≅ h.inverseImage ⋙ Over.star (h.inverseImage.obj a) :=
  NatIso.ofComponents (fun X => Over.isoMk (PreservesLimitPair.iso h.inverseImage a X)
    (by simp [Over.star_obj_hom, prodComparison])) (by
      intro X Y f
      apply Over.OverMorphism.ext
      change h.inverseImage.map (prod.map (𝟙 a) f) ≫ prodComparison h.inverseImage a Y =
        prodComparison h.inverseImage a X ≫ prod.map (𝟙 _) (h.inverseImage.map f)
      apply prod.hom_ext <;> simp only [prodComparison, Category.assoc, prod.lift_fst,
        prod.lift_snd, prod.map_fst, prod.map_snd, ← h.inverseImage.map_comp,
        Category.comp_id, prod.lift_snd_assoc])

/-- A product with the terminal object, followed by forgetting the slice, is the identity. -/
def terminalStarForget [HasTerminal F] :
    Over.star (⊤_ F) ⋙ (Over.equivalenceOfIsTerminal (terminalIsTerminal (C := F))).functor ≅ 𝟭 F :=
  NatIso.ofComponents (fun X => prod.leftUnitor X) (by intro X Y f; change prod.map (𝟙 _) f ≫ prod.snd = prod.snd ≫ f; simp)

end Products
section Section
open CategoryTheory.MonoidalCategory
variable [HasBinaryProducts F] [HasPullbacks B] [HasPullbacks F] [HasTerminal F]
variable [CartesianMonoidalCategory B]
variable (h : GeometricMorphism F B) (a : B) [Closed a]
variable (s : ⊤_ F ⟶ h.inverseImage.obj a)
local instance sliceSectionLocal1 : CartesianMonoidalCategory (Over (h.inverseImage.obj a)) :=
  Over.cartesianMonoidalCategory _
variable [Closed (Over.mk s)]

/-- The constructed geometric morphism lies over `h`, with an invertible comparison. -/
def fromSectionLift : Lift h (slice a) where
  morphism := fromSection h a s
  comparison :=
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (isoWhiskerRight (starPost h a) (Over.pullback s)) _ ≪≫
    isoWhiskerRight (Functor.associator _ _ _) _ ≪≫
    isoWhiskerRight (isoWhiskerLeft _ (Over.starPullbackIsoStar s)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ terminalStarForget ≪≫ Functor.rightUnitor _
end Section
end SquareKit.Internal.GeometricMorphism

namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe v₁ v₂ u₁ u₂
variable {F : Type u₁} {B : Type u₂}
variable [Category.{v₁} F] [Category.{v₂} B]
variable [HasBinaryProducts F] [HasPullbacks B] [HasPullbacks F] [HasTerminal F]
variable [CartesianMonoidalCategory B]
variable (h : GeometricMorphism F B) (a : B) [Closed a]
variable (s : ⊤_ F ⟶ h.inverseImage.obj a)
local instance sliceSectionLocal2 : CartesianMonoidalCategory (Over (h.inverseImage.obj a)) :=
  Over.cartesianMonoidalCategory _
variable [Closed (Over.mk s)]

/-- The comparison forgets the generic coordinate and retains the interpreted value. -/
theorem fromSectionLift_comparison_hom (X : B) :
    (fromSectionLift h a s).comparison.hom.app X =
      pullback.fst (h.inverseImage.map ((Over.star a).obj X).hom) s ≫
        h.inverseImage.map (prod.snd : ((Over.star a).obj X).left ⟶ X) := by
  simp [fromSectionLift, starPost, terminalStarForget, Over.starPullbackIsoStar,
    Over.pullback_map_left, prodComparison, ofEquivalence, ofAdjunction, comp, along, onSlices, slice]
  exact Category.id_comp _
end SquareKit.Internal.GeometricMorphism

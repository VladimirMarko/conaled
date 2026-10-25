import SquareKit.Internal.ClassifierComparison
import SquareKit.SliceExtensive
import SquareKit.Internal.PartitionParameter

/-! The generic complementary predicates and their meaning under a geometric lift. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe v₁ v₂ u₁ u₂
variable {F : Type u₁} {B : Type u₂} [Category.{v₁} F] [Category.{v₂} B]

/-- The identity of a topos, with its canonical comparison over its projection. -/
def identityLift (π : GeometricMorphism F B) : Lift π π where
  morphism := identity F
  comparison := Functor.rightUnitor π.inverseImage

variable [HasTerminal F] [HasBinaryProducts F] [HasPullbacks F] [FinitaryExtensive F]
variable [CartesianMonoidalCategory B] [HasPullbacks B] [FinitaryExtensive B]
variable {h : GeometricMorphism F B} {U : B} (u : U ⟶ ⊤_ B) [Mono u]
variable [Closed (U ⨿ ⊤_ B)]

/-- Interpret both predicates by pulling back the summands along the generic section. -/
def Lift.model (k : Lift h (slice (U ⨿ ⊤_ B))) : PartitionSection.Model (parameterPullback h u) :=
  PartitionSection.ofSection _ (k.section ≫ (classifierObjectComparison h (U := U)).hom)

/-- The two interpreted predicates assemble to the pulled-back generic section. -/
theorem Lift.model_section (k : Lift h (slice (U ⨿ ⊤_ B))) :
    (k.model u).toSection = k.section ≫ (classifierObjectComparison h (U := U)).hom :=
  PartitionSection.ofSection_section _ _

/-- Every compatible transformation preserves both interpreted predicates. -/
def modelFunctor : Lift h (slice (U ⨿ ⊤_ B)) ⥤ PartitionSection.Model (parameterPullback h u) where
  obj k := k.model u
  map α := PartitionSection.Model.homOfSection (by
    rw [Lift.model_section, Lift.model_section, Lift.section_natural α])
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The generic model is obtained at the identity lift of the classifier projection. -/
def genericModel : PartitionSection.Model (parameterPullback (slice (U ⨿ ⊤_ B)) u) :=
  (identityLift (slice (U ⨿ ⊤_ B))).model u
end SquareKit.Internal.GeometricMorphism

namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe v₁ v₂ u₁ u₂
variable {F : Type u₁} {B : Type u₂} [Category.{v₁} F] [Category.{v₂} B]
variable [HasTerminal F] [CartesianMonoidalCategory B] [HasPullbacks B]
variable {h : GeometricMorphism F B} {a : B} [Closed a]

/-- Pulling back the diagonal at the identity lift extracts exactly the lift's section. -/
theorem Lift.generic_pullSection (k : Lift h (slice a)) :
    k.morphism.pullSection (identityLift (slice a)).section ≫ k.comparison.hom.app a = k.section := by
  have ht : (PreservesTerminal.iso k.morphism.inverseImage).inv ≫
      k.morphism.inverseImage.map (identityLift (slice a)).terminalIso.inv = k.terminalIso.inv :=
    (Over.mkIdTerminal.isTerminalObj k.morphism.inverseImage).hom_ext _ _
  dsimp only [pullSection, Lift.section]
  change ((PreservesTerminal.iso k.morphism.inverseImage).inv ≫
    k.morphism.inverseImage.map ((identityLift (slice a)).terminalIso.inv ≫ genericSection a ≫ 𝟙 _)) ≫ _ = _
  rw [Category.comp_id, k.morphism.inverseImage.map_comp]
  simp only [← Category.assoc, ht]
end SquareKit.Internal.GeometricMorphism

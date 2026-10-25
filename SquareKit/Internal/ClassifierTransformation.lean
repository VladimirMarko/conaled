import SquareKit.Internal.ClassifierPseudonaturality
import SquareKit.Internal.TransformationCoherence

/-! Source-transformation compatibility of the classifier comparison. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.Functor
universe v₁ v₂ v₃ u₁ u₂ u₃
variable {F : Type u₁} {B : Type u₂} {G : Type u₃}
variable [Category.{v₁} F] [Category.{v₂} B] [Category.{v₃} G]
variable [CartesianMonoidalCategory F] [HasPullbacks F] [FinitaryExtensive F]
variable [CartesianMonoidalCategory B] [HasPullbacks B] [FinitaryExtensive B]
variable [HasTerminal G] [HasBinaryProducts G] [HasPullbacks G] [FinitaryExtensive G]
variable {f g : GeometricMorphism G F} (α : f ⟶ g) (h : GeometricMorphism F B)
variable {U : B} (u : U ⟶ ⊤_ B) [Mono u] [Closed (U ⨿ ⊤_ B)]

/-- A source transformation acts at each actual predicate carrier after parameter normalization. -/
def sourceModelTransformation :
    sourceModelFunctor f h u ⋙ PartitionSection.mapParameter
      (parameterPullback (f.comp h) u) (parameterPullback (g.comp h) u) (α.app (h.inverseImage.obj U)) ⟶
        sourceModelFunctor g h u where
  app M := ⟨α.app M.P, α.app M.Q, terminal.hom_ext _ _, terminal.hom_ext _ _⟩
  naturality _ _ _ := Subsingleton.elim _ _

/-- The transformed classified predicates are related by the same source transformation. -/
def classifiedSourceTransformation (k : Lift h (slice (U ⨿ ⊤_ B))) :
    (PartitionSection.mapParameter (parameterPullback (f.comp h) u) (parameterPullback (g.comp h) u)
      (α.app (h.inverseImage.obj U))).obj ((k.precomp f).model u) ⟶ (k.precomp g).model u :=
  PartitionSection.Model.homOfSection (by
    rw [PartitionSection.mapParameter_section, Lift.model_section, Lift.model_section]
    simp only [Category.assoc]
    have hn := classifierObjectComparison_natural (h := f.comp h) (k := g.comp h)
      (whiskerLeft h.inverseImage α) U
    change α.app (h.inverseImage.obj (U ⨿ ⊤_ B)) ≫ (classifierObjectComparison (g.comp h)).hom =
      (classifierObjectComparison (f.comp h)).hom ≫ coprod.map (α.app (h.inverseImage.obj U)) (𝟙 (⊤_ G)) at hn
    have hs : (k.precomp f).section ≫ α.app (h.inverseImage.obj (U ⨿ ⊤_ B)) = (k.precomp g).section := by
      rw [Lift.precomp_section, Lift.precomp_section]
      exact pullSection_transformation α k.section
    calc
      _ = ((k.precomp f).section ≫ α.app (h.inverseImage.obj (U ⨿ ⊤_ B))) ≫
          (classifierObjectComparison (g.comp h)).hom := by
        simpa only [Category.assoc] using congrArg (fun t => (k.precomp f).section ≫ t) hn.symm
      _ = _ := by rw [hs])

/-- The classifier's source comparison square commutes for noninvertible transformations too. -/
theorem classifierSource_transformation (k : Lift h (slice (U ⨿ ⊤_ B))) :
    (PartitionSection.mapParameter (parameterPullback (f.comp h) u) (parameterPullback (g.comp h) u)
      (α.app (h.inverseImage.obj U))).map ((classifierSourceIso f h u).hom.app k) ≫
        classifiedSourceTransformation α h u k =
      (sourceModelTransformation α h u).app (k.model u) ≫ (classifierSourceIso g h u).hom.app k :=
  Subsingleton.elim _ _
end SquareKit.Internal.GeometricMorphism

import SquareKit.ArbitrarySourceClassifier
import SquareKit.Internal.SheafPseudopullback
import SquareKit.Internal.GenericModelPullback
import SquareKit.Internal.ClassifierSourceChange
import SquareKit.Internal.PartitionMixedChange
import SquareKit.SheafCartesianClosed
import Examples.SheafBaseChange

/-! Two distinct geometric lifts from the sheaf topos on the diamond site.
The extracted generic sections distinguish false and true even at the stage
where the existing nonconstant sheaf has no global section. -/
noncomputable section
set_option autoImplicit false
namespace Examples.SliceUniversal
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open SquareKit.Internal SquareKit.Internal.GeometricMorphism
open Examples.SheafImage Examples.SheafImage.Diamond Examples.SheafBaseChange
abbrev Source := Sheaf topology Type
local instance sliceUniversalLocal1 : CartesianMonoidalCategory Source := inferInstance
local instance sliceUniversalLocal2 : MonoidalCategory Source :=
  (inferInstance : CartesianMonoidalCategory Source).toMonoidalCategory
local instance sliceUniversalLocal3 : MonoidalClosed Source where
  closed := SquareKit.SheafCartesianClosed.closed

/-- A constant Boolean section of the chosen categorical terminal object. -/
def boolSection (b : Bool) : ⊤_ Source ⟶ D :=
  ⟨{ app _ := ↾fun _ => b, naturality := by intros; ext; rfl }⟩

/-- The test observes an actual terminal section at the top stage of the site. -/
def terminalPoint : (⊤_ Source).obj.obj (op X) :=
  (Limits.terminal.from Examples.SheafImage.terminal).hom.app (op X) ()

theorem boolSection_distinct : boolSection false ≠ boolSection true := by
  intro he
  have h := congrArg (fun f => f.hom.app (op X) terminalPoint) he
  exact Bool.false_ne_true h

local instance sliceUniversalLocal4 : Closed D := (inferInstance : MonoidalClosed Source).closed D

local instance sliceUniversalLocal5 : CartesianMonoidalCategory (Over D) := Over.cartesianMonoidalCategory D
local instance sliceUniversalLocal6 : MonoidalCategory (Over D) :=
  (Over.cartesianMonoidalCategory D).toMonoidalCategory
local instance sliceUniversalLocal7 : MonoidalClosed (Over D) := SquareKit.SheafSliceFunction.closed D

/-- Each section supplies both adjoints and a comparison over the source topos. -/
def boolLift (b : Bool) : Lift (identity Source) (slice D) :=
  (sheafSectionEquivalence (identity Source) D).inverse.obj ⟨boolSection b⟩

/-- Extraction uses the public slice theorem and returns the independently chosen Boolean. -/
theorem boolLift_extract (b : Bool) :
    (boolLift b).section.hom.app (op X) terminalPoint = b := by
  have he := (sheafSectionEquivalence (identity Source) D).counitIso.app ⟨boolSection b⟩
  have e := Discrete.eq_of_hom he.hom
  exact congrArg (fun f => f.hom.app (op X) terminalPoint) e

/-- There is no compatible geometric transformation between the two distinct lifts. -/
theorem boolLifts_no_transformation : ¬ Nonempty (boolLift false ⟶ boolLift true) := by
  rintro ⟨α⟩
  have h := Lift.section_natural α
  have e := congrArg (fun f => f.hom.app (op X) terminalPoint) h
  rw [boolLift_extract, boolLift_extract] at e
  exact Bool.false_ne_true e

/-- The category equivalence retains the selected section, not only its cardinality. -/
theorem boolLift_equivalence (b : Bool) :
    ((sheafSectionEquivalence (identity Source) D).functor.obj (boolLift b)).as = boolSection b :=
  Discrete.eq_of_hom ((sheafSectionEquivalence (identity Source) D).counitIso.app ⟨boolSection b⟩).hom
/-- A nontrivial ambient base change: the projection of the Boolean slice of the diamond topos. -/
def diamondPseudopullback : GeometricMorphism Source (Over ((slice D).inverseImage.obj D)) ≌
    Cone (postcompose (F := Source) (slice D)) (slice D) :=
  sheafPseudopullback (slice D) D

/-- The forward square retains the geometric leg to the Boolean slice. -/
theorem diamondPseudopullback_base
    (k : GeometricMorphism Source (Over ((slice D).inverseImage.obj D))) :
    (diamondPseudopullback.functor.obj k).base = k.comp (slice ((slice D).inverseImage.obj D)) := rfl

/-- Cone arrows retain the independently supplied transformation of the base leg. -/
theorem diamondPseudopullback_base_map
    {k l : GeometricMorphism Source (Over ((slice D).inverseImage.obj D))} (α : k ⟶ l) :
    (diamondPseudopullback.functor.map α).base =
      Functor.whiskerLeft (slice ((slice D).inverseImage.obj D)).inverseImage α := rfl

/-- Ambient change along the Boolean slice retains the displayed witness projection. -/
theorem diamondMixed_witness (Z : Over D) :
    ((pullbackPost (slice D) (boolSection true)).hom.app Z).left ≫
        pullback.fst ((slice D).inverseImage.map Z.hom)
          ((slice D).inverseImage.map (boolSection true)) =
      (slice D).inverseImage.map (pullback.fst Z.hom (boolSection true)) :=
  pullbackPost_fst _ _ _

/-- The same comparison retains the substituted terminal context separately. -/
theorem diamondMixed_context (Z : Over D) :
    ((pullbackPost (slice D) (boolSection true)).hom.app Z).left ≫
        pullback.snd ((slice D).inverseImage.map Z.hom)
          ((slice D).inverseImage.map (boolSection true)) =
      (slice D).inverseImage.map (pullback.snd Z.hom (boolSection true)) :=
  pullbackPost_snd _ _ _

/-- The mixed square for two successive Boolean slice projections pastes on carriers. -/
theorem diamondMixed_pasting (Z : Over D) :
    ((pullbackPost ((slice ((slice D).inverseImage.obj D)).comp (slice D))
      (boolSection true)).hom.app Z).left =
      (slice ((slice D).inverseImage.obj D)).inverseImage.map
        ((pullbackPost (slice D) (boolSection true)).hom.app Z).left ≫
          ((pullbackPost (slice ((slice D).inverseImage.obj D))
            ((slice D).inverseImage.map (boolSection true))).hom.app
              ((Over.post (slice D).inverseImage).obj Z)).left :=
  pullbackPost_composition _ _ _ _
/-- The classifier's two generic predicates really pull back around the Boolean base square. -/
def diamondGenericBaseChange :=
  classifierBaseChangeGenericIso (slice D) (𝟙 (⊤_ Source))

/-- Context composition and the Boolean ambient change give the same witness-preserving route. -/
theorem diamondMixed_context_pasting (Z : Over D) :
    (slice D).inverseImage.map
      (SquareKit.Family.compositionIso Z.hom (boolSection true) (𝟙 (⊤_ Source))).hom ≫
        pullbackComparison (slice D).inverseImage Z.hom (𝟙 (⊤_ Source) ≫ boolSection true) =
      mixedContextPaste (slice D) Z.hom (boolSection true) (𝟙 (⊤_ Source)) :=
  pullbackPost_context_composition _ _ _ _

/-- The canonical normalization carries the old generic predicates to the new generic model. -/
def diamondNormalizedGenericBaseChange :
    (normalizedClassifierLift (slice D)).pullGeneric (𝟙 (⊤_ Source)) ≅
      normalizedGenericModel (slice D) (𝟙 (⊤_ Source)) :=
  normalizedClassifierGenericIso (slice D) (𝟙 (⊤_ Source))

/-- The full cone equivalence now starts at the normalized classifier slice. -/
def diamondNormalizedPseudopullback :
    GeometricMorphism Source (Over ((slice D).inverseImage.obj (⊤_ Source) ⨿ ⊤_ (Over D))) ≌
      Cone (postcompose (F := Source) (slice D)) (slice ((⊤_ Source) ⨿ ⊤_ Source)) :=
  normalizedClassifierPseudopullback (slice D) (⊤_ Source)

/-- Its base comparison is the canonical normalized projection, for every geometric input. -/
def diamondNormalizedBaseComparison
    (k : GeometricMorphism Source (Over ((slice D).inverseImage.obj (⊤_ Source) ⨿ ⊤_ (Over D)))) :
    (diamondNormalizedPseudopullback.functor.obj k).base ≅
      k.comp (slice ((slice D).inverseImage.obj (⊤_ Source) ⨿ ⊤_ (Over D))) :=
  normalizedClassifierPseudopullbackBaseIso (slice D) (⊤_ Source) k

/-- Both normalized cone legs satisfy the comparison square of the full universal property. -/
def diamondNormalizedConeComparison
    (k : GeometricMorphism Source (Over ((slice D).inverseImage.obj (⊤_ Source) ⨿ ⊤_ (Over D)))) :
    diamondNormalizedPseudopullback.functor.obj k ≅ normalizedClassifierCone (slice D) (⊤_ Source) k :=
  normalizedClassifierConeIso (slice D) (⊤_ Source) k
end Examples.SliceUniversal

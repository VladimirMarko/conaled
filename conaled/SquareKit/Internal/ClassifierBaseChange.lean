import SquareKit.Internal.GenericModelPullback
import SquareKit.Internal.SliceBaseChange
import SquareKit.Internal.SliceIso
import SquareKit.Internal.GeometricEquivalence
import SquareKit.Internal.SheafPseudopullback
import SquareKit.Internal.SliceRebase
import SquareKit.Internal.SliceSourceChange
import SquareKit.SliceExtensive

/-! The classifier's ambient-base square preserves its generic diagonal and
actual generic predicate carriers. The normalized slice object is compared explicitly. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe v₁ v₂ u₁ u₂
variable {F : Type u₁} {B : Type u₂} [Category.{v₁} F] [Category.{v₂} B]
variable [CartesianMonoidalCategory F] [HasPullbacks F] [FinitaryExtensive F]
variable [CartesianMonoidalCategory B] [HasPullbacks B] [FinitaryExtensive B]
variable (h : GeometricMorphism F B) {U : B} (u : U ⟶ ⊤_ B) [Mono u]
variable [Closed (U ⨿ ⊤_ B)] [Closed (h.inverseImage.obj (U ⨿ ⊤_ B))]

local instance classifierBaseSliceCartesian :
    CartesianMonoidalCategory (Over (h.inverseImage.obj (U ⨿ ⊤_ B))) :=
  Over.cartesianMonoidalCategory _

/-- The inverse-image classifier object and the normalized parameter-plus-terminal object have equivalent slices. -/
def classifierSliceComparison : Over (h.inverseImage.obj (U ⨿ ⊤_ B)) ≌
    Over (h.inverseImage.obj U ⨿ ⊤_ F) := Over.mapIso (classifierObjectComparison h)

/-- The canonical lift around the actual geometric base-change square. -/
def classifierBaseChangeLift :
    Lift ((slice (h.inverseImage.obj (U ⨿ ⊤_ B))).comp h) (slice (U ⨿ ⊤_ B)) :=
  (identityLift (slice (h.inverseImage.obj (U ⨿ ⊤_ B)))).postSlice h (U ⨿ ⊤_ B)

/-- The base-change square pulls back both generic predicates, not only the classifying object. -/
def classifierBaseChangeGenericIso :
    (classifierBaseChangeLift h (U := U)).pullGeneric u ≅ (classifierBaseChangeLift h (U := U)).model u :=
  (classifierBaseChangeLift h).pullGenericIso u

/-- The generic comparison retains the diagonal section with the explicit coproduct/terminal normalization. -/
theorem classifierBaseChangeGeneric_section :
    ((classifierBaseChangeLift h (U := U)).pullGeneric u).toSection =
      (identityLift (slice (h.inverseImage.obj (U ⨿ ⊤_ B)))).section ≫
        (classifierObjectComparison ((slice (h.inverseImage.obj (U ⨿ ⊤_ B))).comp h) (U := U)).hom := by
  rw [Lift.pullGeneric_section, Lift.model_section]
  change (Lift.postSlice h (U ⨿ ⊤_ B) _).section ≫ _ = _
  rw [Lift.postSlice_section]

variable [Closed (h.inverseImage.obj U ⨿ ⊤_ F)]
local instance normalizedClassifierCartesian :
    CartesianMonoidalCategory (Over (h.inverseImage.obj U ⨿ ⊤_ F)) :=
  Over.cartesianMonoidalCategory _

/-- The normalized geometric square uses the canonical coproduct comparison over the base. -/
def normalizedClassifierLift :
    Lift ((slice (h.inverseImage.obj U ⨿ ⊤_ F)).comp h) (slice (U ⨿ ⊤_ B)) :=
  (sliceIsoLift (classifierObjectComparison h (U := U))).postSlice h (U ⨿ ⊤_ B)

/-- Normalize the parameter of the new classifier's actual generic model. -/
def normalizedGenericModel :
    PartitionSection.Model (parameterPullback ((slice (h.inverseImage.obj U ⨿ ⊤_ F)).comp h) u) :=
  (PartitionSection.changeParameter
    (parameterPullback (slice (h.inverseImage.obj U ⨿ ⊤_ F)) (parameterPullback h u))
    (parameterPullback ((slice (h.inverseImage.obj U ⨿ ⊤_ F)).comp h) u)
    (Iso.refl _)).obj (genericModel (parameterPullback h u))

/-- The normalized square classifies the new generic model, including its diagonal. -/
theorem normalizedClassifier_model_section :
    ((normalizedClassifierLift h).model u).toSection = (normalizedGenericModel h u).toSection := by
  rw [Lift.model_section]
  unfold normalizedGenericModel
  rw [PartitionSection.changeParameter_section]
  unfold genericModel
  rw [Lift.model_section]
  simp only [Iso.refl_hom]
  change (Lift.postSlice h (U ⨿ ⊤_ B) _).section ≫ _ = _
  rw [Lift.postSlice_section, classifierObjectComparison_comp]
  rw [← Category.assoc, sliceIsoLift_section]
  have hid {T P Q : Over (h.inverseImage.obj U ⨿ ⊤_ F)} (s : T ⟶ P ⨿ Q) :
      s = s ≫ coprod.map (𝟙 P) (𝟙 Q) := by simp
  exact hid _

/-- Actual old generic carriers pull back to the normalized classifier's new generic model.
The right endpoint is explicitly the transported `genericModel (parameterPullback h u)`. -/
def normalizedClassifierGenericIso :
    (normalizedClassifierLift h).pullGeneric u ≅ normalizedGenericModel h u :=
  (normalizedClassifierLift h).pullGenericIso u ≪≫ {
    hom := PartitionSection.Model.homOfSection (normalizedClassifier_model_section h u)
    inv := PartitionSection.Model.homOfSection (normalizedClassifier_model_section h u).symm
    hom_inv_id := Subsingleton.elim _ _
    inv_hom_id := Subsingleton.elim _ _ }
end SquareKit.Internal.GeometricMorphism

namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe u v uF vF uB vB
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {F : Type uF} {B : Type uB} [Category.{vF} F] [Category.{vB} B]
variable [CartesianMonoidalCategory F] [HasPullbacks F] [FinitaryExtensive F]
variable [CartesianMonoidalCategory B] [HasPullbacks B] [FinitaryExtensive B]
variable (h : GeometricMorphism F B) (U : B)
variable [Closed (U ⨿ ⊤_ B)] [Closed (h.inverseImage.obj (U ⨿ ⊤_ B))]

/-- The normalized classifier has the full geometric pseudopullback universal property.
This transports the proved equivalence through the canonical coproduct slice comparison. -/
def normalizedClassifierPseudopullback :
    GeometricMorphism (Sheaf J (Type (max u v))) (Over (h.inverseImage.obj U ⨿ ⊤_ F)) ≌
      Cone (postcompose (F := Sheaf J (Type (max u v))) h) (slice (U ⨿ ⊤_ B)) :=
  (postcomposeEquivalence (classifierSliceComparison h (U := U))).trans
    (sheafPseudopullback h (U ⨿ ⊤_ B))

variable [Closed (h.inverseImage.obj U ⨿ ⊤_ F)]

/-- The transported pseudopullback's base leg is canonically the normalized slice projection. -/
def normalizedClassifierPseudopullbackBaseIso
    (k : GeometricMorphism (Sheaf J (Type (max u v))) (Over (h.inverseImage.obj U ⨿ ⊤_ F))) :
    ((normalizedClassifierPseudopullback h U).functor.obj k).base ≅
      k.comp (slice (h.inverseImage.obj U ⨿ ⊤_ F)) :=
  isoOfInverseImage ((Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (starMapIso (classifierObjectComparison h (U := U))) k.inverseImage)

/-- The cone with the normalized base leg and the explicitly normalized geometric square. -/
def normalizedClassifierCone
    (k : GeometricMorphism (Sheaf J (Type (max u v))) (Over (h.inverseImage.obj U ⨿ ⊤_ F))) :
    Cone (postcompose (F := Sheaf J (Type (max u v))) h) (slice (U ⨿ ⊤_ B)) :=
  ⟨k.comp (slice (h.inverseImage.obj U ⨿ ⊤_ F)),
    ((normalizedClassifierLift h (U := U)).precomp k).rebase (Functor.associator _ _ _)⟩

/-- The universal property's transported cone agrees with the normalized square on both legs. -/
def normalizedClassifierConeIso
    (k : GeometricMorphism (Sheaf J (Type (max u v))) (Over (h.inverseImage.obj U ⨿ ⊤_ F))) :
    (normalizedClassifierPseudopullback h U).functor.obj k ≅ normalizedClassifierCone h U k where
  hom := {
    base := (normalizedClassifierPseudopullbackBaseIso h U k).hom
    top := (Functor.associator _ _ _).inv
    over := by
      apply NatTrans.ext
      funext X
      simp [normalizedClassifierCone, normalizedClassifierLift, Lift.rebase, Lift.precomp,
        normalizedClassifierPseudopullback, normalizedClassifierPseudopullbackBaseIso,
        postcomposeEquivalence, sheafPseudopullback, slicePseudopullback, canonicalConeEquivalence,
        canonicalCone, sliceConeFunctor, Lift.postSlice, sliceIsoLift, isoOfInverseImage,
        postcompose, comp, ofEquivalence, ofAdjunction, classifierSliceComparison, slice]
      exact Category.id_comp _ }
  inv := {
    base := (normalizedClassifierPseudopullbackBaseIso h U k).inv
    top := (Functor.associator _ _ _).hom
    over := by
      apply NatTrans.ext
      funext X
      simp [normalizedClassifierCone, normalizedClassifierLift, Lift.rebase, Lift.precomp,
        normalizedClassifierPseudopullback, normalizedClassifierPseudopullbackBaseIso,
        postcomposeEquivalence, sheafPseudopullback, slicePseudopullback, canonicalConeEquivalence,
        canonicalCone, sliceConeFunctor, Lift.postSlice, sliceIsoLift, isoOfInverseImage,
        postcompose, comp, ofEquivalence, ofAdjunction, classifierSliceComparison, slice]
      exact (Category.id_comp _).symm }
  hom_inv_id := Cone.Hom.ext (normalizedClassifierPseudopullbackBaseIso h U k).hom_inv_id
    (Functor.associator _ _ _).inv_hom_id
  inv_hom_id := Cone.Hom.ext (normalizedClassifierPseudopullbackBaseIso h U k).inv_hom_id
    (Functor.associator _ _ _).hom_inv_id
end SquareKit.Internal.GeometricMorphism

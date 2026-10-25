import SquareKit.Internal.GenericModel

/-! The classifier interprets a lift by actual inverse image of its generic
predicates, with parameter transport through the specified comparison over the base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe v₁ v₂ u₁ u₂
variable {F : Type u₁} {B : Type u₂} [Category.{v₁} F] [Category.{v₂} B]
variable [HasTerminal F] [HasBinaryProducts F] [HasPullbacks F] [FinitaryExtensive F]
variable [CartesianMonoidalCategory B] [HasPullbacks B] [FinitaryExtensive B]
variable {h : GeometricMorphism F B} {U : B} (u : U ⟶ ⊤_ B) [Mono u]
variable [Closed (U ⨿ ⊤_ B)]
local instance genericModelPullbackLocal1 : CartesianMonoidalCategory (Over (U ⨿ ⊤_ B)) := Over.cartesianMonoidalCategory _

/-- Pull back both generic carriers, then transport their parameter along the base comparison. -/
def Lift.pullGeneric (k : Lift h (slice (U ⨿ ⊤_ B))) :
    PartitionSection.Model (parameterPullback h u) :=
  (PartitionSection.changeParameter
    (parameterPullback k.morphism (parameterPullback (slice (U ⨿ ⊤_ B)) u))
    (parameterPullback h u) (k.comparison.app U)).obj (pullModel k.morphism (genericModel u))

/-- The actual pulled-back predicates recover the same classified section. -/
theorem Lift.pullGeneric_section (k : Lift h (slice (U ⨿ ⊤_ B))) :
    (k.pullGeneric u).toSection = (k.model u).toSection := by
  unfold Lift.pullGeneric
  rw [PartitionSection.changeParameter_section, pullModel_section]
  unfold genericModel
  rw [Lift.model_section, Lift.model_section]
  dsimp only [pullSection]
  rw [k.morphism.inverseImage.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% (classifierObjectComparison_comp k.morphism (slice (U ⨿ ⊤_ B)) U)]
  have hn := classifierObjectComparison_natural
    (h := k.morphism.comp (slice (U ⨿ ⊤_ B))) (k := h) k.comparison.hom U
  change k.comparison.hom.app (U ⨿ ⊤_ B) ≫ (classifierObjectComparison h).hom =
    (classifierObjectComparison (k.morphism.comp (slice (U ⨿ ⊤_ B)))).hom ≫
      coprod.map (k.comparison.app U).hom (𝟙 (⊤_ F)) at hn
  rw [← hn]
  rw [← Category.assoc, ← Category.assoc]
  exact congrArg (fun s => s ≫ (classifierObjectComparison h).hom) k.generic_pullSection

/-- Generic-model pullback is isomorphic to the classifier interpretation on actual carriers. -/
def Lift.pullGenericIso (k : Lift h (slice (U ⨿ ⊤_ B))) : k.pullGeneric u ≅ k.model u where
  hom := PartitionSection.Model.homOfSection (k.pullGeneric_section u)
  inv := PartitionSection.Model.homOfSection (k.pullGeneric_section u).symm
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _
/-- Generic pullback acts on transformations by their components at the two generic carriers. -/
def pullGenericFunctor : Lift h (slice (U ⨿ ⊤_ B)) ⥤ PartitionSection.Model (parameterPullback h u) where
  obj k := k.pullGeneric u
  map α := {
    left := α.transformation.app (genericModel u).P
    right := α.transformation.app (genericModel u).Q
    left_over := terminal.hom_ext _ _
    right_over := terminal.hom_ext _ _ }
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The generic-model comparison is natural on all compatible transformations. -/
def pullGenericModelIso : pullGenericFunctor (h := h) u ≅ modelFunctor u :=
  NatIso.ofComponents (fun k => k.pullGenericIso u) (by intros; apply Subsingleton.elim)

local instance genericModelPullbackLocal2 : CartesianMonoidalCategory (Over (h.inverseImage.obj (U ⨿ ⊤_ B))) :=
  Over.cartesianMonoidalCategory _
variable [MonoidalClosed (Over (h.inverseImage.obj (U ⨿ ⊤_ B)))]

/-- The equivalence's functor is naturally the actual generic-model pullback functor. -/
def finiteClassifierPullbackIso : pullGenericFunctor (h := h) u ≅ (finiteClassifier h u).functor :=
  NatIso.ofComponents (fun k => k.pullGenericIso u) (by intros; apply Subsingleton.elim)
end SquareKit.Internal.GeometricMorphism

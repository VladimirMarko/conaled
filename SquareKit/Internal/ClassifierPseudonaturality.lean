import SquareKit.Internal.ClassifierSourceCoherence
import SquareKit.Internal.ClassifierRebase
import SquareKit.Internal.SliceSourceCoherence

/-! Explicit unit and composition diagrams for the classifier's source comparison. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.Functor
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄
variable {F : Type u₁} {B : Type u₂} {G : Type u₃} {H : Type u₄}
variable [Category.{v₁} F] [Category.{v₂} B] [Category.{v₃} G] [Category.{v₄} H]
variable [CartesianMonoidalCategory F] [HasPullbacks F] [FinitaryExtensive F]
variable [CartesianMonoidalCategory B] [HasPullbacks B] [FinitaryExtensive B]
variable [CartesianMonoidalCategory G] [HasPullbacks G] [FinitaryExtensive G]
variable [HasTerminal H] [HasBinaryProducts H] [HasPullbacks H] [FinitaryExtensive H]
variable (g : GeometricMorphism H G) (f : GeometricMorphism G F) (h : GeometricMorphism F B)
variable {U : B} (u : U ⟶ ⊤_ B) [Mono u] [Closed (U ⨿ ⊤_ B)]

/-- The two geometric source composites have the same interpreted predicates, after their canonical associator. -/
def classifiedLiftCompIso :
    (Lift.precompFunctor (h := h) (π := slice (U ⨿ ⊤_ B)) f ⋙ Lift.precompFunctor g) ⋙
      modelFunctor (h := g.comp (f.comp h)) u ≅
        Lift.precompFunctor (g.comp f) ⋙ modelFunctor (h := (g.comp f).comp h) u :=
  NatIso.ofComponents (fun k => {
    hom := PartitionSection.Model.homOfSection (by
      change (((k.precomp f).precomp g).model u).toSection = ((k.precomp (g.comp f)).model u).toSection
      rw [Lift.model_section, Lift.model_section, Lift.precomp_section, Lift.precomp_section,
        Lift.precomp_section, pullSection_comp]; rfl)
    inv := PartitionSection.Model.homOfSection (by
      change ((k.precomp (g.comp f)).model u).toSection = (((k.precomp f).precomp g).model u).toSection
      rw [Lift.model_section, Lift.model_section, Lift.precomp_section, Lift.precomp_section,
        Lift.precomp_section, pullSection_comp]; rfl)
    hom_inv_id := Subsingleton.elim _ _
    inv_hom_id := Subsingleton.elim _ _ }) (by intros; apply Subsingleton.elim)

/-- Identity substitution retains the interpreted model, with the canonical inverse-image unitor. -/
def classifiedLiftIdentityIso :
    Lift.precompFunctor (h := h) (π := slice (U ⨿ ⊤_ B)) (identity F) ⋙
      modelFunctor (h := (identity F).comp h) u ≅ modelFunctor (h := h) u :=
  NatIso.ofComponents (fun k => {
    hom := PartitionSection.Model.homOfSection (by
      change ((k.precomp (identity F)).model u).toSection = (k.model u).toSection
      rw [Lift.model_section, Lift.model_section, Lift.precomp_section, pullSection_identity]; rfl)
    inv := PartitionSection.Model.homOfSection (by
      change (k.model u).toSection = ((k.precomp (identity F)).model u).toSection
      rw [Lift.model_section, Lift.model_section, Lift.precomp_section, pullSection_identity]; rfl)
    hom_inv_id := Subsingleton.elim _ _
    inv_hom_id := Subsingleton.elim _ _ }) (by intros; apply Subsingleton.elim)

/-- The source comparison satisfies the identity pseudonaturality diagram. -/
theorem classifierSource_identity :
    (classifierSourceIso (identity F) h u).hom ≫ (classifiedLiftIdentityIso h u).hom =
      whiskerLeft (modelFunctor (h := h) u) (sourceModelIdentityIso h u).hom ≫
        (Functor.rightUnitor (modelFunctor (h := h) u)).hom := by
  apply NatTrans.ext
  funext M
  apply Subsingleton.elim

/-- The direct composite comparison equals the pasted source-comparison squares. -/
theorem classifierSource_composition :
    (Functor.associator (modelFunctor (h := h) u) (sourceModelFunctor f h u)
      (sourceModelFunctor g (f.comp h) u)).hom ≫
      whiskerLeft (modelFunctor (h := h) u) (sourceModelCompIso g f h u).hom ≫
        (classifierSourceIso (g.comp f) h u).hom =
      whiskerRight (classifierSourceIso f h u).hom (sourceModelFunctor g (f.comp h) u) ≫
        (Functor.associator (Lift.precompFunctor f) (modelFunctor (h := f.comp h) u)
          (sourceModelFunctor g (f.comp h) u)).hom ≫
          whiskerLeft (Lift.precompFunctor f) (classifierSourceIso g (f.comp h) u).hom ≫
            (Functor.associator (Lift.precompFunctor f) (Lift.precompFunctor g)
              (modelFunctor (h := g.comp (f.comp h)) u)).inv ≫
              (classifiedLiftCompIso g f h u).hom := by
  apply NatTrans.ext
  funext M
  apply Subsingleton.elim
end SquareKit.Internal.GeometricMorphism

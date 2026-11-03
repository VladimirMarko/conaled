import SquareKit.Internal.ArrowPushout
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-! The arrow pushout construction commutes with functors preserving products
and pushouts. These comparisons are independent of classifier laws. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SquareKit.Internal.ArrowPushout
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]
variable [HasPushouts C] [HasPushouts D]
variable (F : C ⥤ D) [PreservesFiniteProducts F] [PreservesColimitsOfShape WalkingSpan F]
variable (P : C) (a : Arrow C)

/-- Identify the image span with the span formed from the image parameter. -/
def spanComparison : pushout (F.map (snd P a.left)) (F.map (P ◁ a.hom)) ⟶
    (interpretation (F.obj P)).obj (F.mapArrow.obj a) :=
  pushout.map _ _ _ _ (𝟙 _) (CartesianMonoidalCategory.prodComparison F P a.right) (CartesianMonoidalCategory.prodComparison F P a.left)
    (by simp) (prodComparison_natural_whiskerLeft F a.hom)

instance : IsIso (spanComparison F P a) := by
  unfold spanComparison
  infer_instance

/-- The canonical product and pushout comparisons give the change-of-category isomorphism. -/
def changeCategoryObj : F.obj ((interpretation P).obj a) ≅
    (interpretation (F.obj P)).obj (F.mapArrow.obj a) :=
  (PreservesPushout.iso F (snd P a.left) (P ◁ a.hom)).symm ≪≫
    asIso (spanComparison F P a)

@[reassoc (attr := simp)] theorem changeCategory_inl :
    F.map (pushout.inl (snd P a.left) (P ◁ a.hom)) ≫ (changeCategoryObj F P a).hom =
      pushout.inl (snd (F.obj P) (F.obj a.left)) (F.obj P ◁ F.map a.hom) := by
  simp [changeCategoryObj, spanComparison]

@[reassoc (attr := simp)] theorem changeCategory_inr :
    F.map (pushout.inr (snd P a.left) (P ◁ a.hom)) ≫ (changeCategoryObj F P a).hom =
      CartesianMonoidalCategory.prodComparison F P a.right ≫
        pushout.inr (snd (F.obj P) (F.obj a.left)) (F.obj P ◁ F.map a.hom) := by
  simp [changeCategoryObj, spanComparison]

/-- The change-of-category comparison is natural in the entire arrow. -/
def changeCategory : interpretation P ⋙ F ≅ F.mapArrow ⋙ interpretation (F.obj P) :=
  NatIso.ofComponents (changeCategoryObj F P) (by
    intro a b f
    dsimp only [Functor.comp_map]
    apply (cancel_epi (PreservesPushout.iso F (snd P a.left) (P ◁ a.hom)).hom).mp
    apply pushout.hom_ext
    · simp only [← Category.assoc, PreservesPushout.inl_iso_hom]
      rw [← F.map_comp, inl_map, F.map_comp]
      simp only [Category.assoc, changeCategory_inl]
      exact (inl_map (F.obj P) (F.mapArrow.map f)).symm
    · simp only [← Category.assoc, PreservesPushout.inr_iso_hom]
      rw [← F.map_comp, inr_map, F.map_comp]
      simp only [Category.assoc, changeCategory_inr]
      rw [prodComparison_natural_whiskerLeft_assoc]
      exact congrArg (CartesianMonoidalCategory.prodComparison F P a.right ≫ ·)
        (inr_map (F.obj P) (F.mapArrow.map f)).symm)

end SquareKit.Internal.ArrowPushout

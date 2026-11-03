import SquareKit.Internal.SliceBaseChange
import SquareKit.Internal.GeometricCone

/-! The base-change square's universal property on the full cone category,
including transformations which change the geometric leg to the base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.Functor
universe v₁ v₂ v₃ u₁ u₂ u₃
variable {F : Type u₁} {B : Type u₂} {G : Type u₃}
variable [Category.{v₁} F] [Category.{v₂} B] [Category.{v₃} G]
variable [HasTerminal G] [CartesianMonoidalCategory B] [HasPullbacks B]
variable [CartesianMonoidalCategory F] [HasPullbacks F]
variable (f : GeometricMorphism F B) (a : B) [Closed a] [Closed (f.inverseImage.obj a)]

/-- Postcomposition around the square on both legs and their comparison. -/
def sliceConeFunctor : Cone (𝟭 (GeometricMorphism G F)) (slice (f.inverseImage.obj a)) ⥤
    Cone (postcompose (F := G) f) (slice a) where
  obj k := ⟨k.base, k.lift.postSlice f a⟩
  map {k l} α := {
    base := α.base
    top := whiskerLeft (Over.post f.inverseImage) α.top
    over := by
      apply NatTrans.ext
      funext X
      have ho := congrArg (fun t => t.app (f.inverseImage.obj X)) α.over
      change α.top.app ((Over.star (f.inverseImage.obj a)).obj (f.inverseImage.obj X)) ≫
        l.lift.comparison.hom.app (f.inverseImage.obj X) =
          k.lift.comparison.hom.app (f.inverseImage.obj X) ≫ α.base.app (f.inverseImage.obj X) at ho
      change α.top.app ((Over.post f.inverseImage).obj ((Over.star a).obj X)) ≫
        (𝟙 _ ≫ l.lift.morphism.inverseImage.map ((starPost f a).hom.app X) ≫ 𝟙 _ ≫ _) =
        (𝟙 _ ≫ k.lift.morphism.inverseImage.map ((starPost f a).hom.app X) ≫ 𝟙 _ ≫ _) ≫ _
      simp only [Category.id_comp, Category.assoc]
      rw [← reassoc_of% (α.top.naturality ((starPost f a).hom.app X))]
      exact congrArg (fun t => k.lift.morphism.inverseImage.map ((starPost f a).hom.app X) ≫ t) ho }
  map_id _ := Cone.Hom.ext rfl rfl
  map_comp _ _ := Cone.Hom.ext rfl rfl

instance : (sliceConeFunctor (G := G) f a).Faithful where
  map_injective {k l} α β e := by
    have hb : α.base = β.base := congrArg (fun t : (sliceConeFunctor f a).obj k ⟶ (sliceConeFunctor f a).obj l => t.base) e
    apply Cone.Hom.ext hb
    apply Lift.transformation_ext α.base α.top β.top α.over
    rw [hb]
    exact β.over

instance : (sliceConeFunctor (G := G) f a).Full where
  map_surjective {k l} α := by
    have hs := Lift.section_over ((postcompose (F := G) f).map α.base) α.top α.over
    change (k.lift.postSlice f a).section ≫ α.base.app (f.inverseImage.obj a) =
      (l.lift.postSlice f a).section at hs
    rw [Lift.postSlice_section, Lift.postSlice_section] at hs
    let β : k ⟶ l := {
      base := α.base
      top := Lift.mapOfSections α.base hs
      over := Lift.mapOfSections_over α.base hs }
    refine ⟨β, Cone.Hom.ext rfl ?_⟩
    exact Lift.transformation_ext ((postcompose (F := G) f).map α.base)
      ((sliceConeFunctor f a).map β).top α.top ((sliceConeFunctor f a).map β).over α.over
variable [HasBinaryProducts G] [HasPullbacks G]
variable [∀ h : GeometricMorphism G F,
  @MonoidalClosed (Over (h.inverseImage.obj (f.inverseImage.obj a))) inferInstance
    (Over.cartesianMonoidalCategory _).toMonoidalCategory]

instance : (sliceConeFunctor (G := G) f a).EssSurj where
  mem_essImage k := by
    let e := sectionEquivalence k.base (f.inverseImage.obj a)
    let l := e.inverse.obj ⟨k.lift.section⟩
    have hs : (l.postSlice f a).section = k.lift.section := by
      rw [Lift.postSlice_section]
      exact Discrete.eq_of_hom (e.counitIso.app ⟨k.lift.section⟩).hom
    let i : l.postSlice f a ≅ k.lift := {
      hom := Lift.homOfSection hs
      inv := Lift.homOfSection hs.symm
      hom_inv_id := Subsingleton.elim _ _
      inv_hom_id := Subsingleton.elim _ _ }
    exact ⟨⟨k.base, l⟩, ⟨Cone.isoOfLift i⟩⟩

instance : (sliceConeFunctor (G := G) f a).IsEquivalence where

/-- The actual geometric base-change square is a pseudopullback on every source hom category. -/
def slicePseudopullback : GeometricMorphism G (Over (f.inverseImage.obj a)) ≌
    Cone (postcompose (F := G) f) (slice a) :=
  (canonicalConeEquivalence (slice (f.inverseImage.obj a))).trans
    (sliceConeFunctor f a).asEquivalence
end SquareKit.Internal.GeometricMorphism

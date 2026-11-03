import SquareKit.Internal.SliceVaryingBase

/-! The geometric square induced by inverse image on slice categories. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
universe v₁ v₂ v₃ u₁ u₂ u₃
variable {F : Type u₁} {B : Type u₂} {G : Type u₃}
variable [Category.{v₁} F] [Category.{v₂} B] [Category.{v₃} G]
section Products
variable [HasBinaryProducts F] [HasBinaryProducts B]

/-- Inverse image carries the identity display to the identity display. -/
def genericPostIso (f : GeometricMorphism F B) (a : B) :
    (Over.post f.inverseImage).obj (Over.mk (𝟙 a)) ≅ Over.mk (𝟙 (f.inverseImage.obj a)) :=
  Over.isoMk (Iso.refl _) (by simp)

/-- The square comparison carries the actual generic diagonal to the new generic diagonal. -/
theorem genericPost_diagonal (f : GeometricMorphism F B) (a : B) :
    (Over.post f.inverseImage).map (genericSection a) ≫ (starPost f a).hom.app a =
      (genericPostIso f a).hom ≫ genericSection (f.inverseImage.obj a) := by
  apply Over.OverMorphism.ext
  apply prod.hom_ext <;> simp [genericSection, genericPostIso, starPost, prodComparison, ← f.inverseImage.map_comp]

end Products

section Lift
open CategoryTheory.MonoidalCategory
variable [HasTerminal G] [CartesianMonoidalCategory B] [HasPullbacks B]
variable [CartesianMonoidalCategory F] [HasPullbacks F]
variable (f : GeometricMorphism F B) (a : B) [Closed a] [Closed (f.inverseImage.obj a)]
variable {h : GeometricMorphism G F}

/-- Postcompose the actual geometric lift around the base-change square. -/
def Lift.postSlice (k : Lift h (slice (f.inverseImage.obj a))) : Lift (h.comp f) (slice a) where
  morphism := k.morphism.comp (f.onSlices a)
  comparison := (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (starPost f a) k.morphism.inverseImage ≪≫
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft f.inverseImage k.comparison

/-- Base change preserves the extracted section, including the square's comparison maps. -/
theorem Lift.postSlice_section (k : Lift h (slice (f.inverseImage.obj a))) :
    (k.postSlice f a).section = k.section := by
  have ht : (k.postSlice f a).terminalIso.inv ≫
      k.morphism.inverseImage.map (genericPostIso f a).hom = k.terminalIso.inv :=
    (Over.mkIdTerminal.isTerminalObj k.morphism.inverseImage).hom_ext _ _
  dsimp only [Lift.section]
  change (k.postSlice f a).terminalIso.inv ≫
    k.morphism.inverseImage.map ((Over.post f.inverseImage).map (genericSection a)) ≫
      (𝟙 _ ≫ k.morphism.inverseImage.map ((starPost f a).hom.app a) ≫ 𝟙 _ ≫
        k.comparison.hom.app (f.inverseImage.obj a)) = _
  simp only [Category.id_comp]
  rw [← k.morphism.inverseImage.map_comp_assoc, genericPost_diagonal f a,
    k.morphism.inverseImage.map_comp]
  simp only [← Category.assoc, ht]
/-- The square comparison acts on transformations by whiskering with inverse image on slices. -/
def Lift.postSliceFunctor : Lift h (slice (f.inverseImage.obj a)) ⥤ Lift (h.comp f) (slice a) where
  obj k := k.postSlice f a
  map {k l} α := {
    transformation := whiskerLeft (Over.post f.inverseImage) α.transformation
    over := by
      apply NatTrans.ext
      funext X
      have ho := congrArg (fun t => t.app (f.inverseImage.obj X)) α.over
      change α.transformation.app ((Over.star (f.inverseImage.obj a)).obj (f.inverseImage.obj X)) ≫
        l.comparison.hom.app (f.inverseImage.obj X) = k.comparison.hom.app (f.inverseImage.obj X) at ho
      change α.transformation.app ((Over.post f.inverseImage).obj ((Over.star a).obj X)) ≫
        (𝟙 _ ≫ l.morphism.inverseImage.map ((starPost f a).hom.app X) ≫ 𝟙 _ ≫ _) =
        𝟙 _ ≫ k.morphism.inverseImage.map ((starPost f a).hom.app X) ≫ 𝟙 _ ≫ _
      simp only [Category.id_comp]
      rw [← reassoc_of% (α.transformation.naturality ((starPost f a).hom.app X))]
      exact congrArg (fun t => k.morphism.inverseImage.map ((starPost f a).hom.app X) ≫ t) ho }
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _
end Lift
end SquareKit.Internal.GeometricMorphism

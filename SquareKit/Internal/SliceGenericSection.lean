import SquareKit.Internal.SliceSection
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-! The generic section of a slice is the diagonal. Its defining pullback
recovers every object of the slice, including its structure map. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits
universe v u
variable {B : Type u} [Category.{v} B] [HasBinaryProducts B]

/-- The diagonal is a section of the generic object in the slice. -/
def genericSection (a : B) : Over.mk (𝟙 a) ⟶ (Over.star a).obj a :=
  Over.homMk (prod.lift (𝟙 a) (𝟙 a)) (by simp)

/-- The unit of forgetting and forming a constant slice object. -/
def genericUnit {a : B} (Y : Over a) : Y ⟶ (Over.star a).obj Y.left :=
  (Over.forgetAdjStar a).unit.app Y

/-- Every slice object is the inverse image of the diagonal along its structure map. -/
theorem generic_isPullback {a : B} (Y : Over a) :
    IsPullback (genericUnit Y) (Over.mkIdTerminal.from Y)
      ((Over.star a).map Y.hom) (genericSection a) := by
  apply IsPullback.mk'
  · apply Over.OverMorphism.ext
    apply prod.hom_ext <;> simp [genericUnit, genericSection]
  · intro W f g e₁ _
    apply Over.OverMorphism.ext
    have e := congrArg (fun k => k.left ≫ prod.snd) e₁
    simpa [genericUnit] using e
  · intro W f g e
    have h : (f.left ≫ prod.snd) ≫ Y.hom = W.hom := by
      have he := congrArg (fun k => k.left ≫ prod.snd) e
      have hg : g.left = W.hom := by simpa using Over.w g
      simpa [genericSection, hg] using he
    refine ⟨Over.homMk (f.left ≫ prod.snd) h, ?_, Over.mkIdTerminal.hom_ext _ _⟩
    apply Over.OverMorphism.ext
    apply prod.hom_ext
    · simpa [genericUnit, h] using (Over.w f).symm
    · simp [genericUnit]
end SquareKit.Internal.GeometricMorphism

namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe v₁ v₂ u₁ u₂
variable {F : Type u₁} {B : Type u₂} [Category.{v₁} F] [Category.{v₂} B]
variable [HasTerminal F] [CartesianMonoidalCategory B] [HasPullbacks B]
variable {h : GeometricMorphism F B} {a : B} [Closed a]

/-- Left exactness sends the identity display to an actual terminal object. -/
def Lift.terminalIso (k : Lift h (slice a)) :
    k.morphism.inverseImage.obj (Over.mk (𝟙 a)) ≅ ⊤_ F :=
  (Over.mkIdTerminal.isTerminalObj k.morphism.inverseImage).uniqueUpToIso terminalIsTerminal

/-- Pull back the actual diagonal and use the specified comparison over the base. -/
def Lift.section (k : Lift h (slice a)) : ⊤_ F ⟶ h.inverseImage.obj a :=
  k.terminalIso.inv ≫ k.morphism.inverseImage.map (genericSection a) ≫ k.comparison.hom.app a

/-- Compatible geometric transformations preserve the extracted section. -/
theorem Lift.section_natural {k l : Lift h (slice a)} (α : k ⟶ l) : k.section = l.section := by
  have ht : k.terminalIso.inv ≫ α.transformation.app (Over.mk (𝟙 a)) = l.terminalIso.inv :=
    (Over.mkIdTerminal.isTerminalObj l.morphism.inverseImage).hom_ext _ _
  have ho : α.transformation.app ((Over.star a).obj a) ≫ l.comparison.hom.app a =
      k.comparison.hom.app a := congrArg (fun t => t.app a) α.over
  dsimp [Lift.section]
  rw [← ho]
  have hn := α.transformation.naturality (genericSection a)
  rw [reassoc_of% hn]
  simp only [← Category.assoc, ht]
end SquareKit.Internal.GeometricMorphism

namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe v₁ v₂ u₁ u₂
variable {F : Type u₁} {B : Type u₂} [Category.{v₁} F] [Category.{v₂} B]
variable [HasTerminal F] [CartesianMonoidalCategory B] [HasPullbacks B]
variable {h : GeometricMorphism F B} {a : B} [Closed a]

/-- The structure map into the interpreted underlying object. -/
def Lift.value (k : Lift h (slice a)) (Y : Over a) :
    k.morphism.inverseImage.obj Y ⟶ h.inverseImage.obj Y.left :=
  k.morphism.inverseImage.map (genericUnit Y) ≫ k.comparison.hom.app Y.left

/-- Applying a lift to the generic pullback recovers a pullback over its extracted section. -/
theorem Lift.section_isPullback (k : Lift h (slice a)) (Y : Over a) :
    IsPullback (k.value Y) (terminal.from _) (h.inverseImage.map Y.hom) k.section := by
  apply ((generic_isPullback Y).map k.morphism.inverseImage).of_iso
    (Iso.refl _) (k.comparison.app Y.left) k.terminalIso (k.comparison.app a)
  · simp [Lift.value]
  · exact terminal.hom_ext _ _
  · exact k.comparison.hom.naturality Y.hom
  · simp [Lift.section]

/-- Naturality of the recovered underlying-object map. -/
theorem Lift.value_natural (k : Lift h (slice a)) {Y Z : Over a} (f : Y ⟶ Z) :
    k.morphism.inverseImage.map f ≫ k.value Z = k.value Y ≫ h.inverseImage.map f.left := by
  dsimp [Lift.value]
  rw [← Category.assoc, ← k.morphism.inverseImage.map_comp]
  have hn := (Over.forgetAdjStar a).unit.naturality f
  change f ≫ genericUnit Z = genericUnit Y ≫ (Over.star a).map f.left at hn
  rw [hn, k.morphism.inverseImage.map_comp, Category.assoc]
  have hc := k.comparison.hom.naturality f.left
  change k.morphism.inverseImage.map ((Over.star a).map f.left) ≫ _ = _ at hc
  rw [hc, Category.assoc]

variable [HasPullbacks F]

/-- Reconstruct the inverse image as the actual ordinary pullback along the section. -/
def Lift.reconstruction (k : Lift h (slice a)) :
    k.morphism.inverseImage ≅
      Over.post h.inverseImage ⋙ Over.pullback k.section ⋙ Over.forget (⊤_ F) :=
  NatIso.ofComponents (fun Y => (k.section_isPullback Y).isoPullback) (by
    intro Y Z f
    apply pullback.hom_ext
    · change (k.morphism.inverseImage.map f ≫ (k.section_isPullback Z).isoPullback.hom) ≫
        pullback.fst (h.inverseImage.map Z.hom) k.section =
        ((k.section_isPullback Y).isoPullback.hom ≫
        ((Over.pullback k.section).map ((Over.post h.inverseImage).map f)).left) ≫
        pullback.fst (h.inverseImage.map Z.hom) k.section
      rw [Category.assoc, IsPullback.isoPullback_hom_fst, Category.assoc]
      change k.morphism.inverseImage.map f ≫ k.value Z =
        (k.section_isPullback Y).isoPullback.hom ≫
          ((Over.pullback k.section).map ((Over.post h.inverseImage).map f)).left ≫ pullback.fst _ _
      simp only [Over.pullback_map_left, pullback.lift_fst]
      rw [← Category.assoc]
      change k.morphism.inverseImage.map f ≫ k.value Z =
        ((k.section_isPullback Y).isoPullback.hom ≫
          pullback.fst (h.inverseImage.map Y.hom) k.section) ≫ h.inverseImage.map f.left
      rw [IsPullback.isoPullback_hom_fst]
      exact k.value_natural f
    · apply terminal.hom_ext)
end SquareKit.Internal.GeometricMorphism

namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe v₁ v₂ u₁ u₂
variable {F : Type u₁} {B : Type u₂} [Category.{v₁} F] [Category.{v₂} B]
variable [HasTerminal F] [CartesianMonoidalCategory B] [HasPullbacks B]
variable {h : GeometricMorphism F B} {a : B} [Closed a]

/-- A compatible transformation commutes with the recovered value map. -/
theorem Lift.Hom.value {k l : Lift h (slice a)} (α : k ⟶ l) (Y : Over a) :
    α.transformation.app Y ≫ l.value Y = k.value Y := by
  have ho : α.transformation.app ((Over.star a).obj Y.left) ≫ l.comparison.hom.app Y.left =
      k.comparison.hom.app Y.left := congrArg (fun t => t.app Y.left) α.over
  dsimp [Lift.value]
  rw [← reassoc_of% (α.transformation.naturality (genericUnit Y)), ho]

/-- Thinness of the pseudo-slice into an étale morphism follows from pullback uniqueness. -/
instance {k l : Lift h (slice a)} : Subsingleton (k ⟶ l) where
  allEq α β := by
    apply Lift.Hom.ext
    apply NatTrans.ext
    funext Y
    apply (l.section_isPullback Y).hom_ext
    · exact (α.value Y).trans (β.value Y).symm
    · exact terminal.hom_ext _ _

/-- On a constant slice object, forgetting the generic coordinate recovers the base comparison. -/
theorem Lift.value_star_snd (k : Lift h (slice a)) (X : B) :
    k.value ((Over.star a).obj X) ≫ h.inverseImage.map prod.snd = k.comparison.hom.app X := by
  dsimp [Lift.value]
  rw [Category.assoc, ← k.comparison.hom.naturality prod.snd, ← Category.assoc]
  change (k.morphism.inverseImage.map (genericUnit ((Over.star a).obj X)) ≫
    k.morphism.inverseImage.map ((Over.star a).map prod.snd)) ≫ _ = _
  rw [← k.morphism.inverseImage.map_comp]
  have ht := (Over.forgetAdjStar a).right_triangle_components X
  rw [Over.forgetAdjStar_counit_app] at ht
  change genericUnit ((Over.star a).obj X) ≫ (Over.star a).map prod.snd = 𝟙 _ at ht
  rw [ht, k.morphism.inverseImage.map_id, Category.id_comp]
end SquareKit.Internal.GeometricMorphism

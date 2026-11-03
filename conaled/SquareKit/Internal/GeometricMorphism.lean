import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! Geometric morphisms retain both adjoints and left exactness. Transformations
have the direction of their inverse images. The definitions apply to arbitrary
categories; topos hypotheses belong to constructions that require them. -/
set_option autoImplicit false
namespace SquareKit.Internal
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
universe v₁ v₂ v₃ u₁ u₂ u₃

/-- A geometric morphism from `F` to `B`, with specified adjunction. -/
structure GeometricMorphism (F : Type u₁) (B : Type u₂)
    [Category.{v₁} F] [Category.{v₂} B] where
  inverseImage : B ⥤ F
  directImage : F ⥤ B
  adjunction : inverseImage ⊣ directImage
  leftExact : PreservesFiniteLimits inverseImage

attribute [instance] GeometricMorphism.leftExact
namespace GeometricMorphism
variable {F : Type u₁} {B : Type u₂} {C : Type u₃}
variable [Category.{v₁} F] [Category.{v₂} B] [Category.{v₃} C]

instance (h : GeometricMorphism F B) : h.inverseImage.IsLeftAdjoint := h.adjunction.isLeftAdjoint
instance (h : GeometricMorphism F B) : h.directImage.IsRightAdjoint := h.adjunction.isRightAdjoint

/-- All natural transformations of inverse images are retained, not just isomorphisms. -/
instance : Category (GeometricMorphism F B) where
  Hom h k := h.inverseImage ⟶ k.inverseImage
  id h := 𝟙 h.inverseImage
  comp α β := α ≫ β

/-- Identity geometric morphism. -/
def identity (F : Type u₁) [Category.{v₁} F] : GeometricMorphism F F where
  inverseImage := 𝟭 F
  directImage := 𝟭 F
  adjunction := Adjunction.id
  leftExact := inferInstance

/-- Composition reverses the order of inverse images. -/
def comp (h : GeometricMorphism F B) (g : GeometricMorphism B C) :
    GeometricMorphism F C where
  inverseImage := g.inverseImage ⋙ h.inverseImage
  directImage := h.directImage ⋙ g.directImage
  adjunction := g.adjunction.comp h.adjunction
  leftExact := inferInstance

/-- Precomposition on the full category of geometric morphisms. -/
def precompose (h : GeometricMorphism F B) :
    GeometricMorphism B C ⥤ GeometricMorphism F C where
  obj g := h.comp g
  map α := whiskerRight α h.inverseImage
  map_id g := by apply NatTrans.ext; funext X; exact h.inverseImage.map_id _
  map_comp α β := by apply NatTrans.ext; funext X; exact h.inverseImage.map_comp _ _

/-- Postcomposition uses left whiskering on inverse images. -/
def postcompose (g : GeometricMorphism B C) :
    GeometricMorphism F B ⥤ GeometricMorphism F C where
  obj h := h.comp g
  map α := whiskerLeft g.inverseImage α

/-- A lift over a fixed base retains its invertible comparison. -/
structure Lift (h : GeometricMorphism F B) (π : GeometricMorphism C B) where
  morphism : GeometricMorphism F C
  comparison : π.inverseImage ⋙ morphism.inverseImage ≅ h.inverseImage

namespace Lift
variable {h : GeometricMorphism F B} {π : GeometricMorphism C B}

/-- Compatibility with the specified comparison is the pseudo-slice condition. -/
structure Hom (k l : Lift h π) where
  transformation : k.morphism ⟶ l.morphism
  over : whiskerLeft π.inverseImage transformation ≫ l.comparison.hom = k.comparison.hom

@[ext] theorem Hom.ext {k l : Lift h π} {α β : Hom k l}
    (eq : α.transformation = β.transformation) : α = β := by
  cases α; cases β; cases eq; rfl

instance : Category (Lift h π) where
  Hom := Hom
  id k := ⟨𝟙 _, by ext X; exact Category.id_comp _⟩
  comp α β := ⟨α.transformation ≫ β.transformation, by
    change (whiskerLeft π.inverseImage α.transformation ≫
      whiskerLeft π.inverseImage β.transformation) ≫ _ = _
    rw [Category.assoc, β.over, α.over]⟩
  id_comp _ := Hom.ext (Category.id_comp _)
  comp_id _ := Hom.ext (Category.comp_id _)
  assoc _ _ _ := Hom.ext (Category.assoc _ _ _)

/-- The forgetful functor keeps the actual geometric transformation. -/
def forget (h : GeometricMorphism F B) (π : GeometricMorphism C B) :
    Lift h π ⥤ GeometricMorphism F C where
  obj k := k.morphism
  map α := α.transformation

instance : (forget h π).Faithful where
  map_injective := fun eq => Hom.ext eq
end Lift
end GeometricMorphism
end SquareKit.Internal

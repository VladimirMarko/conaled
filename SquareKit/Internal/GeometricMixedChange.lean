import SquareKit.Internal.GeometricSlice
import SquareKit.MixedBaseChange

/-! Ambient inverse image commutes with context substitution by the actual
pullback comparison, retaining both projections and hence their witnesses. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits
universe v₁ v₂ u₁ u₂
variable {F : Type u₁} {B : Type u₂} [Category.{v₁} F] [Category.{v₂} B]
variable [HasPullbacks F] [HasPullbacks B]
variable (h : GeometricMorphism F B) {X Y : B} (σ : X ⟶ Y)

/-- The mixed square for ambient inverse image and context pullback. -/
def pullbackPost : Over.pullback σ ⋙ Over.post h.inverseImage ≅
    Over.post h.inverseImage ⋙ Over.pullback (h.inverseImage.map σ) :=
  MixedBaseChange.iso h.inverseImage σ

/-- The mixed comparison retains the displayed object's projection. -/
@[reassoc (attr := simp)] theorem pullbackPost_fst (Z : Over Y) :
    ((pullbackPost h σ).hom.app Z).left ≫ pullback.fst (h.inverseImage.map Z.hom) (h.inverseImage.map σ) =
      h.inverseImage.map (pullback.fst Z.hom σ) :=
  MixedBaseChange.comparison_fst h.inverseImage σ Z

/-- It also retains the substituted context projection. -/
@[reassoc (attr := simp)] theorem pullbackPost_snd (Z : Over Y) :
    ((pullbackPost h σ).hom.app Z).left ≫ pullback.snd (h.inverseImage.map Z.hom) (h.inverseImage.map σ) =
      h.inverseImage.map (pullback.snd Z.hom σ) :=
  MixedBaseChange.comparison_snd h.inverseImage σ Z
end SquareKit.Internal.GeometricMorphism

namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe v₁ v₂ u₁ u₂
variable {F : Type u₁} {B : Type u₂} [Category.{v₁} F] [Category.{v₂} B]
variable [HasPullbacks F] [HasPullbacks B]
variable (h : GeometricMorphism F B) {X Y : B} (σ : X ⟶ Y)
local instance mixedBaseSliceCartesian : CartesianMonoidalCategory (Over Y) := Over.cartesianMonoidalCategory Y
local instance mixedSourceSliceCartesian : CartesianMonoidalCategory (Over (h.inverseImage.obj Y)) :=
  Over.cartesianMonoidalCategory _
variable [Closed (Over.mk σ)] [Closed (Over.mk (h.inverseImage.map σ))]

/-- Both routes are actual geometric morphisms with constructed right adjoints. -/
def mixedGeometricIso : (h.onSlices X).comp (along σ) ≅
    (along (h.inverseImage.map σ)).comp (h.onSlices Y) where
  hom := (pullbackPost h σ).hom
  inv := (pullbackPost h σ).inv
  hom_inv_id := (pullbackPost h σ).hom_inv_id
  inv_hom_id := (pullbackPost h σ).inv_hom_id
end SquareKit.Internal.GeometricMorphism

namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits
universe v₁ v₂ v₃ u₁ u₂ u₃
variable {F : Type u₁} {B : Type u₂} {C : Type u₃}
variable [Category.{v₁} F] [Category.{v₂} B] [Category.{v₃} C]
variable [HasPullbacks F] [HasPullbacks B] [HasPullbacks C]

/-- Identity ambient inverse image gives the identity mixed comparison. -/
theorem pullbackPost_identity {X Y : B} (σ : X ⟶ Y) (Z : Over Y) :
    ((pullbackPost (identity B) σ).hom.app Z).left = 𝟙 (pullback Z.hom σ) :=
  MixedBaseChange.identity σ Z

/-- Composite ambient inverse image gives the pasted mixed comparisons, retaining both projections. -/
theorem pullbackPost_composition (f : GeometricMorphism F B) (g : GeometricMorphism B C)
    {X Y : C} (σ : X ⟶ Y) (Z : Over Y) :
    ((pullbackPost (f.comp g) σ).hom.app Z).left =
      f.inverseImage.map ((pullbackPost g σ).hom.app Z).left ≫
        ((pullbackPost f (g.inverseImage.map σ)).hom.app ((Over.post g.inverseImage).obj Z)).left :=
  MixedBaseChange.composition g.inverseImage f.inverseImage σ Z
end SquareKit.Internal.GeometricMorphism

namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Limits
universe v₁ v₂ u₁ u₂
variable {F : Type u₁} {B : Type u₂} [Category.{v₁} F] [Category.{v₂} B]
variable [HasPullbacks F] [HasPullbacks B]
variable (h : GeometricMorphism F B) {A X Y Z : B} (p : A ⟶ Y) (σ : X ⟶ Y) (τ : Z ⟶ X)

/-- Pasting the two mixed squares and then flattening the context pullbacks.
The lift records both the transported witness and the final context projection. -/
def mixedContextPaste :
    h.inverseImage.obj (pullback (pullback.snd p σ) τ) ⟶
      pullback (h.inverseImage.map p) (h.inverseImage.map (τ ≫ σ)) :=
  MixedBaseChange.contextPaste h.inverseImage p σ τ

/-- Context-composition coherence for the mixed ambient/context square. -/
theorem pullbackPost_context_composition :
    h.inverseImage.map (SquareKit.Family.compositionIso p σ τ).hom ≫
      pullbackComparison h.inverseImage p (τ ≫ σ) = mixedContextPaste h p σ τ :=
  MixedBaseChange.context_composition h.inverseImage p σ τ
end SquareKit.Internal.GeometricMorphism

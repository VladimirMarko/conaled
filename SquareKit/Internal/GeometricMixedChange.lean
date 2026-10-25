import SquareKit.Internal.GeometricSlice
import SquareKit.Family
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

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
  NatIso.ofComponents (fun Z =>
    Over.isoMk (PreservesPullback.iso h.inverseImage Z.hom σ) (PreservesPullback.iso_hom_snd _ _ _)) (by
      intro Z W f
      apply Over.OverMorphism.ext
      change h.inverseImage.map (pullback.lift (pullback.fst Z.hom σ ≫ f.left)
        (pullback.snd Z.hom σ) _) ≫ (PreservesPullback.iso h.inverseImage W.hom σ).hom =
          (PreservesPullback.iso h.inverseImage Z.hom σ).hom ≫
            pullback.lift (pullback.fst (h.inverseImage.map Z.hom) (h.inverseImage.map σ) ≫ h.inverseImage.map f.left)
              (pullback.snd (h.inverseImage.map Z.hom) (h.inverseImage.map σ)) _
      apply pullback.hom_ext
      · simp only [Category.assoc, PreservesPullback.iso_hom_fst, pullback.lift_fst,
          ← h.inverseImage.map_comp]
        rw [h.inverseImage.map_comp, ← Category.assoc, PreservesPullback.iso_hom_fst]
      · simp only [Category.assoc, PreservesPullback.iso_hom_snd, pullback.lift_snd,
          ← h.inverseImage.map_comp])

/-- The mixed comparison retains the displayed object's projection. -/
@[reassoc (attr := simp)] theorem pullbackPost_fst (Z : Over Y) :
    ((pullbackPost h σ).hom.app Z).left ≫ pullback.fst (h.inverseImage.map Z.hom) (h.inverseImage.map σ) =
      h.inverseImage.map (pullback.fst Z.hom σ) :=
  PreservesPullback.iso_hom_fst _ _ _

/-- It also retains the substituted context projection. -/
@[reassoc (attr := simp)] theorem pullbackPost_snd (Z : Over Y) :
    ((pullbackPost h σ).hom.app Z).left ≫ pullback.snd (h.inverseImage.map Z.hom) (h.inverseImage.map σ) =
      h.inverseImage.map (pullback.snd Z.hom σ) :=
  PreservesPullback.iso_hom_snd _ _ _
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
    ((pullbackPost (identity B) σ).hom.app Z).left = 𝟙 (pullback Z.hom σ) := by
  change pullbackComparison (𝟭 B) Z.hom σ = 𝟙 _
  apply pullback.hom_ext <;> simp [pullbackComparison]

/-- Composite ambient inverse image gives the pasted mixed comparisons, retaining both projections. -/
theorem pullbackPost_composition (f : GeometricMorphism F B) (g : GeometricMorphism B C)
    {X Y : C} (σ : X ⟶ Y) (Z : Over Y) :
    ((pullbackPost (f.comp g) σ).hom.app Z).left =
      f.inverseImage.map ((pullbackPost g σ).hom.app Z).left ≫
        ((pullbackPost f (g.inverseImage.map σ)).hom.app ((Over.post g.inverseImage).obj Z)).left :=
  pullbackComparison_comp g.inverseImage f.inverseImage Z.hom σ
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
  pullbackComparison h.inverseImage (pullback.snd p σ) τ ≫
    pullback.lift
      (pullback.fst (h.inverseImage.map (pullback.snd p σ)) (h.inverseImage.map τ) ≫
        pullbackComparison h.inverseImage p σ ≫
          pullback.fst (h.inverseImage.map p) (h.inverseImage.map σ))
      (pullback.snd (h.inverseImage.map (pullback.snd p σ)) (h.inverseImage.map τ)) (by
        simp only [Category.assoc, pullbackComparison_comp_fst]
        rw [← h.inverseImage.map_comp, pullback.condition, h.inverseImage.map_comp,
          ← Category.assoc, pullback.condition, Category.assoc, ← h.inverseImage.map_comp])

/-- Context-composition coherence for the mixed ambient/context square. -/
theorem pullbackPost_context_composition :
    h.inverseImage.map (SquareKit.Family.compositionIso p σ τ).hom ≫
      pullbackComparison h.inverseImage p (τ ≫ σ) = mixedContextPaste h p σ τ := by
  apply pullback.hom_ext
  · simp only [mixedContextPaste, Category.assoc, pullback.lift_fst,
      pullbackComparison_comp_fst, ← h.inverseImage.map_comp]
    rw [← Category.assoc, pullbackComparison_comp_fst, ← h.inverseImage.map_comp]
    exact congrArg h.inverseImage.map (SquareKit.Family.compositionIso_comparison p σ τ)
  · simp only [mixedContextPaste, Category.assoc, pullback.lift_snd,
      pullbackComparison_comp_snd, ← h.inverseImage.map_comp]
    congr 1
    exact SquareKit.Family.compositionIso_display p σ τ
end SquareKit.Internal.GeometricMorphism

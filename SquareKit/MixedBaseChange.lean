import SquareKit.Family
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-! Mixed ambient/context comparison without a chosen adjoint. Construction and
pasting require only pullbacks; preservation is used only for invertibility. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SquareKit.MixedBaseChange
open CategoryTheory Limits
universe u₁ u₂ u₃ v₁ v₂ v₃
variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
variable [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
variable [HasPullbacks C] [HasPullbacks D] [HasPullbacks E]

/-- The universal pair is a comparison even when the ambient functor has no adjoint. -/
def comparison (F : C ⥤ D) {X Y : C} (σ : X ⟶ Y) :
    Over.pullback σ ⋙ Over.post F ⟶ Over.post F ⋙ Over.pullback (F.map σ) where
  app Z := Over.homMk (pullbackComparison F Z.hom σ)
    (pullbackComparison_comp_snd F Z.hom σ)
  naturality Z W k := by
    apply Over.OverMorphism.ext
    change F.map (pullback.lift (pullback.fst Z.hom σ ≫ k.left)
      (pullback.snd Z.hom σ) _) ≫ pullbackComparison F W.hom σ =
        pullbackComparison F Z.hom σ ≫
          pullback.lift (pullback.fst (F.map Z.hom) (F.map σ) ≫ F.map k.left)
            (pullback.snd (F.map Z.hom) (F.map σ)) _
    apply pullback.hom_ext
    · simp only [Category.assoc, pullbackComparison_comp_fst, pullback.lift_fst,
        ← F.map_comp]
      rw [F.map_comp, ← Category.assoc, pullbackComparison_comp_fst]
    · simp only [Category.assoc, pullbackComparison_comp_snd, pullback.lift_snd,
        ← F.map_comp]

@[reassoc (attr := simp)] theorem comparison_fst (F : C ⥤ D) {X Y : C}
    (σ : X ⟶ Y) (Z : Over Y) :
    ((comparison F σ).app Z).left ≫ pullback.fst (F.map Z.hom) (F.map σ) =
      F.map (pullback.fst Z.hom σ) := pullbackComparison_comp_fst _ _ _

@[reassoc (attr := simp)] theorem comparison_snd (F : C ⥤ D) {X Y : C}
    (σ : X ⟶ Y) (Z : Over Y) :
    ((comparison F σ).app Z).left ≫ pullback.snd (F.map Z.hom) (F.map σ) =
      F.map (pullback.snd Z.hom σ) := pullbackComparison_comp_snd _ _ _

/-- Preservation of these pullbacks supplies invertibility, independently of adjoints. -/
def iso (F : C ⥤ D) [PreservesLimitsOfShape WalkingCospan F]
    {X Y : C} (σ : X ⟶ Y) :
    Over.pullback σ ⋙ Over.post F ≅ Over.post F ⋙ Over.pullback (F.map σ) :=
  NatIso.ofComponents (fun Z => Over.isoMk (PreservesPullback.iso F Z.hom σ)
    (PreservesPullback.iso_hom_snd _ _ _)) (by
      intro Z W k
      exact (comparison F σ).naturality k)

theorem iso_hom (F : C ⥤ D) [PreservesLimitsOfShape WalkingCospan F]
    {X Y : C} (σ : X ⟶ Y) : (iso F σ).hom = comparison F σ := rfl

theorem identity {X Y : C} (σ : X ⟶ Y) (Z : Over Y) :
    ((comparison (𝟭 C) σ).app Z).left = 𝟙 (pullback Z.hom σ) := by
  apply pullback.hom_ext <;> simp [comparison, pullbackComparison]

theorem composition (F : C ⥤ D) (G : D ⥤ E) {X Y : C} (σ : X ⟶ Y) (Z : Over Y) :
    ((comparison (F ⋙ G) σ).app Z).left =
      G.map ((comparison F σ).app Z).left ≫
        ((comparison G (F.map σ)).app ((Over.post F).obj Z)).left :=
  pullbackComparison_comp F G Z.hom σ

/-- Paste both ambient/context squares while retaining the two final projections. -/
def contextPaste (F : C ⥤ D) {A X Y Z : C} (p : A ⟶ Y) (σ : X ⟶ Y) (τ : Z ⟶ X) :
    F.obj (pullback (pullback.snd p σ) τ) ⟶ pullback (F.map p) (F.map (τ ≫ σ)) :=
  pullbackComparison F (pullback.snd p σ) τ ≫
    pullback.lift
      (pullback.fst (F.map (pullback.snd p σ)) (F.map τ) ≫
        pullbackComparison F p σ ≫ pullback.fst (F.map p) (F.map σ))
      (pullback.snd (F.map (pullback.snd p σ)) (F.map τ)) (by
        simp only [Category.assoc, pullbackComparison_comp_fst]
        rw [← F.map_comp, pullback.condition, F.map_comp,
          ← Category.assoc, pullback.condition, Category.assoc, ← F.map_comp])

theorem context_composition (F : C ⥤ D) {A X Y Z : C}
    (p : A ⟶ Y) (σ : X ⟶ Y) (τ : Z ⟶ X) :
    F.map (Family.compositionIso p σ τ).hom ≫ pullbackComparison F p (τ ≫ σ) =
      contextPaste F p σ τ := by
  apply pullback.hom_ext
  · simp only [contextPaste, Category.assoc, pullback.lift_fst,
      pullbackComparison_comp_fst, ← F.map_comp]
    rw [← Category.assoc, pullbackComparison_comp_fst, ← F.map_comp]
    exact congrArg F.map (Family.compositionIso_comparison p σ τ)
  · simp only [contextPaste, Category.assoc, pullback.lift_snd,
      pullbackComparison_comp_snd, ← F.map_comp]
    exact congrArg F.map (Family.compositionIso_display p σ τ)

end SquareKit.MixedBaseChange

import SquareKit.Internal.PathTransport.TwoFamily
import Mathlib.CategoryTheory.Bicategory.Product
/-! The family of two endpoints retains the full product of fiber 2-categories. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
variable {A B : Type u} [Bicategory.{w,v} A] [Bicategory.{w,v} B]
    [Bicategory.Strict A] [Bicategory.Strict B]
/-- Apply a strict fiber functor independently to both endpoints. -/
def doubleFunctor (F : StrictPseudofunctor A B) : StrictPseudofunctor (A × A) (B × B) :=
  StrictPseudofunctor.mk'' {
    obj := fun a => (F.obj a.1, F.obj a.2)
    map := fun f => (F.map f.1, F.map f.2)
    map₂ := fun α => (F.map₂ α.1, F.map₂ α.2)
    map₂_id := fun f => by exact Prod.ext (F.map₂_id f.1) (F.map₂_id f.2)
    map₂_comp := fun α β => by exact Prod.ext (F.map₂_comp α.1 β.1) (F.map₂_comp α.2 β.2)
    map_id := fun a => by exact Prod.ext (F.map_id a.1) (F.map_id a.2)
    map_comp := fun f g => by exact Prod.ext (F.map_comp f.1 g.1) (F.map_comp f.2 g.2)
    map₂_whisker_left := fun f g h α => by
      apply Prod.ext
      · simp [F.mapComp_eq_eqToIso]
      · simp [F.mapComp_eq_eqToIso]
    map₂_whisker_right := fun α h => by
      apply Prod.ext
      · simp [F.mapComp_eq_eqToIso]
      · simp [F.mapComp_eq_eqToIso]
  }
/-- Both endpoint components retain the original higher transformation. -/
def doubleTrans {F G : StrictPseudofunctor A B} (η : StrictTwoTransformation.Trans F G) :
    StrictTwoTransformation.Trans (doubleFunctor F) (doubleFunctor G) where
  app a := (η.app a.1, η.app a.2)
  naturality f := Prod.ext (η.naturality f.1) (η.naturality f.2)
  naturality₂ α := by
    apply Prod.ext
    · simpa [doubleFunctor] using η.naturality₂ α.1
    · simpa [doubleFunctor] using η.naturality₂ α.2

/-- Taking a product with itself preserves the full strict higher action. -/
def doubleClassifier : StrictPseudofunctor StrictTwoCategory.{u,v,w} StrictTwoCategory.{u,v,w} :=
  StrictPseudofunctor.mk'' {
    obj := fun A => ⟨A × A⟩
    map := fun F => doubleFunctor F
    map₂ := fun η => doubleTrans η
    map₂_id := fun F => by apply StrictTwoTransformation.Trans.ext; intro a; rfl
    map₂_comp := fun η θ => by apply StrictTwoTransformation.Trans.ext; intro a; rfl
    map_id := fun A => StrictTwoTransformation.functor_ext rfl
    map_comp := fun F G => StrictTwoTransformation.functor_ext rfl
    map₂_whisker_left := fun F G H η => by
      apply StrictTwoTransformation.Trans.ext; intro a
      repeat rw [StrictTwoTransformation.Trans.comp_app]
      repeat rw [StrictTwoTransformation.Trans.eqToHom_app]
      change _ = 𝟙 _ ≫ _ ≫ 𝟙 _
      simp
      rfl
    map₂_whisker_right := fun η H => by
      apply StrictTwoTransformation.Trans.ext; intro a
      repeat rw [StrictTwoTransformation.Trans.comp_app]
      repeat rw [StrictTwoTransformation.Trans.eqToHom_app]
      change _ = 𝟙 _ ≫ _ ≫ 𝟙 _
      simp
      rfl
  }
universe uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Bicategory.Strict Γ]

/-- Two endpoints of one dependent fiber, with their common base action. -/
def endpointFamily (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ) : Family Γ :=
  F.comp doubleClassifier

theorem endpointFamily_reindex {Δ : Type*} [Bicategory Δ] [Bicategory.Strict Δ]
    (σ : StrictPseudofunctor Δ Γ) (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ) :
    endpointFamily (reindex σ F) = reindex σ (endpointFamily F) :=
  StrictTwoTransformation.functor_ext rfl

instance endpointFiberGroupoid (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
    [∀ γ, IsGroupoid (F.obj γ)] (γ : Γ) : IsGroupoid ((endpointFamily F).obj γ) := by
  change IsGroupoid (F.obj γ × F.obj γ)
  infer_instance

instance endpointFiberLocallyGroupoid (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
    [∀ γ, Bicategory.IsLocallyGroupoid (F.obj γ)] (γ : Γ) :
    Bicategory.IsLocallyGroupoid ((endpointFamily F).obj γ) := by
  intro a b
  change IsGroupoid ((a.1 ⟶ b.1) × (a.2 ⟶ b.2))
  infer_instance
end SquareKit.Internal.PathTransport.TwoFamily

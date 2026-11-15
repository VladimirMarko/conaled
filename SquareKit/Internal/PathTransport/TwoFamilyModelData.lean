import SquareKit.Internal.PathTransport.TwoFamilySigmaReindex
import SquareKit.Internal.PathTransport.TwoFamilySectionLaws
/-! Small strict two-groupoidal contexts and all admitted higher families.
Context extension, constants, reindexing, and dependent sums retain their full
higher structure. The guarded-source model is assembled separately. -/
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
def constantFamily (Γ : Type u) [Bicategory.{u,u} Γ] [Strict Γ] (C : StrictTwoCategory.{u,u,u}) :
    TwoFamily.Family Γ := StrictPseudofunctor.mk'' {
  obj := fun _ => C
  map := fun _ => StrictPseudofunctor.id C
  map₂ := fun _ => 𝟙 (StrictPseudofunctor.id C)
  map₂_id := fun _ => rfl
  map₂_comp := fun _ _ => (Category.id_comp _).symm
  map_id := fun _ => rfl
  map_comp := fun _ _ => (StrictTwoTransformation.functor_comp_id _).symm
  map₂_whisker_left := fun _ _ _ _ => by
    apply StrictTwoTransformation.Trans.ext; intro a
    repeat rw [StrictTwoTransformation.Trans.comp_app]
    repeat rw [StrictTwoTransformation.Trans.eqToHom_app]
    change (𝟙 a : a ⟶ a) = 𝟙 a ≫ 𝟙 a ≫ 𝟙 a
    simp
  map₂_whisker_right := fun _ _ => by
    apply StrictTwoTransformation.Trans.ext; intro a
    repeat rw [StrictTwoTransformation.Trans.comp_app]
    repeat rw [StrictTwoTransformation.Trans.eqToHom_app]
    change (𝟙 a : a ⟶ a) = 𝟙 a ≫ 𝟙 a ≫ 𝟙 a
    simp
}

structure Context extends StrictTwoCategory.{u,u,u} where
  [groupoid : IsGroupoid carrier]
  [locallyGroupoid : IsLocallyGroupoid carrier]
attribute [instance] Context.groupoid Context.locallyGroupoid
instance : CoeSort Context (Type u) := ⟨fun Γ => Γ.carrier⟩
instance (Γ : Context) : Bicategory Γ := Γ.bicategory
instance (Γ : Context) : Strict Γ := Γ.strict
instance (Γ : Context) : IsGroupoid Γ := Γ.groupoid
instance (Γ : Context) : IsLocallyGroupoid Γ := Γ.locallyGroupoid

def Context.empty : Context.{u} where
  carrier := LocallyDiscrete (Discrete PUnit.{u+1})
  bicategory := inferInstance
  strict := inferInstance
  groupoid := by
    refine ⟨fun f => ?_⟩
    exact ⟨⟨⟨inv f.as⟩, Discrete.ext (IsIso.hom_inv_id f.as), Discrete.ext (IsIso.inv_hom_id f.as)⟩⟩
  locallyGroupoid := by
    intro a b
    change IsGroupoid (Discrete (a.as ⟶ b.as))
    infer_instance

structure Family (Γ : Context.{u}) where
  data : TwoFamily.Family.{u,u,u,u,u,u} Γ
  [groupoid : ∀ γ, IsGroupoid (data.obj γ)]
  [locallyGroupoid : ∀ γ, IsLocallyGroupoid (data.obj γ)]
attribute [instance] Family.groupoid Family.locallyGroupoid

namespace Family
variable {Γ Δ : Context.{u}}
def reindex (A : Family Γ) (σ : StrictPseudofunctor Δ Γ) : Family Δ where
  data := TwoFamily.reindex σ A.data
  groupoid := fun δ => A.groupoid (σ.obj δ)
  locallyGroupoid := fun δ => A.locallyGroupoid (σ.obj δ)

def total (A : Family Γ) : Context where
  carrier := TwoFamily.Total A.data
  bicategory := inferInstance
  strict := inferInstance
  groupoid := inferInstance
  locallyGroupoid := inferInstance

@[ext] theorem ext {A B : Family Γ} (h : A.data = B.data) : A = B := by
  cases A
  cases B
  cases h
  rfl

def sigma (A : Family Γ) (B : Family A.total) : Family Γ where
  data := TwoFamily.sigmaFamily A.data B.data
  groupoid := fun γ => inferInstanceAs (IsGroupoid (TwoFamily.Total
    (TwoFamily.fiberRestriction A.data γ B.data)))
  locallyGroupoid := fun γ => inferInstanceAs (IsLocallyGroupoid (TwoFamily.Total
    (TwoFamily.fiberRestriction A.data γ B.data)))
def constant (Γ C : Context.{u}) : Family Γ where
  data := constantFamily Γ C.toStrictTwoCategory
  groupoid := fun _ => C.groupoid
  locallyGroupoid := fun _ => C.locallyGroupoid

theorem reindex_id (A : Family Γ) : A.reindex (StrictPseudofunctor.id Γ) = A :=
  Family.ext (TwoFamily.reindex_id A.data)

theorem reindex_comp {Θ : Context.{u}} (A : Family Γ)
    (σ : StrictPseudofunctor Δ Γ) (τ : StrictPseudofunctor Θ Δ) :
    (A.reindex σ).reindex τ = A.reindex (τ.comp σ) :=
  Family.ext (TwoFamily.reindex_comp A.data σ τ)

theorem constant_reindex (C : Context.{u}) (σ : StrictPseudofunctor Δ Γ) :
    (constant Γ C).reindex σ = constant Δ C :=
  Family.ext (StrictTwoTransformation.functor_ext rfl)

theorem sigma_reindex (A : Family Γ) (B : Family A.total) (σ : StrictPseudofunctor Δ Γ) :
    (A.reindex σ).sigma (B.reindex (TwoFamily.reindexHigher A.data σ)) =
      (A.sigma B).reindex σ :=
  Family.ext (TwoFamily.sigmaFamily_reindex A.data σ B.data)

end Family
end SquareKit.Internal.PathTransport.HigherInterpretation

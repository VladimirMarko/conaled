import SquareKit.Internal.PathTransport.ComparisonContext

noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

namespace Section
variable {Γ Δ : Type u} [Category.{u} Γ] [Category.{u} Δ]
    {A B C : Γ ⥤ Grpd.{u,u}}

theorem familyImage_comp (s : Section A) (α : A ⟶ B) (β : B ⟶ C) :
    s.familyImage (α ≫ β) = (s.familyImage α).familyImage β := by
  apply lift_injective
  simp only [familyImage_lift, whiskerRight_comp, Grothendieck.map_comp_eq,
    CategoryTheory.Functor.assoc]

theorem familyImage_id (s : Section A) : s.familyImage (𝟙 A) = s := by
  apply lift_injective
  simp only [familyImage_lift, whiskerRight_id', Grothendieck.map_id_eq,
    CategoryTheory.Functor.comp_id]

theorem familyImage_eqToHom (s : Section A) (h : A = B) :
    s.familyImage (eqToHom h) = cast (congrArg Section h) s := by
  cases h
  exact familyImage_id s

theorem familyImage_reindex (s : Section A) (α : A ⟶ B) (σ : Δ ⥤ Γ) :
    (s.reindex σ).familyImage (whiskerLeft σ α) = (s.familyImage α).reindex σ := rfl

theorem cast_reindex (s : Section A) {F G : Δ ⥤ Γ} (h : F = G) :
    cast (congrArg Section (congrArg (· ⋙ A) h)) (s.reindex F) = s.reindex G := by
  cases h
  rfl

end Section

namespace Comparison
namespace Family
variable {Γ Δ : Context.{u}}

def reindex (A : Family Γ) (σ : Substitution Δ Γ) : Family Δ where
  left := σ.left ⋙ A.left
  right := σ.right ⋙ A.right
  map := whiskerLeft σ.left A.map ≫ eqToHom (congrArg (· ⋙ A.right) σ.commutes)

@[simp] theorem reindex_id (A : Family Γ) : A.reindex (Substitution.id Γ) = A := by
  apply Family.ext rfl rfl
  apply heq_of_eq
  simp [reindex, Substitution.id]

theorem reindex_comp {Θ : Context.{u}} (A : Family Γ)
    (σ : Substitution Δ Γ) (τ : Substitution Θ Δ) :
    (A.reindex σ).reindex τ = A.reindex (Substitution.comp σ τ) := by
  refine @Family.ext _ ((A.reindex σ).reindex τ) (A.reindex (Substitution.comp σ τ)) rfl rfl ?_
  apply heq_of_eq
  apply NatTrans.ext
  funext γ
  dsimp [reindex, Substitution.comp]
  simp only [Category.assoc, eqToHom_app, eqToHom_trans]

end Family

namespace Section
variable {Γ Δ : Context.{u}} {A : Family Γ}

/-- Reindex both interpretations and derive compatibility from the commuting
substitution square; no new section-comparison premise is supplied. -/
def reindex (s : Section A) (σ : Substitution Δ Γ) : Section (A.reindex σ) where
  left := s.left.reindex σ.left
  right := s.right.reindex σ.right
  commutes := by
    dsimp [Family.reindex]
    rw [GroupoidModel.Section.familyImage_comp,
      GroupoidModel.Section.familyImage_reindex,
      GroupoidModel.Section.familyImage_eqToHom, s.commutes]
    exact GroupoidModel.Section.cast_reindex s.right σ.commutes

theorem hext {B : Family Γ} (h : A = B) {s : Section A} {t : Section B}
    (hl : HEq s.left t.left) (hr : HEq s.right t.right) : HEq s t := by
  cases h
  apply heq_of_eq
  exact Section.ext (eq_of_heq hl) (eq_of_heq hr)

theorem reindex_id (s : Section A) : HEq (s.reindex (Substitution.id Γ)) s :=
  hext A.reindex_id HEq.rfl HEq.rfl

theorem reindex_comp {Θ : Context.{u}} (s : Section A)
    (σ : Substitution Δ Γ) (τ : Substitution Θ Δ) :
    HEq ((s.reindex σ).reindex τ) (s.reindex (Substitution.comp σ τ)) :=
  hext (A.reindex_comp σ τ) HEq.rfl HEq.rfl

end Section
end Comparison
end SquareKit.Internal.PathTransport.GroupoidModel

import SquareKit.Internal.Cubical.ComprehensionTransport

namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

theorem totalHom_reindex {Γ Δ : Context.{u}} {A B : Family Γ} (η : A ⟶ B) (σ : Δ ⟶ Γ) :
    totalHom (Functor.whiskerLeft σ.mapElements η) ≫ liftSub B σ =
      liftSub A σ ≫ totalHom η := rfl

def familyReindexMap {Γ Δ : Context.{u}} (A : Family Γ) (B : Family Δ) (σ : Δ ⟶ Γ)
    (η : B ⟶ reindex A σ) : total B ⟶ total A := totalHom η ≫ liftSub A σ

theorem familyReindexMap_pair {Γ Δ : Context.{u}} (A : Family Γ) (B : Family Δ) (σ : Δ ⟶ Γ)
    (η : B ⟶ reindex A σ) :
    familyReindexMap A B σ η = pair (projection B ≫ σ)
      (Term.map (Functor.whiskerLeft (projection B).mapElements η) (generic B)) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem familyReindexMap_square {Γ Δ : Context.{u}} {A B : Family Γ} {A' B' : Family Δ}
    (e : A ≅ B) (e' : A' ≅ B') (σ : Δ ⟶ Γ)
    (r : A' ⟶ reindex A σ) (s : B' ⟶ reindex B σ)
    (h : e'.hom ≫ s = r ≫ Functor.whiskerLeft σ.mapElements e.hom) :
    (totalIso e').hom ≫ familyReindexMap B B' σ s =
      familyReindexMap A A' σ r ≫ (totalIso e).hom := by
  change totalHom e'.hom ≫ (totalHom s ≫ liftSub B σ) =
    (totalHom r ≫ liftSub A σ) ≫ totalHom e.hom
  rw [← Category.assoc,totalHom_comp,h,← totalHom_comp,Category.assoc,totalHom_reindex,Category.assoc]

end SquareKit.Cubical.Presheaf

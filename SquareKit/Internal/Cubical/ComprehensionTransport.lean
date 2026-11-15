import SquareKit.Internal.Cubical.FillingTransport

/-! A family isomorphism changes the dependent context by a constructed
isomorphism over its base. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

def totalHom {Γ : Context.{u}} {A B : Family Γ} (η : A ⟶ B) : total A ⟶ total B :=
  pair (projection A) (Term.map (Functor.whiskerLeft (projection A).mapElements η) (generic A))

@[simp] theorem totalHom_projection {Γ : Context.{u}} {A B : Family Γ} (η : A ⟶ B) :
    totalHom η ≫ projection B = projection A := rfl

theorem totalHom_comp {Γ : Context.{u}} {A B C : Family Γ} (η : A ⟶ B) (θ : B ⟶ C) :
    totalHom η ≫ totalHom θ = totalHom (η ≫ θ) := rfl

theorem totalHom_id {Γ : Context.{u}} (A : Family Γ) : totalHom (𝟙 A) = 𝟙 (total A) := rfl

def totalIso {Γ : Context.{u}} {A B : Family Γ} (e : A ≅ B) : total A ≅ total B where
  hom := totalHom e.hom
  inv := totalHom e.inv
  hom_inv_id := (totalHom_comp e.hom e.inv).trans ((congrArg totalHom e.hom_inv_id).trans (totalHom_id A))
  inv_hom_id := (totalHom_comp e.inv e.hom).trans ((congrArg totalHom e.inv_hom_id).trans (totalHom_id B))

theorem totalHom_pair {Γ Δ : Context.{u}} {A B : Family Γ} (η : A ⟶ B)
    (σ : Δ ⟶ Γ) (t : Term (reindex A σ)) :
    pair σ t ≫ totalHom η = pair σ (Term.map (Functor.whiskerLeft σ.mapElements η) t) := rfl

end SquareKit.Cubical.Presheaf

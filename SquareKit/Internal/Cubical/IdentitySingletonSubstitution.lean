import SquareKit.Internal.Cubical.IdentitySingleton

/-! Substitution of identity singleton contexts preserves their contraction
and marked face, retaining the selected identity data. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u
namespace IdentitySingleton
variable {Γ Δ : Context.{u}} (A : Family Γ) (a : Term A)

theorem witness_introduce (σ : Δ ⟶ Γ) (t : Term (reindex A σ))
    (p : Term (identity (reindex A σ) (a.reindex σ) t)) :
    Term.map (identityReindex (reindex A (base A a)) (a.reindex (base A a)) (endpoint A a)
      (introduce A a σ t p)) ((witness A a).reindex (introduce A a σ t p)) = p :=
  Term.map_iso_roundtrip (identityReindexIso (reindex A (projection A))
    (a.reindex (projection A)) (generic A) (pair σ t)).symm p

def reindexMap (σ : Δ ⟶ Γ) : context (reindex A σ) (a.reindex σ) ⟶ context A a :=
  introduce A a (base (reindex A σ) (a.reindex σ) ≫ σ)
    (endpoint (reindex A σ) (a.reindex σ)) (witness (reindex A σ) (a.reindex σ))

theorem reindexMap_base (σ : Δ ⟶ Γ) :
    reindexMap A a σ ≫ base A a = base (reindex A σ) (a.reindex σ) ≫ σ := rfl

theorem reindexMap_face (σ : Δ ⟶ Γ) :
    (markedFace A a).reindex (reindexMap A a σ) = markedFace (reindex A σ) (a.reindex σ) := rfl

theorem reindexMap_introduce (σ : Δ ⟶ Γ) {Θ : Context.{u}} (τ : Θ ⟶ Δ)
    (t : Term (reindex (reindex A σ) τ))
    (p : Term (identity (reindex (reindex A σ) τ) ((a.reindex σ).reindex τ) t)) :
    introduce (reindex A σ) (a.reindex σ) τ t p ≫ reindexMap A a σ =
      introduce A a (τ ≫ σ) t p := by
  have h := introduce_reindex A a (base (reindex A σ) (a.reindex σ) ≫ σ)
    (endpoint (reindex A σ) (a.reindex σ)) (witness (reindex A σ) (a.reindex σ))
    (introduce (reindex A σ) (a.reindex σ) τ t p)
  exact h.trans (congrArg (introduce A a (τ ≫ σ) t)
    (witness_introduce (reindex A σ) (a.reindex σ) τ t p))

theorem reindexMap_reflexivity (σ : Δ ⟶ Γ) :
    reflexivity (reindex A σ) (a.reindex σ) ≫ reindexMap A a σ = σ ≫ reflexivity A a :=
  (reindexMap_introduce A a σ (𝟙 Δ) (a.reindex σ) (identityRefl (a.reindex σ))).trans
    (introduce_reindex A a (𝟙 Γ) a (identityRefl a) σ).symm

theorem reindexMap_contraction (σ : Δ ⟶ Γ) :
    contraction (reindex A σ) (a.reindex σ) ≫ reindexMap A a σ =
      liftSub (interval (context A a)) (reindexMap A a σ) ≫ contraction A a := by
  let A' := reindex A σ
  let a' := a.reindex σ
  let τ := reindexMap A a σ
  have hw := witness_introduce A a (base A' a' ≫ σ) (endpoint A' a') (witness A' a')
  let k : Term (identity (reindex A (base A' a' ≫ σ)) (a.reindex (base A' a' ≫ σ))
      (endpoint A' a')) → (total (interval (context A' a')) ⟶ context A a) := fun p =>
    introduce A a (projection (interval (context A' a')) ≫ base A' a' ≫ σ)
      (IdentityContraction.point p) (IdentityContraction.contract p)
  have h₁ := reindexMap_introduce A a σ (projection (interval (context A' a')) ≫ base A' a')
    (IdentityContraction.point (witness A' a')) (IdentityContraction.contract (witness A' a'))
  have h₂ := introduce_reindex A a (projection (interval (context A a)) ≫ base A a)
    (IdentityContraction.point (witness A a)) (IdentityContraction.contract (witness A a))
    (liftSub (interval (context A a)) τ)
  exact h₁.trans ((congrArg k hw).symm.trans h₂.symm)

theorem reindexMap_id : reindexMap A a (𝟙 Γ) = 𝟙 (context A a) := introduce_generic A a

theorem reindexMap_comp (σ : Δ ⟶ Γ) {Θ : Context.{u}} (τ : Θ ⟶ Δ) :
    reindexMap (reindex A σ) (a.reindex σ) τ ≫ reindexMap A a σ = reindexMap A a (τ ≫ σ) :=
  reindexMap_introduce A a σ (base (reindex A (τ ≫ σ)) (a.reindex (τ ≫ σ)) ≫ τ)
    (endpoint (reindex A (τ ≫ σ)) (a.reindex (τ ≫ σ)))
    (witness (reindex A (τ ≫ σ)) (a.reindex (τ ≫ σ)))

end IdentitySingleton
end SquareKit.Cubical.Presheaf

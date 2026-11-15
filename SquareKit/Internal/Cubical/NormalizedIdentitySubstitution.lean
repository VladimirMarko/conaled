import SquareKit.Internal.Cubical.NormalizedIdentityFilling

namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

theorem normalizedIdentity_fromReindexed {Γ Δ : Context.{u}} (A : Family Γ)
    (a b : Term A) (σ : Δ ⟶ Γ)
    (p : Term (normalizedIdentity (reindex A σ) (a.reindex σ) (b.reindex σ))) :
    Term.map (Functor.whiskerLeft σ.mapElements (normalizedIdentityIso A a b).hom)
      (Term.map (identityReindexIso A a b σ).inv
        (Term.map (normalizedIdentityIso (reindex A σ) (a.reindex σ) (b.reindex σ)).inv p)) =
      p.convert (normalizedIdentity_reindex A a b σ).symm := by
  let e := normalizedIdentity_reindex A a b σ
  let q := Term.map (identityReindexIso A a b σ).inv
    (Term.map (normalizedIdentityIso (reindex A σ) (a.reindex σ) (b.reindex σ)).inv p)
  apply Term.map_injective_of_iso (eqToIso e)
  have h := congrArg (fun k => Term.map k.hom q) (normalizedIdentityIso_reindex A a b σ)
  have hc : ∀ {C D : Family Δ} (e : C = D) (t : Term D),
      Term.map (eqToIso e).hom (t.convert e.symm) = t := by
    intro C D e t
    cases e
    rfl
  rw [hc]
  exact h.trans ((congrArg (Term.map
      (normalizedIdentityIso (reindex A σ) (a.reindex σ) (b.reindex σ)).hom)
      (Term.map_iso_roundtrip (identityReindexIso A a b σ).symm
        (Term.map (normalizedIdentityIso (reindex A σ) (a.reindex σ) (b.reindex σ)).inv p))).trans
      (Term.map_iso_roundtrip (normalizedIdentityIso (reindex A σ) (a.reindex σ) (b.reindex σ)).symm p))

end SquareKit.Cubical.Presheaf

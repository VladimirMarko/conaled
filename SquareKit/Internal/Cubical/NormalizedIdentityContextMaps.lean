import SquareKit.Internal.Cubical.ComprehensionReindexSquares
import SquareKit.Internal.Cubical.NormalizedIdentitySingletonSubstitution

namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

private theorem iso_square_inverse {C : Type*} [Category C] {A B D E : C}
    (e : A ≅ B) (s : B ≅ D) (r : A ≅ E) (e' : E ≅ D) (h : e.trans s = r.trans e') :
    e'.hom ≫ s.inv = r.inv ≫ e.hom := by
  have hh := congrArg (fun k : A ≅ D => r.inv ≫ k.hom ≫ s.inv) h
  simpa using hh.symm

namespace NormalizedIdentitySingleton
variable {Γ Δ : Context.{u}} (A : Family Γ) (a : Term A) (σ : Δ ⟶ Γ)

abbrev familyEquality : reindex (fiber A a) (liftSub A σ) = fiber (reindex A σ) (a.reindex σ) :=
  normalizedIdentity_reindex (reindex A (projection A)) (a.reindex (projection A)) (generic A) (liftSub A σ)

def directMap : context (reindex A σ) (a.reindex σ) ⟶ context A a :=
  familyReindexMap (fiber A a) (fiber (reindex A σ) (a.reindex σ)) (liftSub A σ)
    (eqToHom (familyEquality A a σ).symm)

theorem rawMap_eq :
    familyReindexMap (IdentitySingleton.fiber A a) (IdentitySingleton.fiber (reindex A σ) (a.reindex σ))
      (liftSub A σ) (identityReindexIso (reindex A (projection A)) (a.reindex (projection A))
        (generic A) (liftSub A σ)).inv = IdentitySingleton.reindexMap A a σ := rfl

theorem presentation_directMap :
    (presentation (reindex A σ) (a.reindex σ)).hom ≫ directMap A a σ =
      IdentitySingleton.reindexMap A a σ ≫ (presentation A a).hom := by
  have h := iso_square_inverse
    (Functor.isoWhiskerLeft (liftSub A σ).mapElements
      (normalizedIdentityIso (reindex A (projection A)) (a.reindex (projection A)) (generic A)))
    (eqToIso (familyEquality A a σ))
    (identityReindexIso (reindex A (projection A)) (a.reindex (projection A)) (generic A) (liftSub A σ))
    (normalizedIdentityIso (reindex (reindex A (projection A)) (liftSub A σ))
      ((a.reindex (projection A)).reindex (liftSub A σ)) ((generic A).reindex (liftSub A σ)))
    (normalizedIdentityIso_reindex (reindex A (projection A)) (a.reindex (projection A)) (generic A) (liftSub A σ))
  exact (familyReindexMap_square
    (normalizedIdentityIso (reindex A (projection A)) (a.reindex (projection A)) (generic A))
    (normalizedIdentityIso (reindex (reindex A σ) (projection (reindex A σ)))
      ((a.reindex σ).reindex (projection (reindex A σ))) (generic (reindex A σ))) (liftSub A σ)
    _ _ h).trans (congrArg (fun f => f ≫ (presentation A a).hom) (rawMap_eq A a σ))

theorem directMap_eq : directMap A a σ = reindexMap A a σ := by
  apply (cancel_epi (presentation (reindex A σ) (a.reindex σ)).hom).mp
  exact (presentation_directMap A a σ).trans (presentation_reindexMap A a σ).symm

end NormalizedIdentitySingleton
end SquareKit.Cubical.Presheaf

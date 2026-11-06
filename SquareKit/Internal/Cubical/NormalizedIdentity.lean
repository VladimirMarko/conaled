import SquareKit.Internal.Cubical.LocalIdentitySubstitution

/-! Marked Id changes presentation through Mathlib's functor transport. Its
family reindexes by equality while retaining the selected path and face. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

def normalizedIdentity {Γ : Context.{u}} (A : Family Γ) (a b : Term A) : Family Γ :=
  (identity A a b).copyObj (LocalIdentity A a b) (fun x => (localIdentityEquiv A a b x).toIso)

def normalizedIdentityIso {Γ : Context.{u}} (A : Family Γ) (a b : Term A) :
    identity A a b ≅ normalizedIdentity A a b :=
  (identity A a b).isoCopyObj (LocalIdentity A a b) (fun x => (localIdentityEquiv A a b x).toIso)

theorem normalizedIdentity_reindex {Γ Δ : Context.{u}} (A : Family Γ)
    (a b : Term A) (σ : Δ ⟶ Γ) :
    reindex (normalizedIdentity A a b) σ =
      normalizedIdentity (reindex A σ) (a.reindex σ) (b.reindex σ) := by
  have ho : ∀ x, (reindex (normalizedIdentity A a b) σ).obj x =
      (normalizedIdentity (reindex A σ) (a.reindex σ) (b.reindex σ)).obj x :=
    localIdentity_substitution A a b σ
  apply Functor.hext ho
  intro x y f
  apply typeHom_hext (ho x) (ho y)
  intro s t hst
  change LocalIdentity A a b (σ.mapElements.obj x) at s
  change LocalIdentity (reindex A σ) (a.reindex σ) (b.reindex σ) x at t
  have ht : t = ((identityReindex A a b σ).app x s.fromLocal).toLocal :=
    eq_of_heq (hst.symm.trans ((heq_of_eq s.toLocal_fromLocal).symm.trans
      (identityToLocal_substitution A a b σ x s.fromLocal)))
  subst t
  change HEq ((identity A a b).map (σ.mapElements.map f) s.fromLocal).toLocal
    ((identity (reindex A σ) (a.reindex σ) (b.reindex σ)).map f
      (((identityReindex A a b σ).app x s.fromLocal).toLocal.fromLocal)).toLocal
  exact (identityToLocal_substitution A a b σ y
    ((identity A a b).map (σ.mapElements.map f) s.fromLocal)).trans
      (heq_of_eq (congrArg (fun p =>
        ((identity (reindex A σ) (a.reindex σ) (b.reindex σ)).map f p).toLocal)
        (LocalIdentity.fromLocal_toLocal ((identityReindex A a b σ).app x s.fromLocal))).symm)

def normalizedIdentityRefl {Γ : Context.{u}} {A : Family Γ} (a : Term A) :
    Term (normalizedIdentity A a a) := Term.map (normalizedIdentityIso A a a).hom (identityRefl a)

theorem normalizedIdentityRefl_reindex {Γ Δ : Context.{u}} {A : Family Γ}
    (a : Term A) (σ : Δ ⟶ Γ) :
    ((normalizedIdentityRefl a).reindex σ).convert (normalizedIdentity_reindex A a a σ) =
      normalizedIdentityRefl (a.reindex σ) := by
  apply Term.ext
  intro x
  apply eq_of_heq
  exact (Term.convert_val_heq (normalizedIdentity_reindex A a a σ) _ x).trans
    (identityToLocal_substitution A a a σ x ((identityRefl a).val (σ.mapElements.obj x)))

end SquareKit.Cubical.Presheaf

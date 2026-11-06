import SquareKit.Internal.Cubical.IdentityMaps

/-! Pointwise marked-identity action retains its selected data under substitution. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
universe u
variable {Γ Δ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) (a b : Term A) (σ : Δ ⟶ Γ)

theorem normalizedIdentityMap_substitution (x : Δ.Elements)
    (p : LocalIdentity A a b (σ.mapElements.obj x))
    (q : LocalIdentity (reindex A σ) (a.reindex σ) (b.reindex σ) x) (hpq : HEq p q) :
    HEq ((normalizedIdentityMap f a b).app (σ.mapElements.obj x) p)
      ((normalizedIdentityMap (Functor.whiskerLeft σ.mapElements f) (a.reindex σ) (b.reindex σ)).app x q) := by
  have hq : q = ((identityReindex A a b σ).app x p.fromLocal).toLocal :=
    eq_of_heq (hpq.symm.trans ((heq_of_eq p.toLocal_fromLocal).symm.trans
      (identityToLocal_substitution A a b σ x p.fromLocal)))
  subst q
  change HEq (IdentityElement.map f p.fromLocal).toLocal
    (IdentityElement.map (Functor.whiskerLeft σ.mapElements f)
      (((identityReindex A a b σ).app x p.fromLocal).toLocal.fromLocal)).toLocal
  rw [LocalIdentity.fromLocal_toLocal]
  exact identityToLocal_substitution B (a.map f) (b.map f) σ x (IdentityElement.map f p.fromLocal)

theorem normalizedIdentityMap_reindex (p : Term (normalizedIdentity A a b)) :
    ((p.map (normalizedIdentityMap f a b)).reindex σ).convert
      (normalizedIdentity_reindex B (a.map f) (b.map f) σ) =
    ((p.reindex σ).convert (normalizedIdentity_reindex A a b σ)).map
      (normalizedIdentityMap (Functor.whiskerLeft σ.mapElements f) (a.reindex σ) (b.reindex σ)) := by
  apply Term.ext
  intro x
  apply eq_of_heq
  exact (Term.convert_val_heq _ _ x).trans
    (normalizedIdentityMap_substitution f a b σ x (p.val (σ.mapElements.obj x))
      (((p.reindex σ).convert (normalizedIdentity_reindex A a b σ)).val x)
      (Term.convert_val_heq (normalizedIdentity_reindex A a b σ) (p.reindex σ) x).symm)

end SquareKit.Cubical.Presheaf

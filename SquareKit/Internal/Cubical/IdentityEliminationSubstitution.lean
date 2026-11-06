import SquareKit.Internal.Cubical.IdentityElimination
import SquareKit.Internal.Cubical.IdentitySingletonSubstitution
import SquareKit.Internal.Cubical.BackwardFilling

/-! Strict identity elimination commutes with arbitrary context substitution,
using the constructed singleton map and its contraction equations. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u
namespace IdentityElimination
open IdentitySingleton
variable {Γ Δ : Context.{u}} (A : Family Γ) (a : Term A)
  (C : Family (context A a)) (d : Term (reindex C (reflexivity A a)))

def branchReindex (σ : Δ ⟶ Γ) :
    Term (reindex (reindex C (reindexMap A a σ)) (reflexivity (reindex A σ) (a.reindex σ))) :=
  (d.reindex σ).convert (congrArg (fun τ => reindex C τ) (reindexMap_reflexivity A a σ).symm)

theorem box_reindex (σ : Δ ⟶ Γ) :
    HEq (box (reindex A σ) (a.reindex σ) (reindex C (reindexMap A a σ)) (branchReindex A a C d σ))
      ((box A a C d).reindex (reindexMap A a σ)) := by
  let τ := reindexMap A a σ
  apply OpenBox.hext (congrArg (fun q => reindex C q) (reindexMap_contraction A a σ))
  · intro x hx
    apply (tube_val_heq _ _ _ _ x hx).trans
    apply (Term.convert_val_heq _ (d.reindex σ) _).trans
    exact (tube_val_heq A a C d ((liftSub (interval (context A a)) τ).mapElements.obj x) hx).symm
  · intro x
    apply (cap_val_heq _ _ _ _ x).trans
    apply (Term.convert_val_heq _ (d.reindex σ) _).trans
    exact (cap_val_heq A a C d (τ.mapElements.obj x)).symm

theorem eliminate_reindex (G : Composition C) (hG : G.Lawful) (σ : Δ ⟶ Γ) :
    eliminate (reindex A σ) (a.reindex σ) (reindex C (reindexMap A a σ))
      (branchReindex A a C d σ) (G.reindex (reindexMap A a σ)) =
        (eliminate A a C d G).reindex (reindexMap A a σ) := by
  let τ := reindexMap A a σ
  have he := reindexMap_contraction A a σ
  have hc := G.comp_heq he (box_reindex A a C d σ)
  have hu := hG.uniform (contraction A a) (markedFace A a) (box A a C d) τ
  have ht := hc.trans (heq_of_eq hu)
  apply Term.ext
  intro x
  apply eq_of_heq
  apply (Term.convert_val_heq _ _ x).trans
  apply HEq.trans _ (Term.convert_val_heq _ _ (τ.mapElements.obj x)).symm
  exact Term.val_heq_of_heq (congrArg (fun q => reindex C (endpointSub _ true ≫ q)) he) ht rfl

end IdentityElimination
end SquareKit.Cubical.Presheaf

import SquareKit.Internal.Cubical.TelescopeIdentityElimination
import SquareKit.Internal.Cubical.TelescopeFillingSubstitution

/-! Finite-tail identity elimination commutes with context substitution,
including the actual iterated product filler selected by the tail. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

theorem IdentityElimination.eliminate_convert {Γ : Context.{u}} (A : Family Γ) (a : Term A)
    {C D : Family (IdentitySingleton.context A a)} (e : C = D)
    (d : Term (reindex C (IdentitySingleton.reflexivity A a))) (G : Filling C) :
    IdentityElimination.eliminate A a D
      (d.convert (congrArg (fun B => reindex B (IdentitySingleton.reflexivity A a)) e))
      (G.convert e).toComposition =
      (IdentityElimination.eliminate A a C d G.toComposition).convert e := by
  cases e
  rfl

namespace TelescopeIdentityElimination
open IdentitySingleton
variable {Γ Δ : Context.{u}} (A : Family Γ) (a : Term A)
  (T : Telescope (context A a)) (C : Family T.context)
  (d : Term (reindex C (T.map (reflexivity A a)))) (σ : Δ ⟶ Γ)

abbrev substitutedTail := T.reindex (reindexMap A a σ)
abbrev substitutedMotive := reindex C (T.map (reindexMap A a σ))

def substitutedAbstractBranch :
    Term (reindex ((substitutedTail A a T σ).pi (substitutedMotive A a T C σ))
      (reflexivity (reindex A σ) (a.reindex σ))) :=
  (IdentityElimination.branchReindex A a (T.pi C) (branch A a T C d) σ).convert
    (congrArg (fun B => reindex B (reflexivity (reindex A σ) (a.reindex σ)))
      (T.pi_reindex C (reindexMap A a σ)))

def substitutedBranch :
    Term (reindex (substitutedMotive A a T C σ)
      ((substitutedTail A a T σ).map (reflexivity (reindex A σ) (a.reindex σ)))) :=
  ((substitutedTail A a T σ).reindex (reflexivity (reindex A σ) (a.reindex σ))).apply
    ((substitutedAbstractBranch A a T C d σ).convert
      ((substitutedTail A a T σ).pi_reindex (substitutedMotive A a T C σ)
        (reflexivity (reindex A σ) (a.reindex σ))))

theorem branch_substituted :
    branch (reindex A σ) (a.reindex σ) (substitutedTail A a T σ) (substitutedMotive A a T C σ)
      (substitutedBranch A a T C d σ) = substitutedAbstractBranch A a T C d σ := by
  unfold branch substitutedBranch
  rw [Telescope.abstract_apply]
  exact Term.convert_symm _ _

theorem eliminate_reindex (fs : T.Fillings) (hs : fs.Lawful) (G : Filling C) (hG : G.Lawful) :
    eliminate (reindex A σ) (a.reindex σ) (substitutedTail A a T σ) (substitutedMotive A a T C σ)
      (substitutedBranch A a T C d σ) (fs.reindex (reindexMap A a σ)) (hs.reindex _)
      (G.reindex (T.map (reindexMap A a σ))) =
      (eliminate A a T C d fs hs G).reindex (T.map (reindexMap A a σ)) := by
  let τ := reindexMap A a σ
  let K := fs.pi hs G
  have hK := fs.pi_lawful hs G hG
  have hJ := IdentityElimination.eliminate_reindex A a (T.pi C) (branch A a T C d)
    K.toComposition (Filling.toComposition_lawful hK) σ
  unfold eliminate
  rw [branch_substituted]
  rw [← T.apply_reindex]
  apply congrArg (substitutedTail A a T σ).apply
  have hc := IdentityElimination.eliminate_convert (reindex A σ) (a.reindex σ)
    (T.pi_reindex C τ) (IdentityElimination.branchReindex A a (T.pi C) (branch A a T C d) σ)
    (K.reindex τ)
  rw [fs.pi_reindex hs G τ] at hc
  exact hc.trans (congrArg (fun t => t.convert (T.pi_reindex C τ)) hJ)

end TelescopeIdentityElimination
end SquareKit.Cubical.Presheaf

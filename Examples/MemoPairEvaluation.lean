import SquareKit.Internal.DependentJudgments.MemoPairSource
import Examples.GuardedGroupoidMemo

/-! Evaluation of the source pair retains the chosen identity certificate. -/
namespace Examples.MemoPairEvaluation
open SquareKit.GuardedTheory SquareKit.Internal.DependentJudgments
open Contextual.DerivedSemantics Examples.GuardedGroupoidMemo
set_option backward.isDefEq.respectTransparency false
universe u
variable (M : SquareKit.Internal.PathTransport.Typed.Model.{u})
variable (S : Sigma.Capability M.toStructuralModel) {V : Type}
variable (ρ : V → Value M.toStructuralModel)
variable (g a c v η : Contextual.Expression V) (G : M.Context) (A : M.Family G)
variable (C Vv : M.Section G A) (H : M.Section G (M.identity A Vv C))
variable (hg : g.eval (Contextual.algebra M) ρ = .context G)
  (ha : a.eval (Contextual.algebra M) ρ = .family G A)
  (hc : c.eval (Contextual.algebra M) ρ = .term G A C)
  (hv : v.eval (Contextual.algebra M) ρ = .term G A Vv)
  (hη : η.eval (Contextual.algebra M) ρ = .term G (M.identity A Vv C) H)

include hg ha hc in
theorem certificateFamily_eval :
    (MemoPair.sourceCertificateFamily g a c).eval (Contextual.algebra M) ρ =
      .family (M.extend G A) (MemoPair.certificateFamily M.toStructuralModel A C) := by
  have hw := weaken_eval M ρ g a G A hg ha
  exact identity_eval M ρ _ _ _ (M.extend G A) _ _ _
    (subTy_eval M ρ a _ G _ A _ ha hw)
    (generic_eval M ρ g a G A hg ha)
    (subTm_eval M ρ c _ G _ A C _ hc hw)

include hg ha hc hv hη in
theorem pair_eval :
    (MemoPair.sourcePair g a c v η).eval (Sigma.algebra M S) ρ =
      .term G (S.sigma A (MemoPair.certificateFamily M.toStructuralModel A C))
        (MemoPair.pair M.toStructuralModel A C S Vv H) := by
  apply Sigma.pair_eval
  · exact (Sigma.eval_old M S _ ρ).trans hg
  · exact (Sigma.eval_old M S _ ρ).trans ha
  · exact (Sigma.eval_old M S _ ρ).trans (certificateFamily_eval M ρ g a c G A C hg ha hc)
  · exact (Sigma.eval_old M S _ ρ).trans hv
  · apply (Sigma.eval_old M S _ ρ).trans
    apply hη.trans
    exact Value.term_eq (MemoPair.certificateFamily_at M.toStructuralModel A C Vv).symm
      (cast_heq _ _).symm


theorem subTm_eval {G D : M.Context} {A : M.Family G} {x : M.Section G A}
    {t s : Sigma.Expression V} (σ : M.Substitution D G)
    (ht : t.eval (Sigma.algebra M S) ρ = .term G A x)
    (hs : s.eval (Sigma.algebra M S) ρ = .substitution D G σ) :
    (Sigma.subTm t s).eval (Sigma.algebra M S) ρ =
      .term D (M.subTy A σ) (M.subTm x σ) := by
  change SquareKit.Internal.DependentJudgments.operation _ .subTm
    ![t.eval (Sigma.algebra M S) ρ, s.eval (Sigma.algebra M S) ρ] = _
  simp [ht, hs, SquareKit.Internal.DependentJudgments.operation]

end Examples.MemoPairEvaluation

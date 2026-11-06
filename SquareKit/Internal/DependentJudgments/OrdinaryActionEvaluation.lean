import SquareKit.Internal.DependentJudgments.OrdinaryActionSemantics
import SquareKit.Internal.DependentJudgments.OrdinaryActionSource
/-! Evaluation of the source ordinary action retains its selected J term. -/
namespace SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
open GuardedTheory PathTransport.Typed StructuralModel
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (M : Model.{u}) {V : Type} (ρ : V → Value M.toStructuralModel)
theorem ordinaryApply_eval (g a sx st : Expression V)
 (Γ : M.Context) (A C : M.Family Γ)
 (t : M.Section (M.extend Γ A) (M.subTy C (M.weaken Γ A))) (x : M.Section Γ A)
 (hg : g.eval (algebra M) ρ = .context Γ)
 (ha : a.eval (algebra M) ρ = .family Γ A)
 (hx : sx.eval (algebra M) ρ = .term Γ A x)
 (ht : st.eval (algebra M) ρ = .term (M.extend Γ A) (M.subTy C (M.weaken Γ A)) t) :
 (Contextual.ordinaryApply g a sx st).eval (algebra M) ρ = .term Γ C (ordinaryApply M A C t x) := by
 have hs := sectionSub_eval M ρ g a sx Γ A x hg ha hx
 have h := subTm_eval M ρ st _ _ _ _ t _ ht hs
 exact h.trans (Value.term_eq (M.toStructuralModel.weaken_section_type A x C) (cast_heq _ _).symm)
theorem ordinaryAp_eval (g a c sx sy sp st : Expression V)
 (Γ : M.Context) (A C : M.Family Γ)
 (t : M.Section (M.extend Γ A) (M.subTy C (M.weaken Γ A)))
 (x y : M.Section Γ A) (p : M.Section Γ (M.identity A x y))
 (hg : g.eval (algebra M) ρ = .context Γ)
 (ha : a.eval (algebra M) ρ = .family Γ A)
 (hc : c.eval (algebra M) ρ = .family Γ C)
 (hx : sx.eval (algebra M) ρ = .term Γ A x)
 (hy : sy.eval (algebra M) ρ = .term Γ A y)
 (hp : sp.eval (algebra M) ρ = .term Γ (M.identity A x y) p)
 (ht : st.eval (algebra M) ρ = .term (M.extend Γ A) (M.subTy C (M.weaken Γ A)) t) :
 (Contextual.ordinaryAp g a c sx sy sp st).eval (algebra M) ρ =
 .term Γ (M.identity C (ordinaryApply M A C t x) (ordinaryApply M A C t y))
  (ordinaryApValue M A C t x y p) := by
 have hw : (Contextual.weaken g a).eval (algebra M) ρ =
     .substitution (M.extend Γ A) Γ (M.weaken Γ A) := by
   change DependentJudgments.operation M.toStructuralModel .weaken ![g.eval (algebra M) ρ, a.eval (algebra M) ρ] = _
   rw [hg, ha]
   simp [DependentJudgments.operation]
 have hpath := pathProjection_eval M ρ g a sx Γ A x hg ha hx
 have hCw := subTy_eval M ρ c _ _ _ C _ hc hw
 have hDty := subTy_eval M ρ _ _ _ _ _ _ hCw hpath
 have htx := ordinaryApply_eval M ρ g a sx st Γ A C t x hg ha hx ht
 have hleft0 := subTm_eval M ρ _ _ _ _ C _ _ htx hw
 have hleft := subTm_eval M ρ _ _ _ _ _ _ _ hleft0 hpath
 have hright := subTm_eval M ρ st _ _ _ _ t _ ht hpath
 have hD := identity_eval M ρ _ _ _ _ _ _ _ hDty hleft hright
 have hb := reflexivity_eval M ρ c _ _ _ _ hc htx
 have hj := basedJ_eval M ρ a sx (Contextual.ordinaryApMotive g a c sx st)
  (Contextual.ordinaryApBranch g a c sx st) Γ A x (ordinaryApMotive M A C t x)
  (ordinaryApBranch M A C t x) ha hx hD
  (hb.trans (Value.term_eq (ordinaryApMotive_root M A C t x).symm (cast_heq _ _).symm))
 have he := endpoint_eval M ρ g a sx sy sp Γ A x y p hg ha hx hy hp
 have h := subTm_eval M ρ _ _ _ _ _ _ _ hj he
 exact h.trans (Value.term_eq (ordinaryApMotive_endpoint M A C t x y p) (cast_heq _ _).symm)
end SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics

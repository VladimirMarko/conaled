import SquareKit.Internal.PathTransport.DerivedCoherence

/-! Typed substitution extension for named base values. -/
namespace SquareKit.Internal.PathTransport.Typed.Authoring
open SquareKit.Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def substitutionCode {s : SubCode δ γ} (_hs : SubDeriv Δ δ Γ γ σ s) : SubCode δ γ := s

def bindBase (hΓ : CtxDeriv Γ γ) (hs : SubDeriv Ω ω Γ γ σ s) (z : BasePoint Ω ω) :=
  SubDeriv.pair (.base hΓ) hs (z.deriv.annotateType (baseSub_code s).symm)

theorem baseReindex_weaken_pair (ξ : TmCode γ (baseCode γ)) (a : TyCode γ)
    (s : SubCode δ γ) (t : TmCode δ (subTyCode a s)) :
    baseReindexCode (baseReindexCode ξ (weakenCode γ a)) (pairCode a s t) =
      baseReindexCode ξ s :=
  (baseReindex_comp _ _ _).trans
    (congrArg (baseReindexCode ξ) (funext fun M => M.weaken_pair _ _ _))

theorem variable_bindBase (hΓ : CtxDeriv Γ γ) (hs : SubDeriv Ω ω Γ γ σ s) (z : BasePoint Ω ω) :
    ((BasePoint.variable hΓ).reindex (bindBase hΓ hs z)).code = z.code := by
  funext M
  apply eq_of_heq
  exact (castCode_eval _ _ M).trans ((subTm_cast_eval _ _ _ M).trans
    ((M.variable_pair _ _ _).trans (castCode_eval _ _ M)))

def liftCode (a : TyCode γ) (s : SubCode δ γ) :
    SubCode (extendCode δ (subTyCode a s)) (extendCode γ a) :=
  fun M => M.toStructuralModel.lift (a M) (s M)

def liftSubstitution (hΔ : CtxDeriv Δ δ) (hA : TyDeriv Γ γ A a)
    (hs : SubDeriv Δ δ Γ γ σ s) :
    SubDeriv (A.sub σ :: Δ) (extendCode δ (subTyCode a s)) (A :: Γ) (extendCode γ a)
      (Expr.liftSub σ) (liftCode a s) := by
  let hB := TyDeriv.sub hA hs
  let hw := SubDeriv.weaken hΔ hB
  let ht := (TmDeriv.var hΔ hB).rawType (Expr.sub_var_rename (A.sub σ) Nat.succ).symm
  let t := ht.convert (TyEqDeriv.subComp hA hs hw)
  let hp := SubDeriv.pair hA (SubDeriv.comp hs hw) t
  have hr : consSub (.var 0) (fun n => (σ n).sub (Expr.var ∘ Nat.succ)) = Expr.liftSub σ := by
    funext n; cases n with
    | zero => rfl
    | succ n => exact Expr.sub_var_rename (σ n) Nat.succ
  have hc : pairCode a (compCode s (weakenCode δ (subTyCode a s)))
      (castCode (subTyComp_code a s (weakenCode δ (subTyCode a s))) (varCode δ (subTyCode a s))) =
      liftCode a s := by
    funext M
    apply congrArg (M.pairSub _ _)
    exact eq_of_heq ((castCode_eval _ _ M).trans (cast_heq _ _).symm)
  exact hc ▸ SubDeriv.rawTransport hr hp

end SquareKit.Internal.PathTransport.Typed.Authoring

namespace SquareKit.Internal.PathTransport.Typed.StructuralModel
variable (M : StructuralModel)
theorem lift_pair {Γ Δ Ω : M.Context} (A : M.Family Γ) (s : M.Substitution Δ Γ)
    (t : M.Substitution Ω Δ) (v : M.Section Ω (M.subTy (M.subTy A s) t)) :
    M.compSub (M.lift A s) (M.pairSub (M.subTy A s) t v) =
      M.pairSub A (M.compSub s t) (cast (congrArg (M.Section Ω) (M.subTy_comp A s t)) v) := by
  apply M.pair_ext A
  · exact (M.comp_assoc _ _ _).symm.trans
      ((congrArg (fun r => M.compSub r _) (M.weaken_lift A s)).trans
        ((M.comp_assoc _ _ _).trans
          ((congrArg (M.compSub s) (M.weaken_pair _ _ _)).trans (M.weaken_pair _ _ _).symm)))
  · exact (M.subTm_comp _ _ _).symm.trans
      ((M.subTm_congr (M.weaken_lift_type A s) (M.variable_lift A s) _).trans
        ((M.variable_pair _ _ _).trans ((cast_heq _ _).symm.trans (M.variable_pair _ _ _).symm)))
/-- A lifted pair is determined by its projected substitution and variable. -/
theorem lift_pair_ext {Γ Δ Ω : M.Context} (A : M.Family Γ)
    (s : M.Substitution Δ Γ) (t : M.Substitution Ω Δ)
    (v : M.Section Ω (M.subTy (M.subTy A s) t)) (r : M.Substitution Ω (M.extend Γ A))
    (hs : M.compSub s t = M.compSub (M.weaken Γ A) r)
    (hv : HEq v (M.subTm (M.genericVariable Γ A) r)) :
    M.compSub (M.lift A s) (M.pairSub (M.subTy A s) t v) = r := by
  rw [M.lift_pair]
  apply M.pair_ext A
  · exact (M.weaken_pair _ _ _).trans hs
  · exact (M.variable_pair _ _ _).trans ((cast_heq _ _).trans hv)

/-- Compare a lifted pair with a pair whose base substitution is equal. -/
theorem lift_pair_congr {Γ Δ Ω : M.Context} (A : M.Family Γ)
    (s : M.Substitution Δ Γ) (t : M.Substitution Ω Δ)
    (v : M.Section Ω (M.subTy (M.subTy A s) t))
    (r : M.Substitution Ω Γ) (w : M.Section Ω (M.subTy A r))
    (hs : M.compSub s t = r) (hv : HEq v w) :
    M.compSub (M.lift A s) (M.pairSub (M.subTy A s) t v) = M.pairSub A r w :=
  M.lift_pair_ext A s t v _ (hs.trans (M.weaken_pair _ _ _).symm)
    (hv.trans (M.variable_pair _ _ _).symm)

/-- A commuting substitution square and matching elements extend to a square
of comprehension pairs, including their dependent type casts. -/
theorem lift_pair_square {Γ Δ Ω Ξ : M.Context} (A : M.Family Γ)
    (s : M.Substitution Δ Γ) (t : M.Substitution Ω Δ)
    (v : M.Section Ω (M.subTy (M.subTy A s) t))
    (r : M.Substitution Ξ Γ) (w : M.Section Ξ (M.subTy A r))
    (u : M.Substitution Ω Ξ) (hs : M.compSub s t = M.compSub r u)
    (hv : HEq v (M.subTm w u)) :
    M.compSub (M.lift A s) (M.pairSub (M.subTy A s) t v) =
      M.compSub (M.pairSub A r w) u := by
  apply M.lift_pair_ext A s t v _
  · exact hs.trans ((congrArg (fun r => M.compSub r u) (M.weaken_pair _ _ _).symm).trans
      (M.comp_assoc _ _ _))
  · apply hv.trans
    symm
    apply (M.subTm_comp _ _ _).symm.trans
    exact M.subTm_congr
      ((M.subTy_comp _ _ _).trans (congrArg (M.subTy _) (M.weaken_pair _ _ _)))
      (M.variable_pair _ _ _) u
end SquareKit.Internal.PathTransport.Typed.StructuralModel

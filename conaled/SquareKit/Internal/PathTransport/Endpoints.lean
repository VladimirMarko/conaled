import SquareKit.Internal.PathTransport.Named

/-! Typed endpoint substitutions and their structural computation.
These helpers use comprehension and source conversion; they introduce no
new eliminator or source term constructor. -/
namespace SquareKit.Internal.PathTransport.Typed
open SquareKit.Internal.PathTransport
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace StructuralModel
variable (M : StructuralModel.{u})
theorem pathFamily_at {Γ : M.Context} (A : M.Family Γ) (x y : M.Section Γ A) :
    M.subTy (M.pathFamily A x) (M.sectionSub A y) = M.identity A x y := by
  unfold pathFamily
  rw [M.identity_sub]
  exact M.identity_congr (M.weaken_section_type A y A)
    (M.weaken_section_term A y x) (M.variable_section A y)

def endpointSub {Γ : M.Context} (A : M.Family Γ) (x y : M.Section Γ A)
    (p : M.Section Γ (M.identity A x y)) : M.Substitution Γ (M.pathContext A x) :=
  M.pairSub (M.pathFamily A x) (M.sectionSub A y)
    (cast (congrArg (M.Section Γ) (M.pathFamily_at A x y).symm) p)
end StructuralModel

def sectionCode (a : TyCode γ) (ξ : TmCode γ a) : SubCode γ (extendCode γ a) :=
  pairCode a (idCode γ) (castCode (subTyId_code a).symm ξ)

def pathFamilyCode (a : TyCode γ) (ξ : TmCode γ a) : TyCode (extendCode γ a) :=
  identityCode (subTyCode a (weakenCode γ a)) (subTmCode ξ (weakenCode γ a)) (varCode γ a)

theorem sectionCode_eval (a : TyCode γ) (ξ : TmCode γ a) (M : Model) :
    sectionCode a ξ M = M.toStructuralModel.sectionSub (a M) (ξ M) := by
  unfold sectionCode pairCode StructuralModel.sectionSub
  congr 1
  exact eq_of_heq ((castCode_eval _ _ M).trans (cast_heq _ _).symm)

theorem pathFamilyAt_code (a : TyCode γ) (ξ υ : TmCode γ a) :
    subTyCode (pathFamilyCode a ξ) (sectionCode a υ) = identityCode a ξ υ := by
  funext M
  change M.subTy _ (sectionCode a υ M) = _
  rw [sectionCode_eval]
  exact M.toStructuralModel.pathFamily_at _ _ _

def endpointCode (a : TyCode γ) (ξ υ : TmCode γ a)
    (π : TmCode γ (identityCode a ξ υ)) : SubCode γ (pathCode a ξ) :=
  pairCode (pathFamilyCode a ξ) (sectionCode a υ) (castCode (pathFamilyAt_code a ξ υ).symm π)

theorem endpointCode_eval (a : TyCode γ) (ξ υ : TmCode γ a)
    (π : TmCode γ (identityCode a ξ υ)) (M : Model) :
    endpointCode a ξ υ π M = M.toStructuralModel.endpointSub (a M) (ξ M) (υ M) (π M) := by
  unfold endpointCode pairCode StructuralModel.endpointSub
  congr 1
  · exact sectionCode_eval _ _ M
  · exact (castCode_eval _ _ M).trans (cast_heq _ _).symm

theorem endpointCode_root (a : TyCode γ) (ξ : TmCode γ a) :
    endpointCode a ξ ξ (reflCode a ξ) = rootCode a ξ := by
  funext M
  rw [endpointCode_eval]
  rfl

def TyDeriv.rawExpr (h : A = B) (t : TyDeriv Γ γ A a) : TyDeriv Γ γ B a := h ▸ t

/-- Native transport of annotations keeps the actual raw source type fixed. -/
def TmDeriv.annotateType {γ : CtxCode} {a b : TyCode γ} {Γ : RawCtx} {A x : Expr} {ξ : TmCode γ a}
    (h : a = b) (t : TmDeriv Γ γ A a x ξ) :
    TmDeriv Γ γ A b x (castCode h ξ) := by cases h; exact t

def TmEqDeriv.annotateType {γ : CtxCode} {a b : TyCode γ} {Γ : RawCtx} {A t v : Expr}
    {ξ ν : TmCode γ a} (h : a = b) (e : TmEqDeriv Γ γ A a t ξ v ν) :
    TmEqDeriv Γ γ A b t (castCode h ξ) v (castCode h ν) := by cases h; exact e

def TmEqDeriv.annotate {γ : CtxCode} {a : TyCode γ} {Γ : RawCtx} {A t v : Expr}
    {ξ ξ' ν ν' : TmCode γ a} (e : TmEqDeriv Γ γ A a t ξ v ν)
    (hx : ξ = ξ') (hv : ν = ν') : TmEqDeriv Γ γ A a t ξ' v ν' := hx ▸ hv ▸ e

theorem castCode_heq {γ : CtxCode} {a b : TyCode γ} (h : a = b) (ξ : TmCode γ a) :
    HEq (castCode h ξ) ξ := by cases h; rfl

theorem subTmCode_substitution_heq {γ δ : CtxCode} {a : TyCode γ}
    (ξ : TmCode γ a) {s t : SubCode δ γ} (h : s = t) : HEq (subTmCode ξ s) (subTmCode ξ t) := by
  cases h; rfl

theorem subTmId_heq {γ : CtxCode} {a : TyCode γ} (ξ : TmCode γ a) :
    HEq (subTmCode ξ (idCode γ)) ξ :=
  (castCode_heq _ _).symm.trans (heq_of_eq (subTmId_code ξ))

def TyDeriv.pathFamily (hΓ : CtxDeriv Γ γ) (hA : TyDeriv Γ γ A a)
    (hx : TmDeriv Γ γ A a x ξ) :
    TyDeriv (A :: Γ) (extendCode γ a) (.identity (A.rename Nat.succ) (x.rename Nat.succ) (.var 0))
      (pathFamilyCode a ξ) :=
  (TyDeriv.identity (.sub hA (.weaken hΓ hA)) (.sub hx (.weaken hΓ hA))
    ((TmDeriv.var hΓ hA).rawType (Expr.sub_var_rename A Nat.succ).symm)).rawExpr
    (by simp only [Expr.sub_var_rename])

def SubDeriv.section (hΓ : CtxDeriv Γ γ) (hA : TyDeriv Γ γ A a)
    (hx : TmDeriv Γ γ A a x ξ) :
    SubDeriv Γ γ (A :: Γ) (extendCode γ a) (consSub x Expr.var) (sectionCode a ξ) :=
  .pair hA (.id hΓ) (hx.convert (.symm (.subId hA)))

theorem pathFamilyRaw_at (A x y : Expr) :
    (Expr.identity (A.rename Nat.succ) (x.rename Nat.succ) (.var 0)).sub (consSub y Expr.var) =
      .identity A x y := by
  simp only [Expr.sub, Expr.sub_rename]
  have h : consSub y Expr.var ∘ Nat.succ = Expr.var := rfl
  rw [h, Expr.sub_id, Expr.sub_id]
  rfl

def SubDeriv.endpoint (hΓ : CtxDeriv Γ γ) (hA : TyDeriv Γ γ A a)
    (hx : TmDeriv Γ γ A a x ξ) (hy : TmDeriv Γ γ A a y υ)
    (hp : TmDeriv Γ γ (.identity A x y) (identityCode a ξ υ) p π) :
    SubDeriv Γ γ (pathCtx Γ A x) (pathCode a ξ) (consSub p (consSub y Expr.var))
      (endpointCode a ξ υ π) :=
  .pair (.pathFamily hΓ hA hx) (.section hΓ hA hy)
    ((hp.rawType (pathFamilyRaw_at A x y).symm).annotateType (pathFamilyAt_code a ξ υ).symm)

end SquareKit.Internal.PathTransport.Typed

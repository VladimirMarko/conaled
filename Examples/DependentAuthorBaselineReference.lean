import SquareKit.Internal.PathTransport.Authoring
import SquareKit.Internal.DependentJudgments.Sigma.Stability
/-! Coordinator reference for the frozen dependent author trial (#320).
This source is excluded from measured author handoffs. Its experimental scope
and prospective evidence are recorded in docs/research/dependent-author-interface-trial.md. -/
namespace DependentAuthorReference.Baseline
open SquareKit.Internal SquareKit.Internal.PathTransport Typed Authoring
universe u
variable {Γ : RawCtx} {γ : CtxCode.{u}} {A x : Expr} {a : TyCode γ}
  {ξ : TmCode γ a} {n : Nat} {Ξ : RawCtx} {T : TelCode (pathCode a ξ) n}
  {Q p : Expr} {q : TyCode (telTotal T)} {π : TmCode (telTotal T) q}
variable (hΓ : CtxDeriv Γ γ) (hA : TyDeriv Γ γ A a) (hx : TmDeriv Γ γ A a x ξ)
  (hT : TelDeriv (pathCtx Γ A x) (pathCode a ξ) n Ξ T)
  (hQ : TyDeriv (Ξ ++ pathCtx Γ A x) (telTotal T) Q q)
  (hp : TmDeriv (Ξ ++ pathCtx Γ A x) (telTotal T) Q q p π)

def calibration (cmd : @PathCommand Γ γ A x a ξ n Ξ T)
    {Δ : RawCtx} {δ : CtxCode.{u}} {σ : RawSub} {s : SubCode δ γ}
    (hσ : SubDeriv Δ δ Γ γ σ s) := cmd.rebuildConversion hσ

def calibrationLeft (cmd : @PathCommand Γ γ A x a ξ n Ξ T)
    {Δ : RawCtx} {δ : CtxCode.{u}} {σ : RawSub} {s : SubCode δ γ}
    (hσ : SubDeriv Δ δ Γ γ σ s) := cmd.substitutedTerm hσ

def calibrationRight (cmd : @PathCommand Γ γ A x a ξ n Ξ T)
    {Δ : RawCtx} {δ : CtxCode.{u}} {σ : RawSub} {s : SubCode δ γ}
    (hΔ : CtxDeriv Δ δ) (hσ : SubDeriv Δ δ Γ γ σ s) := (cmd.rebuild hΔ hσ).genericTerm

def certificateCommand := PathCommand.make hΓ hA hx hT (Motive.reflexivity hΓ hA hx hT hQ hp)
def certificate := (certificateCommand hΓ hA hx hT hQ hp).genericTerm

variable {Δ Θ : RawCtx} {δ θ : CtxCode.{u}} {σ τ : RawSub}
  {s : SubCode δ (telTotal T)} {t : SubCode θ δ}
variable (hσ : SubDeriv Δ δ (Ξ ++ pathCtx Γ A x) (telTotal T) σ s)
  (hτ : SubDeriv Θ θ Δ δ τ t)

def valueTwice := TmDeriv.sub (TmDeriv.sub hp hσ) hτ
def certificateTwice := TmDeriv.sub (TmDeriv.sub (certificate hΓ hA hx hT hQ hp) hσ) hτ
def valueTypeComparison := TyEqDeriv.subComp hQ hσ hτ
def valueComparison := TmEqDeriv.subComp hp hσ hτ
def certificateTypeComparison := TyEqDeriv.subComp (TyDeriv.identity hQ hp hp) hσ hτ
def certificateComparison := TmEqDeriv.subComp (certificate hΓ hA hx hT hQ hp) hσ hτ

def certificateAligned := (certificateTwice hΓ hA hx hT hQ hp hσ hτ).convert
  (certificateTypeComparison hQ hp hσ hτ)

theorem valueValidity (M : Model.{u}) :
    interpretTm M (valueTwice hp hσ hτ) = subTmCode (subTmCode π s) t M :=
  interpretTm_agrees M _

theorem interpretedCertificateType (M : Model.{u}) :
    interpretTy M (TyDeriv.sub (TyDeriv.sub (TyDeriv.identity hQ hp hp) hσ) hτ) =
      subTyCode (subTyCode (identityCode q π π) s) t M :=
  interpretTy_agrees M _

-- A stable extension carries this exact underlying full model; interpretation
-- of old Typed source uses its reduct and does not invent a Sigma source rule.
theorem extensionSelected (M : Model.{u})
    (_S : DependentJudgments.Sigma.Stable M.toStructuralModel) :
    interpretTm M (certificateTwice hΓ hA hx hT hQ hp hσ hτ) =
    subTmCode (subTmCode
      (jCode a ξ T (certificateCommand hΓ hA hx hT hQ hp).motive.code
        (certificateCommand hΓ hA hx hT hQ hp).motive.branchCode) s) t M :=
  interpretTm_agrees M _

theorem certificateValidity (M : Model.{u}) :
    interpretTm M (certificateTwice hΓ hA hx hT hQ hp hσ hτ) =
    subTmCode (subTmCode
      (jCode a ξ T (certificateCommand hΓ hA hx hT hQ hp).motive.code
        (certificateCommand hΓ hA hx hT hQ hp).motive.branchCode) s) t M :=
  interpretTm_agrees M _

theorem extensionValue (M : Model.{u})
    (_S : DependentJudgments.Sigma.Stable M.toStructuralModel) :
    interpretTm M (valueTwice hp hσ hτ) = subTmCode (subTmCode π s) t M :=
  valueValidity hp hσ hτ M

include hQ hp hσ hτ in
theorem certificateTypeValidity (M : Model.{u}) :
    subTyCode (subTyCode (identityCode q π π) s) t M =
      subTyCode (identityCode q π π) (compCode s t) M :=
  congrFun (typeSound (certificateTypeComparison hQ hp hσ hτ)) M

include hQ hp hσ hτ in
theorem extensionType (M : Model.{u})
    (_S : DependentJudgments.Sigma.Stable M.toStructuralModel) :
    subTyCode (subTyCode (identityCode q π π) s) t M =
      subTyCode (identityCode q π π) (compCode s t) M :=
  congrFun (typeSound (certificateTypeComparison hQ hp hσ hτ)) M

def resultContext := CtxDeriv.telescope (CtxDeriv.path hΓ hA hx) hT
def firstWeakening := SubDeriv.weaken (resultContext hΓ hA hx hT) (TyDeriv.identity hQ hp hp)
def witnessVariable := TmDeriv.var (resultContext hΓ hA hx hT) (TyDeriv.identity hQ hp hp)
def secondFamily := TyDeriv.identity
  (show TyDeriv _ _ (Expr.rename Nat.succ (Expr.identity Q p p)) _ from by
    simpa only [Expr.sub_var_rename] using
      TyDeriv.sub (TyDeriv.identity hQ hp hp) (firstWeakening hΓ hA hx hT hQ hp))
  (witnessVariable hΓ hA hx hT hQ hp) (witnessVariable hΓ hA hx hT hQ hp)
def secondWeakening := SubDeriv.weaken
  (CtxDeriv.ext (resultContext hΓ hA hx hT) (TyDeriv.identity hQ hp hp))
  (secondFamily hΓ hA hx hT hQ hp)
def dependentWeakeningCertificate := certificateTwice hΓ hA hx hT hQ hp
  (firstWeakening hΓ hA hx hT hQ hp) (secondWeakening hΓ hA hx hT hQ hp)
def dependentWeakeningComparison := certificateComparison hΓ hA hx hT hQ hp
  (firstWeakening hΓ hA hx hT hQ hp) (secondWeakening hΓ hA hx hT hQ hp)
end DependentAuthorReference.Baseline

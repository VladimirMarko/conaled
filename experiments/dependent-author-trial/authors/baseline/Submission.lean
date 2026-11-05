import SquareKit.Internal.PathTransport.Authoring
import SquareKit.Internal.DependentJudgments.Sigma.Stability

namespace DependentAuthorTrial.Baseline
open SquareKit.Internal.PathTransport
open SquareKit.Internal.PathTransport.Typed
open SquareKit.Internal.PathTransport.Typed.Authoring

universe u
section Calibration
variable {Γ Ω : RawCtx} {γ ω : CtxCode.{u}} {A x : Expr} {a : TyCode γ}
  {ξ : TmCode γ a} {n : Nat} {Ξ : RawCtx} {T : TelCode (pathCode a ξ) n}
  {σ : RawSub} {s : SubCode ω γ}

def calibration (cmd : @PathCommand Γ γ A x a ξ n Ξ T)
    (hσ : SubDeriv Ω ω Γ γ σ s) := cmd.rebuildConversion hσ

def calibrationLeft (cmd : @PathCommand Γ γ A x a ξ n Ξ T)
    (hσ : SubDeriv Ω ω Γ γ σ s) := cmd.substitutedTerm hσ

def calibrationRight (cmd : @PathCommand Γ γ A x a ξ n Ξ T)
    (hΩ : CtxDeriv Ω ω) (hσ : SubDeriv Ω ω Γ γ σ s) :=
  (cmd.rebuild hΩ hσ).genericTerm

end Calibration

section HeldOut
variable {Γ Ξ Δ Θ : RawCtx} {γ δ θ : CtxCode.{u}} {A x Q p : Expr}
  {a : TyCode γ} {ξ : TmCode γ a} {n : Nat} {T : TelCode (pathCode a ξ) n}
  {q : TyCode (telTotal T)} {π : TmCode (telTotal T) q}
  (hΓ : CtxDeriv Γ γ) (hA : TyDeriv Γ γ A a) (hx : TmDeriv Γ γ A a x ξ)
  (hT : TelDeriv (pathCtx Γ A x) (pathCode a ξ) n Ξ T)
  (hQ : TyDeriv (Ξ ++ pathCtx Γ A x) (telTotal T) Q q)
  (hp : TmDeriv (Ξ ++ pathCtx Γ A x) (telTotal T) Q q p π)

-- Motive.reflexivity constructs the root-tail substitution and converts
-- refl(p[r]) along the symmetry of the source identity-substitution equation.
def certificateCommand := PathCommand.make hΓ hA hx hT
  (Motive.reflexivity hΓ hA hx hT hQ hp)

def certificate := (certificateCommand hΓ hA hx hT hQ hp).genericTerm

def certificateFamily := TyDeriv.identity hQ hp hp

def totalContext := CtxDeriv.telescope (CtxDeriv.path hΓ hA hx) hT

variable {σ τ : RawSub} {s : SubCode δ (telTotal T)} {t : SubCode θ δ}
  (hσ : SubDeriv Δ δ (Ξ ++ pathCtx Γ A x) (telTotal T) σ s)
  (hτ : SubDeriv Θ θ Δ δ τ t)

def valueTwice := TmDeriv.sub (TmDeriv.sub hp hσ) hτ

def certificateTwice := TmDeriv.sub
  (TmDeriv.sub (certificate hΓ hA hx hT hQ hp) hσ) hτ

def valueTypeComparison := TyEqDeriv.subComp hQ hσ hτ

def certificateTypeComparison := TyEqDeriv.subComp (certificateFamily hQ hp) hσ hτ

def valueComparison := TmEqDeriv.subComp hp hσ hτ

def certificateComparison := TmEqDeriv.subComp (certificate hΓ hA hx hT hQ hp) hσ hτ

def certificateAligned := (certificateTwice hΓ hA hx hT hQ hp hσ hτ).convert
  (certificateTypeComparison hQ hp hσ hτ)

def firstWeakening := SubDeriv.weaken (totalContext hΓ hA hx hT) (certificateFamily hQ hp)

def firstContext := CtxDeriv.ext (totalContext hΓ hA hx hT) (certificateFamily hQ hp)

def witnessVariable :
    TmDeriv ((Expr.identity Q p p) :: (Ξ ++ pathCtx Γ A x))
      (extendCode (telTotal T) (identityCode q π π))
      ((Expr.identity Q p p).sub (Expr.var ∘ Nat.succ))
      (subTyCode (identityCode q π π) (weakenCode (telTotal T) (identityCode q π π)))
      (.var 0) (varCode (telTotal T) (identityCode q π π)) := by
  rw [Expr.sub_var_rename]
  exact TmDeriv.var (totalContext hΓ hA hx hT) (certificateFamily hQ hp)

def secondFamily := TyDeriv.identity
  (TyDeriv.sub (certificateFamily hQ hp) (firstWeakening hΓ hA hx hT hQ hp))
  (witnessVariable hΓ hA hx hT hQ hp) (witnessVariable hΓ hA hx hT hQ hp)

def secondWeakening := SubDeriv.weaken (firstContext hΓ hA hx hT hQ hp)
  (secondFamily hΓ hA hx hT hQ hp)

def dependentWeakeningCertificate := certificateTwice hΓ hA hx hT hQ hp
  (firstWeakening hΓ hA hx hT hQ hp) (secondWeakening hΓ hA hx hT hQ hp)

def dependentWeakeningComparison := certificateComparison hΓ hA hx hT hQ hp
  (firstWeakening hΓ hA hx hT hQ hp) (secondWeakening hΓ hA hx hT hQ hp)

theorem valueValidity (M : Model.{u}) :
    interpretTm M (valueTwice hp hσ hτ) = subTmCode (subTmCode π s) t M :=
  interpretTm_agrees M _

theorem certificateValidity (M : Model.{u}) :
    interpretTm M (certificateTwice hΓ hA hx hT hQ hp hσ hτ) =
      subTmCode (subTmCode
        (jCode a ξ T (certificateCommand hΓ hA hx hT hQ hp).motive.code
          (certificateCommand hΓ hA hx hT hQ hp).motive.branchCode) s) t M :=
  interpretTm_agrees M _

include hQ hp hσ hτ in
theorem certificateTypeValidity (M : Model.{u}) :
    subTyCode (subTyCode (identityCode q π π) s) t M =
      subTyCode (identityCode q π π) (compCode s t) M :=
  congrFun (typeSound (certificateTypeComparison hQ hp hσ hτ)) M

theorem extensionSelected (M : Model.{u})
    (_S : SquareKit.Internal.DependentJudgments.Sigma.Stable M.toStructuralModel) :
    interpretTm M (certificateTwice hΓ hA hx hT hQ hp hσ hτ) =
      subTmCode (subTmCode
        (jCode a ξ T (certificateCommand hΓ hA hx hT hQ hp).motive.code
          (certificateCommand hΓ hA hx hT hQ hp).motive.branchCode) s) t M :=
  certificateValidity hΓ hA hx hT hQ hp hσ hτ M

theorem extensionValue (M : Model.{u})
    (_S : SquareKit.Internal.DependentJudgments.Sigma.Stable M.toStructuralModel) :
    interpretTm M (valueTwice hp hσ hτ) = subTmCode (subTmCode π s) t M :=
  valueValidity hp hσ hτ M

include hQ hp hσ hτ in
theorem extensionType (M : Model.{u})
    (_S : SquareKit.Internal.DependentJudgments.Sigma.Stable M.toStructuralModel) :
    subTyCode (subTyCode (identityCode q π π) s) t M =
      subTyCode (identityCode q π π) (compCode s t) M :=
  certificateTypeValidity hQ hp hσ hτ M


-- The extension supplies a full Typed model. Its old-language reduct is exact,
-- so this source derivation is reused unchanged; no source Sigma rule is used.
def extendedCertificate (M : Model.{u})
    (_S : SquareKit.Internal.DependentJudgments.Sigma.Stable M.toStructuralModel) :=
  certificate hΓ hA hx hT hQ hp

theorem extendedValidity (M : Model.{u})
    (S : SquareKit.Internal.DependentJudgments.Sigma.Stable M.toStructuralModel) :
    interpretTm M (extendedCertificate hΓ hA hx hT hQ hp M S) =
      jCode a ξ T (identityCode q π π)
        (certificateCommand hΓ hA hx hT hQ hp).motive.branchCode M :=
  interpretTm_agrees M _

def valueComposite := TmDeriv.sub hp (SubDeriv.comp hσ hτ)

def certificateComposite := TmDeriv.sub (certificate hΓ hA hx hT hQ hp)
  (SubDeriv.comp hσ hτ)

theorem interpretedCertificateComparison (M : Model.{u}) :
    interpretTm M (certificateAligned hΓ hA hx hT hQ hp hσ hτ) =
      interpretTm M (certificateComposite hΓ hA hx hT hQ hp hσ hτ) := by
  rw [interpretTm_agrees, interpretTm_agrees]
  exact congrFun (termSound (certificateComparison hΓ hA hx hT hQ hp hσ hτ)) M

theorem interpretedCertificateTypeComparison (M : Model.{u}) :
    interpretTy M (TyDeriv.sub (TyDeriv.sub (certificateFamily hQ hp) hσ) hτ) =
      interpretTy M (TyDeriv.sub (certificateFamily hQ hp) (SubDeriv.comp hσ hτ)) := by
  rw [interpretTy_agrees, interpretTy_agrees]
  exact certificateTypeValidity hQ hp hσ hτ M

end HeldOut
-- A disclosed concrete source instance retains the z, q and fiber tail.
def workedCertificate := certificate NamedCaller.earlier NamedCaller.base
  NamedCaller.x.deriv NamedCaller.generalized NamedCaller.qAtBType NamedCaller.qAtB

def workedDependentWeakening := dependentWeakeningCertificate NamedCaller.earlier
  NamedCaller.base NamedCaller.x.deriv NamedCaller.generalized
  NamedCaller.qAtBType NamedCaller.qAtB

def workedDependentComparison := dependentWeakeningComparison NamedCaller.earlier
  NamedCaller.base NamedCaller.x.deriv NamedCaller.generalized
  NamedCaller.qAtBType NamedCaller.qAtB

end DependentAuthorTrial.Baseline

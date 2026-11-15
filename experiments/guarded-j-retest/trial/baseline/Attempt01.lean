import SquareKit.Internal.PathTransport.Authoring
import SquareKit.Internal.DependentJudgments.Sigma.Stability
namespace GuardedJRetest.Baseline
open SquareKit.Internal.PathTransport
open SquareKit.Internal.PathTransport.Typed
open SquareKit.Internal.PathTransport.Typed.Authoring
universe u
variable {Γ : RawCtx} {γ : CtxCode.{u}} {A x : Expr} {a : TyCode γ}
  {ξ : TmCode γ a} {n : Nat} {Δ : RawCtx} {T : TelCode (pathCode a ξ) n}
  {Q p : Expr} {q : TyCode (telTotal T)} {π : TmCode (telTotal T) q}
  (hΓ : CtxDeriv Γ γ) (hA : TyDeriv Γ γ A a) (hx : TmDeriv Γ γ A a x ξ)
  (hT : TelDeriv (pathCtx Γ A x) (pathCode a ξ) n Δ T)
  (hQ : TyDeriv (Δ ++ pathCtx Γ A x) (telTotal T) Q q)
  (hp : TmDeriv (Δ ++ pathCtx Γ A x) (telTotal T) Q q p π)

def rootMap := SubDeriv.rootTail hΓ hA hx hT

def calibration : @PathCommand Γ γ A x a ξ n Δ T :=
  PathCommand.make hΓ hA hx hT (Motive.reflexivity hΓ hA hx hT hQ hp)

def inner : TmDeriv (Δ ++ pathCtx Γ A x) (telTotal T)
    (.identity Q p p) (identityCode q π π)
    (genericJRaw n A x (.identity Q p p)
      (.refl (p.sub (Expr.liftSubN n (reflexiveSub x)))))
    (jCode a ξ T (calibration hΓ hA hx hT hQ hp).motive.code
      (calibration hΓ hA hx hT hQ hp).motive.branchCode) :=
  (calibration hΓ hA hx hT hQ hp).genericTerm

def calibrationBranch := (calibration hΓ hA hx hT hQ hp).motive.branchTyping
end GuardedJRetest.Baseline

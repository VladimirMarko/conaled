import SquareKit.Internal.PathTransport.Authoring
import SquareKit.Internal.DependentJudgments.Sigma.Stability

namespace DependentAuthorTrial.Baseline
open SquareKit.Internal.PathTransport
open SquareKit.Internal.PathTransport.Typed
open SquareKit.Internal.PathTransport.Typed.Authoring

universe u
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

end DependentAuthorTrial.Baseline

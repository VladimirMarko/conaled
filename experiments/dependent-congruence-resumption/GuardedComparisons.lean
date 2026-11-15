import SquareKit.Internal.DependentJudgments.TransportReindexing
import SquareKit.Internal.DependentJudgments.Templates

/-! The already adopted guarded boundary supplies fresh-operation comparison
without semantic indices. Its concatenation recipe differs from the legacy
left-path eliminator, so this is comparison evidence, not a migration proof. -/
namespace SquareKit.Internal.DependentJudgments.Contextual.ResumptionExperiment
open SquareKit.GuardedTheory
variable {V : Type} {Ω : List (Judgment V)}
variable {Γ Δ A x y z p q σ : Expression V}

/-- Arbitrary generated typed substitutions, with no all-model equality
arguments at the caller. This uses the existing right-path concat recipe. -/
def concatFresh
    (hx : Tm (Ω := Ω) Γ A x) (hy : Tm (Ω := Ω) Γ A y)
    (hz : Tm (Ω := Ω) Γ A z)
    (hp : Tm (Ω := Ω) Γ (Contextual.identity A x y) p)
    (hq : Tm (Ω := Ω) Γ (Contextual.identity A y z) q)
    (hσ : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (Contextual.subTm (Contextual.concat Γ A x y z p q) σ)
      (Contextual.concat Δ (Contextual.subTy A σ) (Contextual.subTm x σ)
        (Contextual.subTm y σ) (Contextual.subTm z σ)
        (Contextual.subTm p σ) (Contextual.subTm q σ)) :=
  hx.concatSub hy hz hp hq hσ

/-- Both typing derivations and source equality for an arbitrary finite-tail
command are builder outputs, not compatibility premises supplied by a caller. -/
def commandFresh (c : Command Ω Γ A x) (hσ : Sub (Ω := Ω) Δ Γ σ) :=
  c.comparison hσ

end SquareKit.Internal.DependentJudgments.Contextual.ResumptionExperiment

import SquareKit.Internal.DependentJudgments.Templates

namespace DependentAuthorTrial.Candidate
open SquareKit.Internal.DependentJudgments.Contextual

variable {V : Type} {Ω : List (Judgment V)}
variable {Γ Δ A x σ : Expression V}

/-- One-step comparison retains both source operand derivations. -/
def calibration (c : Command Ω Γ A x) (hσ : Sub (Ω := Ω) Δ Γ σ) :
    TypedEquality Ω (total (pathTail A x c.tail σ))
      (subTy c.motive (pathTailMap A x c.tail σ))
      (subTm c.expression (pathTailMap A x c.tail σ)) (c.fresh hσ).expression :=
  c.comparison hσ

end DependentAuthorTrial.Candidate

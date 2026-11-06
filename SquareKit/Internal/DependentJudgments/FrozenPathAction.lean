import SquareKit.Internal.DependentJudgments.FixedPathTransportSource
import SquareKit.Internal.DependentJudgments.OrdinaryActionSource
import SquareKit.Internal.DependentJudgments.FrozenContexts
/-! Ordinary path action on the original frozen selected homotopy. -/
noncomputable section
namespace SquareKit.Internal.DependentJudgments.Contextual.Memo.Frozen
variable {V : Type} {Ω : List (Contextual.Judgment V)}
abbrev Input.pathAction (F : Input Ω) :=
 Contextual.ordinaryAp F.Γ (Contextual.identity F.A F.x F.y) (Contextual.identity F.A F.x F.y)
 F.p F.p' F.h (Contextual.fixedPathTransportTerm F.Γ F.A F.x F.y)
def Input.pathAction_typed (F : Input Ω) : Contextual.Tm (Ω := Ω) F.Γ
 (Contextual.identity (Contextual.identity F.A F.x F.y)
  (Contextual.ordinaryApply F.Γ (Contextual.identity F.A F.x F.y) F.p (Contextual.fixedPathTransportTerm F.Γ F.A F.x F.y))
  (Contextual.ordinaryApply F.Γ (Contextual.identity F.A F.x F.y) F.p' (Contextual.fixedPathTransportTerm F.Γ F.A F.x F.y)))
 F.pathAction :=
 Contextual.Tm.ordinaryAp (F.hx.identity F.hy) (Contextual.Tm.fixedPathTransportTerm F.hx F.hy) F.hp F.hp' F.hh
end SquareKit.Internal.DependentJudgments.Contextual.Memo.Frozen

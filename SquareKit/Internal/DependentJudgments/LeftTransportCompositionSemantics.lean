import SquareKit.Internal.DependentJudgments.LeftTransportCompositionArguments
import SquareKit.Internal.DependentJudgments.PresentedSoundness
import SquareKit.Internal.DependentJudgments.DerivedPathSemantics

/-! Sound interpretation of the generated transport-composition certificate.
The selected witness is the evaluation of that source term. -/
noncomputable section
namespace SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation
open GuardedTheory
set_option backward.isDefEq.respectTransparency false
universe u
variable {V : Type} {Ω : List (Judgment V)} {Γ : Expression V}
namespace LeftTransportComposition.Inputs
variable (C : Inputs Ω Γ) (M : PathTransport.Typed.Model.{u})
  (ρ : V → Value M.toStructuralModel)
  (hρ : ∀ a ∈ Ω, a.eval (model M).toAlgebra ρ)

include hρ
/-- After identifying the interpreted endpoints, soundness retains the value
of the first-path source certificate as the selected equality witness. -/
theorem certificate_evaluates (G : M.Context) (B : M.Family G)
    (left right : M.Section G B)
    (hg : Γ.eval (algebra M) ρ = .context G)
    (hb : C.resultType.eval (algebra M) ρ = .family G B)
    (hl : C.left.eval (algebra M) ρ = .term G B left)
    (hr : C.right.eval (algebra M) ρ = .term G B right) :
    ∃ selected : M.Section G (M.identity B left right),
      C.certificate.eval (algebra M) ρ = .term G (M.identity B left right) selected :=
  C.composition.evaluates M ρ hρ G _ hg
    (DerivedSemantics.identity_eval M ρ C.resultType C.left C.right G B left right hb hl hr)
end LeftTransportComposition.Inputs
end SquareKit.Internal.DependentJudgments.Contextual.TelescopePresentation

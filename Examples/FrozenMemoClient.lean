import Examples.FrozenMemoSignature

/-! A complete interpretation interface for the frozen contextual client.
The constructor derives all output equations from its two source declarations. -/
noncomputable section
namespace Examples.FrozenMemoRealization
open SquareKit.Internal.DependentJudgments
open SquareKit.Internal.DependentJudgments.Contextual.Memo
universe u
structure Client (M : SquareKit.Internal.PathTransport.Typed.Model.{u}) {V : Type}
    {Ω : List (Contextual.Judgment V)} (ρ : V → Value M.toStructuralModel)
    (S : Frozen.Signature Ω) where
  input : InputRealization M ρ S.input
  delta : InputRealization M ρ S.deltaInput
  theta : InputRealization M ρ S.thetaInput
  certificate_twice :
    (Contextual.subTm (Contextual.subTm (S.input.parameters.certificate S.input.p)
      S.sigma) S.tau).eval (Contextual.algebra M) ρ =
    .term theta.context _ theta.selectedCertificate
  dependentAction_twice :
    (Contextual.subTm (Contextual.subTm
      (S.input.parameters.dependentAction S.input.p S.input.p' S.input.h)
      S.sigma) S.tau).eval (Contextual.algebra M) ρ =
    .term theta.context theta.dependentActionFamily theta.dependentAction

def Client.ofTyping (M : SquareKit.Internal.PathTransport.Typed.Model.{u}) {V : Type}
    {Ω : List (Contextual.Judgment V)} (ρ : V → Value M.toStructuralModel)
    (hΩ : ∀ j ∈ Ω, j.eval (Contextual.algebra M) ρ) (S : Frozen.Signature Ω) : Client M ρ S where
  input := InputRealization.ofTyping M ρ hΩ S.input
  delta := InputRealization.ofTyping M ρ hΩ S.deltaInput
  theta := InputRealization.ofTyping M ρ hΩ S.thetaInput
  certificate_twice := certificate_twice_eval M ρ hΩ S (InputRealization.ofTyping M ρ hΩ S.thetaInput)
  dependentAction_twice := dependentAction_twice_eval M ρ hΩ S (InputRealization.ofTyping M ρ hΩ S.thetaInput)

end Examples.FrozenMemoRealization

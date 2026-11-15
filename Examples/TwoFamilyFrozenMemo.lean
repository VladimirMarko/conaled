import Examples.FrozenMemoClient
import Examples.FrozenMemoPairReindex
import SquareKit.Internal.PathTransport.TwoFamilyFullModel

/-! The unchanged frozen client in the constructed strict 2-groupoid model.
Its families may be any admitted higher families, including dependent paths. -/
noncomputable section
namespace Examples.TwoFamilyFrozenMemo
open SquareKit.Internal.PathTransport.HigherInterpretation
open SquareKit.Internal.DependentJudgments
open Examples.GuardedGroupoidMemo
universe u
variable (C D : Context.{u})
local notation "M" => fullModel C D
variable (A : Family Context.empty) (B : Family A.total)

def environment := FrozenMemoSignature.environment M A B

def client : FrozenMemoRealization.Client M (environment C D A B) signature :=
  FrozenMemoRealization.Client.ofTyping M (environment C D A B)
    (FrozenMemoSignature.inputs M A B) signature

def pair := (client C D A B).input.selectedPair (fullSigma C D).toCapability

abbrev sourcePair := MemoPair.sourcePair signature.input.Γ
  (signature.input.parameters.fiber signature.input.p)
  (signature.input.parameters.compositeValue signature.input.p)
  (signature.input.parameters.value signature.input.p)
  (signature.input.parameters.certificate signature.input.p)

theorem pair_twice : ∃ (Δ Θ : (M).Context)
    (σ : (M).Substitution Δ (client C D A B).input.context) (τ : (M).Substitution Θ Δ),
    signature.sigma.eval (Contextual.algebra M) (environment C D A B) =
      .substitution Δ (client C D A B).input.context σ ∧
    signature.tau.eval (Contextual.algebra M) (environment C D A B) = .substitution Θ Δ τ ∧
    (Sigma.subTm (Sigma.subTm sourcePair (signature.sigma.inl Sigma.extraSignature))
      (signature.tau.inl Sigma.extraSignature)).eval
        (Sigma.algebra M (fullSigma C D).toCapability) (environment C D A B) =
      .term Θ _ ((M).subTm ((M).subTm (pair C D A B) σ) τ) :=  FrozenMemoRealization.FrozenSignature.pair_twice M
  (fullSigma C D).toCapability (environment C D A B)
  (FrozenMemoSignature.inputs M A B) signature (client C D A B).input

end Examples.TwoFamilyFrozenMemo

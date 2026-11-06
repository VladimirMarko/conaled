import Examples.FrozenMemoInput
import Examples.FrozenMemoSubstitutions

/-! Interpret the original empty-context signature using two selected families.
No primitive substitutions or output certificates are added to its premises. -/
noncomputable section
namespace Examples.FrozenMemoSignature
open SquareKit.Internal.DependentJudgments
open Examples.GuardedGroupoidMemo
open Examples.FrozenMemoRealization
universe u
variable (M : SquareKit.Internal.PathTransport.Typed.Model.{u})
variable (A : M.Family M.empty) (B : M.Family (M.extend M.empty A))

def environment : Fin 2 → Value M.toStructuralModel :=
  ![.family M.empty A, .family (M.extend M.empty A) B]

theorem inputs : ∀ j ∈ premises, j.eval (Contextual.algebra M) (environment M A B) := by
  intro j hj
  simp only [premises, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl
  · exact ⟨M.empty,A,rfl,rfl⟩
  · exact ⟨M.extend M.empty A,B,
      extend_eval M (environment M A B) Contextual.empty alpha M.empty A rfl rfl,rfl⟩

def input : FrozenMemoRealization.InputRealization M (environment M A B) signature.input :=
  FrozenMemoRealization.InputRealization.ofTyping M (environment M A B) (inputs M A B) signature.input

def delta : FrozenMemoRealization.InputRealization M (environment M A B) signature.deltaInput :=
  FrozenMemoRealization.InputRealization.ofTyping M (environment M A B) (inputs M A B) signature.deltaInput

def theta : FrozenMemoRealization.InputRealization M (environment M A B) signature.thetaInput :=
  FrozenMemoRealization.InputRealization.ofTyping M (environment M A B) (inputs M A B) signature.thetaInput

theorem certificate_twice :
    (Contextual.subTm (Contextual.subTm (signature.input.parameters.certificate signature.input.p)
      signature.sigma) signature.tau).eval (Contextual.algebra M) (environment M A B) =
    .term (theta M A B).context _ (theta M A B).selectedCertificate :=
  FrozenMemoRealization.certificate_twice_eval M (environment M A B) (inputs M A B) signature (theta M A B)

theorem dependentAction_twice :
    (Contextual.subTm (Contextual.subTm
      (signature.input.parameters.dependentAction signature.input.p signature.input.p' signature.input.h)
      signature.sigma) signature.tau).eval (Contextual.algebra M) (environment M A B) =
    .term (theta M A B).context (theta M A B).dependentActionFamily (theta M A B).dependentAction :=
  FrozenMemoRealization.dependentAction_twice_eval M (environment M A B) (inputs M A B) signature (theta M A B)

end Examples.FrozenMemoSignature

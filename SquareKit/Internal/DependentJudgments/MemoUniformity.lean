import SquareKit.Internal.DependentJudgments.FrozenMemo
import SquareKit.Internal.DependentJudgments.TypedMaps

/-! Selected memo observations inherit strict-model preservation from their
source derivations, including the action after both frozen substitutions. -/
namespace SquareKit.Internal.DependentJudgments.Contextual.Memo
open GuardedTheory PathTransport.Typed
set_option backward.isDefEq.respectTransparency false
universe u v
variable {V : Type} {Ω : List (Judgment V)}
variable {M : Model.{u}} {N : Model.{v}} (map : ModelMap M N)
variable (ρ : V → Value M.toStructuralModel) (hΩ : ∀ a ∈ Ω, a.eval (algebra M) ρ)
include hΩ

namespace Parameters
variable (F : Parameters Ω) {p p' h : Expression V}
  (hp : Tm (Ω := Ω) F.Γ F.pathType p) (hp' : Tm (Ω := Ω) F.Γ F.pathType p')
  (hh : Tm (Ω := Ω) F.Γ (identity F.pathType p p') h)

include hp

theorem value_map :
    Value.map map.toStructuralMap ((F.value p).eval (algebra M) ρ) =
      (F.value p).eval (algebra N) (Value.map map.toStructuralMap ∘ ρ) :=
  (F.value_typed hp).interpret_map map ρ hΩ

theorem certificate_map :
    Value.map map.toStructuralMap ((F.certificate p).eval (algebra M) ρ) =
      (F.certificate p).eval (algebra N) (Value.map map.toStructuralMap ∘ ρ) :=
  (F.certificate_typed hp).interpret_map map ρ hΩ

include hp' hh

theorem dependentAction_map :
    Value.map map.toStructuralMap ((F.dependentAction p p' h).eval (algebra M) ρ) =
      (F.dependentAction p p' h).eval (algebra N) (Value.map map.toStructuralMap ∘ ρ) :=
  (F.dependentAction_typed hp hp' hh).interpret_map map ρ hΩ

end Parameters

namespace Frozen.Signature
variable (S : Signature Ω)

theorem certificate_twice_map :
    Value.map map.toStructuralMap
      ((subTm (subTm (S.input.parameters.certificate S.input.p) S.sigma) S.tau).eval (algebra M) ρ) =
    (subTm (subTm (S.input.parameters.certificate S.input.p) S.sigma) S.tau).eval
      (algebra N) (Value.map map.toStructuralMap ∘ ρ) :=
  (((S.input.parameters.certificate_typed S.input.hp).substitute S.sigma_typed).substitute S.tau_typed).interpret_map map ρ hΩ

theorem dependentAction_twice_map :
    Value.map map.toStructuralMap
      ((subTm (subTm (S.input.parameters.dependentAction S.input.p S.input.p' S.input.h) S.sigma) S.tau).eval (algebra M) ρ) =
    (subTm (subTm (S.input.parameters.dependentAction S.input.p S.input.p' S.input.h) S.sigma) S.tau).eval
      (algebra N) (Value.map map.toStructuralMap ∘ ρ) :=
  (((S.input.parameters.dependentAction_typed S.input.hp S.input.hp' S.input.hh).substitute S.sigma_typed).substitute S.tau_typed).interpret_map map ρ hΩ

/-- Reusing the complete target derivation transports typed equality premises;
the resulting comparison is the generated fresh-action equation. -/
theorem freshAction_target (typed : TypedAssumptions Ω) :
    (subTm (subTm (S.input.parameters.dependentAction S.input.p S.input.p' S.input.h) S.sigma) S.tau).eval
      (algebra N) (Value.map map.toStructuralMap ∘ ρ) =
    (((S.input.reindex S.sigma_typed).reindex S.tau_typed).parameters.dependentAction
      (subTm (subTm S.input.p S.sigma) S.tau)
      (subTm (subTm S.input.p' S.sigma) S.tau)
      (subTm (subTm S.input.h S.sigma) S.tau)).eval
      (algebra N) (Value.map map.toStructuralMap ∘ ρ) :=
  interpret_target S.dependentAction_twice map typed ρ hΩ

end Frozen.Signature
end SquareKit.Internal.DependentJudgments.Contextual.Memo

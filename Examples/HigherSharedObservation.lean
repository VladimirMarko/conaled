import Examples.CubicalSharedAssignment
import Examples.ReferenceHigherSharedMeaning

/-! Observe the shared compiler's actual twice-substituted higher witness. -/
noncomputable section
namespace Examples.HigherSharedObservation
open SquareKit.Internal.DependentJudgments
open SquareKit.Internal.DependentJudgments.Contextual
open Reference
open SquareKit.Cubical SquareKit.Cubical.Presheaf SquareKit.Cubical.CategoryCocycles
open Examples.CubicalCocycleAssignment Examples.FrozenMemoStages
open Examples.CubicalSharedAssignment Examples.ReferenceHigherSharedMeaning
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
set_option maxHeartbeats 4000000

private def readLike {M : SquareKit.Internal.PathTransport.Typed.StructuralModel}
    {Γ : M.Context} {A : M.Family Γ} (_ : M.Section Γ A) (v : Value M) := v.termAt Γ A

/-- Decode the actual shared target, retaining its final dependent context. -/
def recovered := readLike (tauHomotopy cocycleModel cocycleBase cocycleRootedFamily).value
  ((SelectedMeaning.realization cocycleModel (Fin 2)).decode
    (FrozenMemoSignature.environment cocycleModel cocycleBase cocycleRootedFamily) _
    ((shared cocycleModel).realization.map
      (FrozenMemoSignature.environment cocycleModel cocycleBase cocycleRootedFamily)
      witnessJudgment (SelectedMeaning.quote (p := witnessJudgment) ReferenceHigherTheoryMaps.witness_twice)))

theorem recovered_eq : recovered = some (tauHomotopy cocycleModel cocycleBase cocycleRootedFamily).value := by
  unfold recovered
  rw [selected_witness]
  exact Value.termAt_term _ _ _

/-- The cast normalizes a proved family equality. The selected value comes
from decoding the compiled expression, not from the normalization proof. -/
def observation : Option Int := recovered.map (fun h =>
  secondObservation (cast (type_eq_of_heq retainedTauHomotopy) (h.down.reindex assignFinal)))

theorem observation_one : observation = some 1 := by
  unfold observation
  rw [recovered_eq]
  change some (secondObservation normalizedTauHomotopy) = some 1
  rw [tauObservation_one]

theorem rejects_truncation : observation ≠ some 0 := by
  rw [observation_one]
  exact fun h => Int.one_ne_zero (Option.some.inj h)

theorem rejects_reflexive : observation ≠ some (secondObservation (secondZero terminal.{0})) := by
  rw [secondObservation_zero]
  exact rejects_truncation

end Examples.HigherSharedObservation

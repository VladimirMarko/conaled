import SquareKit.AssemblyCountdownExtension

/-! Internal iteration retains finite observations and selects through full cuts. -/
namespace InternalCountdown
open Realizability Realizability.Assembly

private def enabled : Hom (encoded Nat) (encoded Bool) :=
  ofComputable (fun _ : Nat => true) (Computable.const true)
private def disabled : Hom (encoded Nat) (encoded Bool) :=
  ofComputable (fun _ : Nat => false) (Computable.const false)

example : ((strictIteration sequenceAlgebra (countdown enabled (Hom.id _))).toFun
    ((3 : Nat),⟨2⟩)).toFun (1 : Nat) = some (4 : Nat) :=
  countdown_iteration _ _ _ _ _

example : ((strictIteration sequenceAlgebra (countdown enabled (Hom.id _))).toFun
    ((3 : Nat),⟨2⟩)).toFun (2 : Nat) = none :=
  countdown_iteration _ _ _ _ _

example : ((cutSelected sequenceAlgebra partialSequences_complete
    (countdown enabled (Hom.id _))).toFun (3 : Nat)).toFun (2 : Nat) = some (5 : Nat) :=
  countdown_selected _ _ _ _

example : ((cutSelected sequenceAlgebra partialSequences_complete
    (countdown disabled (Hom.id _))).toFun (3 : Nat)).toFun (2 : Nat) = none :=
  countdown_selected _ _ _ _

example (q : partialSequences.Carrier) :
    (countdown disabled (Hom.id _)).toFun ((3 : Nat),q) = q := by
  apply Hom.ext
  intro k
  exact countdown_apply _ _ _ _ k

example (k : Nat) : (sequenceFlatten.toFun none).toFun k = none := rfl
example (k : Nat) : (sequenceFlatten.toFun (some (sequenceFlatten.toFun none))).toFun k = none := rfl

end InternalCountdown

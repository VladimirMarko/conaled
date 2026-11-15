import SquareKit.AssemblySequenceTransport
import SquareKit.AssemblyLiftStrength

/-! Coordinate flattening equips complete partial sequences with a strict algebra. -/
namespace Realizability.Assembly
open CategoryTheory

/-- Emit each coordinate before waiting for the outer partial sequence. -/
noncomputable def sequenceFlatten : Hom (programLift partialSequences) partialSequences :=
  curry ((swap (programLift partialSequences) (encoded Nat)).comp
    ((liftStrength (encoded Nat) partialSequences).comp
      ((programLiftMap ((swap (encoded Nat) partialSequences).comp
        (evaluation (encoded Nat) (programLift (encoded Nat))))).comp
        (programLiftMul (encoded Nat)))))

theorem sequenceFlatten_apply (q : Option partialSequences.Carrier) (k : Nat) :
    ((sequenceFlatten.toFun q).toFun k) = q.bind (fun s => s.toFun k) := by
  cases q <;> rfl

noncomputable def sequenceAlgebra : Monad.Algebra programLiftMonad where
  A := partialSequences
  a := sequenceFlatten
  unit := by
    apply Hom.ext
    intro q
    apply Hom.ext
    intro k
    rfl
  assoc := by
    apply Hom.ext
    intro q
    apply Hom.ext
    intro k
    cases q with
    | none => rfl
    | some q => cases q <;> rfl

theorem sequenceFlatten_bounded (n : Nat) (q : Option (boundedSequences n).Carrier) :
    SequenceBounded n (sequenceFlatten.toFun (q.map Subtype.val)) := by
  intro k v hv
  cases q with
  | none => cases hv
  | some q => exact q.property k v hv

noncomputable def boundedSequenceFlatten (n : Nat) :
    Hom (programLift (boundedSequences n)) (boundedSequences n) :=
  factor _ ((programLiftMap (inclusion _ _)).comp sequenceFlatten)
    (sequenceFlatten_bounded n)

noncomputable def boundedSequenceAlgebra (n : Nat) : Monad.Algebra programLiftMonad where
  A := boundedSequences n
  a := boundedSequenceFlatten n
  unit := by
    apply Hom.ext
    intro q
    apply Subtype.ext
    apply Hom.ext
    intro k
    rfl
  assoc := by
    apply Hom.ext
    intro q
    apply Subtype.ext
    apply Hom.ext
    intro k
    cases q with
    | none => rfl
    | some q => cases q <;> rfl

noncomputable def boundedSequenceInclusion (n : Nat) :
    Monad.Algebra.Hom (boundedSequenceAlgebra n) sequenceAlgebra where
  f := inclusion _ _
  h := by
    apply Hom.ext
    intro q
    apply Hom.ext
    intro k
    cases q <;> rfl

noncomputable def sequenceShiftAlgebra (d : Nat) :
    Monad.Algebra.Hom sequenceAlgebra sequenceAlgebra where
  f := sequenceShift d
  h := by
    apply Hom.ext
    intro q
    apply Hom.ext
    intro k
    change Nat at k
    cases q with
    | none => exact (sequenceShift_apply d (sequenceFlatten.toFun none) k).symm
    | some q => exact (sequenceShift_apply d q k).symm

noncomputable def boundedShiftAlgebra {n m : Nat} (d : Nat) (hd : n+d ≤ m) :
    Monad.Algebra.Hom (boundedSequenceAlgebra n) (boundedSequenceAlgebra m) where
  f := boundedShift d hd
  h := by
    apply Hom.ext
    intro q
    apply Subtype.ext
    apply Hom.ext
    intro k
    change Nat at k
    cases q with
    | none => exact (sequenceShift_apply d (sequenceFlatten.toFun none) k).symm
    | some q => exact (sequenceShift_apply d q.val k).symm

end Realizability.Assembly

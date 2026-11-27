import SquareKit.Internal.Cubical.NativeStructureSethood
import SquareKit.Internal.Cubical.CartesianNativeStructureSethood
import Examples.NativeStructureCoherence

/-! Actual integer admissions exercise whole-path sethood and complete recovery. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.NativeStructureSethood
open CategoryTheory
namespace Presheaf
open SquareKit.Cubical.Presheaf StructureIdentity.Coherence
open StructureIdentity.Native StructuredIdentity StructuredIdentity.UaComparison
open Examples.NativeStructureCoherence.Presheaf
open Examples.NativeLatticeTransport.Presheaf (admission carrierSet)
variable {Γ : Context.{1}}

variable (admitted : SmallUniverse.LargeConstructors.Result (constantFamily Γ (ULift.{1} ℤ)))
noncomputable abbrev fromSystem := system admitted 0
noncomputable abbrev toSystem := system admitted 1
noncomputable abbrev whole := homogeneousPath (objects description Γ)
  (objectOf description admitted.code (fromSystem admitted).fields)
  (objectOf description admitted.code (toSystem admitted).fields)

noncomputable def integerWholeSet : Term (HomotopyLevels.isSet (whole admitted)) :=
  wholePathsIsSet description admitted.code admitted.code
    (fromSystem admitted).fields (toSystem admitted).fields (carrierSet admitted)

noncomputable def selected : Term (whole admitted) :=
  Coded.path (a := admitted.code) (b := admitted.code)
    (move admitted 0 1)

/-- The selected inverse recovers the supplied map, fiber witness and preservation together. -/
noncomputable def completeEquivalenceRecovery :=
  explicitLeftInverseAt description admitted.code (fromSystem admitted).fields
    admitted.code (toSystem admitted).fields (move admitted 0 1).native

/-- The other recovery retains the original whole path. -/
noncomputable def completePathRecovery :=
  explicitRightInverseAt description admitted.code (fromSystem admitted).fields
    admitted.code (toSystem admitted).fields (selected admitted)

noncomputable def integerThreePath (p q : Term (whole admitted))
    (H K : Term (homogeneousPath (whole admitted) p q)) :
    Term (homogeneousPath (homogeneousPath (whole admitted) p q) H K) :=
  wholeThreePath description admitted.code admitted.code
    (fromSystem admitted).fields (toSystem admitted).fields (carrierSet admitted) p q H K

/-- Two constructed 2-paths share the selected whole path as both endpoints. -/
noncomputable def doubleRefl : Term (homogeneousPath (whole admitted) (selected admitted) (selected admitted)) := by
  let O := objectsFilling description Γ
  let W := pathFilling (O.1.reindex (projection (interval Γ))) (O.2.reindex _)
    (objectOf description admitted.code (fromSystem admitted).fields)
    (objectOf description admitted.code (toSystem admitted).fields)
  have hW := pathFilling_lawful (O.1.reindex (projection (interval Γ))) (O.2.reindex _)
    (objectOf description admitted.code (fromSystem admitted).fields)
    (objectOf description admitted.code (toSystem admitted).fields)
  let p := selected admitted
  exact homogeneousConcat W hW (homogeneousRefl p) (homogeneousRefl p)

noncomputable def constructedThreePath :=
  integerThreePath admitted (selected admitted) (selected admitted)
    (homogeneousRefl (selected admitted)) (doubleRefl admitted)

/-- Actual admissions specialize the generic checked constructions. -/
noncomputable def actualIntegerWholeSet := integerWholeSet (Γ := Γ) (admission ℤ)
noncomputable def actualIntegerThreePath := constructedThreePath (Γ := Γ) (admission ℤ)
noncomputable def actualEquivalenceRecovery := completeEquivalenceRecovery (Γ := Γ) (admission ℤ)
noncomputable def actualPathRecovery := completePathRecovery (Γ := Γ) (admission ℤ)

namespace Lattice
open StructureIdentity.Native Examples.CompositionalStructureIdentity
open Examples.NativeLatticeTransport.Presheaf
variable {X Y : Type} [Lattice X] [Lattice Y]
  (a : SmallUniverse.LargeConstructors.Result (constantFamily Γ (ULift.{1} X)))
  (b : SmallUniverse.LargeConstructors.Result (constantFamily Γ (ULift.{1} Y))) (e : X ≃o Y)

noncomputable def wholeSet :=
  wholePathsIsSet rawLattice a.code b.code (fields a) (movedFields a b e) (carrierSet b)

/-- Compare the existing lattice whole-path comparison with another supplied parallel 2-path. -/
noncomputable def compare
    (q : Term (homogeneousPath (objects rawLattice Γ)
      (objectOf rawLattice a.code (fields a)) (objectOf rawLattice b.code (movedFields a b e))))
    (h : Term (homogeneousPath (SmallUniverse.NativeUnivalence.paths a.code b.code)
      (Term.map (carrierProjection rawLattice a.code b.code (fields a) (movedFields a b e)) (rawPath a b e))
      (Term.map (carrierProjection rawLattice a.code b.code (fields a) (movedFields a b e)) q)))
    (K : Term (homogeneousPath (homogeneousPath (objects rawLattice Γ)
      (objectOf rawLattice a.code (fields a)) (objectOf rawLattice b.code (movedFields a b e)))
      (rawPath a b e) q)) :=
  wholeThreePath rawLattice a.code b.code (fields a) (movedFields a b e) (carrierSet b)
    (rawPath a b e) q (LatticeControl.compare a b e q h) K
end Lattice
end Presheaf
namespace Cartesian
open SquareKit.Cubical.Cartesian StructureIdentity.Coherence
open StructureIdentity.Native StructuredIdentity StructuredIdentity.UaComparison
open Examples.NativeStructureCoherence.Cartesian
open Examples.NativeLatticeTransport.Cartesian (admission carrierSet)
variable {Γ : Context.{1}}

variable (admitted : SmallUniverse.LargeConstructors.Result (constantFamily Γ (ULift.{1} ℤ)))
noncomputable abbrev fromSystem := system admitted 0
noncomputable abbrev toSystem := system admitted 1
noncomputable abbrev whole := homogeneousPath (objects description Γ)
  (objectOf description admitted.code (fromSystem admitted).fields)
  (objectOf description admitted.code (toSystem admitted).fields)

noncomputable def integerWholeSet : Term (HomotopyLevels.isSet (whole admitted)) :=
  wholePathsIsSet description admitted.code admitted.code
    (fromSystem admitted).fields (toSystem admitted).fields (carrierSet admitted)

noncomputable def selected : Term (whole admitted) :=
  Coded.path (a := admitted.code) (b := admitted.code)
    (move admitted 0 1)

/-- The selected inverse recovers the supplied map, fiber witness and preservation together. -/
noncomputable def completeEquivalenceRecovery :=
  explicitLeftInverseAt description admitted.code (fromSystem admitted).fields
    admitted.code (toSystem admitted).fields (move admitted 0 1).native

/-- The other recovery retains the original whole path. -/
noncomputable def completePathRecovery :=
  explicitRightInverseAt description admitted.code (fromSystem admitted).fields
    admitted.code (toSystem admitted).fields (selected admitted)

noncomputable def integerThreePath (p q : Term (whole admitted))
    (H K : Term (homogeneousPath (whole admitted) p q)) :
    Term (homogeneousPath (homogeneousPath (whole admitted) p q) H K) :=
  wholeThreePath description admitted.code admitted.code
    (fromSystem admitted).fields (toSystem admitted).fields (carrierSet admitted) p q H K

/-- Two constructed 2-paths share the selected whole path as both endpoints. -/
noncomputable def doubleRefl : Term (homogeneousPath (whole admitted) (selected admitted) (selected admitted)) := by
  let O := objectsFilling description Γ
  let W := pathFilling (O.1.reindex (projection (interval Γ))) (O.2.reindex _)
    (objectOf description admitted.code (fromSystem admitted).fields)
    (objectOf description admitted.code (toSystem admitted).fields)
  have hW := pathFilling_lawful (O.1.reindex (projection (interval Γ))) (O.2.reindex _)
    (objectOf description admitted.code (fromSystem admitted).fields)
    (objectOf description admitted.code (toSystem admitted).fields)
  let p := selected admitted
  exact homogeneousConcat W hW (homogeneousRefl p) (homogeneousRefl p)

noncomputable def constructedThreePath :=
  integerThreePath admitted (selected admitted) (selected admitted)
    (homogeneousRefl (selected admitted)) (doubleRefl admitted)

/-- Actual admissions specialize the generic checked constructions. -/
noncomputable def actualIntegerWholeSet := integerWholeSet (Γ := Γ) (admission ℤ)
noncomputable def actualIntegerThreePath := constructedThreePath (Γ := Γ) (admission ℤ)
noncomputable def actualEquivalenceRecovery := completeEquivalenceRecovery (Γ := Γ) (admission ℤ)
noncomputable def actualPathRecovery := completePathRecovery (Γ := Γ) (admission ℤ)

namespace Lattice
open StructureIdentity.Native Examples.CompositionalStructureIdentity
open Examples.NativeLatticeTransport.Cartesian
variable {X Y : Type} [Lattice X] [Lattice Y]
  (a : SmallUniverse.LargeConstructors.Result (constantFamily Γ (ULift.{1} X)))
  (b : SmallUniverse.LargeConstructors.Result (constantFamily Γ (ULift.{1} Y))) (e : X ≃o Y)

noncomputable def wholeSet :=
  wholePathsIsSet rawLattice a.code b.code (fields a) (movedFields a b e) (carrierSet b)

/-- Compare the existing lattice whole-path comparison with another supplied parallel 2-path. -/
noncomputable def compare
    (q : Term (homogeneousPath (objects rawLattice Γ)
      (objectOf rawLattice a.code (fields a)) (objectOf rawLattice b.code (movedFields a b e))))
    (h : Term (homogeneousPath (SmallUniverse.NativeUnivalence.paths a.code b.code)
      (Term.map (carrierProjection rawLattice a.code b.code (fields a) (movedFields a b e)) (rawPath a b e))
      (Term.map (carrierProjection rawLattice a.code b.code (fields a) (movedFields a b e)) q)))
    (K : Term (homogeneousPath (homogeneousPath (objects rawLattice Γ)
      (objectOf rawLattice a.code (fields a)) (objectOf rawLattice b.code (movedFields a b e)))
      (rawPath a b e) q)) :=
  wholeThreePath rawLattice a.code b.code (fields a) (movedFields a b e) (carrierSet b)
    (rawPath a b e) q (LatticeControl.compare a b e q h) K
end Lattice
end Cartesian
end Examples.NativeStructureSethood

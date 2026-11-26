import Examples.CubicalNativeUnivalenceSectionBeta
import SquareKit.Internal.Cubical.NativeUnivalence

set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalNativeUnivalence
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open Examples.CubicalGlue Examples.CubicalUnivalenceTransport
open CubicalNativeUnivalenceUa CubicalNativeUnivalenceSectionBeta
open SmallUniverse.NativeUnivalence

noncomputable def booleanUnivalence :=
  univalence (constantLocal terminal Bool).code (constantLocal terminal Bool).code

/-- The path produced by decoding the full actual transport equivalence is
natively homotopic to the original nonidentity Boolean universe loop. -/
noncomputable def recoveredBooleanLoopPath : Term (homogeneousPath
    (paths (constantLocal terminal Bool).code (constantLocal terminal Bool).code)
    recoveredBooleanLoop booleanUniverseLoop) := by
  let a := (constantLocal terminal Bool).code
  let p := leftInverseAt a a booleanUniverseLoop
  exact pathLam (pathApp p)
    ((pathApp_zero p).trans equivToPath_booleanInternalEquivalence) (pathApp_one p)

/-- The right inverse retains the entire chosen internal transport witness. -/
noncomputable def booleanEquivalenceRoundtrip :=
  rightInverseAt (constantLocal terminal Bool).code (constantLocal terminal Bool).code
    (𝟙 (raisedContext terminal)) booleanInternalEquivalence

noncomputable def integerUnivalence :=
  univalence (constantLocal terminal Int).code (constantLocal terminal Int).code

/-- The same theorem applies after adjoining an interval parameter. -/
noncomputable def booleanIntervalUnivalence :=
  univalence
    (projection (interval (raisedContext terminal)) ≫ (constantLocal terminal Bool).code)
    (projection (interval (raisedContext terminal)) ≫ (constantLocal terminal Bool).code)

end Examples.CubicalNativeUnivalence

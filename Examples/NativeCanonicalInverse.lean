import Examples.NativeStructureCoherence

/-! A typed boundary for the complete canonical inverse witness and its whole
selected structure-path comparison. The supplied-witness client stays available. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace Examples.NativeCanonicalInverse
open CategoryTheory SquareKit.Cubical.Presheaf
open StructureIdentity.Coherence StructureIdentity.Native
open Examples.NativeStructureCoherence.Presheaf
variable {Γ : Context.{1}}
variable (admitted : SmallUniverse.LargeConstructors.Result (constantFamily Γ (ULift.{1} ℤ)))

/-- Name the full canonical witness before specializing the dependent comparison.
No contraction or inverse data is replaced with the strict-isomorphism witness. -/
def witness : HomotopyEquivalence (move (Γ := Γ) admitted 0 1).witness.selectedInverse :=
  (move admitted 0 1).witness.selectedInverseEquivalence
    (SmallUniverse.NativeDecode.filling admitted.code) (SmallUniverse.NativeDecode.filling_lawful _)
    (SmallUniverse.NativeDecode.filling admitted.code) (SmallUniverse.NativeDecode.filling_lawful _)

/-- Both endpoints are the original admitted selected structure paths. -/
def comparison :=
  Coded.inversion (a := admitted.code) (b := admitted.code)
    (s := system admitted 0) (t := system admitted 1) (move admitted 0 1)
    (witness admitted) (Examples.NativeLatticeTransport.Presheaf.carrierSet admitted)

/-- The canonical route at the same actual integer admission as the direct client. -/
def actualComparison {Γ : Context.{1}} :=
  comparison (Examples.NativeLatticeTransport.Presheaf.admission (Γ := Γ) ℤ)

end Examples.NativeCanonicalInverse

import PrivateMathematics
import Examples.CubicalAuthorTransport

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace JournalTrial.Author
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open Examples.CubicalStateTransport Examples.CubicalStatePackageFamily
open Examples.CubicalStatePackageUa Examples.CubicalStructuredState
open Examples.CubicalUnivalenceTransport Examples.CubicalGlue
variable (E : HomotopyEquivalence nativeMap)
open Examples.CubicalAuthorTransport
noncomputable def change : Change Journals Journals := ⟨nativeMap, E⟩

noncomputable def mainPath : NativePath E sourceLength targetLength := by
  have hp : Preserves (change E).carrier sourceLength targetLength := by
    apply Preserves.of_eq
    change sourceLength.conjugate (admittedCarrier (S := Journals) (T := Journals) nativeMap E) = targetLength
    rw [Private.carrier E]; exact Private.length_eq
  simpa only [Change.PackagePath, Change.line, Change.carrier, change] using
    (change E).path (p := sourceLength) (q := targetLength) hp
noncomputable def mainSection : Term (package (admittedLine (S := Journals) (T := Journals) nativeMap E)).family :=
  (change E).nativeSection sourceLength
theorem mainSection_exact : mainSection E = transported (S := Journals) (T := Journals) nativeMap E sourceLength := rfl
 theorem mainSection_recovery : mainSection E =
    pullPackage (admittedLine (S := Journals) (T := Journals) nativeMap E)
      (admittedPresentation (S := Journals) (T := Journals) nativeMap E)
      (sourceLength.conjugate (admittedCarrier (S := Journals) (T := Journals) nativeMap E)) :=
  (change E).native_recovery sourceLength
noncomputable def mainDecoded : StatePackage Journals :=
  (change E).transport sourceLength
theorem mainDecoded_exact : mainDecoded E = targetPackage (S := Journals) (T := Journals) nativeMap E sourceLength := rfl
 theorem mainDecoded_target : mainDecoded E = targetLength := by
  apply (change E).transport_of_preserves
  apply Preserves.of_eq
  change sourceLength.conjugate (admittedCarrier (S := Journals) (T := Journals) nativeMap E) = targetLength
  rw [Private.carrier E]; exact Private.length_eq
theorem mainPath_recovery :
    (uaStructureIdentity (S := Journals) (T := Journals) nativeMap E sourceLength targetLength).symm
      ((uaStructureIdentity (S := Journals) (T := Journals) nativeMap E sourceLength targetLength) (mainPath E)) = mainPath E :=
  by
    exact (uaStructureIdentity (S := Journals) (T := Journals) nativeMap E sourceLength targetLength).symm_apply_apply (mainPath E)

noncomputable def variationPath : NativePath E sourceSum targetSum := by
  have hp : Preserves (change E).carrier sourceSum targetSum := by
    apply Preserves.of_eq
    change sourceSum.conjugate (admittedCarrier (S := Journals) (T := Journals) nativeMap E) = targetSum
    rw [Private.carrier E]; exact Private.sum_eq
  simpa only [Change.PackagePath, Change.line, Change.carrier, change] using
    (change E).path (p := sourceSum) (q := targetSum) hp
noncomputable def variationSection : Term (package (admittedLine (S := Journals) (T := Journals) nativeMap E)).family :=
  (change E).nativeSection sourceSum
theorem variationSection_exact : variationSection E = transported (S := Journals) (T := Journals) nativeMap E sourceSum := rfl
 theorem variationSection_recovery : variationSection E =
    pullPackage (admittedLine (S := Journals) (T := Journals) nativeMap E)
      (admittedPresentation (S := Journals) (T := Journals) nativeMap E)
      (sourceSum.conjugate (admittedCarrier (S := Journals) (T := Journals) nativeMap E)) :=
  (change E).native_recovery sourceSum
noncomputable def variationDecoded : StatePackage Journals :=
  (change E).transport sourceSum
theorem variationDecoded_exact : variationDecoded E = targetPackage (S := Journals) (T := Journals) nativeMap E sourceSum := rfl
 theorem variationDecoded_target : variationDecoded E = targetSum := by
  apply (change E).transport_of_preserves
  apply Preserves.of_eq
  change sourceSum.conjugate (admittedCarrier (S := Journals) (T := Journals) nativeMap E) = targetSum
  rw [Private.carrier E]; exact Private.sum_eq
theorem variationPath_recovery :
    (uaStructureIdentity (S := Journals) (T := Journals) nativeMap E sourceSum targetSum).symm
      ((uaStructureIdentity (S := Journals) (T := Journals) nativeMap E sourceSum targetSum) (variationPath E)) = variationPath E :=
  by
    exact (uaStructureIdentity (S := Journals) (T := Journals) nativeMap E sourceSum targetSum).symm_apply_apply (variationPath E)
theorem reject : IsEmpty (NativePath E sourceLength badTarget) := by
  refine ⟨fun r => ?_⟩
  have h := ((uaStructureIdentity (S := Journals) (T := Journals) nativeMap E sourceLength badTarget) r).invariant
  rw [Private.carrier E] at h
  have hx := congrFun h (([0] : List Nat), [])
  change (([0] : List Nat).reverse.length = ([] : List Nat).reverse.length) = True at hx
  simp at hx
end JournalTrial.Author

import PrivateMathematics

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace JournalTrial.Author
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open Examples.CubicalStateTransport Examples.CubicalStatePackageFamily
open Examples.CubicalStatePackageUa Examples.CubicalStructuredState
open Examples.CubicalUnivalenceTransport Examples.CubicalGlue
variable (E : HomotopyEquivalence nativeMap)

noncomputable def mainPath : NativePath E sourceLength targetLength :=
  (uaStructureIdentity (S := Journals) (T := Journals) nativeMap E sourceLength targetLength).symm
    (Preserves.of_eq (by rw [Private.carrier E]; exact Private.length_eq))
noncomputable def mainSection : Term (package (admittedLine (S := Journals) (T := Journals) nativeMap E)).family :=
  transported (S := Journals) (T := Journals) nativeMap E sourceLength
theorem mainSection_exact : mainSection E = transported (S := Journals) (T := Journals) nativeMap E sourceLength := rfl
 theorem mainSection_recovery : mainSection E =
    pullPackage (admittedLine (S := Journals) (T := Journals) nativeMap E)
      (admittedPresentation (S := Journals) (T := Journals) nativeMap E)
      (sourceLength.conjugate (admittedCarrier (S := Journals) (T := Journals) nativeMap E)) :=
  transported_recovery (S := Journals) (T := Journals) nativeMap E sourceLength
noncomputable def mainDecoded : StatePackage Journals :=
  targetPackage (S := Journals) (T := Journals) nativeMap E sourceLength
theorem mainDecoded_exact : mainDecoded E = targetPackage (S := Journals) (T := Journals) nativeMap E sourceLength := rfl
 theorem mainDecoded_target : mainDecoded E = targetLength := by
  rw [mainDecoded, targetPackage_eq, Private.carrier E]
  exact Private.length_eq
theorem mainPath_recovery :
    (uaStructureIdentity (S := Journals) (T := Journals) nativeMap E sourceLength targetLength).symm
      ((uaStructureIdentity (S := Journals) (T := Journals) nativeMap E sourceLength targetLength) (mainPath E)) = mainPath E :=
  (uaStructureIdentity (S := Journals) (T := Journals) nativeMap E sourceLength targetLength).symm_apply_apply _

noncomputable def variationPath : NativePath E sourceSum targetSum :=
  (uaStructureIdentity (S := Journals) (T := Journals) nativeMap E sourceSum targetSum).symm
    (Preserves.of_eq (by rw [Private.carrier E]; exact Private.sum_eq))
noncomputable def variationSection : Term (package (admittedLine (S := Journals) (T := Journals) nativeMap E)).family :=
  transported (S := Journals) (T := Journals) nativeMap E sourceSum
theorem variationSection_exact : variationSection E = transported (S := Journals) (T := Journals) nativeMap E sourceSum := rfl
 theorem variationSection_recovery : variationSection E =
    pullPackage (admittedLine (S := Journals) (T := Journals) nativeMap E)
      (admittedPresentation (S := Journals) (T := Journals) nativeMap E)
      (sourceSum.conjugate (admittedCarrier (S := Journals) (T := Journals) nativeMap E)) :=
  transported_recovery (S := Journals) (T := Journals) nativeMap E sourceSum
noncomputable def variationDecoded : StatePackage Journals :=
  targetPackage (S := Journals) (T := Journals) nativeMap E sourceSum
theorem variationDecoded_exact : variationDecoded E = targetPackage (S := Journals) (T := Journals) nativeMap E sourceSum := rfl
 theorem variationDecoded_target : variationDecoded E = targetSum := by
  rw [variationDecoded, targetPackage_eq, Private.carrier E]
  exact Private.sum_eq
theorem variationPath_recovery :
    (uaStructureIdentity (S := Journals) (T := Journals) nativeMap E sourceSum targetSum).symm
      ((uaStructureIdentity (S := Journals) (T := Journals) nativeMap E sourceSum targetSum) (variationPath E)) = variationPath E :=
  (uaStructureIdentity (S := Journals) (T := Journals) nativeMap E sourceSum targetSum).symm_apply_apply _
theorem reject : IsEmpty (NativePath E sourceLength badTarget) := by
  refine ⟨fun r => ?_⟩
  have h := ((uaStructureIdentity (S := Journals) (T := Journals) nativeMap E sourceLength badTarget) r).invariant
  rw [Private.carrier E] at h
  have hx := congrFun h (([0] : List Nat), [])
  change (([0] : List Nat).reverse.length = ([] : List Nat).reverse.length) = True at hx
  simp at hx
end JournalTrial.Author

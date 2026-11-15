import Examples.UnivalentAuthorTrial.Task
import Examples.CubicalAuthorTransport

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace JournalTrial.FacadeAuthor
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open Examples.CubicalStateTransport Examples.CubicalStatePackageFamily
open Examples.CubicalStatePackageUa Examples.CubicalStructuredState
open Examples.CubicalUnivalenceTransport Examples.CubicalGlue
open Examples.CubicalAuthorTransport

variable (E : HomotopyEquivalence nativeMap)

def change : Change Journals Journals := ⟨nativeMap, E⟩

theorem carrier_eq : (change E).carrier = reverseJournals := by
  apply Equiv.ext
  intro s
  change (constantLocal _ Journals).decodeCodeIso.hom.app point
    ((codeIso reverseJournals).hom.app point
      ((constantLocal _ Journals).decodeCodeIso.inv.app point s)) = reverseJournals s
  exact congrArg (fun t => t.val point) (codeIso_action reverseJournals s)

theorem length_preserved : Preserves (change E).carrier sourceLength targetLength := by
  rw [carrier_eq]
  apply Preserves.of_eq
  apply statePackage_ext
  · rfl
  · funext s
    simp [StatePackage.conjugate, sourceLength, targetLength, reverseJournals]
  · funext s
    simp [StatePackage.conjugate, sourceLength, targetLength, reverseJournals]

theorem sum_preserved : Preserves (change E).carrier sourceSum targetSum := by
  rw [carrier_eq]
  apply Preserves.of_eq
  apply statePackage_ext
  · rfl
  · funext s
    simp [StatePackage.conjugate, sourceSum, targetSum, reverseJournals]
  · funext s
    simp [StatePackage.conjugate, sourceSum, targetSum, reverseJournals]

def mainPath : NativePath E sourceLength targetLength :=
  (uaStructureIdentity nativeMap E sourceLength targetLength).symm (length_preserved E)

def mainSection : Term (package (admittedLine nativeMap E)).family :=
  (change E).nativeSection sourceLength

theorem mainSection_exact : mainSection E = transported nativeMap E sourceLength := rfl

theorem mainSection_recovery : mainSection E =
    pullPackage (admittedLine nativeMap E) (admittedPresentation nativeMap E)
      (sourceLength.conjugate (admittedCarrier nativeMap E)) :=
  (change E).native_recovery sourceLength

def mainDecoded : StatePackage Journals := (change E).transport sourceLength

theorem mainDecoded_exact : mainDecoded E = targetPackage nativeMap E sourceLength := rfl

theorem mainDecoded_target : mainDecoded E = targetLength :=
  (change E).transport_of_preserves (length_preserved E)

theorem mainPath_recovery :
    (uaStructureIdentity nativeMap E sourceLength targetLength).symm
      ((uaStructureIdentity nativeMap E sourceLength targetLength) (mainPath E)) =
        mainPath E := (uaStructureIdentity nativeMap E sourceLength targetLength).symm_apply_apply (mainPath E)

def variationPath : NativePath E sourceSum targetSum :=
  (uaStructureIdentity nativeMap E sourceSum targetSum).symm (sum_preserved E)

def variationSection : Term (package (admittedLine nativeMap E)).family :=
  (change E).nativeSection sourceSum

theorem variationSection_exact : variationSection E = transported nativeMap E sourceSum := rfl

theorem variationSection_recovery : variationSection E =
    pullPackage (admittedLine nativeMap E) (admittedPresentation nativeMap E)
      (sourceSum.conjugate (admittedCarrier nativeMap E)) :=
  (change E).native_recovery sourceSum

def variationDecoded : StatePackage Journals := (change E).transport sourceSum

theorem variationDecoded_exact : variationDecoded E = targetPackage nativeMap E sourceSum := rfl

theorem variationDecoded_target : variationDecoded E = targetSum :=
  (change E).transport_of_preserves (sum_preserved E)

theorem variationPath_recovery :
    (uaStructureIdentity nativeMap E sourceSum targetSum).symm
      ((uaStructureIdentity nativeMap E sourceSum targetSum) (variationPath E)) =
        variationPath E := (uaStructureIdentity nativeMap E sourceSum targetSum).symm_apply_apply (variationPath E)

theorem reject : IsEmpty (NativePath E sourceLength badTarget) := by
  refine ⟨fun r => ?_⟩
  have h := (change E).packageIdentity sourceLength badTarget r
  rw [carrier_eq] at h
  have hi := congrFun h.invariant ([1], [])
  have hf : False := by simpa [StatePackage.conjugate, sourceLength, badTarget,
    reverseJournals] using (Eq.mpr hi trivial)
  exact hf

example : (mainDecoded E).step ([2,3], [5]) = ([1,2,3], [1,5]) := by
  rw [mainDecoded_target]
  rfl

example : (variationDecoded E).invariant ([2,3], [5]) ∧
    ¬ (mainDecoded E).invariant ([2,3], [5]) := by
  rw [variationDecoded_target, mainDecoded_target]
  simp [targetSum, targetLength]

example : (mainDecoded E).invariant ([2], [3]) ∧
    ¬ (variationDecoded E).invariant ([2], [3]) := by
  rw [variationDecoded_target, mainDecoded_target]
  simp [targetSum, targetLength]

end JournalTrial.FacadeAuthor
end

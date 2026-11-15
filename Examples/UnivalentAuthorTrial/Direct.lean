import Examples.UnivalentAuthorTrial.Task

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
noncomputable section
namespace JournalTrial.DirectAuthor
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open Examples.CubicalStateTransport Examples.CubicalStatePackageFamily
open Examples.CubicalStatePackageUa Examples.CubicalStructuredState
open Examples.CubicalUnivalenceTransport Examples.CubicalGlue

 theorem carrier_of_codeIso {S T : Type} (e : S ≃ T)
    (E : HomotopyEquivalence (codeIso e).hom) :
    admittedCarrier (codeIso e).hom E = e := by
  apply Equiv.ext
  intro s
  change (constantLocal _ T).decodeCodeIso.hom.app point
    ((codeIso e).hom.app point ((constantLocal _ S).decodeCodeIso.inv.app point s)) = e s
  exact congrArg (fun t => t.val point) (codeIso_action e s)

variable (E : HomotopyEquivalence nativeMap)

theorem carrier_eq : admittedCarrier nativeMap E = reverseJournals :=
  carrier_of_codeIso reverseJournals E

theorem length_conjugate : sourceLength.conjugate reverseJournals = targetLength := by
  apply statePackage_ext
  · rfl
  · funext s
    simp [StatePackage.conjugate, sourceLength, targetLength, reverseJournals]
  · funext s
    simp [StatePackage.conjugate, sourceLength, targetLength, reverseJournals]

def mainPath : NativePath E sourceLength targetLength :=
  (uaStructureIdentity nativeMap E sourceLength targetLength).symm
    (Preserves.of_eq (by rw [carrier_eq E]; exact length_conjugate))

def mainSection := transported nativeMap E sourceLength

theorem mainSection_exact : mainSection E = transported nativeMap E sourceLength := rfl

theorem mainSection_recovery : mainSection E =
    pullPackage (admittedLine nativeMap E) (admittedPresentation nativeMap E)
      (sourceLength.conjugate (admittedCarrier nativeMap E)) :=
  transported_recovery nativeMap E sourceLength

def mainDecoded := targetPackage nativeMap E sourceLength

theorem mainDecoded_exact : mainDecoded E = targetPackage nativeMap E sourceLength := rfl

theorem mainDecoded_target : mainDecoded E = targetLength := by
  rw [mainDecoded, targetPackage_eq, carrier_eq E, length_conjugate]

theorem mainPath_recovery :
    (uaStructureIdentity nativeMap E sourceLength targetLength).symm
      ((uaStructureIdentity nativeMap E sourceLength targetLength) (mainPath E)) = mainPath E :=
  (uaStructureIdentity nativeMap E sourceLength targetLength).symm_apply_apply _

theorem sum_conjugate : sourceSum.conjugate reverseJournals = targetSum := by
  apply statePackage_ext
  · rfl
  · funext s
    simp [StatePackage.conjugate, sourceSum, targetSum, reverseJournals]
  · funext s
    simp [StatePackage.conjugate, sourceSum, targetSum, reverseJournals]

def variationPath : NativePath E sourceSum targetSum :=
  (uaStructureIdentity nativeMap E sourceSum targetSum).symm
    (Preserves.of_eq (by rw [carrier_eq E]; exact sum_conjugate))

def variationSection := transported nativeMap E sourceSum

theorem variationSection_exact : variationSection E = transported nativeMap E sourceSum := rfl

theorem variationSection_recovery : variationSection E =
    pullPackage (admittedLine nativeMap E) (admittedPresentation nativeMap E)
      (sourceSum.conjugate (admittedCarrier nativeMap E)) :=
  transported_recovery nativeMap E sourceSum

def variationDecoded := targetPackage nativeMap E sourceSum

theorem variationDecoded_exact : variationDecoded E = targetPackage nativeMap E sourceSum := rfl

theorem variationDecoded_target : variationDecoded E = targetSum := by
  rw [variationDecoded, targetPackage_eq, carrier_eq E, sum_conjugate]

theorem variationPath_recovery :
    (uaStructureIdentity nativeMap E sourceSum targetSum).symm
      ((uaStructureIdentity nativeMap E sourceSum targetSum) (variationPath E)) = variationPath E :=
  (uaStructureIdentity nativeMap E sourceSum targetSum).symm_apply_apply _

theorem reject : IsEmpty (NativePath E sourceLength badTarget) := by
  refine ⟨fun r => ?_⟩
  have h := ((uaStructureIdentity nativeMap E sourceLength badTarget) r).package_eq
  rw [carrier_eq E, length_conjugate] at h
  have hi := congrArg (fun p : StatePackage Journals => p.invariant ([], [1])) h
  simp [targetLength, badTarget] at hi

example : (mainDecoded E).step ([2,3], [5]) = ([1,2,3], [1,5]) := by
  rw [mainDecoded_target]
  rfl

example : (variationDecoded E).invariant ([2,3], [5]) ∧
    ¬ (mainDecoded E).invariant ([2,3], [5]) := by
  rw [variationDecoded_target, mainDecoded_target]
  simp [targetLength, targetSum]

example : (mainDecoded E).invariant ([2], [3]) ∧
    ¬ (variationDecoded E).invariant ([2], [3]) := by
  rw [variationDecoded_target, mainDecoded_target]
  simp [targetLength, targetSum]

end JournalTrial.DirectAuthor
end

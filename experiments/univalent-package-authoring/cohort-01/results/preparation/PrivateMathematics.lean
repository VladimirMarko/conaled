import TrialTask

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
namespace JournalTrial.Private
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open Examples.CubicalStateTransport Examples.CubicalStatePackageFamily
open Examples.CubicalStatePackageUa Examples.CubicalStructuredState
open Examples.CubicalUnivalenceTransport Examples.CubicalGlue

 theorem carrier (E : HomotopyEquivalence nativeMap) :
    admittedCarrier (S := Journals) (T := Journals) nativeMap E = reverseJournals := by
  apply Equiv.ext
  intro s
  change (constantLocal _ Journals).decodeCodeIso.hom.app point
    ((codeIso reverseJournals).hom.app point
      ((constantLocal _ Journals).decodeCodeIso.inv.app point s)) = reverseJournals s
  exact congrArg (fun t => t.val point) (codeIso_action reverseJournals s)

 theorem length_eq : sourceLength.conjugate reverseJournals = targetLength := by
  apply statePackage_ext
  · rfl
  · funext s
    simp [StatePackage.conjugate, reverseJournals, sourceLength, targetLength]
  · funext s
    simp [StatePackage.conjugate, reverseJournals, sourceLength, targetLength]

 theorem sum_eq : sourceSum.conjugate reverseJournals = targetSum := by
  apply statePackage_ext
  · rfl
  · funext s
    simp [StatePackage.conjugate, reverseJournals, sourceSum, targetSum]
  · funext s
    simp [StatePackage.conjugate, reverseJournals, sourceSum, targetSum]

end JournalTrial.Private

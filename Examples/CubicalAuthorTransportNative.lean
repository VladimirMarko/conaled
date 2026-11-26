import Examples.UnivalentAuthorTrial.Task
import Examples.CubicalAuthorTransportCalibration

/-! Regression for #577 using the published #534 task. The original cohort is
unchanged; this module exercises the repaired facade and its full native oracle.
It is not a fresh author trial. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace JournalTrial.RepairedFacade
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
  Change.nativePath nativeMap E (length_preserved E)

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
        mainPath E := Change.native_path_recovery nativeMap E (mainPath E)

def variationPath : NativePath E sourceSum targetSum :=
  Change.nativePath nativeMap E (sum_preserved E)

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
        variationPath E := Change.native_path_recovery nativeMap E (variationPath E)

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

example : (variationDecoded E).Invariant ([2,3], [5]) ∧
    ¬ (mainDecoded E).Invariant ([2,3], [5]) := by
  rw [variationDecoded_target, mainDecoded_target]
  simp [targetSum, targetLength]

example : (mainDecoded E).Invariant ([2], [3]) ∧
    ¬ (variationDecoded E).Invariant ([2], [3]) := by
  rw [variationDecoded_target, mainDecoded_target]
  simp [targetSum, targetLength]

end JournalTrial.RepairedFacade
end

section NativeOracle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
namespace JournalTrial.RepairedOracle
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open Examples.CubicalStateTransport Examples.CubicalStatePackageFamily
open Examples.CubicalStatePackageUa Examples.CubicalStructuredState

variable (E : HomotopyEquivalence nativeMap) 

/-- Full records, including dependent proposition and proof fields. -/
theorem complete_packages : (RepairedFacade.mainDecoded E) = targetLength ∧ (RepairedFacade.variationDecoded E) = targetSum :=
  ⟨(RepairedFacade.mainDecoded_target E), (RepairedFacade.variationDecoded_target E)⟩

/-- Universal observations use independently defined targets, not conjugation. -/
theorem all_observations (a b : List Nat) :
    (RepairedFacade.mainDecoded E).initial = ([], []) ∧
    (RepairedFacade.mainDecoded E).step (a,b) = (1::a,1::b) ∧
    ((RepairedFacade.mainDecoded E).Invariant (a,b) ↔ a.length = b.length) ∧
    (RepairedFacade.variationDecoded E).initial = ([], []) ∧
    (RepairedFacade.variationDecoded E).step (a,b) = (1::a,1::b) ∧
    ((RepairedFacade.variationDecoded E).Invariant (a,b) ↔ a.sum = b.sum) := by
  rw [(RepairedFacade.mainDecoded_target E), (RepairedFacade.variationDecoded_target E)]
  exact ⟨rfl, rfl, Iff.rfl, rfl, rfl, Iff.rfl⟩

/-- The step check distinguishes prepend from append away from the initial orbit. -/
theorem separating_observations :
    (RepairedFacade.mainDecoded E).step ([2,3],[5]) = ([1,2,3],[1,5]) ∧
    ¬ (RepairedFacade.mainDecoded E).Invariant ([2,3],[5]) ∧
    (RepairedFacade.variationDecoded E).Invariant ([2,3],[5]) ∧
    (RepairedFacade.mainDecoded E).Invariant ([2],[3]) ∧
    ¬ (RepairedFacade.variationDecoded E).Invariant ([2],[3]) := by
  rw [(RepairedFacade.mainDecoded_target E), (RepairedFacade.variationDecoded_target E)]
  simp [targetLength, targetSum]

/-- Decode the submitted nativeSection itself at the final endpoint. -/
theorem section_decodes :
    (readOut (admittedLine (S := Journals) (T := Journals) nativeMap E) (endpointPoint true)
      ((RepairedFacade.mainSection E).val (endpointPoint true))).conjugate
      ((admittedFinish (S := Journals) (T := Journals) nativeMap E).app point).toEquiv = targetLength := by
  rw [(RepairedFacade.mainSection_exact E)]
  exact (RepairedFacade.mainDecoded_exact E).symm.trans (RepairedFacade.mainDecoded_target E)

theorem variation_section_decodes :
    (readOut (admittedLine (S := Journals) (T := Journals) nativeMap E) (endpointPoint true)
      ((RepairedFacade.variationSection E).val (endpointPoint true))).conjugate
      ((admittedFinish (S := Journals) (T := Journals) nativeMap E).app point).toEquiv = targetSum := by
  rw [(RepairedFacade.variationSection_exact E)]
  exact (RepairedFacade.variationDecoded_exact E).symm.trans (RepairedFacade.variationDecoded_target E)

/-- Full sections at every generalized point, including dependent proof data. -/
theorem sections_recovered :
    (RepairedFacade.mainSection E) = pullPackage (admittedLine (S := Journals) (T := Journals) nativeMap E) (admittedPresentation (S := Journals) (T := Journals) nativeMap E)
      (sourceLength.conjugate (admittedCarrier (S := Journals) (T := Journals) nativeMap E)) ∧
    (RepairedFacade.variationSection E) = pullPackage (admittedLine (S := Journals) (T := Journals) nativeMap E) (admittedPresentation (S := Journals) (T := Journals) nativeMap E)
      (sourceSum.conjugate (admittedCarrier (S := Journals) (T := Journals) nativeMap E)) :=
  ⟨(RepairedFacade.mainSection_recovery E), (RepairedFacade.variationSection_recovery E)⟩

theorem path_start : (pathApp (RepairedFacade.mainPath E)).reindex (endpointSub terminal false) =
    (pullPackage (admittedLine (S := Journals) (T := Journals) nativeMap E) (admittedPresentation (S := Journals) (T := Journals) nativeMap E)
      (sourceLength.conjugate (admittedCarrier (S := Journals) (T := Journals) nativeMap E))).reindex (endpointSub terminal false) :=
  pathApp_zero (RepairedFacade.mainPath E)

theorem path_finish : (pathApp (RepairedFacade.mainPath E)).reindex (endpointSub terminal true) =
    (pullPackage (admittedLine (S := Journals) (T := Journals) nativeMap E) (admittedPresentation (S := Journals) (T := Journals) nativeMap E)
      targetLength).reindex (endpointSub terminal true) := pathApp_one (RepairedFacade.mainPath E)

theorem variation_path_start : (pathApp (RepairedFacade.variationPath E)).reindex (endpointSub terminal false) =
    (pullPackage (admittedLine (S := Journals) (T := Journals) nativeMap E) (admittedPresentation (S := Journals) (T := Journals) nativeMap E)
      (sourceSum.conjugate (admittedCarrier (S := Journals) (T := Journals) nativeMap E))).reindex (endpointSub terminal false) :=
  pathApp_zero (RepairedFacade.variationPath E)

theorem variation_path_finish : (pathApp (RepairedFacade.variationPath E)).reindex (endpointSub terminal true) =
    (pullPackage (admittedLine (S := Journals) (T := Journals) nativeMap E) (admittedPresentation (S := Journals) (T := Journals) nativeMap E)
      targetSum).reindex (endpointSub terminal true) := pathApp_one (RepairedFacade.variationPath E)

theorem paths_recovered :
    (uaStructureIdentity (S := Journals) (T := Journals) nativeMap E sourceLength targetLength).symm
      ((uaStructureIdentity (S := Journals) (T := Journals) nativeMap E sourceLength targetLength) (RepairedFacade.mainPath E)) = (RepairedFacade.mainPath E) ∧
    (uaStructureIdentity (S := Journals) (T := Journals) nativeMap E sourceSum targetSum).symm
      ((uaStructureIdentity (S := Journals) (T := Journals) nativeMap E sourceSum targetSum) (RepairedFacade.variationPath E)) = (RepairedFacade.variationPath E) :=
  ⟨(RepairedFacade.mainPath_recovery E), (RepairedFacade.variationPath_recovery E)⟩

theorem source_decodings :
    sourcePackage (S := Journals) (T := Journals) nativeMap E sourceLength = sourceLength ∧
    sourcePackage (S := Journals) (T := Journals) nativeMap E sourceSum = sourceSum :=
  ⟨sourcePackage_eq (S := Journals) (T := Journals) nativeMap E sourceLength,
    sourcePackage_eq (S := Journals) (T := Journals) nativeMap E sourceSum⟩

theorem negative : IsEmpty (NativePath E sourceLength badTarget) := RepairedFacade.reject E

end JournalTrial.RepairedOracle

namespace JournalTrial.RepairedOracle
open SquareKit.Cubical SquareKit.Cubical.Presheaf Examples.CubicalUnivalenceTransport
noncomputable def admittedWitness : HomotopyEquivalence nativeMap :=
  HomotopyEquivalence.ofIso (codeIso reverseJournals)
example := all_observations admittedWitness
example := section_decodes admittedWitness
example := variation_section_decodes admittedWitness
example := paths_recovered admittedWitness
example := negative admittedWitness
end JournalTrial.RepairedOracle

end NativeOracle

namespace Examples.CubicalAuthorTransportNative
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open CubicalAuthorTransport CubicalAuthorTransportCalibration
open CubicalStateTransport CubicalStatePackageFamily CubicalStructuredState
open CubicalFiniteStateIdentity

/-- Unlike the journal case, the witness here is the generic composition of two
native contractions. The resulting path retains that witness and both packages. -/
noncomputable def composedPath :
    StructuredPath (admittedLine twice.map twice.equivalence)
      (admittedPresentation twice.map twice.equivalence)
      (admittedCarrier twice.map twice.equivalence)
      evenPackage (evenPackage.conjugate (successor.trans successor)) :=
  Change.nativePath twice.map twice.equivalence (Preserves.of_eq
    ((Change.transport_eq twice evenPackage).symm.trans twice_package))

theorem composed_path_finish :
    (pathApp composedPath).reindex (endpointSub terminal true) =
      (pullPackage (admittedLine twice.map twice.equivalence)
        (admittedPresentation twice.map twice.equivalence)
        (evenPackage.conjugate (successor.trans successor))).reindex
          (endpointSub terminal true) := pathApp_one composedPath

theorem composed_path_recovery :
    (uaStructureIdentity twice.map twice.equivalence evenPackage
      (evenPackage.conjugate (successor.trans successor))).symm
      ((uaStructureIdentity twice.map twice.equivalence evenPackage
        (evenPackage.conjugate (successor.trans successor))) composedPath) = composedPath :=
  Change.native_path_recovery twice.map twice.equivalence composedPath

/-- Recover preservation from the new native path, then use it for the complete
transported record. This connects path construction to decoded observations. -/
theorem composed_decoded : twice.transport evenPackage =
    evenPackage.conjugate (successor.trans successor) :=
  Change.transport_of_preserves twice
    ((uaStructureIdentity twice.map twice.equivalence evenPackage
      (evenPackage.conjugate (successor.trans successor))) composedPath)

theorem composed_observations :
    (twice.transport evenPackage).initial = 2 ∧
    (twice.transport evenPackage).step 4 = 6 ∧
    (twice.transport evenPackage).Invariant 2 ∧
    ¬ (twice.transport evenPackage).Invariant 3 := by
  rw [composed_decoded]
  change (2 : Int) = 2 ∧ (6 : Int) = 6 ∧ (0 : Int) % 2 = 0 ∧ ¬ (1 : Int) % 2 = 0
  decide

end Examples.CubicalAuthorTransportNative


namespace JournalTrial.RepairedFacade
open Examples.CubicalAuthorTransport Examples.CubicalStructuredState
open SquareKit.Cubical.Presheaf
variable (E : HomotopyEquivalence nativeMap)

theorem mainPath_exact : mainPath E =
    (uaStructureIdentity nativeMap E sourceLength targetLength).symm (length_preserved E) :=
  Change.nativePath_eq nativeMap E (length_preserved E)

end JournalTrial.RepairedFacade

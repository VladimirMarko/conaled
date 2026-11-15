import Examples.UnivalentAuthorTrial.Direct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
namespace JournalTrial.DirectOracle
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open Examples.CubicalStateTransport Examples.CubicalStatePackageFamily
open Examples.CubicalStatePackageUa Examples.CubicalStructuredState

variable (E : HomotopyEquivalence nativeMap) 

/-- Full records, including dependent proposition and proof fields. -/
theorem complete_packages : (DirectAuthor.mainDecoded E) = targetLength ∧ (DirectAuthor.variationDecoded E) = targetSum :=
  ⟨(DirectAuthor.mainDecoded_target E), (DirectAuthor.variationDecoded_target E)⟩

/-- Universal observations use independently defined targets, not conjugation. -/
theorem all_observations (a b : List Nat) :
    (DirectAuthor.mainDecoded E).initial = ([], []) ∧
    (DirectAuthor.mainDecoded E).step (a,b) = (1::a,1::b) ∧
    ((DirectAuthor.mainDecoded E).invariant (a,b) ↔ a.length = b.length) ∧
    (DirectAuthor.variationDecoded E).initial = ([], []) ∧
    (DirectAuthor.variationDecoded E).step (a,b) = (1::a,1::b) ∧
    ((DirectAuthor.variationDecoded E).invariant (a,b) ↔ a.sum = b.sum) := by
  rw [(DirectAuthor.mainDecoded_target E), (DirectAuthor.variationDecoded_target E)]
  exact ⟨rfl, rfl, Iff.rfl, rfl, rfl, Iff.rfl⟩

/-- The step check distinguishes prepend from append away from the initial orbit. -/
theorem separating_observations :
    (DirectAuthor.mainDecoded E).step ([2,3],[5]) = ([1,2,3],[1,5]) ∧
    ¬ (DirectAuthor.mainDecoded E).invariant ([2,3],[5]) ∧
    (DirectAuthor.variationDecoded E).invariant ([2,3],[5]) ∧
    (DirectAuthor.mainDecoded E).invariant ([2],[3]) ∧
    ¬ (DirectAuthor.variationDecoded E).invariant ([2],[3]) := by
  rw [(DirectAuthor.mainDecoded_target E), (DirectAuthor.variationDecoded_target E)]
  simp [targetLength, targetSum]

/-- Decode the submitted nativeSection itself at the final endpoint. -/
theorem section_decodes :
    (readOut (admittedLine (S := Journals) (T := Journals) nativeMap E) (endpointPoint true)
      ((DirectAuthor.mainSection E).val (endpointPoint true))).conjugate
      ((admittedFinish (S := Journals) (T := Journals) nativeMap E).app point).toEquiv = targetLength := by
  rw [(DirectAuthor.mainSection_exact E)]
  exact (DirectAuthor.mainDecoded_exact E).symm.trans (DirectAuthor.mainDecoded_target E)

theorem variation_section_decodes :
    (readOut (admittedLine (S := Journals) (T := Journals) nativeMap E) (endpointPoint true)
      ((DirectAuthor.variationSection E).val (endpointPoint true))).conjugate
      ((admittedFinish (S := Journals) (T := Journals) nativeMap E).app point).toEquiv = targetSum := by
  rw [(DirectAuthor.variationSection_exact E)]
  exact (DirectAuthor.variationDecoded_exact E).symm.trans (DirectAuthor.variationDecoded_target E)

/-- Full sections at every generalized point, including dependent proof data. -/
theorem sections_recovered :
    (DirectAuthor.mainSection E) = pullPackage (admittedLine (S := Journals) (T := Journals) nativeMap E) (admittedPresentation (S := Journals) (T := Journals) nativeMap E)
      (sourceLength.conjugate (admittedCarrier (S := Journals) (T := Journals) nativeMap E)) ∧
    (DirectAuthor.variationSection E) = pullPackage (admittedLine (S := Journals) (T := Journals) nativeMap E) (admittedPresentation (S := Journals) (T := Journals) nativeMap E)
      (sourceSum.conjugate (admittedCarrier (S := Journals) (T := Journals) nativeMap E)) :=
  ⟨(DirectAuthor.mainSection_recovery E), (DirectAuthor.variationSection_recovery E)⟩

theorem path_start : (pathApp (DirectAuthor.mainPath E)).reindex (endpointSub terminal false) =
    (pullPackage (admittedLine (S := Journals) (T := Journals) nativeMap E) (admittedPresentation (S := Journals) (T := Journals) nativeMap E)
      (sourceLength.conjugate (admittedCarrier (S := Journals) (T := Journals) nativeMap E))).reindex (endpointSub terminal false) :=
  pathApp_zero (DirectAuthor.mainPath E)

theorem path_finish : (pathApp (DirectAuthor.mainPath E)).reindex (endpointSub terminal true) =
    (pullPackage (admittedLine (S := Journals) (T := Journals) nativeMap E) (admittedPresentation (S := Journals) (T := Journals) nativeMap E)
      targetLength).reindex (endpointSub terminal true) := pathApp_one (DirectAuthor.mainPath E)

theorem variation_path_start : (pathApp (DirectAuthor.variationPath E)).reindex (endpointSub terminal false) =
    (pullPackage (admittedLine (S := Journals) (T := Journals) nativeMap E) (admittedPresentation (S := Journals) (T := Journals) nativeMap E)
      (sourceSum.conjugate (admittedCarrier (S := Journals) (T := Journals) nativeMap E))).reindex (endpointSub terminal false) :=
  pathApp_zero (DirectAuthor.variationPath E)

theorem variation_path_finish : (pathApp (DirectAuthor.variationPath E)).reindex (endpointSub terminal true) =
    (pullPackage (admittedLine (S := Journals) (T := Journals) nativeMap E) (admittedPresentation (S := Journals) (T := Journals) nativeMap E)
      targetSum).reindex (endpointSub terminal true) := pathApp_one (DirectAuthor.variationPath E)

theorem paths_recovered :
    (uaStructureIdentity (S := Journals) (T := Journals) nativeMap E sourceLength targetLength).symm
      ((uaStructureIdentity (S := Journals) (T := Journals) nativeMap E sourceLength targetLength) (DirectAuthor.mainPath E)) = (DirectAuthor.mainPath E) ∧
    (uaStructureIdentity (S := Journals) (T := Journals) nativeMap E sourceSum targetSum).symm
      ((uaStructureIdentity (S := Journals) (T := Journals) nativeMap E sourceSum targetSum) (DirectAuthor.variationPath E)) = (DirectAuthor.variationPath E) :=
  ⟨(DirectAuthor.mainPath_recovery E), (DirectAuthor.variationPath_recovery E)⟩

theorem source_decodings :
    sourcePackage (S := Journals) (T := Journals) nativeMap E sourceLength = sourceLength ∧
    sourcePackage (S := Journals) (T := Journals) nativeMap E sourceSum = sourceSum :=
  ⟨sourcePackage_eq (S := Journals) (T := Journals) nativeMap E sourceLength,
    sourcePackage_eq (S := Journals) (T := Journals) nativeMap E sourceSum⟩

theorem negative : IsEmpty (NativePath E sourceLength badTarget) := DirectAuthor.reject E

end JournalTrial.DirectOracle

namespace JournalTrial.DirectOracle
open SquareKit.Cubical SquareKit.Cubical.Presheaf Examples.CubicalUnivalenceTransport
noncomputable def admittedWitness : HomotopyEquivalence nativeMap :=
  HomotopyEquivalence.ofIso (codeIso reverseJournals)
example := all_observations admittedWitness
example := section_decodes admittedWitness
example := variation_section_decodes admittedWitness
example := paths_recovered admittedWitness
example := negative admittedWitness
#print axioms DirectAuthor.mainPath
#print axioms DirectAuthor.variationPath
#print axioms DirectAuthor.mainSection_recovery
#print axioms DirectAuthor.variationSection_recovery
#print axioms DirectAuthor.mainDecoded_target
#print axioms DirectAuthor.variationDecoded_target
#print axioms DirectAuthor.reject
#print axioms all_observations
#print axioms sections_recovered
#print axioms paths_recovered
#print axioms negative
end JournalTrial.DirectOracle

import Examples.UnivalentAuthorTrial.Facade

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
namespace JournalTrial.FacadeOracle
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open Examples.CubicalStateTransport Examples.CubicalStatePackageFamily
open Examples.CubicalStatePackageUa Examples.CubicalStructuredState

variable (E : HomotopyEquivalence nativeMap) 

/-- Full records, including dependent proposition and proof fields. -/
theorem complete_packages : (FacadeAuthor.mainDecoded E) = targetLength ∧ (FacadeAuthor.variationDecoded E) = targetSum :=
  ⟨(FacadeAuthor.mainDecoded_target E), (FacadeAuthor.variationDecoded_target E)⟩

/-- Universal observations use independently defined targets, not conjugation. -/
theorem all_observations (a b : List Nat) :
    (FacadeAuthor.mainDecoded E).initial = ([], []) ∧
    (FacadeAuthor.mainDecoded E).step (a,b) = (1::a,1::b) ∧
    ((FacadeAuthor.mainDecoded E).Invariant (a,b) ↔ a.length = b.length) ∧
    (FacadeAuthor.variationDecoded E).initial = ([], []) ∧
    (FacadeAuthor.variationDecoded E).step (a,b) = (1::a,1::b) ∧
    ((FacadeAuthor.variationDecoded E).Invariant (a,b) ↔ a.sum = b.sum) := by
  rw [(FacadeAuthor.mainDecoded_target E), (FacadeAuthor.variationDecoded_target E)]
  exact ⟨rfl, rfl, Iff.rfl, rfl, rfl, Iff.rfl⟩

/-- The step check distinguishes prepend from append away from the initial orbit. -/
theorem separating_observations :
    (FacadeAuthor.mainDecoded E).step ([2,3],[5]) = ([1,2,3],[1,5]) ∧
    ¬ (FacadeAuthor.mainDecoded E).Invariant ([2,3],[5]) ∧
    (FacadeAuthor.variationDecoded E).Invariant ([2,3],[5]) ∧
    (FacadeAuthor.mainDecoded E).Invariant ([2],[3]) ∧
    ¬ (FacadeAuthor.variationDecoded E).Invariant ([2],[3]) := by
  rw [(FacadeAuthor.mainDecoded_target E), (FacadeAuthor.variationDecoded_target E)]
  simp [targetLength, targetSum]

/-- Decode the submitted nativeSection itself at the final endpoint. -/
theorem section_decodes :
    (readOut (admittedLine (S := Journals) (T := Journals) nativeMap E) (endpointPoint true)
      ((FacadeAuthor.mainSection E).val (endpointPoint true))).conjugate
      ((admittedFinish (S := Journals) (T := Journals) nativeMap E).app point).toEquiv = targetLength := by
  rw [(FacadeAuthor.mainSection_exact E)]
  exact (FacadeAuthor.mainDecoded_exact E).symm.trans (FacadeAuthor.mainDecoded_target E)

theorem variation_section_decodes :
    (readOut (admittedLine (S := Journals) (T := Journals) nativeMap E) (endpointPoint true)
      ((FacadeAuthor.variationSection E).val (endpointPoint true))).conjugate
      ((admittedFinish (S := Journals) (T := Journals) nativeMap E).app point).toEquiv = targetSum := by
  rw [(FacadeAuthor.variationSection_exact E)]
  exact (FacadeAuthor.variationDecoded_exact E).symm.trans (FacadeAuthor.variationDecoded_target E)

/-- Full sections at every generalized point, including dependent proof data. -/
theorem sections_recovered :
    (FacadeAuthor.mainSection E) = pullPackage (admittedLine (S := Journals) (T := Journals) nativeMap E) (admittedPresentation (S := Journals) (T := Journals) nativeMap E)
      (sourceLength.conjugate (admittedCarrier (S := Journals) (T := Journals) nativeMap E)) ∧
    (FacadeAuthor.variationSection E) = pullPackage (admittedLine (S := Journals) (T := Journals) nativeMap E) (admittedPresentation (S := Journals) (T := Journals) nativeMap E)
      (sourceSum.conjugate (admittedCarrier (S := Journals) (T := Journals) nativeMap E)) :=
  ⟨(FacadeAuthor.mainSection_recovery E), (FacadeAuthor.variationSection_recovery E)⟩

theorem path_start : (pathApp (FacadeAuthor.mainPath E)).reindex (endpointSub terminal false) =
    (pullPackage (admittedLine (S := Journals) (T := Journals) nativeMap E) (admittedPresentation (S := Journals) (T := Journals) nativeMap E)
      (sourceLength.conjugate (admittedCarrier (S := Journals) (T := Journals) nativeMap E))).reindex (endpointSub terminal false) :=
  pathApp_zero (FacadeAuthor.mainPath E)

theorem path_finish : (pathApp (FacadeAuthor.mainPath E)).reindex (endpointSub terminal true) =
    (pullPackage (admittedLine (S := Journals) (T := Journals) nativeMap E) (admittedPresentation (S := Journals) (T := Journals) nativeMap E)
      targetLength).reindex (endpointSub terminal true) := pathApp_one (FacadeAuthor.mainPath E)

theorem variation_path_start : (pathApp (FacadeAuthor.variationPath E)).reindex (endpointSub terminal false) =
    (pullPackage (admittedLine (S := Journals) (T := Journals) nativeMap E) (admittedPresentation (S := Journals) (T := Journals) nativeMap E)
      (sourceSum.conjugate (admittedCarrier (S := Journals) (T := Journals) nativeMap E))).reindex (endpointSub terminal false) :=
  pathApp_zero (FacadeAuthor.variationPath E)

theorem variation_path_finish : (pathApp (FacadeAuthor.variationPath E)).reindex (endpointSub terminal true) =
    (pullPackage (admittedLine (S := Journals) (T := Journals) nativeMap E) (admittedPresentation (S := Journals) (T := Journals) nativeMap E)
      targetSum).reindex (endpointSub terminal true) := pathApp_one (FacadeAuthor.variationPath E)

theorem paths_recovered :
    (uaStructureIdentity (S := Journals) (T := Journals) nativeMap E sourceLength targetLength).symm
      ((uaStructureIdentity (S := Journals) (T := Journals) nativeMap E sourceLength targetLength) (FacadeAuthor.mainPath E)) = (FacadeAuthor.mainPath E) ∧
    (uaStructureIdentity (S := Journals) (T := Journals) nativeMap E sourceSum targetSum).symm
      ((uaStructureIdentity (S := Journals) (T := Journals) nativeMap E sourceSum targetSum) (FacadeAuthor.variationPath E)) = (FacadeAuthor.variationPath E) :=
  ⟨(FacadeAuthor.mainPath_recovery E), (FacadeAuthor.variationPath_recovery E)⟩

theorem source_decodings :
    sourcePackage (S := Journals) (T := Journals) nativeMap E sourceLength = sourceLength ∧
    sourcePackage (S := Journals) (T := Journals) nativeMap E sourceSum = sourceSum :=
  ⟨sourcePackage_eq (S := Journals) (T := Journals) nativeMap E sourceLength,
    sourcePackage_eq (S := Journals) (T := Journals) nativeMap E sourceSum⟩

theorem negative : IsEmpty (NativePath E sourceLength badTarget) := FacadeAuthor.reject E

end JournalTrial.FacadeOracle

namespace JournalTrial.FacadeOracle
open SquareKit.Cubical SquareKit.Cubical.Presheaf Examples.CubicalUnivalenceTransport
noncomputable def admittedWitness : HomotopyEquivalence nativeMap :=
  HomotopyEquivalence.ofIso (codeIso reverseJournals)
example := all_observations admittedWitness
example := section_decodes admittedWitness
example := variation_section_decodes admittedWitness
example := paths_recovered admittedWitness
example := negative admittedWitness
#print axioms FacadeAuthor.mainPath
#print axioms FacadeAuthor.variationPath
#print axioms FacadeAuthor.mainSection_recovery
#print axioms FacadeAuthor.variationSection_recovery
#print axioms FacadeAuthor.mainDecoded_target
#print axioms FacadeAuthor.variationDecoded_target
#print axioms FacadeAuthor.reject
#print axioms all_observations
#print axioms sections_recovered
#print axioms paths_recovered
#print axioms negative
end JournalTrial.FacadeOracle

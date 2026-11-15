import PrivateFeasibility

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
namespace JournalTrial.Oracle
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open Examples.CubicalStateTransport Examples.CubicalStatePackageFamily
open Examples.CubicalStatePackageUa Examples.CubicalStructuredState

variable (E : HomotopyEquivalence nativeMap) 

/-- Full records, including dependent proposition and proof fields. -/
theorem complete_packages : (Author.mainDecoded E) = targetLength ∧ (Author.variationDecoded E) = targetSum :=
  ⟨(Author.mainDecoded_target E), (Author.variationDecoded_target E)⟩

/-- Universal observations use independently defined targets, not conjugation. -/
theorem all_observations (a b : List Nat) :
    (Author.mainDecoded E).initial = ([], []) ∧
    (Author.mainDecoded E).step (a,b) = (1::a,1::b) ∧
    ((Author.mainDecoded E).invariant (a,b) ↔ a.length = b.length) ∧
    (Author.variationDecoded E).initial = ([], []) ∧
    (Author.variationDecoded E).step (a,b) = (1::a,1::b) ∧
    ((Author.variationDecoded E).invariant (a,b) ↔ a.sum = b.sum) := by
  rw [(Author.mainDecoded_target E), (Author.variationDecoded_target E)]
  exact ⟨rfl, rfl, Iff.rfl, rfl, rfl, Iff.rfl⟩

/-- The step check distinguishes prepend from append away from the initial orbit. -/
theorem separating_observations :
    (Author.mainDecoded E).step ([2,3],[5]) = ([1,2,3],[1,5]) ∧
    ¬ (Author.mainDecoded E).invariant ([2,3],[5]) ∧
    (Author.variationDecoded E).invariant ([2,3],[5]) ∧
    (Author.mainDecoded E).invariant ([2],[3]) ∧
    ¬ (Author.variationDecoded E).invariant ([2],[3]) := by
  rw [(Author.mainDecoded_target E), (Author.variationDecoded_target E)]
  simp [targetLength, targetSum]

/-- Decode the submitted nativeSection itself at the final endpoint. -/
theorem section_decodes :
    (readOut (admittedLine (S := Journals) (T := Journals) nativeMap E) (endpointPoint true)
      ((Author.mainSection E).val (endpointPoint true))).conjugate
      ((admittedFinish (S := Journals) (T := Journals) nativeMap E).app point).toEquiv = targetLength := by
  rw [(Author.mainSection_exact E)]
  exact (Author.mainDecoded_exact E).symm.trans (Author.mainDecoded_target E)

theorem variation_section_decodes :
    (readOut (admittedLine (S := Journals) (T := Journals) nativeMap E) (endpointPoint true)
      ((Author.variationSection E).val (endpointPoint true))).conjugate
      ((admittedFinish (S := Journals) (T := Journals) nativeMap E).app point).toEquiv = targetSum := by
  rw [(Author.variationSection_exact E)]
  exact (Author.variationDecoded_exact E).symm.trans (Author.variationDecoded_target E)

/-- Full sections at every generalized point, including dependent proof data. -/
theorem sections_recovered :
    (Author.mainSection E) = pullPackage (admittedLine (S := Journals) (T := Journals) nativeMap E) (admittedPresentation (S := Journals) (T := Journals) nativeMap E)
      (sourceLength.conjugate (admittedCarrier (S := Journals) (T := Journals) nativeMap E)) ∧
    (Author.variationSection E) = pullPackage (admittedLine (S := Journals) (T := Journals) nativeMap E) (admittedPresentation (S := Journals) (T := Journals) nativeMap E)
      (sourceSum.conjugate (admittedCarrier (S := Journals) (T := Journals) nativeMap E)) :=
  ⟨(Author.mainSection_recovery E), (Author.variationSection_recovery E)⟩

theorem path_start : (pathApp (Author.mainPath E)).reindex (endpointSub terminal false) =
    (pullPackage (admittedLine (S := Journals) (T := Journals) nativeMap E) (admittedPresentation (S := Journals) (T := Journals) nativeMap E)
      (sourceLength.conjugate (admittedCarrier (S := Journals) (T := Journals) nativeMap E))).reindex (endpointSub terminal false) :=
  pathApp_zero (Author.mainPath E)

theorem path_finish : (pathApp (Author.mainPath E)).reindex (endpointSub terminal true) =
    (pullPackage (admittedLine (S := Journals) (T := Journals) nativeMap E) (admittedPresentation (S := Journals) (T := Journals) nativeMap E)
      targetLength).reindex (endpointSub terminal true) := pathApp_one (Author.mainPath E)

theorem variation_path_start : (pathApp (Author.variationPath E)).reindex (endpointSub terminal false) =
    (pullPackage (admittedLine (S := Journals) (T := Journals) nativeMap E) (admittedPresentation (S := Journals) (T := Journals) nativeMap E)
      (sourceSum.conjugate (admittedCarrier (S := Journals) (T := Journals) nativeMap E))).reindex (endpointSub terminal false) :=
  pathApp_zero (Author.variationPath E)

theorem variation_path_finish : (pathApp (Author.variationPath E)).reindex (endpointSub terminal true) =
    (pullPackage (admittedLine (S := Journals) (T := Journals) nativeMap E) (admittedPresentation (S := Journals) (T := Journals) nativeMap E)
      targetSum).reindex (endpointSub terminal true) := pathApp_one (Author.variationPath E)

theorem paths_recovered :
    (uaStructureIdentity (S := Journals) (T := Journals) nativeMap E sourceLength targetLength).symm
      ((uaStructureIdentity (S := Journals) (T := Journals) nativeMap E sourceLength targetLength) (Author.mainPath E)) = (Author.mainPath E) ∧
    (uaStructureIdentity (S := Journals) (T := Journals) nativeMap E sourceSum targetSum).symm
      ((uaStructureIdentity (S := Journals) (T := Journals) nativeMap E sourceSum targetSum) (Author.variationPath E)) = (Author.variationPath E) :=
  ⟨(Author.mainPath_recovery E), (Author.variationPath_recovery E)⟩

theorem source_decodings :
    sourcePackage (S := Journals) (T := Journals) nativeMap E sourceLength = sourceLength ∧
    sourcePackage (S := Journals) (T := Journals) nativeMap E sourceSum = sourceSum :=
  ⟨sourcePackage_eq (S := Journals) (T := Journals) nativeMap E sourceLength,
    sourcePackage_eq (S := Journals) (T := Journals) nativeMap E sourceSum⟩

theorem negative : IsEmpty (NativePath E sourceLength badTarget) := Author.reject E

end JournalTrial.Oracle

namespace JournalTrial.Oracle
open SquareKit.Cubical SquareKit.Cubical.Presheaf Examples.CubicalUnivalenceTransport
noncomputable def admittedWitness : HomotopyEquivalence nativeMap :=
  HomotopyEquivalence.ofIso (codeIso reverseJournals)
example := all_observations admittedWitness
example := section_decodes admittedWitness
example := variation_section_decodes admittedWitness
example := paths_recovered admittedWitness
example := negative admittedWitness
#print axioms Author.mainPath
#print axioms Author.variationPath
#print axioms Author.mainSection_recovery
#print axioms Author.variationSection_recovery
#print axioms Author.mainDecoded_target
#print axioms Author.variationDecoded_target
#print axioms Author.reject
#print axioms all_observations
#print axioms sections_recovered
#print axioms paths_recovered
#print axioms negative
end JournalTrial.Oracle

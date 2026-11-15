import AuthorSubmission
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace JournalTrial.InterfaceCheck
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open Examples.CubicalStateTransport Examples.CubicalStatePackageFamily
open Examples.CubicalStatePackageUa Examples.CubicalStructuredState
variable (E : HomotopyEquivalence nativeMap)
example : NativePath E sourceLength targetLength := Author.mainPath E
example : Term (package (admittedLine (S := Journals) (T := Journals) nativeMap E)).family := Author.mainSection E
example : Author.mainSection E = transported (S := Journals) (T := Journals) nativeMap E sourceLength := Author.mainSection_exact E
example : Author.mainSection E = pullPackage
    (admittedLine (S := Journals) (T := Journals) nativeMap E)
    (admittedPresentation (S := Journals) (T := Journals) nativeMap E)
    (sourceLength.conjugate (admittedCarrier (S := Journals) (T := Journals) nativeMap E)) := Author.mainSection_recovery E
example : StatePackage Journals := Author.mainDecoded E
example : Author.mainDecoded E = targetPackage (S := Journals) (T := Journals) nativeMap E sourceLength := Author.mainDecoded_exact E
example : Author.mainDecoded E = targetLength := Author.mainDecoded_target E
example : (uaStructureIdentity (S := Journals) (T := Journals) nativeMap E sourceLength targetLength).symm
    ((uaStructureIdentity (S := Journals) (T := Journals) nativeMap E sourceLength targetLength) (Author.mainPath E)) = Author.mainPath E := Author.mainPath_recovery E
example : NativePath E sourceSum targetSum := Author.variationPath E
example : Term (package (admittedLine (S := Journals) (T := Journals) nativeMap E)).family := Author.variationSection E
example : Author.variationSection E = transported (S := Journals) (T := Journals) nativeMap E sourceSum := Author.variationSection_exact E
example : Author.variationSection E = pullPackage
    (admittedLine (S := Journals) (T := Journals) nativeMap E)
    (admittedPresentation (S := Journals) (T := Journals) nativeMap E)
    (sourceSum.conjugate (admittedCarrier (S := Journals) (T := Journals) nativeMap E)) := Author.variationSection_recovery E
example : StatePackage Journals := Author.variationDecoded E
example : Author.variationDecoded E = targetPackage (S := Journals) (T := Journals) nativeMap E sourceSum := Author.variationDecoded_exact E
example : Author.variationDecoded E = targetSum := Author.variationDecoded_target E
example : (uaStructureIdentity (S := Journals) (T := Journals) nativeMap E sourceSum targetSum).symm
    ((uaStructureIdentity (S := Journals) (T := Journals) nativeMap E sourceSum targetSum) (Author.variationPath E)) = Author.variationPath E := Author.variationPath_recovery E
example : IsEmpty (NativePath E sourceLength badTarget) := Author.reject E
end JournalTrial.InterfaceCheck
end

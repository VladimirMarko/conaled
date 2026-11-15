import Examples.CubicalUnivalenceTransport
import SquareKit.Internal.Cubical.NativeUnivalenceComparison

set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalNativeUnivalenceTransport
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open Examples.CubicalGlue Examples.CubicalUnivalenceTransport
open SmallUniverse.NativeUnivalence
variable {S T : Type} (e : S ≃ T)

noncomputable def nativeTransport :=
  pathToMap (ua (constantLocal terminal S).code (constantLocal terminal T).code
    (Raising.map (codeIso e).hom) (HomotopyEquivalence.ofIso (Raising.iso (codeIso e))))

noncomputable def observedNative (s : S) : Term (constantFamily terminal T) :=
  Term.map (constantLocal terminal T).decodeCodeIso.hom
    (Raising.lowerTerm (Term.map (nativeTransport e) (Raising.raiseTerm (input s))))

/-- The observation comes from the actual universal-El filler on the generic native ua line. -/
theorem observedNative_eq (s : S) : observedNative e s = constantSection (e s) :=
  (discretePath_endpoints (homogeneousPathMap (constantLocal terminal T).decodeCodeIso.hom
    (Raising.lowerPath (uaComparison (constantLocal terminal S).code (constantLocal terminal T).code
      (Raising.map (codeIso e).hom) (HomotopyEquivalence.ofIso (Raising.iso (codeIso e)))
      (Raising.raiseTerm (input s)))))).symm.trans (codeIso_action e s)

theorem boolean_true_to_false : observedNative booleanTransposition true = constantSection false :=
  observedNative_eq booleanTransposition true

theorem successor_three_to_four :
    observedNative CubicalStateTransport.successor 3 = constantSection 4 :=
  observedNative_eq CubicalStateTransport.successor 3

/-- The comparison also identifies full chosen native equivalences, not only their observed Boolean action. -/
noncomputable def fullChosenComparison :=
  uaEquivalenceComparison (constantLocal terminal S).code (constantLocal terminal T).code
    (Raising.map (codeIso e).hom) (HomotopyEquivalence.ofIso (Raising.iso (codeIso e)))

noncomputable def booleanFullChosenComparison := fullChosenComparison booleanTransposition


end Examples.CubicalNativeUnivalenceTransport

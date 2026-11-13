import Examples.CubicalNativeUnivalenceTransport
import SquareKit.Internal.Cubical.EquivalenceIsoTransport

set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalEquivalenceIsoTransport
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open Examples.CubicalGlue Examples.CubicalUnivalenceTransport
open Examples.CubicalNativeUnivalenceTransport SmallUniverse.NativeUnivalence
variable {S T : Type} (e : S ≃ T)

noncomputable def decodedTransport :=
  (Raising.iso (constantLocal terminal S).decodeCodeIso).inv ≫ nativeTransport e ≫
    (Raising.iso (constantLocal terminal T).decodeCodeIso).hom

/-- Transfer the actual universal transport's chosen fiber contraction to the
explicit constant-carrier presentations. -/
noncomputable def decodedEquivalence : HomotopyEquivalence (decodedTransport e) :=
  (pathToEquivalence (ua (constantLocal terminal S).code (constantLocal terminal T).code
    (Raising.map (codeIso e).hom) (HomotopyEquivalence.ofIso (Raising.iso (codeIso e))))).conjugateIso
    (Raising.iso (constantLocal terminal S).decodeCodeIso).symm
    (Raising.iso (constantLocal terminal T).decodeCodeIso)

noncomputable def observed (s : S) := Raising.lowerTerm
  (Term.map (decodedTransport e) (Raising.raiseTerm (constantSection s)))

theorem observed_eq (s : S) : observed e s = constantSection (e s) := by
  exact observedNative_eq e s

noncomputable def booleanChosenEquivalence := decodedEquivalence booleanTransposition

theorem boolean_true_to_false : observed booleanTransposition true = constantSection false :=
  observed_eq booleanTransposition true

noncomputable def successorChosenEquivalence := decodedEquivalence CubicalStateTransport.successor

theorem successor_three_to_four :
    observed CubicalStateTransport.successor 3 = constantSection 4 :=
  observed_eq CubicalStateTransport.successor 3

end Examples.CubicalEquivalenceIsoTransport

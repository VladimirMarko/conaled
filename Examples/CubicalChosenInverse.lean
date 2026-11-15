import Examples.CubicalFiberwiseHomotopyRetracts
import SquareKit.Internal.Cubical.ChosenInverseHomotopies

set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalChosenInverse
open CategoryTheory SquareKit.Cubical.Presheaf
open CubicalContractibleTotals CubicalFiberwiseHomotopyRetracts
variable {Γ : Context.{0}}

/-- Use the equivalence constructed from contractible totals, while retaining
path reversal as the supplied inverse and its actual right roundtrip. -/
noncomputable def reversalLeftHomotopy : Term (homogeneousPath
    (reindex (forwardPaths (Γ := Γ)) (projection forwardPaths))
    (Term.map (Functor.whiskerLeft (projection forwardPaths).mapElements reversal.inv)
      (Term.map (Functor.whiskerLeft (projection forwardPaths).mapElements reverseMap)
        (generic forwardPaths))) (generic forwardPaths)) :=
  reversalFromTotals.chosenLeftInverse forwardFilling forwardFilling_lawful
    reversal.inv (isoRoundtrip reversal)

end Examples.CubicalChosenInverse

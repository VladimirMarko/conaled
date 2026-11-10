import SquareKit.WitnessProduct
import Examples.WitnessEquivalence

namespace Examples.WitnessProduct
open SquareKit Examples.WitnessEquivalence

abbrev component := WitnessProduct.equiv one one witnesses witnesses

def leftWitness : component.Rel (a := ((),())) (b := ((),())) ((),()) ((),()) := (true,false)
def rightWitness : component.Rel (a := ((),())) (b := ((),())) ((),()) ((),()) := (false,true)
example : leftWitness ≠ rightWitness := by
  change (true,false) ≠ (false,true)
  decide
example : (WitnessProduct.fst_laws witnesses witnesses).congr (a := ((),())) (b := ((),())) (f := ((),())) (g := ((),())) leftWitness = true := rfl
example : (WitnessProduct.snd_laws witnesses witnesses).congr (a := ((),())) (b := ((),())) (f := ((),())) (g := ((),())) leftWitness = false := rfl
example : component.symm (a := ((),())) (b := ((),())) (f := ((),())) (g := ((),())) leftWitness = (false,true) := rfl

end Examples.WitnessProduct

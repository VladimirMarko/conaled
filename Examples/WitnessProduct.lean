import SquareKit.WitnessProduct
import Examples.WitnessEquivalence

namespace Examples.WitnessProduct
open SquareKit Examples.WitnessEquivalence

abbrev component := WitnessProduct.equiv one one witnesses witnesses

def leftWitness : component.Rel ((),()) ((),()) := (true,false)
def rightWitness : component.Rel ((),()) ((),()) := (false,true)
example : leftWitness ≠ rightWitness := by decide
example : (WitnessProduct.fst_laws witnesses witnesses).congr leftWitness = true := rfl
example : (WitnessProduct.snd_laws witnesses witnesses).congr leftWitness = false := rfl
example : component.symm leftWitness = (false,true) := rfl

end Examples.WitnessProduct

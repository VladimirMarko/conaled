import SquareKit.InterpretationDiagnostics
import TaskSetup462
import Examples.PrivateReference462



namespace PrivateApplicability462

theorem extension : Tasks462.H1.changeCodes.Extension Tasks462.H1.source :=
  PrivateReference462.H1.extension

theorem product_zero : Tasks462.H2.productWeight 0 = 0 :=
  PrivateReference462.H2.productCost.map_zero

theorem product_add : ∀ a b : Nat,
    Tasks462.H2.productWeight (a+b) = Tasks462.H2.productWeight a + Tasks462.H2.productWeight b :=
  PrivateReference462.H2.productCost.map_add

theorem final_zero : Tasks462.H2.finalWeight 0 = 0 :=
  PrivateReference462.H2.finalCost.map_zero

theorem final_add : ∀ a b : Nat × Nat,
    Tasks462.H2.finalWeight (a+b) = Tasks462.H2.finalWeight a + Tasks462.H2.finalWeight b :=
  PrivateReference462.H2.finalCost.map_add

theorem shifted_zero_refuted : ¬ Tasks462.H2.shifted 0 = 0 :=
  PrivateReference462.H2.shifted_zero_rejected

end PrivateApplicability462

namespace GeneratedFull
def selectedSource := Tasks462.H1.source
def route := Tasks462.H1.changeCodes
def requirement_0 : Prop := SquareKit.DiagonalConstruction.Map.Extension route selectedSource
#transport_requirement GeneratedFull.requirement_0
def requestPresent : Unit := ()
#check selectedSource.code
#check selectedSource.witness
#check route.code selectedSource.code
#check route.value selectedSource.witness
theorem certificate_0 : requirement_0 := PrivateApplicability462.extension
def result := route.selectedExtension selectedSource certificate_0
theorem observation : result.witness = route.value selectedSource.witness :=
  route.extension_witness selectedSource certificate_0
#check result.code
#check result.witness
#transport_audit GeneratedFull.result

end GeneratedFull

namespace GeneratedImage
def selectedSource := Tasks462.H1.source
def route := Tasks462.H1.changeCodes
def requestPresent : Unit := ()
#check selectedSource.code
#check selectedSource.witness
#check route.code selectedSource.code
#check route.value selectedSource.witness
def result := route.selectedImage selectedSource
#check result.code
#check result.witness
#transport_audit GeneratedImage.result

end GeneratedImage

namespace GeneratedProduct
def weight : (Nat) → (Nat × Nat) := Tasks462.H2.productWeight
def initial : Resources.Measured (Int) (Nat) := Tasks462.H2.compiledSeed
def transition : (Int) → (Int) → Resources.Measured (Int) (Nat) := Tasks462.H2.transition
def requirement_0 : Prop := weight 0 = 0
#transport_requirement GeneratedProduct.requirement_0
def requirement_1 : Prop := ∀ a b : (Nat), weight (a+b) = weight a + weight b
#transport_requirement GeneratedProduct.requirement_1
def requestPresent : Unit := ()
#check initial
#check transition
#check weight
theorem certificate_0 : requirement_0 := PrivateApplicability462.product_zero
theorem certificate_1 : requirement_1 := PrivateApplicability462.product_add
def hom : (Nat) →+ (Nat × Nat) :=
  { toFun := weight, map_zero' := certificate_0, map_add' := certificate_1 }
theorem result (xs : List (Int)) :
    Resources.reweight hom (Resources.bind initial (Resources.run transition xs)) =
    Resources.bind (Resources.reweight hom initial)
      (Resources.run (fun i s => Resources.reweight hom (transition i s)) xs) :=
  InterpretationAssistance.seeded_reweight hom initial transition xs
#check initial
#check transition
#check weight
#transport_audit GeneratedProduct.result

end GeneratedProduct

namespace GeneratedFinal
def weight : (Nat × Nat) → (Nat) := Tasks462.H2.finalWeight
def initial : Resources.Measured (Int) (Nat × Nat) := Resources.reweight Tasks462.H2.productWeight Tasks462.H2.compiledSeed
def transition : (Int) → (Int) → Resources.Measured (Int) (Nat × Nat) := fun x acc => Resources.reweight Tasks462.H2.productWeight (Tasks462.H2.transition x acc)
def requirement_0 : Prop := weight 0 = 0
#transport_requirement GeneratedFinal.requirement_0
def requirement_1 : Prop := ∀ a b : (Nat × Nat), weight (a+b) = weight a + weight b
#transport_requirement GeneratedFinal.requirement_1
def requestPresent : Unit := ()
#check initial
#check transition
#check weight
theorem certificate_0 : requirement_0 := PrivateApplicability462.final_zero
theorem certificate_1 : requirement_1 := PrivateApplicability462.final_add
def hom : (Nat × Nat) →+ (Nat) :=
  { toFun := weight, map_zero' := certificate_0, map_add' := certificate_1 }
theorem result (xs : List (Int)) :
    Resources.reweight hom (Resources.bind initial (Resources.run transition xs)) =
    Resources.bind (Resources.reweight hom initial)
      (Resources.run (fun i s => Resources.reweight hom (transition i s)) xs) :=
  InterpretationAssistance.seeded_reweight hom initial transition xs
#check initial
#check transition
#check weight
#transport_audit GeneratedFinal.result

end GeneratedFinal

namespace PrivateGeneratedConsumers462
open SquareKit.DiagonalConstruction

theorem full_code : GeneratedFull.result.code = some false := rfl
theorem full_witness : GeneratedFull.result.witness = false := GeneratedFull.observation

theorem full_representation (b : Option Bool) :
    Tasks462.H1.targetEval GeneratedFull.result.code b =
      diagonal Tasks462.H1.targetEval Tasks462.H1.targetStep b := GeneratedFull.result.represents b

theorem omitted_input : Tasks462.H1.targetEval GeneratedFull.result.code none = false :=
  full_representation none

theorem image_code : GeneratedImage.result.code.val = GeneratedFull.result.code := rfl
theorem image_value : GeneratedImage.result.witness = GeneratedFull.result.witness := rfl

theorem image_representation (b : {b // ∃ a, Tasks462.H1.changeCodes.code a = b}) :
    Tasks462.H1.targetEval GeneratedImage.result.code.val b.val =
      diagonal Tasks462.H1.targetEval Tasks462.H1.targetStep b.val := GeneratedImage.result.represents b

theorem not_onto : ¬ Function.Surjective Tasks462.H1.changeCodes.code := PrivateReference462.H1.not_onto

theorem image_excludes_none : ¬ ∃ b : {b // ∃ a, Tasks462.H1.changeCodes.code a = b}, b.val = none :=
  PrivateReference462.H1.restricted_excludes_none

theorem wrong_source : ¬ (∀ a, Tasks462.H1.sourceEval true a =
    diagonal Tasks462.H1.sourceEval Tasks462.H1.sourceStep a) := PrivateReference462.H1.wrong_source_code

open Examples.RecursiveCompilation

theorem product_execution (xs : List Int) :
    Resources.reweight GeneratedProduct.hom (ListFoldCompiler.compile counted total xs) =
      PrivateReference462.H2.productExecution xs := GeneratedProduct.result xs

theorem second_execution (xs : List Int) :
    Resources.reweight GeneratedFinal.hom (PrivateReference462.H2.productExecution xs) =
      PrivateReference462.H2.finalExecution xs := GeneratedFinal.result xs

theorem composed_execution (xs : List Int) :
    Resources.reweight (GeneratedFinal.hom.comp GeneratedProduct.hom)
      (ListFoldCompiler.compile counted total xs) = PrivateReference462.H2.finalExecution xs := by
  change Resources.reweight GeneratedFinal.hom
    (Resources.reweight GeneratedProduct.hom (ListFoldCompiler.compile counted total xs)) = _
  rw [product_execution, second_execution]

theorem composed_observation (xs : List Int) :
    Resources.reweight (GeneratedFinal.hom.comp GeneratedProduct.hom)
      (ListFoldCompiler.compile counted total xs) = (xs.sum,7*(1+2*xs.length)) :=
  (composed_execution xs).trans (PrivateReference462.H2.final_observation xs)

theorem empty : Resources.reweight (GeneratedFinal.hom.comp GeneratedProduct.hom)
    (ListFoldCompiler.compile counted total []) = (0,7) := composed_observation []

theorem two : Resources.reweight (GeneratedFinal.hom.comp GeneratedProduct.hom)
    (ListFoldCompiler.compile counted total [1,2]) = (3,35) := composed_observation [1,2]

end PrivateGeneratedConsumers462
#transport_audit PrivateGeneratedConsumers462.composed_observation

import SquareKit.InterpretationDiagnostics
import TaskSetup462

import TaskSetup462
namespace AssistedH2
open Tasks462.H2
theorem product_zero : productWeight 0 = 0 := rfl
theorem product_add (a b : Nat) : productWeight (a+b) = productWeight a + productWeight b := by
  apply Prod.ext
  · rfl
  · change 2*(a+b) = 2*a+2*b
    omega
theorem final_zero : finalWeight 0 = 0 := rfl
theorem final_add (a b : Nat × Nat) : finalWeight (a+b) = finalWeight a + finalWeight b := by
  change (a.1+b.1)+3*(a.2+b.2) = (a.1+3*a.2)+(b.1+3*b.2)
  omega
end AssistedH2

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
theorem certificate_0 : requirement_0 := AssistedH2.product_zero
theorem certificate_1 : requirement_1 := AssistedH2.product_add
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
theorem certificate_0 : requirement_0 := AssistedH2.final_zero
theorem certificate_1 : requirement_1 := AssistedH2.final_add
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

namespace AssistedH2
open Tasks462.H2 Examples.RecursiveCompilation
abbrev productHom := GeneratedProduct.hom
abbrev finalHom := GeneratedFinal.hom
def composedHom : Nat →+ Nat := finalHom.comp productHom

def originalExecution (xs : List Int) : Resources.Measured Int Nat :=
  Resources.bind compiledSeed (Resources.run transition xs)
def productExecution (xs : List Int) : Resources.Measured Int (Nat × Nat) :=
  Resources.bind (Resources.reweight productHom compiledSeed)
    (Resources.run (fun x acc => Resources.reweight productHom (transition x acc)) xs)
def finalExecution (xs : List Int) : Resources.Measured Int Nat :=
  Resources.bind (Resources.reweight finalHom (Resources.reweight productHom compiledSeed))
    (Resources.run (fun x acc => Resources.reweight finalHom
      (Resources.reweight productHom (transition x acc))) xs)

theorem product_transport (xs : List Int) :
    Resources.reweight productHom (originalExecution xs) = productExecution xs :=
  GeneratedProduct.result xs
theorem final_transport (xs : List Int) :
    Resources.reweight finalHom (productExecution xs) = finalExecution xs :=
  GeneratedFinal.result xs
theorem composite_transport (xs : List Int) :
    Resources.reweight composedHom (originalExecution xs) = finalExecution xs := by
  change Resources.reweight finalHom (Resources.reweight productHom (originalExecution xs)) = _
  rw [product_transport, final_transport]

theorem compiled_connection (xs : List Int) :
    ListFoldCompiler.compile counted total xs = originalExecution xs := rfl

theorem ordinary_result (xs : List Int) :
    ListFoldCompiler.compile ordinary total xs = xs.sum := total_compiled xs
theorem counted_result (xs : List Int) :
    ListFoldCompiler.compile counted total xs = (xs.sum, 1+2*xs.length) := total_counted xs
theorem original_result (xs : List Int) :
    originalExecution xs = (xs.sum, 1+2*xs.length) := total_counted xs

theorem source_execution (xs : List Int) :
    ListFoldCompiler.Executes meaning addBody xs 0 xs.sum xs.length := by
  have h := ListFoldCompiler.iterate_executes meaning addBody xs (0 : Int)
  have hm : ListFoldCompiler.iterate meaning addBody 0 xs = xs.sum := total_meaning xs
  rw [hm] at h
  exact h

theorem product_result (xs : List Int) :
    productExecution xs = (xs.sum, (1+2*xs.length, 2*(1+2*xs.length))) := by
  rw [← product_transport, original_result]
  rfl

theorem composed_formula (n : Nat) : composedHom n = 7*n := by
  change n+3*(2*n) = 7*n
  omega

theorem final_result (xs : List Int) :
    finalExecution xs = (xs.sum, 7*(1+2*xs.length)) := by
  rw [← composite_transport, original_result]
  change (xs.sum, composedHom (1+2*xs.length)) = _
  rw [composed_formula]

theorem empty_case : finalExecution [] = (0,7) := by
  simpa using final_result []
theorem pair_case : finalExecution [1,2] = (3,35) := by
  simpa using final_result [1,2]

theorem shifted_not_zero : shifted 0 ≠ 0 := by decide
-- The zero law prevents certification of this function as an additive homomorphism.
-- It does not prevent defining the function or using other resource observations.
theorem shifted_no_hom : ¬ ∃ h : Nat →+ Nat, ∀ n, h n = shifted n := by
  rintro ⟨h, he⟩
  apply shifted_not_zero
  rw [← he 0, map_zero]
end AssistedH2

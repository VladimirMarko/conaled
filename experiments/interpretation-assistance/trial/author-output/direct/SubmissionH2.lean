import TaskSetup462

namespace Tasks462.H2.Direct
open FirstOrderCompiler Examples.RecursiveCompilation

-- The maps have the supplied functions as their underlying functions.
def productHom : Nat →+ Nat × Nat where
  toFun := productWeight
  map_zero' := rfl
  map_add' m n := by
    apply Prod.ext
    · rfl
    · exact Nat.mul_add 2 m n

def finalHom : Nat × Nat →+ Nat where
  toFun := finalWeight
  map_zero' := rfl
  map_add' p q := by
    rcases p with ⟨u,v⟩
    rcases q with ⟨w,z⟩
    change (u+w) + 3*(v+z) = (u+3*v) + (w+3*z)
    omega

def composedHom : Nat →+ Nat := finalHom.comp productHom

theorem composed_value (n : Nat) : composedHom n = 7*n := by
  change n + 3*(2*n) = 7*n
  omega

def nativeExec (xs : List Int) : Resources.Measured Int Nat :=
  Resources.bind compiledSeed (Resources.run transition xs)

def productSeed : Resources.Measured Int (Nat × Nat) :=
  Resources.reweight productHom compiledSeed

def productStep (x acc : Int) : Resources.Measured Int (Nat × Nat) :=
  Resources.reweight productHom (transition x acc)

def productExec (xs : List Int) : Resources.Measured Int (Nat × Nat) :=
  Resources.bind productSeed (Resources.run productStep xs)

def finalSeed : Resources.Measured Int Nat := Resources.reweight finalHom productSeed

def finalStep (x acc : Int) : Resources.Measured Int Nat :=
  Resources.reweight finalHom (productStep x acc)

def finalExec (xs : List Int) : Resources.Measured Int Nat :=
  Resources.bind finalSeed (Resources.run finalStep xs)

-- Both laws transport the seed, bind, and run, with product observations
-- present in the intermediate execution itself.
theorem product_transport (xs : List Int) :
    Resources.reweight productHom (nativeExec xs) = productExec xs :=
  InterpretationAssistance.seeded_reweight productHom compiledSeed transition xs

theorem final_transport (xs : List Int) :
    Resources.reweight finalHom (productExec xs) = finalExec xs :=
  InterpretationAssistance.seeded_reweight finalHom productSeed productStep xs

theorem composed_transport (xs : List Int) :
    Resources.reweight composedHom
      (Resources.bind compiledSeed (Resources.run transition xs)) =
      Resources.bind finalSeed (Resources.run finalStep xs) := by
  change Resources.reweight finalHom (Resources.reweight productHom (nativeExec xs)) =
    finalExec xs
  rw [product_transport, final_transport]

theorem native_connection (xs : List Int) :
    nativeExec xs = ListFoldCompiler.compile counted total xs := rfl

theorem ordinary_result (xs : List Int) :
    ListFoldCompiler.compile ordinary total xs = xs.sum := total_compiled xs

theorem original_counted_result (xs : List Int) :
    ListFoldCompiler.compile counted total xs = (xs.sum, 1+2*xs.length) :=
  total_counted xs

theorem native_result (xs : List Int) : nativeExec xs = (xs.sum, 1+2*xs.length) :=
  (native_connection xs).trans (original_counted_result xs)

theorem source_execution (xs : List Int) :
    ListFoldCompiler.Executes meaning addBody xs
      (FirstOrderCompiler.eval meaning seed ())
      (ListFoldCompiler.eval meaning total xs) xs.length :=
  ListFoldCompiler.iterate_executes meaning addBody xs _

theorem source_sum_visits (xs : List Int) :
    ListFoldCompiler.Executes meaning addBody xs 0 xs.sum xs.length := by
  have h := source_execution xs
  rw [total_meaning] at h
  exact h

theorem product_result (xs : List Int) :
    productExec xs = (xs.sum, (1+2*xs.length, 2*(1+2*xs.length))) := by
  rw [← product_transport, native_result]
  rfl

theorem final_result (xs : List Int) :
    finalExec xs = (xs.sum, 7*(1+2*xs.length)) := by
  change Resources.bind finalSeed (Resources.run finalStep xs) = _
  rw [← composed_transport]
  change Resources.reweight composedHom (nativeExec xs) = _
  rw [native_result]
  exact congrArg (fun n => (xs.sum,n)) (composed_value (1+2*xs.length))

theorem empty_case : finalExec [] = (0,7) := final_result []
theorem two_case : finalExec [1,2] = (3,35) := final_result [1,2]

theorem shifted_not_zero : shifted 0 ≠ 0 := by decide

-- A homomorphism with precisely this underlying function cannot exist:
-- its required zero law contradicts the checked value at zero.
theorem shifted_no_certificate : ¬ ∃ h : Nat →+ Nat, ∀ n, h n = shifted n := by
  rintro ⟨h, hh⟩
  apply shifted_not_zero
  rw [← hh 0]
  exact h.map_zero

end Tasks462.H2.Direct

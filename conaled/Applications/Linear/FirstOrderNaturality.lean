import SquareKit.FirstOrderNaturality
import Applications.Linear.Compiler
import SquareKit.MatrixCategory

namespace MatrixCompiler.Naturality
open SquareKit FirstOrderCompiler MatrixCompiler Maps
variable (R : Type) [CommSemiring R]

/-- Compile into coordinate functions using the non-strict product comparison.
The primitives are matrix actions; pairing splits and rejoins finite coordinates. -/
def coordinateModel : FirstOrderNaturality.Model FunctionCategory.ops (Prim R) (fun a => Slots a → R) :=
  FirstOrderNaturality.targetImage (target R) (matrixFunctions R) FunctionCategory.terminal FunctionCategory.products
    (matrixFunctionTerminal R) (matrixFunctionProducts R)
    (fun p => (primitive R p).mulVec)

theorem coordinate_preserves : FirstOrderNaturality.Preserves (matrixFunctions R) (equality _)
    (FirstOrderNaturality.ofTarget (target R)) (coordinateModel R) :=
  FirstOrderNaturality.targetImage_preserves (target R) (matrixFunctions R) _ _ _ _
    (matrixFunctionTerminal_laws R) (matrixFunctionProducts_laws R) _ (fun _ => rfl)

/-- The map is the composition of matrix evaluation and coordinate interpretation.
Its preservation proof uses shared composition laws, with no further induction. -/
theorem compile_coordinates (t : Term (Prim R) Γ a) (x : Slots (context Γ) → R) :
    (FirstOrderCompiler.compile (target R) t).mulVec x = FirstOrderNaturality.compile (coordinateModel R) t x := by
  have h := FirstOrderNaturality.naturality (matrixFunctions_laws R) (equalityCongr _)
    (FirstOrderNaturality.targetImage_congr (target R) (matrixFunctions R) _ _ _ _ _
      (equalityCongr _) FunctionCategory.productCongr) (coordinate_preserves R) t
  have hp := congrFun h x
  change (FirstOrderNaturality.compile (FirstOrderNaturality.ofTarget (target R)) t).mulVec x = _ at hp
  rw [FirstOrderNaturality.compile_ofTarget] at hp
  exact hp

/-- The compatibility adapter recovers the existing arbitrary-input matrix theorem. -/
theorem compile_values (t : Term (Prim R) Γ a) (ρ : Val R (context Γ)) :
    denote R (FirstOrderCompiler.compile (target R) t) ρ = eval (meaning R) t ρ :=
  FirstOrderNaturality.compile_sound (target R) (sound R) t ρ

/-- Independent expected arithmetic, connected to the new non-strict compiler. -/
theorem coordinate_linearCombination (x y : R) :
    decode .base (FirstOrderNaturality.compile (coordinateModel R) (linearCombination R)
      (encode _ ((), (x, y)))) = 2*x + 3*y := by
  rw [← compile_coordinates]
  exact compile_values R (linearCombination R) ((), (x, y))

/-- The compatibility theorem also retains the binder example for every input. -/
theorem additive_let (x y : Nat) :
    (FirstOrderCompiler.compile additiveTarget letExample).run (((), y), x) =
      2 * (x + y) + x :=
  FirstOrderNaturality.compile_sound additiveTarget additiveSound letExample (((), y), x)

/-- A recursive interpretation whose object family is finite coordinate spaces,
not source types. This case requires no primitive vocabulary. -/
def finiteModel : FirstOrderNaturality.Model (MatrixCategory.ops R)
    (fun _ _ => Empty)
    (FirstOrderNaturality.objects (MatrixCategory.terminal R) (MatrixCategory.products R)
      (⟨⟨Fin 1, inferInstance, inferInstance⟩⟩ : MatrixCategory.Object R)) :=
  FirstOrderNaturality.cartesian _ _ _ (fun p => nomatch p)

def duplicate : Term (fun _ _ => Empty) [.base] (.prod .base .base) :=
  .pair (.var .here) (.var .here)

theorem duplicate_left (i j : Fin 1) :
    FirstOrderNaturality.compile (finiteModel R) duplicate (.inl i) (.inr j) =
      if i = j then 1 else 0 := rfl

theorem duplicate_right (i j : Fin 1) :
    FirstOrderNaturality.compile (finiteModel R) duplicate (.inr i) (.inr j) =
      if i = j then 1 else 0 := rfl

end MatrixCompiler.Naturality

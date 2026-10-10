import Applications.Incremental.Core
import SquareKit.Arithmetic
import Mathlib.Tactic.Ring
import Mathlib.Data.Rat.Defs

/-! Exact finite changes for arithmetic, including the quadratic cross term. -/
namespace Incremental

@[reducible] def additive (R : Type) [Add R] : ChangeObj := ⟨R, R, (· + ·)⟩

def addMap (R : Type) [CommRing R] : Map (product (additive R) (additive R)) (additive R) where
  run p := p.1 + p.2
  change _ dp := dp.1 + dp.2
  correct _ _ := by dsimp [product, additive]; ring

def mulMap (R : Type) [CommRing R] : Map (product (additive R) (additive R)) (additive R) where
  run p := p.1 * p.2
  change p dp := p.1 * dp.2 + dp.1 * p.2 + dp.1 * dp.2
  correct _ _ := by dsimp [product, additive]; ring

def squareMap (R : Type) [CommRing R] : Map (additive R) (additive R) where
  run x := x * x
  change x dx := 2 * x * dx + dx * dx
  correct _ _ := by dsimp [additive]; ring

def arithmeticPrimitives (R : Type) [CommRing R] :
    Compiler.Primitives (additive R) Arithmetic.Prim (@Arithmetic.meaning R _) where
  change := fun {a b} p => match p with
    | .literal _ => fun _ _ => 0
    | .add => fun _ dp => dp.1 + dp.2
    | .mul => fun p dp => p.1 * dp.2 + dp.1 * p.2 + dp.1 * dp.2
    | .neg => fun _ dx => -dx
  correct p x dx := by
    cases p <;> dsimp [Arithmetic.meaning, Compiler.update, additive] <;> ring

theorem all_arithmetic_updates (R : Type) [CommRing R]
    (t : FirstOrderCompiler.Term Arithmetic.Prim Γ a) (x) (dx) :
    Compiler.update (additive R) a (FirstOrderCompiler.eval Arithmetic.meaning t x)
        ((FirstOrderCompiler.compile (Compiler.target (additive R) (arithmeticPrimitives R)) t).change x dx) =
      FirstOrderCompiler.eval Arithmetic.meaning t
        (Compiler.update (additive R) (FirstOrderCompiler.context Γ) x dx) :=
  Compiler.compile_update (additive R) (arithmeticPrimitives R) t x dx

theorem shared_update (x y dx dy : ℤ) :
    FirstOrderCompiler.eval Arithmetic.meaning Arithmetic.shared ((), (x, y)) +
      ((FirstOrderCompiler.compile (Compiler.target (additive ℤ) (arithmeticPrimitives ℤ))
          Arithmetic.shared).change ((), (x, y)) ((), (dx, dy))) =
      ((x + dx) * (y + dy)) * ((x + dx) * (y + dy)) + (x + dx) :=
  all_arithmetic_updates ℤ Arithmetic.shared ((), (x, y)) ((), (dx, dy))

/-- Dropping the finite-change cross term is observably incorrect. -/
theorem tangent_is_not_a_finite_change :
    (0 : ℤ) * 0 + (2 * 0 * 1) ≠ (0 + 1) * (0 + 1) := by decide

def cachedSquareExample : Cache (squareMap ℤ) :=
  ((initializeCache (squareMap ℤ) 7).advance 2).advance (-3)

theorem cachedSquareExample_correct :
    cachedSquareExample.input = 6 ∧ cachedSquareExample.output = 36 := by decide

end Incremental

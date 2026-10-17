import Examples.MatrixCompilerPreservation
import SquareKit.CommaAgreement
import Applications.Linear.Compiler
import Applications.Stack.Machine

/-!
# Two independent backends for every linear source program

The matrix target computes by finite sums. The stack target executes explicit
push/pop/projection/primitive instructions. Synchronizing their squares gives
a checked joint implementation for every source term, arbitrary coordinates,
and arbitrary preserved stack tail.
-/
namespace Examples.MatrixStack
open FirstOrderCompiler

variable (R : Type) [CommSemiring R]

def jointSquare (t : Term (MatrixCompiler.Prim R) Γ a) (s : List Ty) :
    Squares.Square
      (Squares.synchronized
        (MatrixCompiler.decode (R := R) (context Γ))
        (Prod.fst : Val R (context Γ) × StackMachine.Stack R s → Val R (context Γ)))
      (Squares.synchronized
        (MatrixCompiler.decode (R := R) a)
        (Prod.fst : Val R a × StackMachine.Stack R s → Val R a)) :=
  SquareKit.Comma.Exact.toSquare (SquareKit.Comma.Exact.agree
    (SquareKit.Comma.Exact.ofSquare (MatrixCompiler.compileSquare R t))
    (SquareKit.Comma.Exact.ofSquare
      (StackMachine.compileSquare (MatrixCompiler.meaning R) t s)) rfl)

/-- The complete bytecode result equals the matrix result and original tail. -/
theorem agree_preserving_tail (t : Term (MatrixCompiler.Prim R) Γ a)
    (s : List Ty) (x : MatrixCompiler.Slots (context Γ) → R)
    (z : StackMachine.Stack R s) :
    StackMachine.run (MatrixCompiler.meaning R)
      ((compile (StackMachine.target (MatrixCompiler.Prim R) (MatrixCompiler.meaning R)) t).code s)
      (MatrixCompiler.decode (context Γ) x, z) =
    (MatrixCompiler.decode a ((compile (MatrixCompiler.target R) t).mulVec x), z) := by
  apply Prod.ext
  · exact (((jointSquare R t s).impl ⟨(x, MatrixCompiler.decode _ x, z), rfl⟩).property).symm
  · have h := (compile
      (StackMachine.target (MatrixCompiler.Prim R) (MatrixCompiler.meaning R)) t).correct
        s (MatrixCompiler.decode _ x) z
    have hs := congrArg (fun p : Val R a × StackMachine.Stack R s => p.2) h
    exact hs

/-- The two outputs of the synchronized implementation always agree. -/
theorem joint_outputs_agree (t : Term (MatrixCompiler.Prim R) Γ a) (s : List Ty)
    (p : (Squares.synchronized
      (MatrixCompiler.decode (R := R) (context Γ))
      (Prod.fst : Val R (context Γ) × StackMachine.Stack R s → Val R (context Γ))).R) :
    MatrixCompiler.decode a (((jointSquare R t s).impl p).val.1) =
      (((jointSquare R t s).impl p).val.2).1 :=
  ((jointSquare R t s).impl p).property

def naturalInput (x y : ℕ) : MatrixCompiler.Slots (context [.prod .base .base]) → ℕ :=
  MatrixCompiler.encode _ ((), (x, y))

theorem linear_example_with_tail (x y z : ℕ) :
    StackMachine.run (MatrixCompiler.meaning ℕ)
      ((compile (StackMachine.target (MatrixCompiler.Prim ℕ) (MatrixCompiler.meaning ℕ))
        (MatrixCompiler.linearCombination ℕ)).code [.base]) (((), (x, y)), (z, ())) =
      (2*x + 3*y, (z, ())) :=
  StackMachine.compile_correct (MatrixCompiler.meaning ℕ)
    (MatrixCompiler.linearCombination ℕ) [.base] ((), (x, y)) (z, ())

theorem generated_coefficients :
    let M := compile (MatrixCompiler.target ℕ) (MatrixCompiler.linearCombination ℕ)
    (M () (.inr (.inl ())), M () (.inr (.inr ()))) = (2, 3) := by
  decide

end Examples.MatrixStack

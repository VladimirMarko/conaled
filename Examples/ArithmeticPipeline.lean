import SquareKit.CommaAgreement
import SquareKit.Arithmetic
import Applications.AD.Compiler
import Applications.Stack.Machine
import Applications.Incremental.Arithmetic
import Applications.Intervals.Arithmetic

/-!
# One source program, several composed correctness contracts

Every theorem here uses the same `Arithmetic.Prim` source signature. Over the
reals it compiles to analytically certified AD. Over the rationals it compiles
to typed stack code, exact finite-change code, and enclosing intervals.

`stack_after_update` equates recomputation by the stack machine with updating
its old result using the separately compiled incremental program.
`stack_enclosed` transports the interval theorem to the actual stack result.
`incremental_output_enclosed` pastes all three contracts together. These
theorems quantify over all typed source terms, contexts, values, and stack
tails; they are not comparisons of a few sampled executions.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Examples.ArithmeticPipeline

open FirstOrderCompiler
open Applications.AD

/-! ## The shared signature has locally certified real derivatives -/

noncomputable def realADPrimitives : Applications.AD.FirstOrder.PrimitiveD Arithmetic.Prim
  | _, _, .literal n => DMap.constant (n : ℝ)
  | _, _, .add => DMap.add DMap.fst DMap.snd
  | _, _, .mul => DMap.mul DMap.fst DMap.snd
  | _, _, .neg => DMap.neg DMap.ident

theorem realAD_meaning :
    @Applications.AD.FirstOrder.meaning Arithmetic.Prim realADPrimitives =
      @Arithmetic.meaning ℝ _ := by
  funext a b p x
  cases p <;> rfl

/-- The derivative is of the independent, shared-signature source evaluator. -/
theorem compile_hasFDerivAt (t : Term Arithmetic.Prim Γ a)
    (ρ : Val ℝ (context Γ)) :
    HasFDerivAt (eval Arithmetic.meaning t)
      ((Applications.AD.FirstOrder.compile realADPrimitives t).derivative ρ) ρ := by
  simpa only [realAD_meaning] using
    Applications.AD.FirstOrder.compile_hasFDerivAt realADPrimitives t ρ

theorem compile_real_forward (t : Term Arithmetic.Prim Γ a)
    (ρ v : Val ℝ (context Γ)) :
    tangent (Applications.AD.FirstOrder.compile realADPrimitives t) (ρ, v) =
      (eval Arithmetic.meaning t ρ, fderiv ℝ (eval Arithmetic.meaning t) ρ v) := by
  simpa only [realAD_meaning] using
    Applications.AD.FirstOrder.compile_forward realADPrimitives t ρ v

/-! ## Exact rational backends -/

abbrev QVal (a : Ty) := Val ℚ a
abbrev QDelta (a : Ty) := Incremental.Compiler.Delta (Incremental.additive ℚ) a

def update (a : Ty) : QVal a → QDelta a → QVal a :=
  Incremental.Compiler.update (Incremental.additive ℚ) a

def incremental (t : Term Arithmetic.Prim Γ a) :=
  FirstOrderCompiler.compile
    (Incremental.Compiler.target (Incremental.additive ℚ) (Incremental.arithmeticPrimitives ℚ)) t

def stackCode (t : Term Arithmetic.Prim Γ a) (s : List Ty) :
    StackMachine.Program Arithmetic.Prim (context Γ) s a s :=
  (FirstOrderCompiler.compile (StackMachine.target Arithmetic.Prim (@Arithmetic.meaning ℚ _)) t).code s

def stackRun (t : Term Arithmetic.Prim Γ a) (s : List Ty)
    (ρ : QVal (context Γ)) (z : StackMachine.Stack ℚ s) : QVal a × StackMachine.Stack ℚ s :=
  StackMachine.run Arithmetic.meaning (stackCode t s) (ρ, z)

theorem stackRun_correct (t : Term Arithmetic.Prim Γ a) (s : List Ty)
    (ρ : QVal (context Γ)) (z : StackMachine.Stack ℚ s) :
    stackRun t s ρ z = (eval Arithmetic.meaning t ρ, z) :=
  StackMachine.compile_correct Arithmetic.meaning t s ρ z

/-- Independent stack recomputation agrees with the incremental finite update, tail included. -/
theorem stack_after_update (t : Term Arithmetic.Prim Γ a) (s : List Ty)
    (ρ : QVal (context Γ)) (dρ : QDelta (context Γ)) (z : StackMachine.Stack ℚ s) :
    stackRun t s (update (context Γ) ρ dρ) z =
      (update a (stackRun t s ρ z).1 ((incremental t).change ρ dρ), z) := by
  let i : Squares.Square
      (Incremental.updateRep (Incremental.Compiler.object (Incremental.additive ℚ) (context Γ)))
      (Incremental.updateRep (Incremental.Compiler.object (Incremental.additive ℚ) a)) := {
    impl p := (eval Arithmetic.meaning t p.1, (incremental t).change p.1 p.2)
    spec := eval Arithmetic.meaning t
    commutes p := Incremental.Compiler.compile_update (Incremental.additive ℚ)
      (Incremental.arithmeticPrimitives ℚ) t p.1 p.2 }
  let joint := SquareKit.Comma.Exact.toSquare (SquareKit.Comma.Exact.agree
    (R₂ := QVal (context Γ) × StackMachine.Stack ℚ s)
    (T₂ := QVal a × StackMachine.Stack ℚ s)
    (SquareKit.Comma.Exact.ofSquare i)
    (SquareKit.Comma.Exact.ofSquare (StackMachine.compileSquare (B := ℚ) Arithmetic.meaning t s)) rfl)
  have h := (joint.impl ⟨((ρ, dρ), update (context Γ) ρ dρ, z), rfl⟩).property
  apply Prod.ext
  ·
    rw [stackRun_correct t s ρ z]
    exact h.symm
  · change (stackRun t s (update (context Γ) ρ dρ) z).2 = z
    have ht := congrArg (fun p : QVal a × StackMachine.Stack ℚ s => p.2)
      (stackRun_correct t s (update (context Γ) ρ dρ) z)
    exact ht

/-- Interval enclosure applies to the actual bytecode result, for every related input. -/
theorem stack_enclosed (t : Term Arithmetic.Prim Γ a) (s : List Ty)
    (ρ : QVal (context Γ)) (z : StackMachine.Stack ℚ s)
    {box : (FirstOrderRelations.encoding IntervalAnalysis.representation (context Γ)).R}
    (hbox : (FirstOrderRelations.encoding IntervalAnalysis.representation (context Γ)).Rel box ρ) :
    (FirstOrderRelations.encoding IntervalAnalysis.representation a).Rel
      ((IntervalAnalysis.compile t).impl box) (stackRun t s ρ z).1 := by
  rw [stackRun_correct]
  exact IntervalAnalysis.compile_contains t hbox

/-- Pasting stack, incremental, and interval contracts preserves the enclosure. -/
theorem incremental_output_enclosed (t : Term Arithmetic.Prim Γ a) (s : List Ty)
    (ρ : QVal (context Γ)) (dρ : QDelta (context Γ)) (z : StackMachine.Stack ℚ s)
    {box : (FirstOrderRelations.encoding IntervalAnalysis.representation (context Γ)).R}
    (hbox : (FirstOrderRelations.encoding IntervalAnalysis.representation (context Γ)).Rel
      box (update (context Γ) ρ dρ)) :
    (FirstOrderRelations.encoding IntervalAnalysis.representation a).Rel
      ((IntervalAnalysis.compile t).impl box)
      (update a (stackRun t s ρ z).1 ((incremental t).change ρ dρ)) := by
  have h := stack_enclosed t s (update (context Γ) ρ dρ) z hbox
  rw [stack_after_update] at h
  exact h

/-! ## The nonlinear let-shared source is identical across these backends -/

theorem shared_real_derivative (x y dx dy : ℝ) :
    (Applications.AD.FirstOrder.compile realADPrimitives Arithmetic.shared).derivative
        ((), (x, y)) ((), (dx, dy)) =
      (2 * x * y * y + 1) * dx + (2 * x * x * y) * dy := by
  change (x * y) * (x * dy + y * dx) + (x * y) * (x * dy + y * dx) + dx = _
  ring

theorem shared_updated_enclosed (x y dx dy : ℚ) (I J : IntervalAnalysis.Interval)
    (hx : IntervalAnalysis.Contains I (x + dx))
    (hy : IntervalAnalysis.Contains J (y + dy)) :
    IntervalAnalysis.Contains ((IntervalAnalysis.compile Arithmetic.shared).impl ((), (I, J)))
      ((stackRun Arithmetic.shared [] ((), (x, y)) ()).1 +
        (incremental Arithmetic.shared).change ((), (x, y)) ((), (dx, dy))) :=
  incremental_output_enclosed Arithmetic.shared [] ((), (x, y)) ((), (dx, dy)) ()
    (box := ((), (I, J))) ⟨True.intro, hx, hy⟩

theorem shared_stack_example :
    stackRun Arithmetic.shared [] ((), ((3 : ℚ), 2)) () = (39, ()) := by
  rw [stackRun_correct, Arithmetic.eval_shared]
  norm_num

#print axioms compile_hasFDerivAt
#print axioms stack_after_update
#print axioms stack_enclosed
#print axioms incremental_output_enclosed

end Examples.ArithmeticPipeline

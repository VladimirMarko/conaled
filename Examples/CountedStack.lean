import Applications.Stack.Measured
import Examples.MatrixStack
import Examples.ArithmeticPipeline
import Examples.WeakMachine

/-! Matched direct and compositional resource proofs for existing compiler clients.
The optional Budget predicate leaves the compiler and its value contracts intact. -/
namespace Examples.CountedStack
open FirstOrderCompiler StackMachine

/-- Recover the existing matrix comparison by erasing only the new counter. -/
theorem matrix_agreement (R : Type) [CommSemiring R]
    (t : Term (MatrixCompiler.Prim R) Γ a) (s : List Ty)
    (x : MatrixCompiler.Slots (context Γ) → R) (z : Stack R s) :
    (runMeasured (MatrixCompiler.meaning R)
      ((compile (target (MatrixCompiler.Prim R) (MatrixCompiler.meaning R)) t).code s)
      (MatrixCompiler.decode (context Γ) x,z)).1 =
    (MatrixCompiler.decode a ((compile (MatrixCompiler.target R) t).mulVec x),z) := by
  rw [runMeasured_value]
  exact MatrixStack.agree_preserving_tail R t s x z

/-- The arbitrary related-input interval theorem still observes the executed value. -/
theorem arithmetic_enclosed (t : Term Arithmetic.Prim Γ a) (s : List Ty)
    (ρ : ArithmeticPipeline.QVal (context Γ)) (z : Stack ℚ s)
    {box : (FirstOrderRelations.encoding IntervalAnalysis.representation (context Γ)).R}
    (hbox : (FirstOrderRelations.encoding IntervalAnalysis.representation (context Γ)).Rel box ρ) :
    (FirstOrderRelations.encoding IntervalAnalysis.representation a).Rel
      ((IntervalAnalysis.compile t).impl box)
      (runMeasured Arithmetic.meaning (ArithmeticPipeline.stackCode t s) (ρ,z)).1.1 := by
  rw [runMeasured_value]
  exact ArithmeticPipeline.stack_enclosed t s ρ z hbox

/-- The incremental composition keeps its old independent implementation. -/
theorem arithmetic_after_update (t : Term Arithmetic.Prim Γ a) (s : List Ty)
    (ρ : ArithmeticPipeline.QVal (context Γ))
    (dρ : ArithmeticPipeline.QDelta (context Γ)) (z : Stack ℚ s) :
    (runMeasured Arithmetic.meaning (ArithmeticPipeline.stackCode t s)
      (ArithmeticPipeline.update (context Γ) ρ dρ,z)).1 =
    (ArithmeticPipeline.update a (ArithmeticPipeline.stackRun t s ρ z).1
      ((ArithmeticPipeline.incremental t).change ρ dρ),z) := by
  rw [runMeasured_value]
  exact ArithmeticPipeline.stack_after_update t s ρ dρ z

def linear := compile (target (MatrixCompiler.Prim ℕ) (MatrixCompiler.meaning ℕ))
  (MatrixCompiler.linearCombination ℕ)
def triple : Certified (MatrixCompiler.Prim ℕ) (MatrixCompiler.meaning ℕ) .base .base :=
  .primitive (.scale 3)
def linearThenTriple := triple.comp linear

def shared := compile (target Arithmetic.Prim (@Arithmetic.meaning ℚ _)) Arithmetic.shared
def negate : Certified Arithmetic.Prim (@Arithmetic.meaning ℚ _) .base .base :=
  .primitive .neg
def sharedThenNegate := negate.comp shared

/-- Component evidence comes from the compiled instruction sequence. -/
theorem linear_budget : linear.Budget (linear.code []).instructions := by
  intro s x z
  rw [runMeasured_cost]
  exact Nat.le_refl _

set_option maxHeartbeats 800000 in
theorem shared_budget : shared.Budget (shared.code []).instructions := by
  intro s x z
  rw [runMeasured_cost]
  exact Nat.le_refl _

theorem triple_budget : triple.Budget 1 :=
  Certified.Budget.primitive (meaning := MatrixCompiler.meaning ℕ) (MatrixCompiler.Prim.scale 3)

theorem negate_budget : negate.Budget 1 :=
  Certified.Budget.primitive (meaning := @Arithmetic.meaning ℚ _) Arithmetic.Prim.neg

/-- Direct route: expose sequencing and pass the intermediate state explicitly. -/
theorem linear_direct (s) (x : Val ℕ (context [.prod .base .base])) (z : Stack ℕ s) :
    (runMeasured (MatrixCompiler.meaning ℕ) (linearThenTriple.code s) (x,z)).2 ≤
      (linear.code []).instructions + 1 := by
  change (runMeasured _ ((linear.code s).append (triple.code s)) (x,z)).2 ≤ _
  rw [runMeasured_append]
  simp only [Resources.bind, linear.measured_correct]
  exact Nat.add_le_add (linear_budget s x z) (triple_budget s _ z)

/-- Optional route: the same component evidence and identical claimed bound. -/
theorem linear_adapter : linearThenTriple.Budget ((linear.code []).instructions + 1) :=
  linear_budget.comp triple_budget

theorem shared_direct (s) (x : Val ℚ (context [.prod .base .base])) (z : Stack ℚ s) :
    (runMeasured Arithmetic.meaning (sharedThenNegate.code s) (x,z)).2 ≤
      (shared.code []).instructions + 1 := by
  change (runMeasured _ ((shared.code s).append (negate.code s)) (x,z)).2 ≤ _
  rw [runMeasured_append]
  simp only [Resources.bind, shared.measured_correct]
  exact Nat.add_le_add (shared_budget s x z) (negate_budget s _ z)

theorem shared_adapter : sharedThenNegate.Budget ((shared.code []).instructions + 1) :=
  shared_budget.comp negate_budget

theorem linear_value_tail (s) (x y : ℕ) (z : Stack ℕ s) :
    (runMeasured (MatrixCompiler.meaning ℕ) (linearThenTriple.code s) (((),(x,y)),z)).1 =
      (3*(2*x+3*y),z) := linearThenTriple.measured_correct s _ z

theorem shared_value_tail (s) (x y : ℚ) (z : Stack ℚ s) :
    (runMeasured Arithmetic.meaning (sharedThenNegate.code s) (((),(x,y)),z)).1 =
      (-((x*y)*(x*y)+x),z) := sharedThenNegate.measured_correct s _ z

end Examples.CountedStack

namespace Examples.CountedStack.Partial
open SquareKit.HigherOrderComparison (Ty empty)
open SquareKit.WeakHigherOrder SquareKit.WeakMachine

/-- A syntactic function is related even though every invocation diverges. -/
theorem looping_related : Related (.arr .ground .ground) (loopingFunction : Term [] _)
    (fun _ => .spin) := by
  refine ⟨.omega,rfl,?_⟩
  intro x v hx
  exact ⟨.omega,.refl,.loop⟩

/-- A higher-order caller returns this partial function as a value. -/
theorem retained_partial_function :
    Behavior (Related (.arr .ground .ground)) (.app identity loopingFunction)
      (.done 1 (fun _ => .spin)) :=
  related_application Examples.WeakMachine.identity_related looping_related

theorem applied_loop (n : Nat) :
    Behavior (Related .ground) (.app loopingFunction (.lit n)) .spin :=
  related_application looping_related rfl

/-- Return/divergence adequacy replaces a total execution field. -/
theorem no_totality (n : Nat) : Infinite (.app loopingFunction (.lit n)) ∧
    ∀ m, ¬ SquareKit.WeakMachine.Returns (.app loopingFunction (.lit n)) m := by
  constructor
  · exact (divergence_denotation _).mpr rfl
  · intro m h
    have bad := (return_denotation _ m).mp h
    cases bad

end Examples.CountedStack.Partial

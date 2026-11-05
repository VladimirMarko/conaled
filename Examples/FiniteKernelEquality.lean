import Applications.Probability.FiniteKernelEquality
import Examples.MetropolisHastings

/-! Exact iteration and counterexamples to weakening the observation boundary. -/
namespace Applications.Probability.Examples
open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- An existing kernel-only computation now recovers the actual exact table. -/
theorem deterministic_two_steps_exact :
    (Table.deterministic Bool.not : Table bitSpace bitSpace).steps 2 =
      Table.deterministic id := by
  apply Table.kernel_injective
  apply Kernel.ext
  intro x
  rw [deterministic_two_steps, Table.kernel_deterministic]
  rfl

/-- Arbitrary-table composition laws require no direct matrix-sum proof. -/
example {W X Y Z : FiniteSpace} (h : Table Y Z) (g : Table X Y) (f : Table W X) :
    Table.comp (Table.comp h g) f = Table.comp h (Table.comp g f) :=
  Table.comp_assoc h g f

/-- Concatenating the retained MH client's iterations keeps exact rational entries. -/
example (n m : ℕ) :
    (FiniteMHExamples.asymmetric.transition : Table bitSpace bitSpace).steps (n + m) =
      Table.comp (FiniteMHExamples.asymmetric.transition.steps m)
        (FiniteMHExamples.asymmetric.transition.steps n) := Table.steps_add (X := bitSpace) FiniteMHExamples.asymmetric.transition n m

/-- The stronger facade remains compatible with the established full kernel. -/
example (X : FiniteSpace) (t : Table X X) (n m : ℕ) :
    (Table.comp (t.steps m) (t.steps n)).kernel = kernelSteps t.kernel (n + m) := by
  rw [← Table.steps_add, table_steps_meaning]

/-- Outside the nonnegative domain, clipping loses exact numeric information. -/
example : mass (-1) = mass (-2) ∧ (-1 : ℚ) ≠ -2 := by
  constructor
  · simp only [mass, Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat]
    rw [ENNReal.ofReal_of_nonpos (by norm_num : (-1 : ℝ) ≤ 0),
      ENNReal.ofReal_of_nonpos (by norm_num : (-2 : ℝ) ≤ 0)]
  · norm_num

abbrev pairSpace : FiniteSpace := ⟨Bool × Bool, inferInstance, inferInstance⟩
abbrev singletonSpace : FiniteSpace := ⟨Unit, inferInstance, inferInstance⟩
def leftOutput : Table singletonSpace pairSpace := Table.deterministic (fun _ => (false, false))
def rightOutput : Table singletonSpace pairSpace := Table.deterministic (fun _ => (false, true))

def firstMarginal (t : Table singletonSpace pairSpace) (x : singletonSpace) (a : Bool) : ℚ :=
  ∑ b : Bool, t.entry x (a, b)

theorem same_first_marginal : firstMarginal leftOutput = firstMarginal rightOutput := by
  funext x a
  simp only [firstMarginal, Fintype.sum_bool, leftOutput, rightOutput, Table.deterministic]
  cases a <;> norm_num [Prod.mk.injEq]

theorem different_tables : leftOutput ≠ rightOutput := by
  intro h
  have bad := congrArg (fun t : Table singletonSpace pairSpace => t.entry () (false, false)) h
  norm_num [leftOutput, rightOutput, Table.deterministic] at bad
  cases (Prod.mk.inj bad).2

theorem different_full_kernels : leftOutput.kernel ≠ rightOutput.kernel := by
  intro h
  exact different_tables (Table.kernel_injective h)

end Applications.Probability.Examples

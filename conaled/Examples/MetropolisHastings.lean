import Applications.Probability.MetropolisHastings

/-! Checked composition through the public finite-table interpretation. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Applications.Probability.Examples

abbrev bitSpace : FiniteSpace := ⟨Bool, inferInstance, inferInstance⟩

/-- Exact two-step probability: 0→1→0 contributes 1/3. -/
theorem asymmetric_two_steps :
    (FiniteMHExamples.asymmetric.transition.steps 2).entry false false = 1/3 := by
  norm_num [Table.steps, Table.comp, Table.deterministic, FiniteMH.transition,
    FiniteMH.rejection, FiniteMH.accepted, FiniteMH.acceptance,
    FiniteMHExamples.asymmetric, Fintype.sum_bool]

/-- The same calculation describes the composed ideal kernel. -/
theorem asymmetric_two_kernel_steps :
    kernelSteps (FiniteMHExamples.asymmetric.transition.kernel (α := bitSpace)) 2 false {false}
      = mass (1/3) := by
  rw [← table_steps_meaning bitSpace, Table.kernel_singleton, asymmetric_two_steps]

/-- Pure negation embeds as a deterministic kernel, and two negations restore the bit. -/
theorem deterministic_two_steps (x : Bool) :
    ((Table.deterministic Bool.not : Table bitSpace bitSpace).steps 2).kernel x =
      Measure.dirac x := by
  rw [table_steps_meaning bitSpace]
  simp only [kernelSteps, Table.kernel_deterministic, Kernel.comp_id,
    Kernel.deterministic_comp_deterministic]
  simp [Kernel.deterministic_apply]

/-- Kernel interpretation transports the whole finite-step output distribution. -/
theorem finite_distribution (X : FiniteSpace) (t : Table X X) (μ : Measure X) (n : ℕ) :
    μ.bind (t.steps n).kernel = μ.bind (kernelSteps t.kernel n) := by
  rw [table_steps_meaning X]

/-- Arbitrary finite MH iteration preserves the normalized target measure. -/
theorem mh_steps_stationary (X : FiniteSpace) [Nonempty X] (m : FiniteMH X) (n : ℕ) :
    (m.transition.steps n).kernel.Invariant m.targetMeasure := by
  rw [table_steps_meaning X]
  exact invariant_steps m.invariant n

/-- One MH step followed by two MH steps preserves the same target. -/
theorem mh_one_then_two (X : FiniteSpace) [Nonempty X] (m : FiniteMH X) :
    ((m.transition.steps 2).kernel ∘ₖ m.transition.kernel).Invariant m.targetMeasure :=
  invariant_comp (mh_steps_stationary X m 2) m.invariant

end Applications.Probability.Examples

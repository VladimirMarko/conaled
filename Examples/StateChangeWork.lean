import Applications.Probability.StateChangeDeadline
import Examples.SamplerWorkload

/-! Suppression preserves all actual row work, while reducing output handling. -/
namespace Examples.StateChangeWork
open Applications Applications.Probability
open SamplerWorkload
abbrev τ := TableSampler.unitTariff
abbrev model := SamplerWorkload.model
abbrev rows := SamplerWorkload.rows
abbrev prepared := SamplerWorkload.prepared
abbrev compiled := SamplerWorkload.compiled
abbrev overhead := SamplerWorkload.overhead

def tape (i : ℕ) : Bool := decide (i=2 ∨ i=3)

/-- The first 0011 row returns the current state; the next 0000 changes it. -/
theorem delivery : Progress.Delivers (TableProducer.changes rows tape)
    (TableProducer.start rows true 0) [false] (TableProducer.start rows false 8) 8 := by
  exact .cons (Progress.search_sound (fuel := 8) (by decide +kernel)) (.nil _)

example : (StateChangeWork.workload prepared τ overhead 1 tape true 0 8).1=
    ([false],TableProducer.start rows false 8) :=
  StateChangeWork.workload_delivers prepared rows (prepareLoader_value _ _ _) τ overhead 1
    tape true 0 delivery

/-- Setup 24; suppressed row 29+22+2+1; changed row 30+22+2+1+1;
one final output-handling unit. All three row preparations are retained. -/
example : (StateChangeWork.workload prepared τ overhead 1 tape true 0 4).1.1=[] ∧
    (StateChangeWork.workload prepared τ overhead 1 tape true 0 4).2=78 ∧
    (StateChangeWork.workload prepared τ overhead 1 tape true 0 8).2=135 := by
  decide +kernel

/-- Compilation pays its full setup, then all three lookups. -/
example : compiled.2+(StateChangeWork.workload compiled.1 τ overhead 1 tape true 0 8).2=118 := by
  decide +kernel

example : (StateChangeWork.workload prepared τ overhead 1 tape true 0 8).2≤
    24+8*(26+22+2+1+1)+1 := by
  apply StateChangeWork.workload_bound prepared rows (prepareLoader_value _ _ _) τ overhead 1
    tape 26 22 (fun x => by cases x <;> decide +kernel)
    (fun x => by cases x <;> decide +kernel) true 0 delivery

/-- Pausing after the suppressed return does not discard the prepared row. -/
example : Resources.run (StateChangeWork.tick prepared τ overhead 1 tape)
    (List.replicate 4 () ++ List.replicate 4 ()) (beginWork prepared τ true 0).1=
    Resources.bind (Resources.run (StateChangeWork.tick prepared τ overhead 1 tape)
      (List.replicate 4 ()) (beginWork prepared τ true 0).1)
      (Resources.run (StateChangeWork.tick prepared τ overhead 1 tape) (List.replicate 4 ())) :=
  Resources.run_append _ _ _ _

/-- This MH self proposal is accepted: state-change filtering is not acceptance filtering. -/
example : model.acceptance true true=1 ∧ model.proposal.entry true true=1/2 ∧
    model.rejection true=1/6 := by
  constructor
  · norm_num [FiniteMH.acceptance,FiniteMHExamples.asymmetric]
  constructor
  · norm_num [FiniteMHExamples.asymmetric]
  · exact FiniteMHExamples.asymmetric_rejection

open MeasureTheory in
open scoped ENNReal in
example : CoinPaths.law (StateChangeDeadline.fastChange rows 4 true (5*4))ᶜ≤
    (2/3 : ℝ≥0∞)^4+4*(2⁻¹ : ℝ≥0∞)^4 := by
  apply StateChangeDeadline.fastChange_failure_bound rows true (5*4) (2/3) ((2⁻¹)^4)
  · apply ENNReal.div_le_of_le_mul
    norm_num
  · rw [Table.prepare_returns_mass]
    norm_num [FiniteMH.transition,FiniteMH.accepted,FiniteMH.acceptance,
      FiniteMH.rejection,FiniteMHExamples.asymmetric,Fintype.sum_bool,mass,ENNReal.ofReal_div_of_pos]
  · have h := SamplerExpectedWork.row_deadline rows true 4
    have hw : SamplerExpectedWork.maxWidth rows=5 := by decide +kernel
    simpa [hw] using h

theorem exit_positive (x : Bool) : 0<StateChangeSampler.exit model.transition x := by
  cases x <;> norm_num [StateChangeSampler.exit,FiniteMH.transition,FiniteMH.accepted,
    FiniteMH.acceptance,FiniteMH.rejection,FiniteMHExamples.asymmetric,Fintype.sum_bool]

open scoped ENNReal in
theorem self_bound (x : Bool) : mass (model.transition.entry x x)≤mass (2/3) := by
  unfold mass
  apply ENNReal.ofReal_le_ofReal
  exact_mod_cast (show model.transition.entry x x≤2/3 by
    cases x <;> norm_num [FiniteMH.transition,FiniteMH.accepted,FiniteMH.acceptance,
      FiniteMH.rejection,FiniteMHExamples.asymmetric,Fintype.sum_bool])

open scoped ENNReal in
theorem self_bound_strict : mass (2/3)<1 := by
  unfold mass
  push_cast
  rw [← ENNReal.ofReal_one,ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  norm_num

open MeasureTheory in
open scoped ENNReal in
example : CoinPaths.law (StateChangeDeadline.deadline rows 2 true 0 640)≤
    2*((mass (2/3))^8+8*(2⁻¹ : ℝ≥0∞)^8) := by
  have h := StateChangeDeadline.deadline_bound model.transition exit_positive rows
    (fun x s a => Table.prepare_returns_mass _ _ _ _ _) (mass (2/3)) self_bound_strict self_bound
    2 true 0 8 8
  have hw : SamplerExpectedWork.maxWidth rows=5 := by decide +kernel
  simpa [hw] using h

open MeasureTheory in
open scoped ENNReal in
/-- A full charged deadline, including preparation after suppressed transitions.
The finite bound is conservative; it is distinct from the exact 135-unit run. -/
example : CoinPaths.law (StateChangeDeadline.workDeadline prepared rows τ overhead 1 0 2 true 0 33306)≤
    2*((mass (2/3))^8+8*(2⁻¹ : ℝ≥0∞)^8) := by
  have h := StateChangeDeadline.workDeadline_bound model.transition exit_positive rows
    (fun x s a => Table.prepare_returns_mass _ _ _ _ _) prepared (prepareLoader_value _ _ _)
    τ overhead 1 0 26 22 (fun x => by cases x <;> decide +kernel)
    (fun x => by cases x <;> decide +kernel) (mass (2/3)) self_bound_strict self_bound 2 true 0 8 8
  have hw : SamplerExpectedWork.maxWidth rows=5 := by decide +kernel
  have hprep : (prepared true).2=22 := by decide +kernel
  simpa [hw,hprep,SamplerWork.initialization,TableSampler.unitTariff,Examples.SamplerWorkload.overhead] using h

end Examples.StateChangeWork

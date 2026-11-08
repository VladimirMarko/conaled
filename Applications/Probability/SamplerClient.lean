import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Tactic

/-! Independent finite sampling contract for the represented-sampler comparison. -/
open MeasureTheory
namespace Applications.Probability.SamplerClient

noncomputable def fair : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac false + (1 / 2 : ℝ≥0∞) • Measure.dirac true

def function (b x : Bool) : Bool := b ^^ x

def selected (b t u : Bool) : Bool × Bool × Bool × Bool :=
  (b, t, function b t, function (function b t) u)

noncomputable def pairMeaning : Measure (Bool × Bool) :=
  (1 / 4 : ℝ≥0∞) • Measure.dirac (false, false) +
  (1 / 4 : ℝ≥0∞) • Measure.dirac (false, true) +
  (1 / 4 : ℝ≥0∞) • Measure.dirac (true, false) +
  (1 / 4 : ℝ≥0∞) • Measure.dirac (true, true)

noncomputable def tripleMeaning : Measure (Bool × Bool × Bool) :=
  (fair.prod fair).prod fair |>.map (fun p => (p.1.1, p.1.2, p.2))

example : selected false true true = (false, true, true, false) := rfl
example : selected true false true = (true, false, true, false) := rfl
example (b : Bool) : function b b = false := by cases b <;> rfl
example : function false ≠ function true := by
  intro h
  have := congrFun h false
  contradiction

end Applications.Probability.SamplerClient

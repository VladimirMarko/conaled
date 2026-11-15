import Applications.Numerals.Decimal
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Field.GeomSum

/-!
# Rational residuals of fractional numeral steps

The trace records rational observations in source digit order. It describes
residual propagation, independently of an executor or a partial decoder.
Actual floating observations must establish this relation separately. The
uniform envelopes retain their local-error hypotheses; they are not primitive
rounding laws or bounds for every floating numeral execution.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Numerals.FloatingError

/-- Exact rational observations of the four values at a decimal fold step. -/
structure Step where
  digit : Nat
  tailValue : ℚ
  convertedValue : ℚ
  addedValue : ℚ
  outputValue : ℚ
deriving DecidableEq, Repr

def Step.conversionError (s : Step) : ℚ := s.convertedValue - (s.digit : ℚ)
def Step.additionError (s : Step) : ℚ := s.addedValue - (s.convertedValue + s.tailValue)
def Step.divisionError (s : Step) : ℚ := s.outputValue - s.addedValue / 10

/-- Conversion and addition residuals are divided before the division residual is added. -/
def Step.localError (s : Step) : ℚ :=
  (s.conversionError + s.additionError) / 10 + s.divisionError

/-- The three source-operation residuals remain separately observable. -/
def Step.operationBound (s : Step) : ℚ :=
  (|s.conversionError| + |s.additionError|) / 10 + |s.divisionError|

/-- Source input order is retained, while a right fold evaluates its tail first. -/
inductive Trace : List Nat → List Step → ℚ → Prop where
  | nil : Trace [] [] 0
  | cons (s : Step) {digits : List Nat} {steps : List Step}
      (tail : Trace digits steps s.tailValue) :
      Trace (s.digit :: digits) (s :: steps) s.outputValue

/-- A residual at source depth `i` is attenuated by `10^i`. -/
def propagate (weight : Step → ℚ) : List Step → ℚ
  | [] => 0
  | s :: steps => weight s + propagate weight steps / 10

def signedError (steps : List Step) : ℚ := propagate Step.localError steps
def errorBound (steps : List Step) : ℚ := propagate (fun s => |s.localError|) steps
def operationBound (steps : List Step) : ℚ := propagate Step.operationBound steps

/-- An independent indexed sum, including every occurrence of a repeated step. -/
def weightedSum (weight : Step → ℚ) (steps : List Step) : ℚ :=
  (steps.zipIdx.map (fun p => weight p.1 / (10 : ℚ) ^ p.2)).sum

theorem step_decomposition (s : Step) :
    s.outputValue = ((s.digit : ℚ) + s.tailValue) / 10 + s.localError := by
  dsimp [Step.localError, Step.conversionError, Step.additionError, Step.divisionError]
  ring

theorem trace_length {digits : List Nat} {steps : List Step} {value : ℚ}
    (h : Trace digits steps value) : steps.length = digits.length := by
  induction h with
  | nil => rfl
  | cons s tail ih => simpa using ih

theorem trace_digits {digits : List Nat} {steps : List Step} {value : ℚ}
    (h : Trace digits steps value) : steps.map Step.digit = digits := by
  induction h with
  | nil => rfl
  | cons s tail ih => simp [ih]

theorem trace_error_identity {digits : List Nat} {steps : List Step} {value : ℚ}
    (h : Trace digits steps value) :
    value = Decimal.fractionFold digits + signedError steps := by
  induction h with
  | nil => simp [Decimal.fractionFold, signedError, propagate]
  | cons s tail ih =>
    change s.outputValue = ((s.digit : ℚ) + Decimal.fractionFold _) / 10 +
      (s.localError + signedError _ / 10)
    rw [step_decomposition, ih]
    ring

theorem trace_error_identity_rat {digits : List Nat} {steps : List Step} {value : ℚ}
    (h : Trace digits steps value) :
    value - Decimal.fractionRat digits = signedError steps := by
  have hi := trace_error_identity h
  rw [Decimal.fractionFold_eq_fraction] at hi
  rw [hi]
  ring

private theorem weighted_from (weight : Step → ℚ) (steps : List Step) (i : Nat) :
    (steps.zipIdx i |>.map (fun p => weight p.1 / (10 : ℚ) ^ p.2)).sum =
      propagate weight steps / (10 : ℚ) ^ i := by
  induction steps generalizing i with
  | nil => simp [propagate]
  | cons s steps ih =>
    simp only [List.zipIdx_cons, List.map_cons, List.sum_cons, propagate]
    rw [ih, pow_succ]
    simp only [add_div, div_div, mul_comm]

theorem propagate_eq_weightedSum (weight : Step → ℚ) (steps : List Step) :
    propagate weight steps = weightedSum weight steps := by
  simpa only [pow_zero, div_one, weightedSum] using (weighted_from weight steps 0).symm

theorem signedError_eq_weightedSum (steps : List Step) :
    signedError steps = weightedSum Step.localError steps :=
  propagate_eq_weightedSum _ _

theorem trace_weighted_error {digits : List Nat} {steps : List Step} {value : ℚ}
    (h : Trace digits steps value) :
    value - Decimal.fractionRat digits = weightedSum Step.localError steps := by
  rw [trace_error_identity_rat h, signedError_eq_weightedSum]

theorem propagate_nonneg (weight : Step → ℚ) (steps : List Step)
    (h : ∀ s ∈ steps, 0 ≤ weight s) : 0 ≤ propagate weight steps := by
  induction steps with
  | nil => exact le_rfl
  | cons s steps ih =>
    exact add_nonneg (h s List.mem_cons_self)
      (div_nonneg (ih (fun t ht => h t (List.mem_cons_of_mem s ht))) (by norm_num))

theorem errorBound_nonneg (steps : List Step) : 0 ≤ errorBound steps :=
  propagate_nonneg _ _ (fun s _ => abs_nonneg s.localError)

theorem propagate_mono (left right : Step → ℚ) (steps : List Step)
    (h : ∀ s ∈ steps, left s ≤ right s) :
    propagate left steps ≤ propagate right steps := by
  induction steps with
  | nil => exact le_rfl
  | cons s steps ih =>
    exact add_le_add (h s List.mem_cons_self)
      (div_le_div_of_nonneg_right (ih (fun t ht => h t (List.mem_cons_of_mem s ht)))
        (by norm_num))

theorem signedError_abs_le (steps : List Step) : |signedError steps| ≤ errorBound steps := by
  rw [signedError_eq_weightedSum, errorBound, propagate_eq_weightedSum]
  have triangle := List.le_sum_of_subadditive (fun q : ℚ => |q|) (by norm_num)
    (fun a b => abs_add_le a b)
    (steps.zipIdx.map (fun p => p.1.localError / (10 : ℚ) ^ p.2))
  simpa [weightedSum, List.map_map, Function.comp_def, abs_div] using triangle

theorem localError_abs_le_operationBound (s : Step) :
    |s.localError| ≤ s.operationBound := by
  change |(s.conversionError + s.additionError) / 10 + s.divisionError| ≤ _
  calc
    _ ≤ |(s.conversionError + s.additionError) / 10| + |s.divisionError| := abs_add_le _ _
    _ = |s.conversionError + s.additionError| / 10 + |s.divisionError| := by
      norm_num [abs_div]
    _ ≤ (|s.conversionError| + |s.additionError|) / 10 + |s.divisionError| :=
      add_le_add
        (div_le_div_of_nonneg_right (abs_add_le s.conversionError s.additionError)
          (by norm_num : (0 : ℚ) ≤ 10)) le_rfl

theorem errorBound_le_operationBound (steps : List Step) :
    errorBound steps ≤ operationBound steps :=
  propagate_mono _ _ _ (fun s _ => localError_abs_le_operationBound s)

theorem operationBound_nonneg (steps : List Step) : 0 ≤ operationBound steps :=
  (errorBound_nonneg steps).trans (errorBound_le_operationBound steps)

theorem trace_absolute_error {digits : List Nat} {steps : List Step} {value : ℚ}
    (h : Trace digits steps value) :
    |value - Decimal.fractionRat digits| ≤ errorBound steps := by
  rw [trace_error_identity_rat h]
  exact signedError_abs_le steps

theorem trace_operation_error {digits : List Nat} {steps : List Step} {value : ℚ}
    (h : Trace digits steps value) :
    |value - Decimal.fractionRat digits| ≤ operationBound steps :=
  (trace_absolute_error h).trans (errorBound_le_operationBound steps)

/-- The coarse envelope requires the common upper bound to be nonnegative. -/
theorem propagate_uniform (weight : Step → ℚ) (steps : List Step)
    (epsilon : ℚ) (he : 0 ≤ epsilon) (h : ∀ s ∈ steps, weight s ≤ epsilon) :
    propagate weight steps ≤ (10 / 9 : ℚ) * epsilon := by
  induction steps with
  | nil => exact mul_nonneg (by norm_num) he
  | cons s steps ih =>
    calc
      propagate weight (s :: steps) ≤ epsilon + ((10 / 9 : ℚ) * epsilon) / 10 :=
        add_le_add (h s List.mem_cons_self)
          (div_le_div_of_nonneg_right (ih (fun t ht => h t (List.mem_cons_of_mem s ht)))
            (by norm_num))
      _ = (10 / 9 : ℚ) * epsilon := by ring

/-- The local-error premise is separate from any primitive floating accuracy theorem. -/
theorem errorBound_uniform (steps : List Step) (epsilon : ℚ) (he : 0 ≤ epsilon)
    (h : ∀ s ∈ steps, |s.localError| ≤ epsilon) :
    errorBound steps ≤ (10 / 9 : ℚ) * epsilon :=
  propagate_uniform (fun s => |s.localError|) steps epsilon he h

theorem trace_uniform_error {digits : List Nat} {steps : List Step} {value : ℚ}
    (trace : Trace digits steps value) (epsilon : ℚ) (he : 0 ≤ epsilon)
    (h : ∀ s ∈ steps, |s.localError| ≤ epsilon) :
    |value - Decimal.fractionRat digits| ≤ (10 / 9 : ℚ) * epsilon :=
  (trace_absolute_error trace).trans (errorBound_uniform steps epsilon he h)

private theorem propagate_const (steps : List Step) (epsilon : ℚ) :
    propagate (fun _ => epsilon) steps =
      epsilon * ∑ i ∈ Finset.range steps.length, (1 / 10 : ℚ) ^ i := by
  induction steps with
  | nil => simp [propagate]
  | cons s steps ih =>
    rw [propagate, ih, List.length_cons, Finset.sum_range_succ']
    simp only [pow_zero, pow_succ]
    rw [← Finset.sum_mul]
    ring

/-- The finite envelope also holds for negative weights and a negative common bound. -/
theorem propagate_uniform_length (weight : Step → ℚ) (steps : List Step)
    (epsilon : ℚ) (h : ∀ s ∈ steps, weight s ≤ epsilon) :
    propagate weight steps ≤
      (10 / 9 : ℚ) * epsilon * (1 - 1 / (10 : ℚ) ^ steps.length) := by
  have hb := propagate_mono weight (fun _ => epsilon) steps h
  rw [propagate_const] at hb
  calc
    propagate weight steps ≤ epsilon * ∑ i ∈ Finset.range steps.length, (1 / 10 : ℚ) ^ i := hb
    _ = (10 / 9 : ℚ) * epsilon * (1 - 1 / (10 : ℚ) ^ steps.length) := by
      rw [geom_sum_eq (by norm_num : (1 / 10 : ℚ) ≠ 1), one_div_pow]
      ring

/-- The existing absolute-error API retains its nonnegative-epsilon argument. -/
theorem errorBound_uniform_length (steps : List Step) (epsilon : ℚ) (_he : 0 ≤ epsilon)
    (h : ∀ s ∈ steps, |s.localError| ≤ epsilon) :
    errorBound steps ≤
      (10 / 9 : ℚ) * epsilon * (1 - 1 / (10 : ℚ) ^ steps.length) :=
  propagate_uniform_length (fun s => |s.localError|) steps epsilon h

theorem trace_uniform_error_length {digits : List Nat} {steps : List Step} {value : ℚ}
    (trace : Trace digits steps value) (epsilon : ℚ) (he : 0 ≤ epsilon)
    (h : ∀ s ∈ steps, |s.localError| ≤ epsilon) :
    |value - Decimal.fractionRat digits| ≤
      (10 / 9 : ℚ) * epsilon * (1 - 1 / (10 : ℚ) ^ digits.length) := by
  have hbound := errorBound_uniform_length steps epsilon he h
  rw [trace_length trace] at hbound
  exact (trace_absolute_error trace).trans hbound

end Numerals.FloatingError

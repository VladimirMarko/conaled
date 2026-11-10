import Applications.Numerals.Floating
import Applications.Numerals.FloatingError
import Applications.Floating.Observation

/-!
# Observing actual decimal steps and checking their residual bounds

Execution operations, partial decoding and correctness laws are independent.
The observer retains the actual result even when observations fail. Its empty
certificate is rational zero; relating that certificate to the actual execution
seed requires a separate zero-decoding law. Trace-only mathematics does not.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Numerals.Floating

open Numerals.FloatingError
open _root_.Floating.Observation
variable {α : Type}

structure Certificate where
  value : ℚ
  steps : List Step
  deriving DecidableEq, Repr

def observeStep (read : α → Option ℚ) (d : Nat)
    (converted added output : α) (tail : Option Certificate) : Option Certificate := do
  let prior ← tail
  let qd ← read converted
  let qs ← read added
  let qo ← read output
  pure ⟨qo, ⟨d, prior.value, qd, qs, qo⟩ :: prior.steps⟩

def run (ops : Operations α) (read : α → Option ℚ) : List Nat → α × Option Certificate
  | [] => (ops.zero, some ⟨0, []⟩)
  | d :: ds =>
      let tail := run ops read ds
      let converted := ops.convert d
      let added := ops.add converted tail.1
      let output := ops.divideTen added
      (output, observeStep read d converted added output tail.2)

theorem run_value (ops : Operations α) (read : α → Option ℚ) (digits : List Nat) :
    (run ops read digits).1 = fraction ops digits := by
  induction digits with
  | nil => rfl
  | cons d ds ih => simp only [run, fraction, List.foldr_cons, ih]

theorem observeStep_eq_some_iff (read : α → Option ℚ) (d : Nat)
    (converted added output : α) (tail : Option Certificate) (c : Certificate) :
    observeStep read d converted added output tail = some c ↔
      ∃ prior qd qs qo, tail = some prior ∧ read converted = some qd ∧
        read added = some qs ∧ read output = some qo ∧
        (⟨qo, ⟨d, prior.value, qd, qs, qo⟩ :: prior.steps⟩ : Certificate) = c := by
  cases ht : tail <;> cases hd : read converted <;>
    cases hs : read added <;> cases ho : read output <;>
    simp [observeStep, hd, hs, ho]

private theorem observeStep_sound (read : α → Option ℚ) (d : Nat)
    (converted added output : α) (tail : Option Certificate) (digits : List Nat)
    (ht : ∀ c, tail = some c → Trace digits c.steps c.value)
    (c : Certificate) (hc : observeStep read d converted added output tail = some c) :
    read output = some c.value ∧ Trace (d :: digits) c.steps c.value := by
  obtain ⟨prior, qd, qs, qo, hp, _, _, ho, he⟩ :=
    (observeStep_eq_some_iff read d converted added output tail c).mp hc
  subst c
  exact ⟨ho, Trace.cons ⟨d, prior.value, qd, qs, qo⟩ (ht prior hp)⟩

/-- The recorded rational trace starts at its constructed zero, without a decoder law. -/
theorem run_trace (ops : Operations α) (read : α → Option ℚ) (digits : List Nat)
    (c : Certificate) (hc : (run ops read digits).2 = some c) :
    Trace digits c.steps c.value := by
  induction digits generalizing c with
  | nil =>
    have he : (⟨0, []⟩ : Certificate) = c := by simpa [run] using hc
    subst c
    exact Trace.nil
  | cons d ds ih =>
    exact (observeStep_sound read d (ops.convert d)
      (ops.add (ops.convert d) (run ops read ds).1)
      (ops.divideTen (ops.add (ops.convert d) (run ops read ds).1))
      (run ops read ds).2 ds ih c hc).2

/-- The seed law is needed to identify the empty certificate with the actual result. -/
theorem run_sound (ops : Operations α) (read : α → Option ℚ)
    (zero_decodes : read ops.zero = some 0) (digits : List Nat)
    (c : Certificate) (hc : (run ops read digits).2 = some c) :
    read (fraction ops digits) = some c.value ∧ Trace digits c.steps c.value := by
  cases digits with
  | nil =>
    have he : (⟨0, []⟩ : Certificate) = c := by simpa [run] using hc
    subst c
    exact ⟨zero_decodes, Trace.nil⟩
  | cons d ds =>
    have h := observeStep_sound read d (ops.convert d)
      (ops.add (ops.convert d) (run ops read ds).1)
      (ops.divideTen (ops.add (ops.convert d) (run ops read ds).1))
      (run ops read ds).2 ds (run_trace ops read ds) c hc
    simpa only [run_value, fraction, List.foldr_cons] using h

/-- The actual conversion, sum and quotient are observed independently of `run`. -/
def Observes (ops : Operations α) (read : α → Option ℚ) : List Nat → List Step → Prop
  | [], [] => True
  | d :: ds, s :: ss =>
      s.digit = d ∧ read (fraction ops ds) = some s.tailValue ∧
      read (ops.convert d) = some s.convertedValue ∧
      read (ops.add (ops.convert d) (fraction ops ds)) = some s.addedValue ∧
      read (fraction ops (d :: ds)) = some s.outputValue ∧ Observes ops read ds ss
  | _, _ => False

theorem run_observations (ops : Operations α) (read : α → Option ℚ)
    (zero_decodes : read ops.zero = some 0) (digits : List Nat)
    (c : Certificate) (hc : (run ops read digits).2 = some c) :
    Observes ops read digits c.steps := by
  induction digits generalizing c with
  | nil =>
    have he : (⟨0, []⟩ : Certificate) = c := by simpa [run] using hc
    subst c
    trivial
  | cons d ds ih =>
    obtain ⟨prior, qd, qs, qo, hp, hd, hs, ho, he⟩ :=
      (observeStep_eq_some_iff read d (ops.convert d)
        (ops.add (ops.convert d) (run ops read ds).1)
        (ops.divideTen (ops.add (ops.convert d) (run ops read ds).1))
        (run ops read ds).2 c).mp hc
    subst c
    refine ⟨rfl, (run_sound ops read zero_decodes ds prior hp).1, hd, ?_, ?_, ih prior hp⟩
    · simpa only [run_value] using hs
    · simpa only [run_value, fraction, List.foldr_cons] using ho

theorem observations_digit_conversion (ops : Operations α) (read : α → Option ℚ)
    (exact_digit : ∀ d, d < 10 → read (ops.convert d) = some (d : ℚ))
    (digits : List Nat) (steps : List Step) (hd : Decimal.Digits digits)
    (ho : Observes ops read digits steps) : ∀ s ∈ steps, s.conversionError = 0 := by
  induction digits generalizing steps with
  | nil =>
    cases steps with
    | nil => simp
    | cons s ss => contradiction
  | cons d ds ih =>
    cases steps with
    | nil => contradiction
    | cons s ss =>
      obtain ⟨hdigit, _, hconvert, _, _, htail⟩ := ho
      have he : s.convertedValue = (d : ℚ) :=
        Option.some.inj (hconvert.symm.trans (exact_digit d (hd d List.mem_cons_self)))
      have hs : s.conversionError = 0 := by simp [Step.conversionError, he, hdigit]
      have hi := ih ss (fun e he => hd e (List.mem_cons_of_mem d he)) htail
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hs
      · exact hi t ht

/-- Tests all source stages, not only the final value. The empty case is deliberately true. -/
def StagesFinite (ops : Operations α) (finite : α → Bool) : List Nat → Prop
  | [] => True
  | d :: ds =>
      StagesFinite ops finite ds ∧ finite (ops.convert d) = true ∧
      finite (ops.add (ops.convert d) (fraction ops ds)) = true ∧
      finite (ops.divideTen (ops.add (ops.convert d) (fraction ops ds))) = true

abbrev FiniteRun (ops : Operations α) (read : α → Option ℚ) : List Nat → Prop :=
  StagesFinite ops (fun value => (read value).isSome)

private theorem observeStep_isSome (read : α → Option ℚ) (d : Nat)
    (converted added output : α) (tail : Option Certificate) :
    (observeStep read d converted added output tail).isSome = true ↔
      tail.isSome = true ∧ (read converted).isSome = true ∧
      (read added).isSome = true ∧ (read output).isSome = true := by
  cases ht : tail <;> cases hd : read converted <;>
    cases hs : read added <;> cases ho : read output <;>
    simp [observeStep, hd, hs, ho]

theorem run_finite_iff (ops : Operations α) (read : α → Option ℚ) (digits : List Nat) :
    (run ops read digits).2.isSome = true ↔ FiniteRun ops read digits := by
  induction digits with
  | nil => simp [run, FiniteRun, StagesFinite]
  | cons d ds ih =>
    change (observeStep read d _ _ _ _).isSome = true ↔ _
    rw [observeStep_isSome, ih, run_value]
    rfl

theorem run_none_iff (ops : Operations α) (read : α → Option ℚ) (digits : List Nat) :
    (run ops read digits).2 = none ↔ ¬ FiniteRun ops read digits := by
  rw [← run_finite_iff]
  cases (run ops read digits).2 <;> simp

theorem run_error_identity (ops : Operations α) (read : α → Option ℚ) (digits : List Nat)
    (c : Certificate) (hc : (run ops read digits).2 = some c) :
    c.value - Decimal.fractionRat digits = weightedSum Step.localError c.steps :=
  trace_weighted_error (run_trace ops read digits c hc)

theorem run_error_bound (ops : Operations α) (read : α → Option ℚ) (digits : List Nat)
    (c : Certificate) (hc : (run ops read digits).2 = some c) :
    |c.value - Decimal.fractionRat digits| ≤ errorBound c.steps :=
  trace_absolute_error (run_trace ops read digits c hc)

theorem run_operation_bound (ops : Operations α) (read : α → Option ℚ) (digits : List Nat)
    (c : Certificate) (hc : (run ops read digits).2 = some c) :
    |c.value - Decimal.fractionRat digits| ≤ operationBound c.steps :=
  trace_operation_error (run_trace ops read digits c hc)

theorem run_digits (ops : Operations α) (read : α → Option ℚ) (digits : List Nat)
    (c : Certificate) (hc : (run ops read digits).2 = some c) :
    c.steps.map Step.digit = digits := trace_digits (run_trace ops read digits c hc)

theorem run_length (ops : Operations α) (read : α → Option ℚ) (digits : List Nat)
    (c : Certificate) (hc : (run ops read digits).2 = some c) :
    c.steps.length = digits.length := trace_length (run_trace ops read digits c hc)

/-- The conservative source bound test; it does not test final error directly. -/
def certify (ops : Operations α) (read : α → Option ℚ)
    (digits : List Nat) (tolerance : ℚ) : Bool :=
  match (run ops read digits).2 with
  | none => false
  | some c => decide (operationBound c.steps ≤ tolerance)

theorem certify_iff (ops : Operations α) (read : α → Option ℚ)
    (digits : List Nat) (tolerance : ℚ) :
    certify ops read digits tolerance = true ↔
      ∃ c, (run ops read digits).2 = some c ∧ operationBound c.steps ≤ tolerance := by
  cases hc : (run ops read digits).2 <;> simp [certify, hc]

theorem certify_sound (ops : Operations α) (read : α → Option ℚ)
    (zero_decodes : read ops.zero = some 0) (digits : List Nat) (tolerance : ℚ)
    (h : certify ops read digits tolerance = true) :
    ∃ value, read (fraction ops digits) = some value ∧
      |value - Decimal.fractionRat digits| ≤ tolerance := by
  obtain ⟨c, hc, hb⟩ := (certify_iff ops read digits tolerance).mp h
  exact ⟨c.value, (run_sound ops read zero_decodes digits c hc).1,
    (run_operation_bound ops read digits c hc).trans hb⟩

/-- A single observation followed by the same source bound test, retaining failure. -/
def releaseCertificate (ops : Operations α) (read : α → Option ℚ)
    (digits : List Nat) (tolerance : ℚ) : Option Certificate :=
  match (run ops read digits).2 with
  | none => none
  | some c => if operationBound c.steps ≤ tolerance then some c else none

theorem releaseCertificate_eq_some_iff (ops : Operations α) (read : α → Option ℚ)
    (digits : List Nat) (tolerance : ℚ) (c : Certificate) :
    releaseCertificate ops read digits tolerance = some c ↔
      (run ops read digits).2 = some c ∧ operationBound c.steps ≤ tolerance := by
  cases hc : (run ops read digits).2 with
  | none => simp [releaseCertificate, hc]
  | some prior =>
    by_cases he : prior = c
    · subst c
      by_cases hb : operationBound prior.steps ≤ tolerance <;>
        simp [releaseCertificate, hc, hb]
    · by_cases hb : operationBound prior.steps ≤ tolerance <;>
        simp [releaseCertificate, hc, hb, he]

theorem releaseCertificate_isSome (ops : Operations α) (read : α → Option ℚ)
    (digits : List Nat) (tolerance : ℚ) :
    (releaseCertificate ops read digits tolerance).isSome = certify ops read digits tolerance := by
  cases hc : (run ops read digits).2 with
  | none => simp [releaseCertificate, certify, hc]
  | some c =>
    by_cases hb : operationBound c.steps ≤ tolerance <;>
      simp [releaseCertificate, certify, hc, hb]

theorem releaseCertificate_sound (ops : Operations α) (read : α → Option ℚ)
    (zero_decodes : read ops.zero = some 0) (digits : List Nat) (tolerance : ℚ)
    (c : Certificate) (h : releaseCertificate ops read digits tolerance = some c) :
    read (fraction ops digits) = some c.value ∧ Trace digits c.steps c.value ∧
      operationBound c.steps ≤ tolerance ∧ |c.value - Decimal.fractionRat digits| ≤ tolerance := by
  obtain ⟨hc, hb⟩ := (releaseCertificate_eq_some_iff ops read digits tolerance c).mp h
  exact ⟨(run_sound ops read zero_decodes digits c hc).1, run_trace ops read digits c hc,
    hb, (run_operation_bound ops read digits c hc).trans hb⟩

def analyze64 (digits : List Nat) : Option Certificate := (run operations64 decode64 digits).2
def analyze32 (digits : List Nat) : Option Certificate := (run operations32 decode32 digits).2
def certify64 (digits : List Nat) (tolerance : ℚ) : Bool :=
  certify operations64 decode64 digits tolerance
def certify32 (digits : List Nat) (tolerance : ℚ) : Bool :=
  certify operations32 decode32 digits tolerance

theorem analyze64_sound (digits : List Nat) (c : Certificate) (hc : analyze64 digits = some c) :
    decode64 (fraction64 digits) = some c.value ∧ Trace digits c.steps c.value :=
  run_sound operations64 decode64 decode64_zero digits c hc

theorem analyze32_sound (digits : List Nat) (c : Certificate) (hc : analyze32 digits = some c) :
    decode32 (fraction32 digits) = some c.value ∧ Trace digits c.steps c.value :=
  run_sound operations32 decode32 decode32_zero digits c hc

theorem analyze64_error (digits : List Nat) (c : Certificate) (hc : analyze64 digits = some c) :
    c.value - Decimal.fractionRat digits = weightedSum Step.localError c.steps ∧
      |c.value - Decimal.fractionRat digits| ≤ operationBound c.steps :=
  ⟨run_error_identity operations64 decode64 digits c hc,
    run_operation_bound operations64 decode64 digits c hc⟩

theorem analyze32_error (digits : List Nat) (c : Certificate) (hc : analyze32 digits = some c) :
    c.value - Decimal.fractionRat digits = weightedSum Step.localError c.steps ∧
      |c.value - Decimal.fractionRat digits| ≤ operationBound c.steps :=
  ⟨run_error_identity operations32 decode32 digits c hc,
    run_operation_bound operations32 decode32 digits c hc⟩

theorem analyze64_observations (digits : List Nat) (c : Certificate)
    (hc : analyze64 digits = some c) : Observes operations64 decode64 digits c.steps :=
  run_observations operations64 decode64 decode64_zero digits c hc

theorem analyze32_observations (digits : List Nat) (c : Certificate)
    (hc : analyze32 digits = some c) : Observes operations32 decode32 digits c.steps :=
  run_observations operations32 decode32 decode32_zero digits c hc

theorem analyze64_digit_conversion (digits : List Nat) (c : Certificate)
    (hd : Decimal.Digits digits) (hc : analyze64 digits = some c) :
    ∀ s ∈ c.steps, s.conversionError = 0 :=
  observations_digit_conversion operations64 decode64 decode64_digit digits c.steps hd
    (analyze64_observations digits c hc)

theorem analyze32_digit_conversion (digits : List Nat) (c : Certificate)
    (hd : Decimal.Digits digits) (hc : analyze32 digits = some c) :
    ∀ s ∈ c.steps, s.conversionError = 0 :=
  observations_digit_conversion operations32 decode32 decode32_digit digits c.steps hd
    (analyze32_observations digits c hc)

theorem analyze64_finite_iff (digits : List Nat) :
    (analyze64 digits).isSome = true ↔ StagesFinite operations64 Float.isFinite digits := by
  simpa only [analyze64, FiniteRun, decode64_isFinite] using
    run_finite_iff operations64 decode64 digits

theorem analyze32_finite_iff (digits : List Nat) :
    (analyze32 digits).isSome = true ↔ StagesFinite operations32 Float32.isFinite digits := by
  simpa only [analyze32, FiniteRun, decode32_isFinite] using
    run_finite_iff operations32 decode32 digits

theorem analyze64_none_iff (digits : List Nat) :
    analyze64 digits = none ↔ ¬ StagesFinite operations64 Float.isFinite digits := by
  simpa only [analyze64, FiniteRun, decode64_isFinite] using
    run_none_iff operations64 decode64 digits

theorem analyze32_none_iff (digits : List Nat) :
    analyze32 digits = none ↔ ¬ StagesFinite operations32 Float32.isFinite digits := by
  simpa only [analyze32, FiniteRun, decode32_isFinite] using
    run_none_iff operations32 decode32 digits

theorem certify64_sound (digits : List Nat) (tolerance : ℚ)
    (h : certify64 digits tolerance = true) :
    ∃ value, decode64 (fraction64 digits) = some value ∧
      |value - Decimal.fractionRat digits| ≤ tolerance :=
  certify_sound operations64 decode64 decode64_zero digits tolerance h

theorem certify32_sound (digits : List Nat) (tolerance : ℚ)
    (h : certify32 digits tolerance = true) :
    ∃ value, decode32 (fraction32 digits) = some value ∧
      |value - Decimal.fractionRat digits| ≤ tolerance :=
  certify_sound operations32 decode32 decode32_zero digits tolerance h

end Numerals.Floating

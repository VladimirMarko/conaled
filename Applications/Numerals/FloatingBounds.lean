import Applications.Numerals.FloatingObserver

/-!
# Constructing proper-digit observations from local step laws

The operations, partial decoder and zero-decoding law remain separate. Local
addition/division laws construct successful observations and closed ranges at
every step of the unchanged right fold. Actual Float/Float32 instances must
establish these laws from their formatted operations; they are not supplied here.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Numerals.Floating

open Numerals.FloatingError
variable {α : Type}

/-- Local observation, range and residual obligations for the source operations. -/
structure StepLaws (ops : Operations α) (read : α → Option ℚ) (addEps divEps : ℚ) : Prop where
  addition_nonneg : 0 ≤ addEps
  division_nonneg : 0 ≤ divEps
  digit_exact : ∀ d, d < 10 → read (ops.convert d) = some (d : ℚ)
  addition : ∀ (d : Nat) (x : α) (q : ℚ), d < 10 →
    read x = some q → 0 ≤ q → q ≤ 1 →
    ∃ sum, read (ops.add (ops.convert d) x) = some sum ∧
      0 ≤ sum ∧ sum ≤ 10 ∧ |sum - ((d : ℚ) + q)| ≤ addEps
  division : ∀ (x : α) (q : ℚ), read x = some q → 0 ≤ q → q ≤ 10 →
    ∃ value, read (ops.divideTen x) = some value ∧
      0 ≤ value ∧ value ≤ 1 ∧ |value - q / 10| ≤ divEps

/-- Proper-input range and residual facts for an independently recorded step. -/
structure StepBounds (addEps divEps : ℚ) (s : Step) : Prop where
  digit_proper : s.digit < 10
  conversion_exact : s.convertedValue = (s.digit : ℚ)
  tail_nonneg : 0 ≤ s.tailValue
  tail_le_one : s.tailValue ≤ 1
  sum_nonneg : 0 ≤ s.addedValue
  sum_le_ten : s.addedValue ≤ 10
  output_nonneg : 0 ≤ s.outputValue
  output_le_one : s.outputValue ≤ 1
  addition_error : |s.additionError| ≤ addEps
  division_error : |s.divisionError| ≤ divEps

theorem StepBounds.conversion_error {a b : ℚ} {s : Step} (h : StepBounds a b s) :
    s.conversionError = 0 := by
  simp only [Step.conversionError, h.conversion_exact, sub_self]

theorem StepBounds.operation_bound {a b : ℚ} {s : Step} (h : StepBounds a b s) :
    s.operationBound ≤ a / 10 + b := by
  rw [Step.operationBound, h.conversion_error, abs_zero, zero_add]
  exact add_le_add (div_le_div_of_nonneg_right h.addition_error (by norm_num)) h.division_error

/-- Construct success and all intermediate bounds, with no assumed finite-run premise. -/
theorem proper_run (ops : Operations α) (read : α → Option ℚ)
    (zero_decodes : read ops.zero = some 0) (a b : ℚ)
    (laws : StepLaws ops read a b) (digits : List Nat) (hd : Decimal.Digits digits) :
    ∃ c, (run ops read digits).2 = some c ∧
      read (fraction ops digits) = some c.value ∧
      0 ≤ c.value ∧ c.value ≤ 1 ∧ ∀ s ∈ c.steps, StepBounds a b s := by
  induction digits with
  | nil =>
    refine ⟨⟨0, []⟩, rfl, zero_decodes, ?_, ?_, ?_⟩
    · exact le_rfl
    · norm_num
    · simp
  | cons d ds ih =>
    have hdp := hd d List.mem_cons_self
    have hds : Decimal.Digits ds := fun e he => hd e (List.mem_cons_of_mem d he)
    obtain ⟨prior, hp, hq, hq0, hq1, hsteps⟩ := ih hds
    obtain ⟨sum, hs, hs0, hs10, hsa⟩ :=
      laws.addition d (fraction ops ds) prior.value hdp hq hq0 hq1
    obtain ⟨value, hv, hv0, hv1, hvb⟩ :=
      laws.division (ops.add (ops.convert d) (fraction ops ds)) sum hs hs0 hs10
    let step : Step := ⟨d, prior.value, (d : ℚ), sum, value⟩
    let result : Certificate := ⟨value, step :: prior.steps⟩
    have hr : (run ops read (d :: ds)).2 = some result := by
      change observeStep read d (ops.convert d)
        (ops.add (ops.convert d) (run ops read ds).1)
        (ops.divideTen (ops.add (ops.convert d) (run ops read ds).1))
        (run ops read ds).2 = some result
      rw [hp, run_value]
      simp [observeStep, laws.digit_exact d hdp, hs, hv, result, step]
    refine ⟨result, hr, ?_, hv0, hv1, ?_⟩
    · simpa only [fraction, List.foldr_cons] using hv
    · intro s hmem
      rcases List.mem_cons.mp hmem with rfl | ht
      · exact ⟨hdp, rfl, hq0, hq1, hs0, hs10, hv0, hv1, hsa, hvb⟩
      · exact hsteps s ht

theorem proper_finite_run (ops : Operations α) (read : α → Option ℚ)
    (zero_decodes : read ops.zero = some 0) (a b : ℚ)
    (laws : StepLaws ops read a b) (digits : List Nat) (hd : Decimal.Digits digits) :
    FiniteRun ops read digits := by
  obtain ⟨c, hc, _⟩ := proper_run ops read zero_decodes a b laws digits hd
  apply (run_finite_iff ops read digits).mp
  rw [hc]
  rfl

theorem proper_certificate (ops : Operations α) (read : α → Option ℚ)
    (zero_decodes : read ops.zero = some 0) (a b : ℚ)
    (laws : StepLaws ops read a b) (digits : List Nat) (hd : Decimal.Digits digits)
    (c : Certificate) (hc : (run ops read digits).2 = some c) :
    0 ≤ c.value ∧ c.value ≤ 1 ∧ ∀ s ∈ c.steps, StepBounds a b s := by
  obtain ⟨cert, hcert, _, h0, h1, hs⟩ := proper_run ops read zero_decodes a b laws digits hd
  have he : cert = c := Option.some.inj (hcert.symm.trans hc)
  subst cert
  exact ⟨h0, h1, hs⟩

theorem proper_operation_bound_length (ops : Operations α) (read : α → Option ℚ)
    (zero_decodes : read ops.zero = some 0) (a b : ℚ)
    (laws : StepLaws ops read a b) (digits : List Nat) (hd : Decimal.Digits digits)
    (c : Certificate) (hc : (run ops read digits).2 = some c) :
    operationBound c.steps ≤
      (10 / 9 : ℚ) * (a / 10 + b) * (1 - 1 / (10 : ℚ) ^ digits.length) := by
  have hs := (proper_certificate ops read zero_decodes a b laws digits hd c hc).2.2
  have h := propagate_uniform_length Step.operationBound c.steps (a / 10 + b)
    (fun s hm => (hs s hm).operation_bound)
  rw [run_length ops read digits c hc] at h
  exact h

theorem proper_operation_bound (ops : Operations α) (read : α → Option ℚ)
    (zero_decodes : read ops.zero = some 0) (a b : ℚ)
    (laws : StepLaws ops read a b) (digits : List Nat) (hd : Decimal.Digits digits)
    (c : Certificate) (hc : (run ops read digits).2 = some c) :
    operationBound c.steps ≤ (10 / 9 : ℚ) * (a / 10 + b) := by
  have hs := (proper_certificate ops read zero_decodes a b laws digits hd c hc).2.2
  have he : 0 ≤ a / 10 + b :=
    add_nonneg (div_nonneg laws.addition_nonneg (by norm_num)) laws.division_nonneg
  exact propagate_uniform Step.operationBound c.steps (a / 10 + b) he
    (fun s hm => (hs s hm).operation_bound)

theorem proper_error_length (ops : Operations α) (read : α → Option ℚ)
    (zero_decodes : read ops.zero = some 0) (a b : ℚ)
    (laws : StepLaws ops read a b) (digits : List Nat) (hd : Decimal.Digits digits)
    (c : Certificate) (hc : (run ops read digits).2 = some c) :
    |c.value - Decimal.fractionRat digits| ≤
      (10 / 9 : ℚ) * (a / 10 + b) * (1 - 1 / (10 : ℚ) ^ digits.length) :=
  (run_operation_bound ops read digits c hc).trans
    (proper_operation_bound_length ops read zero_decodes a b laws digits hd c hc)

theorem proper_error (ops : Operations α) (read : α → Option ℚ)
    (zero_decodes : read ops.zero = some 0) (a b : ℚ)
    (laws : StepLaws ops read a b) (digits : List Nat) (hd : Decimal.Digits digits)
    (c : Certificate) (hc : (run ops read digits).2 = some c) :
    |c.value - Decimal.fractionRat digits| ≤ (10 / 9 : ℚ) * (a / 10 + b) :=
  (run_operation_bound ops read digits c hc).trans
    (proper_operation_bound ops read zero_decodes a b laws digits hd c hc)

/-- The existing operation-bound checker accepts every proper list at the derived tolerance. -/
theorem proper_certify (ops : Operations α) (read : α → Option ℚ)
    (zero_decodes : read ops.zero = some 0) (a b : ℚ)
    (laws : StepLaws ops read a b) (digits : List Nat) (hd : Decimal.Digits digits) :
    certify ops read digits ((10 / 9 : ℚ) * (a / 10 + b)) = true := by
  obtain ⟨c, hc, _⟩ := proper_run ops read zero_decodes a b laws digits hd
  exact (certify_iff ops read digits _).mpr
    ⟨c, hc, proper_operation_bound ops read zero_decodes a b laws digits hd c hc⟩

end Numerals.Floating

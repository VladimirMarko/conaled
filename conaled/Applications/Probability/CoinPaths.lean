import Applications.Probability.SearchObservation
import Mathlib.Probability.ProductMeasure
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Independent coin paths and finite delivery

The ideal randomness source is Mathlib's countable product measure. Operational
execution consumes this tape one bit at a time, preserving the unused suffix
between emissions. This model makes no claim about a concrete random generator.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace Applications.Probability.CoinPaths

abbrev Tape := ℕ → Bool

/-- An ideal fair bit; the product law below specifies independence. -/
noncomputable def fairCoin : Measure Bool :=
  (2⁻¹ : ℝ≥0∞) • Measure.dirac false + (2⁻¹ : ℝ≥0∞) • Measure.dirac true

instance : IsProbabilityMeasure fairCoin := ⟨by
  simp only [fairCoin, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  exact ENNReal.inv_two_add_inv_two⟩

@[simp] theorem fairCoin_singleton (b : Bool) : fairCoin {b} = (2⁻¹ : ℝ≥0∞) := by
  cases b <;> norm_num [fairCoin]

/-- A genuine infinite independent fair-bit law, rather than assumed tail bounds. -/
noncomputable def law : Measure Tape := Measure.infinitePi (fun _ : ℕ => fairCoin)

instance : IsProbabilityMeasure law := by unfold law; infer_instance

/-- Every assignment to finitely many distinct coordinates has its independent
fair-coin probability, including noncontiguous observations. -/
theorem cylinder_mass (indices : Finset ℕ) (bits : Tape) :
    law (Set.pi indices (fun i => {bits i})) = (2⁻¹ : ℝ≥0∞) ^ indices.card := by
  rw [law, Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  simp

/-- Failure to see a true bit in the next `n` positions from cursor `s`. -/
def timeout (s n : ℕ) : Set Tape :=
  Set.pi (Finset.Ico s (s + n)) (fun _ => {false})

theorem mem_timeout (ω : Tape) (s n : ℕ) :
    ω ∈ timeout s n ↔ ∀ i, s ≤ i → i < s + n → ω i = false := by
  simp [timeout, Set.mem_pi]

theorem measurableSet_timeout (s n : ℕ) : MeasurableSet (timeout s n) := by
  exact MeasurableSet.pi (Finset.countable_toSet _) (fun _ _ => measurableSet_singleton _)

/-- The exact deadline risk counts inspected bits; at zero fuel it is one. -/
theorem timeout_mass (s n : ℕ) : law (timeout s n) = (2⁻¹ : ℝ≥0∞) ^ n := by
  rw [law, timeout, Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  simp

/-- Every tail contains a success almost surely. The quantifier is over all
cursors on one sampled tape, so it can be reused after a random finite wait. -/
theorem ae_tail_success : ∀ᵐ ω ∂law, ∀ s, ∃ i, s ≤ i ∧ ω i = true := by
  rw [ae_all_iff]
  intro s
  rw [ae_iff]
  apply le_antisymm _ zero_le
  apply ge_of_tendsto (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2⁻¹ : ℝ≥0∞)) (by norm_num))
  apply Filter.Eventually.of_forall
  intro n
  calc
    law {ω | ¬ ∃ i, s ≤ i ∧ ω i = true} ≤ law (timeout s n) := by
      apply measure_mono
      intro ω h
      rw [mem_timeout]
      intro i hi _
      cases hb : ω i with
      | false => rfl
      | true => exact False.elim (h ⟨i, hi, hb⟩)
    _ = _ := timeout_mass s n

/-- Inspect one fresh bit. A success emits unit and advances; a failure is silent. -/
def retry (ω : Tape) : Progress.Producer ℕ Unit := fun s =>
  if ω s then .inl ((), s + 1) else .inr (s + 1)

theorem measurableSteps_retry : ProbabilityProgress.MeasurableSteps retry := by
  intro s r
  have eq : {ω | retry ω s = r} =
      ({ω : Tape | ω s = true} ∩ {ω | Sum.inl ((), s + 1) = r}) ∪
      ({ω : Tape | ω s = false} ∩ {ω | Sum.inr (s + 1) = r}) := by
    ext ω
    cases h : ω s <;> simp [retry, h]
  rw [eq]
  have h : Measurable (fun ω : Tape => ω s) := measurable_pi_apply s
  exact ((h (measurableSet_singleton true)).inter
    (MeasurableSet.const _)).union
    ((h (measurableSet_singleton false)).inter
    (MeasurableSet.const _))

theorem timeout_succ (ω : Tape) (s n : ℕ) :
    ω ∈ timeout s (n + 1) ↔ ω s = false ∧ ω ∈ timeout (s + 1) n := by
  simp only [mem_timeout]
  constructor
  · intro h
    exact ⟨h s le_rfl (by omega), fun i hi hj => h i (by omega) (by omega)⟩
  · rintro ⟨hs, h⟩ i hi hj
    by_cases he : i = s
    · simpa [he] using hs
    · exact h i (by omega) (by omega)

/-- The operational fuel search times out exactly on the finite failure cylinder. -/
theorem search_none_iff (ω : Tape) (s n : ℕ) :
    Progress.search (retry ω) n s = none ↔ ω ∈ timeout s n := by
  induction n generalizing s with
  | zero => simp [Progress.search, mem_timeout]; omega
  | succ n ih =>
    rw [timeout_succ]
    cases h : ω s <;> simp [Progress.search, retry, h, ih]

theorem search_timeout_mass (s n : ℕ) :
    law {ω | Progress.search (retry ω) n s = none} = (2⁻¹ : ℝ≥0∞) ^ n := by
  simp only [search_none_iff, Set.ofPred_mem_eq]
  exact timeout_mass s n

/-- The generic operational event is exactly the concrete finite-bit cylinder. -/
theorem operational_timeout_eq (s n : ℕ) :
    ProbabilityProgress.timeout retry s n = timeout s n := by
  ext ω
  rw [ProbabilityProgress.timeout_iff_search_none, search_none_iff]

theorem measurableSet_search_timeout (s n : ℕ) :
    MeasurableSet {ω | Progress.search (retry ω) n s = none} := by
  simpa only [search_none_iff, Set.ofPred_mem_eq] using measurableSet_timeout s n

/-- Every fixed finite deadline retains strictly positive failure risk. -/
theorem search_timeout_pos (s n : ℕ) :
    0 < law {ω | Progress.search (retry ω) n s = none} := by
  rw [search_timeout_mass]
  exact bot_lt_iff_ne_bot.mpr (pow_ne_zero n (by norm_num))

/-- A later true bit supplies a finite operational derivation, not merely a
probability-one assertion about a separately defined stopping time. -/
theorem terminates_of_success (ω : Tape) (s : ℕ)
    (h : ∃ i, s ≤ i ∧ ω i = true) : Progress.Terminates (retry ω) s := by
  obtain ⟨i, hi, hit⟩ := h
  have hn : Progress.search (retry ω) (i + 1) s ≠ none := by
    intro he
    have hall := (mem_timeout ω s (i + 1)).mp ((search_none_iff ω s (i + 1)).mp he)
    have := hall i hi (by omega)
    simp [hit] at this
  cases he : Progress.search (retry ω) (i + 1) s with
  | none => exact False.elim (hn he)
  | some p => exact ⟨p.1, p.2, Progress.search_sound he⟩

theorem ae_terminates : ∀ᵐ ω ∂law, ∀ s, Progress.Terminates (retry ω) s := by
  filter_upwards [ae_tail_success] with ω h s
  exact terminates_of_success ω s (h s)

/-- Arbitrarily many emissions occur in finite work almost surely, using one
tape throughout. This does not assert a deterministic deadline. -/
theorem ae_productive : ∀ᵐ ω ∂law, ∀ s, Progress.Productive (retry ω) s := by
  filter_upwards [ae_terminates] with ω h s
  apply Progress.productive_of_next (fun _ => True) _ s trivial
  intro t _
  obtain ⟨⟨a, z⟩, k, hk⟩ := h t
  exact ⟨a, z, k, hk, trivial⟩

/-- The exceptional all-false tape really diverges; almost sure progress is
strictly weaker than progress on every tape. -/
theorem all_false_not_terminates (s : ℕ) :
    ¬ Progress.Terminates (retry (fun _ => false)) s := by
  rintro ⟨a, k, h⟩
  exact Progress.silent_no_evaluation (fun n => n + 1) h

end Applications.Probability.CoinPaths

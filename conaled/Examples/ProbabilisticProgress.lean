import Applications.Probability.CoinPaths
import Applications.Probability.HittingTimes
import Applications.Probability.Productivity
import Applications.Probability.HeavyTail

/-!
# Consumers of stochastic progress contracts

The two sequential clients retain the same tape and its return cursor. Failure
is an ordinary returned tag; zero fuel and a silent loop are different events.
-/
namespace Examples.ProbabilisticProgress
open MeasureTheory ProbabilityProgress
open scoped ENNReal
open Applications.Probability

/-- Two waits consume consecutive portions of one tape. -/
def twoEmissions (ω : CoinPaths.Tape) :=
  Progress.sequential (CoinPaths.retry ω) (CoinPaths.retry ω) Prod.snd

theorem twoEmissions_terminates :
    AlmostSureTerminates CoinPaths.law twoEmissions (fun _ => Sum.inl 0) := by
  apply sequential_ae CoinPaths.law CoinPaths.retry CoinPaths.retry (fun _ => 0) Prod.snd
    (fun _ _ => True) (fun _ _ => True)
  · filter_upwards [CoinPaths.ae_terminates] with ω h
    obtain ⟨a,k,he⟩ := h 0
    exact ⟨a,k,he,trivial⟩
  · exact Filter.Eventually.of_forall fun _ _ _ => trivial
  · filter_upwards [CoinPaths.ae_terminates] with ω h t _
    exact h t

/-- A downstream countdown is initialized by the random cursor produced by retry. -/
def retryThenCountdown (ω : CoinPaths.Tape) :=
  Progress.sequential (CoinPaths.retry ω) HeavyTail.countdown Prod.snd

theorem retryThenCountdown_terminates :
    AlmostSureTerminates CoinPaths.law retryThenCountdown (fun _ => Sum.inl 0) := by
  apply sequential_ae CoinPaths.law CoinPaths.retry (fun _ => HeavyTail.countdown)
    (fun _ => 0) Prod.snd (fun _ _ => True) (fun _ _ => True)
  · filter_upwards [CoinPaths.ae_terminates] with ω h
    obtain ⟨a,k,he⟩ := h 0
    exact ⟨a,k,he,trivial⟩
  · exact Filter.Eventually.of_forall fun _ _ _ => trivial
  · exact Filter.Eventually.of_forall fun _ t _ => ⟨(),t+1,HeavyTail.countdown_evaluates t⟩

/-- On alternating failures and successes, two emissions consume four bits. -/
theorem alternating_two_emissions :
    Progress.Evaluates (twoEmissions (fun n => n % 2 == 1)) (.inl 0) ((),4) 4 := by
  have first : Progress.Evaluates (CoinPaths.retry (fun n => n % 2 == 1)) 0 ((),2) 2 :=
    .next rfl (.done rfl)
  have second : Progress.Evaluates (CoinPaths.retry (fun n => n % 2 == 1)) 2 ((),4) 2 :=
    .next rfl (.done rfl)
  exact Progress.sequential_evaluates (start := Prod.snd) first second

theorem retry_productive :
    AlmostSureProductive CoinPaths.law CoinPaths.retry (fun _ => 0) := by
  apply (almostSureProductive_iff _ _ _).mpr
  filter_upwards [CoinPaths.ae_productive] with ω h
  exact h 0

theorem retry_prefix_events_measurable (n budget : Nat) :
    MeasurableSet (prefixDelivered CoinPaths.retry 0 n budget) :=
  measurable_prefixDelivered _ CoinPaths.measurableSteps_retry _ _ _

theorem retry_deadline_risk (budget : Nat) :
    CoinPaths.law (timeout CoinPaths.retry 0 budget) = (2⁻¹ : ℝ≥0∞)^budget := by
  rw [CoinPaths.operational_timeout_eq, CoinPaths.timeout_mass]

theorem retry_result_mass : results CoinPaths.law CoinPaths.retry 0 Set.univ = 1 := by
  rw [results_mass _ _ CoinPaths.measurableSteps_retry]
  apply (ae_iff_prob_eq_one (measurableSet_setOfPred.mp
    (measurable_termination _ CoinPaths.measurableSteps_retry 0))).mp
  filter_upwards [CoinPaths.ae_terminates] with ω h
  exact h 0

/-- Finite expectation does not follow from almost-sure operational termination. -/
theorem countdown_almostSureTerminates :
    AlmostSureTerminates HeavyTail.sampleLaw (fun _ => HeavyTail.countdown)
      (fun n => 2^n) :=
  Filter.Eventually.of_forall HeavyTail.all_samples_terminate

example : (∫⁻ n, ((2^n+1 : Nat) : ℝ≥0∞) ∂HeavyTail.sampleLaw) = ∞ :=
  HeavyTail.lintegral_cost_eq_top

/-- In this fixture false is an explicit failure tag, true would be success. -/
def explicitFailure : Execution Unit Unit Bool := fun _ _ => .inl false

private theorem measurable_failure : MeasurableSteps explicitFailure :=
  fun _ r => MeasurableSet.const (Sum.inl false = r)

theorem failure_retains_unit_mass :
    results (Measure.dirac ()) explicitFailure () {Sum.inr (false,1)} = 1 := by
  rw [results_some _ _ measurable_failure]
  have he : {ω | Progress.Evaluates (explicitFailure ω) () false 1} = Set.univ := by
    ext ω
    exact ⟨fun _ => trivial, fun _ => Progress.Evaluates.done rfl⟩
  rw [he, measure_univ]

theorem failure_zero_deadline : timeout explicitFailure () 0 = Set.univ := by
  ext ω
  simp only [timeout, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  rintro ⟨a,k,hk,he⟩
  have hk0 : k = 0 := by omega
  subst k; cases he

theorem failure_one_deadline : timeout explicitFailure () 1 = ∅ := by
  ext ω
  simp only [timeout, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
  exact ⟨false,1,le_rfl,.done rfl⟩

/-- The false branch never returns; its probability is not normalized away. -/
def partialReturn : Execution Bool Unit Unit := fun b _ => if b then .inl () else .inr ()

private theorem measurable_partial : MeasurableSteps partialReturn :=
  fun _ _ => Set.Countable.measurableSet (Set.to_countable _)

theorem partial_termination : termination partialReturn () = {true} := by
  ext b
  cases b with
  | false =>
    simp only [termination, Progress.Terminates, Set.mem_ofPred_eq,
      Set.mem_singleton_iff, Bool.false_eq_true, iff_false, not_exists]
    intro a k he
    exact Progress.silent_no_evaluation id he
  | true =>
    simp only [Set.mem_singleton_iff, iff_true]
    exact ⟨(),1,.done rfl⟩

theorem partial_result_mass : results CoinPaths.fairCoin partialReturn () Set.univ = (2⁻¹ : ℝ≥0∞) := by
  rw [results_mass _ _ measurable_partial, partial_termination, CoinPaths.fairCoin_singleton]

theorem partial_divergence_mass : CoinPaths.fairCoin (termination partialReturn ())ᶜ = (2⁻¹ : ℝ≥0∞) := by
  rw [divergence_mass _ _ measurable_partial, partial_result_mass]
  norm_num

/-- A silent loop has no first prefix, so it is not an indefinitely productive source. -/
theorem all_false_not_productive : ¬ Progress.Productive (CoinPaths.retry (fun _ => false)) 0 := by
  intro h
  obtain ⟨xs,t,k,hlen,hd⟩ := h 1
  cases hd with
  | nil => simp at hlen
  | cons he _ => exact CoinPaths.all_false_not_terminates 0 ⟨_,_,he⟩

/-- Tail composition preserves the random intermediate cursor instead of
multiplying marginal success probabilities. -/
theorem retryThenCountdown_tail (k l : Nat) :
    CoinPaths.law (timeout retryThenCountdown (.inl 0) (k+l)) ≤
      (2⁻¹ : ℝ≥0∞)^k + CoinPaths.law
        (downstreamTimeout CoinPaths.retry (fun _ => HeavyTail.countdown) 0 Prod.snd k l) := by
  have h := sequential_tail_le CoinPaths.law CoinPaths.retry
    (fun _ => HeavyTail.countdown) 0 Prod.snd k l
  rw [CoinPaths.operational_timeout_eq, CoinPaths.timeout_mass] at h
  exact h

/-- The same geometric tail is the distribution of the operational hitting time. -/
theorem retry_hitting_tail (budget : Nat) :
    CoinPaths.law {ω | ¬ hittingTime CoinPaths.retry 0 ω ≤ (budget : WithTop Nat)} =
      (2⁻¹ : ℝ≥0∞)^budget := by
  have eq : {ω | ¬ hittingTime CoinPaths.retry 0 ω ≤ (budget : WithTop Nat)} =
      timeout CoinPaths.retry 0 budget := by
    ext ω
    simp only [Set.mem_ofPred_eq, hittingTime_le_iff, not_not]
  rw [eq]
  exact retry_deadline_risk budget

/-- Observing every rejected update still emits the current state. -/
theorem reject_only_updates_productive (s : Nat) :
    Progress.Productive (Progress.guarded (fun x : Nat => (x,x))) s :=
  Progress.guarded_productive _ _

/-- Dropping all rejected observations changes the progress obligation. -/
theorem accepted_only_not_productive (s : Nat) :
    ¬ Progress.Productive
      (Progress.filterProducer (fun _ : Nat => false) (fun x : Nat => (x,x))) s :=
  Progress.filter_no_match _ _ (fun _ => rfl) s

end Examples.ProbabilisticProgress

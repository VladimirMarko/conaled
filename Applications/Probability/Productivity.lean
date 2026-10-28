import Applications.Probability.Execution

/-!
# Almost-sure finite observations

Finite output traces and their deadline events are measurable for countable
state and output spaces. Every requested length may have its own null exception
set: their countable union is still null. On the remaining environments all
finite observations coexist, and determinism makes their output prefixes agree.
-/
namespace ProbabilityProgress
open MeasureTheory
variable {Ω S A : Type} [MeasurableSpace Ω]

private theorem delivers_nil (step : Progress.Producer S A) (s t : S) (k : Nat) :
    Progress.Delivers step s [] t k ↔ t = s ∧ k = 0 := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact .nil _

private theorem delivers_cons (step : Progress.Producer S A) (s t : S)
    (a : A) (xs : List A) (k : Nat) :
    Progress.Delivers step s (a :: xs) t k ↔
      ∃ z i j, k = i + j ∧ Progress.Evaluates step s (a, z) i ∧
        Progress.Delivers step z xs t j := by
  constructor
  · intro h
    cases h with
    | cons first rest => exact ⟨_, _, _, rfl, first, rest⟩
  · rintro ⟨z, i, j, rfl, first, rest⟩
    exact .cons first rest

/-- The event records exact outputs, final state, and atomic transition count. -/
theorem measurable_delivers [Countable S]
    (step : Ω → Progress.Producer S A) (hm : MeasurableSteps step)
    (s : S) (xs : List A) (t : S) (k : Nat) :
    MeasurableSet {ω | Progress.Delivers (step ω) s xs t k} := by
  induction xs generalizing s t k with
  | nil => simp only [delivers_nil]; exact MeasurableSet.const _
  | cons a xs ih =>
    simp only [delivers_cons, Set.ofPred_exists]
    exact MeasurableSet.iUnion fun z => MeasurableSet.iUnion fun i =>
      MeasurableSet.iUnion fun j => (MeasurableSet.const (k = i + j)).inter
        ((measurable_evaluates step hm s (a,z) i).inter (ih z t j))

/-- Delivery of the requested output count by a finite transition deadline. -/
def prefixDelivered (step : Ω → Progress.Producer S A) (s : S)
    (length deadline : Nat) : Set Ω :=
  {ω | ∃ xs t k, xs.length = length ∧ k ≤ deadline ∧
    Progress.Delivers (step ω) s xs t k}

theorem measurable_prefixDelivered [Countable S] [Countable A]
    (step : Ω → Progress.Producer S A) (hm : MeasurableSteps step)
    (s : S) (length deadline : Nat) :
    MeasurableSet (prefixDelivered step s length deadline) := by
  simp only [prefixDelivered, Set.ofPred_exists]
  exact MeasurableSet.iUnion fun xs => MeasurableSet.iUnion fun t =>
    MeasurableSet.iUnion fun k => (MeasurableSet.const (xs.length = length)).inter
      ((MeasurableSet.const (k ≤ deadline)).inter (measurable_delivers step hm s xs t k))

theorem measurable_prefixTimeout [Countable S] [Countable A]
    (step : Ω → Progress.Producer S A) (hm : MeasurableSteps step)
    (s : S) (length deadline : Nat) :
    MeasurableSet (prefixDelivered step s length deadline)ᶜ :=
  (measurable_prefixDelivered step hm s length deadline).compl

/-- All lengths refer to the same environment and initial state. -/
def AlmostSureProductive (μ : Measure Ω) (step : Ω → Progress.Producer S A)
    (start : Ω → S) : Prop :=
  ∀ n : Nat, ∀ᵐ ω ∂μ, ∃ xs t k, xs.length = n ∧
    Progress.Delivers (step ω) (start ω) xs t k

/-- Countably many almost-sure finite-delivery statements hold jointly almost surely. -/
theorem almostSureProductive_iff (μ : Measure Ω)
    (step : Ω → Progress.Producer S A) (start : Ω → S) :
    AlmostSureProductive μ step start ↔
      ∀ᵐ ω ∂μ, Progress.Productive (step ω) (start ω) := by
  exact ae_all_iff.symm

/-- One conull set admits coherent prefixes of every length. This does not claim
that generating the infinite stream terminates. -/
theorem ae_coherent_prefixes (μ : Measure Ω)
    (step : Ω → Progress.Producer S A) (start : Ω → S)
    (h : AlmostSureProductive μ step start) :
    ∀ᵐ ω ∂μ, ∃ prefixes : Nat → List A,
      (∀ n, (prefixes n).length = n ∧ ∃ t k,
        Progress.Delivers (step ω) (start ω) (prefixes n) t k) ∧
      ∀ m n, (prefixes m).take n = (prefixes n).take m := by
  filter_upwards [(almostSureProductive_iff μ step start).mp h] with ω hω
  choose xs t k hlen hdelivery using hω
  refine ⟨xs, fun n => ⟨hlen n, t n, k n, hdelivery n⟩, ?_⟩
  intro m n
  simpa only [hlen] using (hdelivery m).coherent (hdelivery n)

/-- Guarded producers specialize the almost-sure contract under any environment law. -/
theorem guarded_almostSureProductive (μ : Measure Ω)
    (c : Ω → Progress.Coalgebra S A) (start : Ω → S) :
    AlmostSureProductive μ (fun ω => Progress.guarded (c ω)) start := by
  apply (almostSureProductive_iff _ _ _).mpr
  exact Filter.Eventually.of_forall fun ω => Progress.guarded_productive (c ω) (start ω)

/-- Inserting one silent transition per output preserves almost-sure productivity. -/
theorem paused_almostSureProductive (μ : Measure Ω)
    (c : Ω → Progress.Coalgebra S A) (start : Ω → S) :
    AlmostSureProductive μ (fun ω => Progress.paused (c ω))
      (fun ω => (false, start ω)) := by
  intro n
  apply Filter.Eventually.of_forall
  intro ω
  exact ⟨Progress.unfold (c ω) (start ω) n,
    (false, Progress.advance (c ω) (start ω) n), 2 * n,
    Progress.unfold_length _ _ _, Progress.paused_delivery _ _ _⟩

end ProbabilityProgress

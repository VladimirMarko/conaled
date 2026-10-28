import Applications.Progress.Streams
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Random-environment executions

A single probability space supplies the entire execution, including shared
randomness. Each environment determines an ordinary atomic machine. Countable
states and outputs and measurable step fibers imply measurable finite traces.
No independence, scheduler, fuel bound, or termination certificate is assumed.
-/
namespace ProbabilityProgress
open MeasureTheory
open scoped ENNReal
variable {Ω S T A B : Type} [MeasurableSpace Ω]

/-- Random choices are resolved by an environment; state can retain a tape cursor. -/
abbrev Execution (Ω S A : Type) := Ω → Progress.Machine S A

/-- Measurability is local to one transition at a fixed state. -/
def MeasurableSteps (step : Execution Ω S A) : Prop :=
  ∀ s r, MeasurableSet {ω | step ω s = r}

private theorem evaluates_succ (step : Progress.Machine S A) (s : S) (a : A) (n : Nat) :
    Progress.Evaluates step s a (n+1) ↔
      (n = 0 ∧ step s = .inl a) ∨
      ∃ t, step s = .inr t ∧ Progress.Evaluates step t a n := by
  constructor
  · intro h
    cases h with
    | done h => exact Or.inl ⟨rfl, h⟩
    | next h j => exact Or.inr ⟨_, h, j⟩
  · rintro (⟨rfl, h⟩ | ⟨t, h, j⟩)
    · exact .done h
    · exact .next h j

/-- Finite evaluation events are measurable because finite derivations have
countably many possible intermediate states. -/
theorem measurable_evaluates [Countable S] (step : Execution Ω S A)
    (hm : MeasurableSteps step) (s : S) (a : A) (n : Nat) :
    MeasurableSet {ω | Progress.Evaluates (step ω) s a n} := by
  induction n generalizing s with
  | zero =>
    have : {ω | Progress.Evaluates (step ω) s a 0} = ∅ := by
      ext ω; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h; cases h
    rw [this]; exact MeasurableSet.empty
  | succ n ih =>
    have eq : {ω | Progress.Evaluates (step ω) s a (n+1)} =
        ({ω | n = 0} ∩ {ω | step ω s = .inl a}) ∪
        ⋃ t, ({ω | step ω s = .inr t} ∩
          {ω | Progress.Evaluates (step ω) t a n}) := by
      ext ω
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq,
        Set.mem_iUnion, evaluates_succ]
    rw [eq]
    exact ((MeasurableSet.const _).inter (hm _ _)).union
      (MeasurableSet.iUnion fun t => (hm s (.inr t)).inter (ih t))

/-- Termination is existential finite operational evaluation, independent of search. -/
def termination (step : Execution Ω S A) (s : S) : Set Ω :=
  {ω | Progress.Terminates (step ω) s}

theorem measurable_termination [Countable S] [Countable A]
    (step : Execution Ω S A) (hm : MeasurableSteps step) (s : S) :
    MeasurableSet (termination step s) := by
  simpa only [termination, Progress.Terminates, Set.ofPred_exists] using
    (MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun n =>
      measurable_evaluates step hm s a n)

/-- A timeout is absence of a return by the supplied deadline, not a divergent
path. Explicit failures can be represented in `A` by a sum type. -/
def timeout (step : Execution Ω S A) (s : S) (deadline : Nat) : Set Ω :=
  {ω | ¬ ∃ a n, n ≤ deadline ∧ Progress.Evaluates (step ω) s a n}

theorem measurable_timeout [Countable S] [Countable A]
    (step : Execution Ω S A) (hm : MeasurableSteps step) (s : S) (d : Nat) :
    MeasurableSet (timeout step s d) := by
  convert (MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun n =>
      (MeasurableSet.const (n ≤ d)).inter (measurable_evaluates step hm s a n)).compl using 1
  ext ω; simp [timeout]

/-- Infinite nontermination is precisely timeout at every finite deadline. -/
theorem divergence_eq_all_timeouts (step : Execution Ω S A) (s : S) :
    (termination step s)ᶜ = ⋂ d, timeout step s d := by
  ext ω
  simp only [termination, Progress.Terminates, timeout, Set.mem_compl_iff,
    Set.mem_ofPred_eq, Set.mem_iInter]
  constructor
  · intro h d ⟨a,n,_,hn⟩; exact h ⟨a,n,hn⟩
  · intro h ⟨a,n,hn⟩; exact h n ⟨a,n,le_rfl,hn⟩

/-- Almost-sure progress permits exceptional divergent paths. -/
def AlmostSureTerminates (μ : Measure Ω) (step : Execution Ω S A)
    (start : Ω → S) : Prop := ∀ᵐ ω ∂μ, Progress.Terminates (step ω) (start ω)

/-- Sequential progress retains intermediate values and downstream domains on
one joint environment. The downstream premise may hold only almost everywhere;
it must cover the value actually produced by stage one. -/
theorem sequential_ae (μ : Measure Ω) (f : Execution Ω S A) (g : Execution Ω T B)
    (s : Ω → S) (start : A → T) (mid : Ω → A → Prop) (dom : Ω → T → Prop)
    (first : ∀ᵐ ω ∂μ, ∃ a k, Progress.Evaluates (f ω) (s ω) a k ∧ mid ω a)
    (feeds : ∀ᵐ ω ∂μ, ∀ a, mid ω a → dom ω (start a))
    (second : ∀ᵐ ω ∂μ, ∀ t, dom ω t → Progress.Terminates (g ω) t) :
    AlmostSureTerminates μ (fun ω => Progress.sequential (f ω) (g ω) start)
      (fun ω => .inl (s ω)) := by
  filter_upwards [first, feeds, second] with ω hf hfeed hg
  obtain ⟨a,k,h,hm⟩ := hf
  obtain ⟨b,l,j⟩ := hg _ (hfeed a hm)
  exact ⟨b,k+l,Progress.sequential_evaluates h j⟩

/-- Deterministic totality embeds by constant machines under any environment law. -/
theorem deterministic_terminates (μ : Measure Ω) (step : Progress.Machine S A)
    (s : S) (h : Progress.Terminates step s) :
    AlmostSureTerminates μ (fun _ => step) (fun _ => s) :=
  Filter.Eventually.of_forall (fun _ => h)

/-- A random initial state has measurable fibers in the selected countable fragment. -/
def MeasurableStart (start : Ω → S) : Prop :=
  ∀ s, MeasurableSet {ω | start ω = s}

theorem measurable_evaluates_start [Countable S] (step : Execution Ω S A)
    (hm : MeasurableSteps step) (start : Ω → S) (hs : MeasurableStart start)
    (a : A) (k : Nat) :
    MeasurableSet {ω | Progress.Evaluates (step ω) (start ω) a k} := by
  have eq : {ω | Progress.Evaluates (step ω) (start ω) a k} =
      ⋃ s, ({ω | start ω = s} ∩ {ω | Progress.Evaluates (step ω) s a k}) := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨start ω,rfl,h⟩, fun ⟨s,hs,h⟩ => hs ▸ h⟩
  rw [eq]
  exact MeasurableSet.iUnion fun s => (hs s).inter (measurable_evaluates step hm s a k)

/-- The Dirac interpretation recovers exactly the existing deterministic contract. -/
theorem deterministic_dirac_iff (step : Progress.Machine S A) (s : S) :
    AlmostSureTerminates (Measure.dirac ()) (fun _ : Unit => step) (fun _ => s) ↔
      Progress.Terminates step s := by
  simp [AlmostSureTerminates, ae_dirac_eq]

/-- Failure of the downstream deadline after an actual first-stage return.
The intermediate value remains coupled to its original environment. -/
def downstreamTimeout (f : Execution Ω S A) (g : Execution Ω T B)
    (s : S) (start : A → T) (firstBudget secondBudget : Nat) : Set Ω :=
  {ω | ∃ a k, k ≤ firstBudget ∧ Progress.Evaluates (f ω) s a k ∧
    ω ∈ timeout g (start a) secondBudget}

/-- Sequential tail accounting needs a joint law but no independence assumption. -/
theorem sequential_tail_le (μ : Measure Ω) (f : Execution Ω S A)
    (g : Execution Ω T B) (s : S) (start : A → T) (k l : Nat) :
    μ (timeout (fun ω => Progress.sequential (f ω) (g ω) start) (.inl s) (k+l)) ≤
      μ (timeout f s k) + μ (downstreamTimeout f g s start k l) := by
  classical
  calc
    _ ≤ μ (timeout f s k ∪ downstreamTimeout f g s start k l) := by
      apply measure_mono
      intro ω h
      by_cases hf : ω ∈ timeout f s k
      · exact Or.inl hf
      · right
        simp only [timeout, Set.mem_ofPred_eq, not_not] at hf
        obtain ⟨a,i,hi,he⟩ := hf
        refine ⟨a,i,hi,he,?_⟩
        intro hg
        obtain ⟨b,j,hj,je⟩ := hg
        exact h ⟨b,i+j,Nat.add_le_add hi hj,Progress.sequential_evaluates he je⟩
    _ ≤ _ := measure_union_le _ _

private theorem measurable_fiber_map {X Y : Type} [Countable X]
    (f : Ω → X) (hf : ∀ x, MeasurableSet {ω | f ω = x}) (g : X → Y) (y : Y) :
    MeasurableSet {ω | g (f ω) = y} := by
  have eq : {ω | g (f ω) = y} = ⋃ x, ({ω | f ω = x} ∩ {ω | g x = y}) := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨f ω,rfl,h⟩, fun ⟨x,hx,hy⟩ => hx ▸ hy⟩
  rw [eq]
  exact MeasurableSet.iUnion fun x => (hf x).inter (MeasurableSet.const _)

/-- Sequential composition stays within the measurable countable fragment. -/
theorem measurableSteps_sequential [Countable S] [Countable T] [Countable A] [Countable B]
    (f : Execution Ω S A) (g : Execution Ω T B) (start : A → T)
    (hf : MeasurableSteps f) (hg : MeasurableSteps g) :
    MeasurableSteps (fun ω => Progress.sequential (f ω) (g ω) start) := by
  intro s r
  cases s with
  | inl s =>
    exact measurable_fiber_map (fun ω => f ω s) (hf s)
      (fun x => match x with
        | .inl a => .inr (.inr (start a))
        | .inr t => .inr (.inl t)) r
  | inr t =>
    exact measurable_fiber_map (fun ω => g ω t) (hg t)
      (fun x => match x with
        | .inl b => .inl b
        | .inr t' => .inr (.inr t')) r

theorem measurable_downstreamTimeout [Countable S] [Countable T]
    [Countable A] [Countable B] (f : Execution Ω S A) (g : Execution Ω T B)
    (hf : MeasurableSteps f) (hg : MeasurableSteps g)
    (s : S) (start : A → T) (k l : Nat) :
    MeasurableSet (downstreamTimeout f g s start k l) := by
  simp only [downstreamTimeout, Set.ofPred_exists]
  exact MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun i =>
    (MeasurableSet.const (i ≤ k)).inter
      ((measurable_evaluates f hf s a i).inter (measurable_timeout g hg (start a) l))

end ProbabilityProgress

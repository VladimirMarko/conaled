import Applications.Probability.Results
import Applications.Probability.Productivity

/-!
# Operational return times

A return time records the unique finite evaluation cost, or infinity when no
finite evaluation exists. Its finite sublevel events are exactly successful
deadlines; the definition does not assign a finite cost to divergent paths.
-/
namespace ProbabilityProgress
open MeasureTheory
variable {Ω S A : Type} [MeasurableSpace Ω]

/-- Number of atomic transitions to the return, with infinity for divergence. -/
noncomputable def hittingTime (step : Execution Ω S A) (s : S) (ω : Ω) : WithTop Nat :=
  match outcome step s ω with
  | .inl () => ⊤
  | .inr (_, k) => k

/-- Finite times come from actual evaluations, including explicit failure returns. -/
theorem hittingTime_eq_nat_iff (step : Execution Ω S A) (s : S) (ω : Ω) (k : Nat) :
    hittingTime step s ω = (k : WithTop Nat) ↔
      ∃ a, Progress.Evaluates (step ω) s a k := by
  cases ho : outcome step s ω with
  | inl u =>
    cases u
    simp [hittingTime, ho]
    intro a he
    have := (outcome_some_iff step s ω a k).mpr he
    simp [ho] at this
  | inr r =>
    rcases r with ⟨a,j⟩
    have he := (outcome_some_iff step s ω a j).mp ho
    simp only [hittingTime, ho]
    norm_cast
    constructor
    · rintro rfl; exact ⟨a,he⟩
    · rintro ⟨b,hb⟩; exact (he.unique hb).2

theorem hittingTime_eq_top_iff (step : Execution Ω S A) (s : S) (ω : Ω) :
    hittingTime step s ω = ⊤ ↔ ω ∉ termination step s := by
  rw [← outcome_none_iff step s ω]
  cases h : outcome step s ω with
  | inl u => cases u; simp [hittingTime, h]
  | inr r => simp [hittingTime, h]

/-- A finite deadline succeeds precisely when it bounds the operational return time. -/
theorem hittingTime_le_iff (step : Execution Ω S A) (s : S) (ω : Ω) (budget : Nat) :
    hittingTime step s ω ≤ (budget : WithTop Nat) ↔
      ω ∉ timeout step s budget := by
  classical
  simp only [timeout, Set.mem_ofPred_eq, not_not]
  cases ho : outcome step s ω with
  | inl u =>
    cases u
    simp [hittingTime, ho]
    intro a k _ he
    have := (outcome_some_iff step s ω a k).mpr he
    simp [ho] at this
  | inr r =>
    rcases r with ⟨a,j⟩
    have he := (outcome_some_iff step s ω a j).mp ho
    simp only [hittingTime, ho]
    norm_cast
    constructor
    · intro hj; exact ⟨a,j,hj,he⟩
    · rintro ⟨b,k,hk,hb⟩
      rwa [(he.unique hb).2]

theorem hittingTime_sublevel (step : Execution Ω S A) (s : S) (budget : Nat) :
    {ω | hittingTime step s ω ≤ (budget : WithTop Nat)} = (timeout step s budget)ᶜ := by
  ext ω
  exact hittingTime_le_iff step s ω budget

theorem measurable_hittingTime_sublevel [Countable S] [Countable A]
    (step : Execution Ω S A) (hm : MeasurableSteps step) (s : S) (budget : Nat) :
    MeasurableSet {ω | hittingTime step s ω ≤ (budget : WithTop Nat)} := by
  rw [hittingTime_sublevel]
  exact (measurable_timeout step hm s budget).compl

end ProbabilityProgress

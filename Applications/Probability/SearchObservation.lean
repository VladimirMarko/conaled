import Applications.Probability.Execution

/-!
# Finite search observes operational deadlines

A fuel search reports exactly the evaluations within its bound. This connects
executable observations to the probability events defined from derivations.
-/
namespace ProbabilityProgress

/-- Returned cost never exceeds supplied fuel. -/
theorem search_cost_le {S A : Type} {step : Progress.Machine S A}
    {fuel s a k} (h : Progress.search step fuel s = some (a, k)) : k ≤ fuel := by
  induction fuel generalizing s a k with
  | zero => simp [Progress.search] at h
  | succ fuel ih =>
    simp only [Progress.search] at h
    split at h
    next e => cases h; omega
    next t e =>
      cases hs : Progress.search step fuel t with
      | none => simp [hs] at h
      | some p =>
        rcases p with ⟨v,n⟩
        simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        exact Nat.succ_le_succ (ih hs)

/-- Timeout observes finite absence of a derivation, not infinite divergence. -/
theorem timeout_iff_search_none {Ω S A : Type} [MeasurableSpace Ω]
    (step : Execution Ω S A) (ω : Ω) (s : S) (n : Nat) :
    ω ∈ timeout step s n ↔ Progress.search (step ω) n s = none := by
  constructor
  · intro h
    cases he : Progress.search (step ω) n s with
    | none => rfl
    | some p =>
      exact False.elim (h ⟨p.1,p.2,search_cost_le he,Progress.search_sound he⟩)
  · intro h ⟨a,k,hk,he⟩
    have := Progress.search_complete he hk
    rw [h] at this
    cases this

end ProbabilityProgress

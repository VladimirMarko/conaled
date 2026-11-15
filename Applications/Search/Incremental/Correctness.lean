import Applications.Search.Incremental.Termination
import Applications.Search.Incremental.Bellman

/-! Goal correctness follows from a full-drain continuation. Early stopping
retains residual inconsistent vertices; it does not assert global optimality. -/
set_option autoImplicit false
set_option warningAsError true
namespace Search.Incremental
variable {n : Nat}

theorem stopped_frozen (w : Graph n) (start goal : Fin n) (h : Fin n → ℚ)
    (s : State n) (hs : Valid w start s) (hn : ¬ active goal h s) : Frozen w start h s.g goal := by
  have hc : s.g goal = s.rhs goal := by
    by_contra he
    exact hn (Or.inr he)
  refine ⟨by simpa [hs.1] using hc, ?_⟩
  intro v hv
  have hvm : v ∈ s.queue := (hs.2.2.1 v).mpr (by simpa [hs.1] using hv)
  have hk : labelKey h s.g s.rhs goal ≤ topKey h s :=
    le_of_not_gt (fun ht => hn (Or.inl ht))
  cases hu : select h s with
  | none => have he := (select_none h s).mp hu; simp [he] at hvm
  | some u =>
    have hm := (select_spec h s u hu).2 v hvm
    have hp : labelKey h s.g s.rhs goal ≤ labelKey h s.g s.rhs u := by
      simpa [topKey, hu] using hk
    simpa only [key, hs.1] using hp.trans hm

theorem frozen_correct (w : Graph n) (hw : Positive w) (start : Fin n)
    (h : Fin n → ℚ) (hh : ∀ u v, (h u : Cost) ≤ w u v + (h v : Cost))
    (s : State n) (hs : Valid w start s) (v : Fin n) (hv : Frozen w start h s.g v) :
    DistanceResult w start v (s.g v) := by
  obtain ⟨out, he⟩ := drain_total w hw start h hh s hs
  obtain ⟨us, ht, ho, hn⟩ := runWith_stopped w hw start h (fun s => select h s ≠ none) (2*n) s out hs he
  have hq : out.queue = [] := (select_none h out).mp (not_ne_iff.mp hn)
  have hb : Bellman w start out.g := by
    intro u
    have hc : out.g u = out.rhs u := by
      by_contra he
      have hm := (ho.2.2.1 u).mpr he
      simp [hq] at hm
    simpa only [ho.1] using hc
  have hc := bellman_correct hw ho.2.2.2 hb v
  have heq := (ht.frozen w hw start h hh v hv).2.1
  simpa only [heq] using hc

theorem run_correct (w : Graph n) (hw : Positive w) (start goal : Fin n)
    (h : Fin n → ℚ) (hh : ∀ u v, (h u : Cost) ≤ w u v + (h v : Cost))
    (fuel : Nat) (s out : State n) (hs : Valid w start s)
    (he : run w start goal h fuel s = .stopped out) :
    Valid w start out ∧ DistanceResult w start goal (out.g goal) := by
  obtain ⟨_, _, ho, hn⟩ := runWith_stopped w hw start h (active goal h) fuel s out hs he
  exact ⟨ho, frozen_correct w hw start h hh out ho goal (stopped_frozen w start goal h out ho hn)⟩

def Outcome.getStopped (out : Outcome n) (he : ∃ s, out = .stopped s) : State n :=
  match out with
  | .stopped s => s
  | .exhausted _ => False.elim (by obtain ⟨s, hs⟩ := he; cases hs)

theorem Outcome.getStopped_eq (out : Outcome n) (he : ∃ s, out = .stopped s) :
    out = .stopped (out.getStopped he) := by
  cases out with
  | stopped => rfl
  | exhausted => obtain ⟨s, hs⟩ := he; cases hs

/-- The fuel is justified internally by the finite legal-trace theorem. -/
def complete (w : Graph n) (hw : Positive w) (start goal : Fin n)
    (h : Fin n → ℚ) (hh : ∀ u v, (h u : Cost) ≤ w u v + (h v : Cost))
    (s : State n) (hs : Valid w start s) : State n :=
  (run w start goal h (2*n) s).getStopped (run_total w hw start goal h hh s hs)

theorem complete_run (w : Graph n) (hw : Positive w) (start goal : Fin n)
    (h : Fin n → ℚ) (hh : ∀ u v, (h u : Cost) ≤ w u v + (h v : Cost))
    (s : State n) (hs : Valid w start s) :
    run w start goal h (2*n) s = .stopped (complete w hw start goal h hh s hs) :=
  Outcome.getStopped_eq _ _

theorem complete_correct (w : Graph n) (hw : Positive w) (start goal : Fin n)
    (h : Fin n → ℚ) (hh : ∀ u v, (h u : Cost) ≤ w u v + (h v : Cost))
    (s : State n) (hs : Valid w start s) :
    Valid w start (complete w hw start goal h hh s hs) ∧
      DistanceResult w start goal ((complete w hw start goal h hh s hs).g goal) :=
  run_correct w hw start goal h hh (2*n) s _ hs (complete_run w hw start goal h hh s hs)

end Search.Incremental

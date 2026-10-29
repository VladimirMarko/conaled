import Applications.Durability.ResourceEvents
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

namespace Durability.Diagnostic

abbrev Edge (N : Nat) := Fin N × Fin N
abbrev History (N : Nat) := List (Record (Edge N))

/-- Independent set-of-edges and nonempty-path specification. Repeated edges
with distinct request identities remain distinct records in the history. -/
def Edges (h : History N) (u v : Fin N) : Prop := (u,v) ∈ h.map Record.payload
instance (h : History N) (u v : Fin N) : Decidable (Edges h u v) := by unfold Edges; infer_instance
def Reach (h : History N) := Relation.TransGen (Edges h)
def Acyclic (h : History N) : Prop := ∀ v, ¬ Reach h v v

/-- Finite exhaustive recomputation. Intersect all transitive relations that
contain the edge relation. This deliberately favors a short correctness
argument over an efficient closure algorithm. -/
def closed (s : Finset (Edge N)) : Prop :=
  ∀ u v w : Fin N, (u,v) ∈ s → (v,w) ∈ s → (u,w) ∈ s
def contains (h : History N) (s : Finset (Edge N)) : Prop :=
  ∀ u v : Fin N, Edges h u v → (u,v) ∈ s
instance (s : Finset (Edge N)) : Decidable (closed s) := by unfold closed; infer_instance
instance (h : History N) (s : Finset (Edge N)) : Decidable (contains h s) := by
  unfold contains Edges; infer_instance
def closure (h : History N) : Finset (Edge N) :=
  Finset.univ.filter fun p => ∀ s : Finset (Edge N), contains h s → closed s → p ∈ s

theorem closure_correct (h : History N) (u v : Fin N) :
    (u,v) ∈ closure h ↔ Reach h u v := by
  simp only [closure, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro all
    classical
    let s : Finset (Edge N) := Finset.univ.filter fun p => Reach h p.1 p.2
    have hc : contains h s := by
      intro a b edge
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.TransGen.single edge⟩
    have ht : closed s := by
      intro a b c ab bc
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp ab).2.trans (Finset.mem_filter.mp bc).2⟩
    exact (Finset.mem_filter.mp (all s hc ht)).2
  · intro path s hc ht
    induction path with
    | single edge => exact hc _ _ edge
    | tail path edge ih => exact ht _ _ _ ih (hc _ _ edge)

def acyclic (h : History N) : Bool := decide (∀ v : Fin N, (v,v) ∉ closure h)
theorem acyclic_correct (h : History N) : acyclic h = true ↔ Acyclic h := by
  simp [acyclic, Acyclic, closure_correct]

/-- Admission inspects the whole proposed authoritative snapshot. It never
authorizes a new request from a delayed diagnostic. -/
def allows (h : History N) (e : Record (Edge N)) : Bool := acyclic (h ++ [e])
theorem admit_safe (h : History N) (e : Record (Edge N)) (ok : allows h e = true) :
    Acyclic (h ++ [e]) := (acyclic_correct _).mp ok

theorem edge_append (h : History N) (e : Record (Edge N)) :
    Edges (h ++ [e]) e.payload.1 e.payload.2 := by simp [Edges]

theorem reach_append {h : History N} (e : Record (Edge N)) {u v}
    (path : Reach h u v) : Reach (h ++ [e]) u v := by
  induction path with
  | single edge => exact .single (by simpa [Edges] using Or.inl edge)
  | tail path edge ih => exact ih.tail (by simpa [Edges] using Or.inl edge)

theorem admit_no_cycle {h : History N} {e : Record (Edge N)} (ok : allows h e = true) :
    e.payload.1 ≠ e.payload.2 ∧ ¬ Reach h e.payload.2 e.payload.1 := by
  have safe := admit_safe h e ok
  constructor
  · intro eq
    have self := edge_append h e
    rw [eq] at self
    exact safe _ (.single self)
  · intro back
    exact safe _ ((Relation.TransGen.single (edge_append h e)).trans (reach_append e back))

/-- The adapter restricts exactly new commits. All retry, rejection, identity,
recovery and acknowledgment transitions remain the underlying protocol's. -/
def AdmittedStep (ev : Event (Edge N)) (s t : Machine (Edge N)) : Prop :=
  Step ev s t ∧ match ev with
    | .commit e => ∃ h, s.cache = some h ∧ allows h e = true
    | _ => True

inductive AdmissionReply (N : Nat) where
  | protocol (event : Event (Edge N))
  | cycleRejected (request : Record (Edge N))

/-- A fresh cyclic proposal is rejected before invocation, leaving the ready
service unchanged. Existing identities continue through the protocol's retry
or conflicting-reuse rules rather than being misreported as graph failures. -/
inductive AdmissionStep : AdmissionReply N → Machine (Edge N) → Machine (Edge N) → Prop
  | protocol {ev s t} : AdmittedStep ev s t → AdmissionStep (.protocol ev) s t
  | cycle {s h e} : s.cache = some h → s.active = none → s.pending = none →
      Fresh h e → allows h e = false → AdmissionStep (.cycleRejected e) s s

theorem cycle_rejection_preserves {e} {s t : Machine (Edge N)}
    (reject : AdmissionStep (.cycleRejected e) s t) : t = s := by
  cases reject
  rfl

theorem admitted_step_safe {ev} {s t : Machine (Edge N)} {a}
    (rel : Related s a) (safe : Acyclic a.history) (step : AdmittedStep ev s t) :
    ∃ b, SpecStep ev a b ∧ Related t b ∧ Acyclic b.history := by
  obtain ⟨b, spec, after⟩ := step.1.simulation rel
  refine ⟨b, spec, after, ?_⟩
  cases spec with
  | commit online active fresh =>
    obtain ⟨h, hc, ok⟩ := step.2
    rw [(rel.ready hc).2] at ok
    exact admit_safe _ _ ok
  | _ => exact safe

theorem empty_acyclic : Acyclic ([] : History N) := by
  intro v path
  cases path with
  | single edge => simp [Edges] at edge
  | tail path edge => simp [Edges] at edge

theorem admitted_script_safe (events : List (Event (Edge N))) {s t a}
    (rel : Related s a) (safe : Acyclic a.history)
    (run : Interaction.Events.interpret AdmittedStep events s t) :
    ∃ b, Interaction.Events.interpret SpecStep events a b ∧ Related t b ∧ Acyclic b.history := by
  induction events generalizing s a with
  | nil => cases run; exact ⟨a,rfl,rel,safe⟩
  | cons ev events ih =>
    obtain ⟨mid, first, rest⟩ := run
    obtain ⟨b, source, relation, invariant⟩ := admitted_step_safe rel safe first
    obtain ⟨c, tail, relation', invariant'⟩ := ih relation invariant rest
    exact ⟨c, ⟨b, source, tail⟩, relation', invariant'⟩

theorem acyclic_prefix {h tail : History N} (safe : Acyclic (h ++ tail)) : Acyclic h := by
  have lift : ∀ {u v}, Reach h u v → Reach (h ++ tail) u v := by
    intro u v path
    induction path with
    | single edge => exact .single (by simp [Edges] at *; exact Or.inl edge)
    | tail path edge ih => exact ih.tail (by simp [Edges] at *; exact Or.inl edge)
  exact fun v path => safe v (lift path)

/-- A checked acyclic final history supplies the guard at each earlier commit.
This lemma connects existing concrete storage executions to the admission
adapter; it does not change the adapter's current-cache check. -/
theorem admit_execution (events : List (Event (Edge N))) {s t a}
    (rel : Related s a) (run : Interaction.Events.interpret Step events s t)
    (safe : ∀ h, Represents t.disk t.root h → Acyclic h) :
    Interaction.Events.interpret AdmittedStep events s t := by
  induction events generalizing s a with
  | nil => exact run
  | cons ev events ih =>
    obtain ⟨mid,step,rest⟩ := run
    obtain ⟨next,sourceStep,relation⟩ := step.simulation rel
    refine ⟨mid,⟨step,?_⟩,ih relation rest⟩
    cases sourceStep with
    | commit online active fresh =>
      obtain ⟨last,sourceRest,lastRel⟩ := script_simulation _ relation rest
      obtain ⟨suffix,eq⟩ := spec_script_prefix sourceRest
      have invariant : Acyclic (a.history ++ [_]) := acyclic_prefix (eq ▸ safe _ lastRel.root)
      exact ⟨a.history, by simpa [online] using rel.cache,
        (acyclic_correct _).mpr invariant⟩
    | _ => trivial

end Durability.Diagnostic

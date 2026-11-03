import SquareKit.InteractionEvents
import Mathlib.Tactic

/-!
# One accepted obligation and its external attempts

A bounded authority-inspired experiment. Request values are arbitrary; no
codec, identifier width or finite request universe is part of the contract.
An attempt counter records local leases, not a downstream fencing mechanism.
`effects` counts external executions of this one obligation. The model does
not equate atomic acceptance with external completion or durable physical IO.
-/
namespace Interaction.Obligation
universe u

structure State (Request : Type u) where
  receipt : Option Request
  intent : Option Request
  attempts : Nat
  effects : Nat
  settled : Bool
  deriving DecidableEq

def empty {R : Type u} : State R := ⟨none, none, 0, 0, false⟩

/-- Independent semantic requirement for a fresh acceptance. -/
def Accepted {R : Type u} (r : R) (t : State R) : Prop :=
  t.receipt = some r ∧ t.intent = some r ∧ t.attempts = 0 ∧
    t.effects = 0 ∧ t.settled = false

def Ready {R : Type u} (s : State R) : Prop :=
  s.receipt = none ∧ s.intent = none ∧ s.attempts = 0 ∧
    s.effects = 0 ∧ s.settled = false

/-- Only admission is partial: `none` is known rejection before external effects,
not an encoding of an external failure or an unknown execution. -/
def tryAccept {R : Type u} (r : R) (s : State R) : Option (State R) :=
  if s.receipt.isNone && s.intent.isNone && s.attempts == 0 &&
      s.effects == 0 && !s.settled then
    some ⟨some r, some r, 0, 0, false⟩
  else none

def AcceptSpec {R : Type u} (r : R) (s t : State R) : Prop :=
  Ready s ∧ Accepted r t

theorem tryAccept_iff {R : Type u} (r : R) (s t : State R) :
    tryAccept r s = some t ↔ AcceptSpec r s t := by
  cases s with | mk sr si sa se ss =>
  cases t with | mk tr ti ta te ts =>
  simp only [tryAccept, AcceptSpec, Ready, Accepted]
  split
  · rename_i h
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq,
      Option.isNone_iff_eq_none] at h
    simp only [Option.some.injEq, State.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl, rfl, rfl, rfl⟩
      exact ⟨by tauto, by simp⟩
    · rintro ⟨_, rfl, rfl, rfl, rfl, rfl⟩
      simp
  · rename_i h
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq,
      Option.isNone_iff_eq_none] at h
    simp only [reduceCtorEq, false_iff, not_and]
    intro ready accepted
    exact False.elim (h (by tauto))

theorem admission_complete {R : Type u} (r : R) {s : State R} (ready : Ready s) :
    ∃ t, tryAccept r s = some t ∧ Accepted r t := by
  let t : State R := ⟨some r, some r, 0, 0, false⟩
  have accepted : Accepted r t := ⟨rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨t, (tryAccept_iff r s t).mpr ⟨ready, accepted⟩, accepted⟩

/-- Identity is stable across leases, effects and observations. -/
def Bound {R : Type u} (r : R) (s : State R) : Prop :=
  s.receipt = some r ∧ s.intent = some r

def lease {R : Type u} (s : State R) : State R :=
  { s with attempts := s.attempts + 1 }

def execute {R : Type u} (s : State R) : State R :=
  { s with effects := s.effects + 1 }

/-- A lost reply retains the effect and leaves settlement unresolved. -/
def observe {R : Type u} (known : Bool) (s : State R) : State R :=
  { s with settled := known && 0 < s.effects }

/-- Independent operation contracts retain world-state changes on missing reply. -/
def LeaseSpec {R : Type u} (s t : State R) : Prop :=
  t.receipt = s.receipt ∧ t.intent = s.intent ∧
  t.attempts = s.attempts + 1 ∧ t.effects = s.effects ∧ t.settled = s.settled

def EffectSpec {R : Type u} (s t : State R) : Prop :=
  t.receipt = s.receipt ∧ t.intent = s.intent ∧
  t.attempts = s.attempts ∧ t.effects = s.effects + 1 ∧ t.settled = s.settled

def ObservationSpec {R : Type u} (known : Bool) (s t : State R) : Prop :=
  t.receipt = s.receipt ∧ t.intent = s.intent ∧
  t.attempts = s.attempts ∧ t.effects = s.effects ∧
  t.settled = (known && 0 < s.effects)

inductive Event (R : Type u) where
  | accept (request : R)
  | lease
  | effect
  | observation (known : Bool)

/-- Mathematical event meanings, defined separately from executable handlers. -/
def meaning {R : Type u} : Event R → State R → State R → Prop
  | .accept r => AcceptSpec r
  | .lease => LeaseSpec
  | .effect => EffectSpec
  | .observation known => ObservationSpec known

def handler {R : Type u} : Event R → State R → State R → Prop
  | .accept r, s, t => tryAccept r s = some t
  | .lease, s, t => t = lease s
  | .effect, s, t => t = execute s
  | .observation known, s, t => t = observe known s

theorem handler_sound {R : Type u} (e : Event R) (s t : State R)
    (h : handler e s t) : meaning e s t := by
  cases e with
  | accept r => exact (tryAccept_iff r s t).mp h
  | lease => subst t; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | effect => subst t; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | observation known => subst t; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem meaning_bound {R : Type u} (r : R) (e : Event R) :
    Stable (meaning e) (Bound r) := by
  intro s t hs h
  cases e with
  | accept q =>
    have impossible : (some r : Option R) = none := hs.1.symm.trans h.1.1
    cases impossible
  | lease => exact ⟨h.1.trans hs.1, h.2.1.trans hs.2⟩
  | effect => exact ⟨h.1.trans hs.1, h.2.1.trans hs.2⟩
  | observation known => exact ⟨h.1.trans hs.1, h.2.1.trans hs.2⟩

/-- All scripted endpoint contracts transfer from independent meanings. -/
theorem script_safe {R : Type u} {script : List (Event R)} {P Q : State R → Prop}
    (h : Safe P (Events.interpret meaning script) Q) :
    Safe P (Events.interpret handler script) Q :=
  Events.interpret_safe handler_sound h

theorem script_bound {R : Type u} (r : R) (script : List (Event R)) :
    Safe (Bound r) (Events.interpret handler script) (Bound r) :=
  script_safe (Events.interpret_invariant (meaning_bound r) script)

/-- Direct relation interface for acceptance followed by a lease. -/
def direct {R : Type u} (r : R) : State R → State R → Prop :=
  Relation.Comp (AcceptSpec r) LeaseSpec

def Leased {R : Type u} (r : R) (s : State R) : Prop :=
  Bound r s ∧ s.attempts = 1 ∧ s.effects = 0 ∧ s.settled = false

theorem direct_contract {R : Type u} (r : R) : Safe Ready (direct r) (Leased r) := by
  rintro s t _ ⟨a, ⟨_, receipt, intent, attempts, effects, settled⟩,
    tr, ti, ta, te, ts⟩
  exact ⟨⟨tr.trans receipt, ti.trans intent⟩,
    ta.trans (congrArg (· + 1) attempts), te.trans effects, ts.trans settled⟩

/-- Interpreter syntax agrees with the independently written direct interface. -/
theorem script_meaning {R : Type u} (r : R) :
    Events.interpret meaning [.accept r, .lease] = direct r := by
  funext s t
  simp [Events.interpret, meaning, direct, Relation.Comp]

theorem event_contract {R : Type u} (r : R) :
    Safe Ready (Events.interpret handler [.accept r, .lease]) (Leased r) := by
  apply script_safe
  rw [script_meaning]
  exact direct_contract r

/-- A lease counter is not downstream fencing: an old delayed execution can
still increment effects after another lease. Both executions remain visible. -/
theorem delayed_attempt {R : Type u} (s : State R) :
    (execute (lease (execute s))).effects = s.effects + 2 ∧
    (execute (lease (execute s))).attempts = s.attempts + 1 := by
  simp [execute, lease, Nat.add_assoc]
end Interaction.Obligation

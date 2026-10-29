import Applications.Durability.Recovery
import SquareKit.InteractionEvents

namespace Durability

def Fresh {P : Type} (h : List (Record P)) (e : Record P) : Prop :=
  ∀ r ∈ h, r.key ≠ e.key

inductive Event (P : Type) where
  | internal | invoke (e : Record P) | commit (e : Record P)
  | acknowledge (e : Record P) | reject (e : Record P)
  | query (h : List (Record P)) | crash | recover (h : List (Record P))
  deriving DecidableEq

structure Abstract (P : Type) where
  history : List (Record P)
  active : Option (Record P)
  online : Bool
  deriving DecidableEq

/-- Independent accepted-history specification. It contains no cell layout,
codec, root, checkpoint, or reconstruction algorithm. -/
inductive SpecStep {P : Type} : Event P → Abstract P → Abstract P → Prop
  | internal {a} : SpecStep .internal a a
  | invoke {a e} : a.online = true → a.active = none →
      SpecStep (.invoke e) a { a with active := some e }
  | commit {a e} : a.online = true → a.active = some e → Fresh a.history e →
      SpecStep (.commit e) a { a with history := a.history ++ [e] }
  | acknowledge {a e} : a.online = true → a.active = some e → e ∈ a.history →
      SpecStep (.acknowledge e) a { a with active := none }
  | reject {a e r} : a.online = true → a.active = some e → r ∈ a.history →
      r.key = e.key → r ≠ e → SpecStep (.reject e) a { a with active := none }
  | query {a} : a.online = true → a.active = none →
      SpecStep (.query a.history) a a
  | crash {a} : SpecStep .crash a { a with active := none, online := false }
  | recover {a} : a.online = false →
      SpecStep (.recover a.history) a { a with online := true }

structure Machine (P : Type) where
  disk : Heap (Cell P)
  root : Root
  cache : Option (List (Record P))
  active : Option (Record P)
  pending : Option (Plan P)
  buffered : Heap (Cell P)
  cursor : Option (Cursor P)
  /-- Allocation ownership history. It prevents reuse even after reclamation;
  an implementation must provide a fresh-name mechanism satisfying this model. -/
  used : Set Nat

def initial {P : Type} : Machine P :=
  ⟨fun _ => none, emptyRoot, some [], none, none, fun _ => none, none, ∅⟩

def initialAbstract {P : Type} : Abstract P := ⟨[], none, true⟩

/-- Source snapshot and layout certificate remain volatile until publication.
Writing a cell and making it durable are separate transitions. -/
inductive Step {P : Type} : Event P → Machine P → Machine P → Prop
  | invoke {s h e} : s.cache = some h → s.active = none → s.pending = none →
      Step (.invoke e) s { s with active := some e }
  | prepare {s h p} : s.cache = some h → s.pending = none →
      p.source = s.disk → p.before = h → p.appended = s.active →
      (∀ e, p.appended = some e → Fresh h e) →
      (∀ i c, p.writes i = some c → i ∉ s.used) →
      Step .internal s { s with pending := some p, buffered := (fun _ => none), used := s.used ∪ {i | ∃ c, p.writes i = some c} }
  | write {s p i c} : s.pending = some p → p.writes i = some c →
      Step .internal s { s with buffered := put s.buffered i c }
  | persist {s p i c} : s.pending = some p → p.writes i = some c →
      s.buffered i = some c → (s.disk i = none ∨ s.disk i = some c) →
      Step .internal s { s with disk := put s.disk i c }
  | publish {s p} : s.pending = some p → Extends p.writes s.disk →
      Step (match p.appended with | none => .internal | some e => .commit e) s
        { s with root := p.root, cache := some p.after, pending := none, buffered := fun _ => none }
  | acknowledge {s h e} : s.cache = some h → s.active = some e → s.pending = none →
      e ∈ h → Step (.acknowledge e) s { s with active := none }
  | reject {s h e r} : s.cache = some h → s.active = some e → s.pending = none →
      r ∈ h → r.key = e.key → r ≠ e →
      Step (.reject e) s { s with active := none }
  | query {s h} : s.cache = some h → s.active = none → s.pending = none →
      Step (.query h) s s
  | crash {s} : Step .crash s { s with cache := none, active := none, pending := none, buffered := (fun _ => none), cursor := none }
  | startRead {s c} : s.cache = none → s.cursor = none →
      StartRead s.disk s.root c → Step .internal s { s with cursor := some c }
  | read {s c d} : s.cache = none → s.cursor = some c → Read s.disk c d →
      Step .internal s { s with cursor := some d }
  | recover {s h} : s.cache = none → s.cursor = some (.done h) →
      Step (.recover h) s { s with cache := some h, cursor := none }
  | reclaim {s h disk'} : s.cache = some h → s.active = none → s.pending = none →
      KeepsRoot s.disk disk' s.root →
      (∀ i c, disk' i = some c → s.disk i = some c) →
      Step .internal s { s with disk := disk' }

structure Related {P : Type} (s : Machine P) (a : Abstract P) : Prop where
  root : Represents s.disk s.root a.history
  cache : s.cache = if a.online then some a.history else none
  active : s.active = a.active
  pending : ∀ p, s.pending = some p →
    p.before = a.history ∧ p.appended = a.active ∧ Extends p.source s.disk ∧
    (∀ e, p.appended = some e → Fresh a.history e) ∧ a.online = true
  cursor : ∀ c, s.cursor = some c → CursorRep s.disk c a.history
  /-- No active recovery cursor can overlap normal operation or writes. -/
  cursor_offline : ∀ c, s.cursor = some c → a.online = false
  offline_pending : a.online = false → s.pending = none
  offline_active : a.online = false → a.active = none

theorem related_initial {P : Type} : Related (initial : Machine P) initialAbstract := by
  constructor
  · exact empty_rep _
  · rfl
  · rfl
  · simp [initial]
  · simp [initial]
  · simp [initial]
  · simp [initialAbstract]
  · simp [initialAbstract]

theorem Related.ready {P : Type} {s : Machine P} {a : Abstract P}
    (rel : Related s a) {h} (hc : s.cache = some h) : a.online = true ∧ h = a.history := by
  rw [rel.cache] at hc
  cases eq : a.online <;> simp_all

theorem Related.offline {P : Type} {s : Machine P} {a : Abstract P}
    (rel : Related s a) (hc : s.cache = none) : a.online = false := by
  rw [rel.cache] at hc
  cases eq : a.online <;> simp_all

theorem Related.noCursor {P : Type} {s : Machine P} {a : Abstract P}
    (rel : Related s a) (online : a.online = true) : s.cursor = none := by
  cases eq : s.cursor with
  | none => rfl
  | some c => have bad := rel.cursor_offline c eq; simp [online] at bad

theorem put_compatible {C : Type} {s : Heap C} {i c}
    (compatible : s i = none ∨ s i = some c) : Extends s (put s i c) := by
  rcases compatible with empty | same
  · exact extends_put s i c empty
  · intro j x hx
    by_cases eq : j = i
    · subst j; have e := same.symm.trans hx; cases e; simp [put]
    · simp [put, eq, hx]

end Durability

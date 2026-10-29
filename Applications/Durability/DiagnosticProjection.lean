import Applications.Durability.DiagnosticGraph

namespace Durability.Diagnostic

structure View (N : Nat) where
  count : Nat
  paths : Finset (Edge N)
  deriving DecidableEq

def recompute (h : History N) : View N := ⟨h.length, closure h⟩

/-- The accepted history can be read independently from committed events;
invocation, retry acknowledgments and diagnostics do not append records. -/
def committedRecords : List (Event P) → List (Record P)
  | [] => []
  | .commit e :: es => e :: committedRecords es
  | _ :: es => committedRecords es

theorem source_history {events : List (Event P)} {a b : Abstract P}
    (run : Interaction.Events.interpret SpecStep events a b) :
    b.history = a.history ++ committedRecords events := by
  induction events generalizing a with
  | nil => cases run; simp [committedRecords]
  | cons ev events ih =>
    obtain ⟨mid, step, rest⟩ := run
    rw [ih rest]
    cases step <;> simp [committedRecords,List.append_assoc]

/-- One fixed schema/generation and an append-only history. A position is
meaningful only relative to that history, never as a global history identity. -/
structure Published (D : Type) where
  position : Nat
  view : D
  deriving DecidableEq

def Agrees (observe : List (Record P) → D) (h : List (Record P)) (v : Published D) : Prop :=
  ∃ pre, pre <+: h ∧ v.position = pre.length ∧ v.view = observe pre

theorem agrees_exact {observe : List (Record P) → D} {h v} (ok : Agrees observe h v) :
    v.position ≤ h.length ∧ v.view = observe (h.take v.position) := by
  obtain ⟨pre, ⟨suffix,rfl⟩, pos, view⟩ := ok
  rw [pos, List.take_left]
  exact ⟨by simp, view⟩

theorem agrees_extend {observe : List (Record P) → D} {h v}
    (ok : Agrees observe h v) (suffix : List (Record P)) : Agrees observe (h ++ suffix) v := by
  obtain ⟨pre, ⟨rest,eq⟩, pos, view⟩ := ok
  exact ⟨pre, ⟨rest ++ suffix, by simp [← eq,List.append_assoc]⟩, pos, view⟩

structure Rebuild (P : Type) where
  seen : List (Record P)
  todo : List (Record P)

structure Projector (P D : Type) where
  machine : Machine P
  published : Option (Published D)
  rebuilding : Option (Rebuild P)

/-- Publication and the cursor are volatile. Crash discards both; no durable
incremental view is assumed. A completed tuple is installed in one local step. -/
inductive ProjectionStep (observe : List (Record P) → D) :
    Projector P D → Projector P D → Prop
  | storage {s t ev} : Step ev s.machine t → ev ≠ .crash →
      ProjectionStep observe s {s with machine := t}
  | crash {s} : ProjectionStep observe s ⟨crashState s.machine,none,none⟩
  | start {s h} : s.machine.cache = some h →
      ProjectionStep observe s {s with rebuilding := some ⟨[],h⟩}
  | scan {s seen e todo} : s.rebuilding = some ⟨seen,e::todo⟩ →
      ProjectionStep observe s {s with rebuilding := some ⟨seen ++ [e],todo⟩}
  | publish {s h} : s.rebuilding = some ⟨h,[]⟩ →
      ProjectionStep observe s {s with published := some ⟨h.length,observe h⟩, rebuilding := none}

structure ProjectionInv (observe : List (Record P) → D) (s : Projector P D) (a : Abstract P) : Prop where
  storage : Related s.machine a
  published : ∀ v, s.published = some v → Agrees observe a.history v
  rebuilding : ∀ b, s.rebuilding = some b → b.seen ++ b.todo <+: a.history

theorem projection_preserves {observe : List (Record P) → D} {s t a}
    (inv : ProjectionInv observe s a) (step : ProjectionStep observe s t) :
    ∃ b, ProjectionInv observe t b := by
  cases step with
  | storage run noncrash =>
    obtain ⟨b, source, rel⟩ := run.simulation inv.storage
    obtain ⟨suffix, hist⟩ := source.prefix
    refine ⟨b, rel, ?_, ?_⟩
    · intro v pub
      rw [hist]
      exact agrees_extend (inv.published v pub) suffix
    · intro build hb
      obtain ⟨rest, eq⟩ := inv.rebuilding build hb
      exact ⟨rest ++ suffix, by simp [hist, ← eq, List.append_assoc]⟩
  | crash =>
    obtain ⟨b, source, rel⟩ := Step.crash.simulation inv.storage
    exact ⟨b, rel, by simp, by simp⟩
  | start ready =>
    refine ⟨a, inv.storage, inv.published, ?_⟩
    intro build eq
    cases eq
    simp only [List.nil_append]
    rw [(inv.storage.ready ready).2]
  | scan hb =>
    refine ⟨a, inv.storage, inv.published, ?_⟩
    intro build eq
    cases eq
    simpa [List.append_assoc] using inv.rebuilding _ hb
  | publish hb =>
    refine ⟨a, inv.storage, ?_, by simp⟩
    intro v eq
    cases eq
    exact ⟨_, by simpa using inv.rebuilding _ hb, rfl, rfl⟩

/-- Synchronous snapshot query computes every field from the same ready cache. -/
def synchronous (observe : List (Record P) → D) (s : Machine P) : Option (Published D) :=
  s.cache.map fun h => ⟨h.length, observe h⟩

theorem synchronous_correct {observe : List (Record P) → D} {s : Machine P} {a h}
    (rel : Related s a) (ready : s.cache = some h) :
    synchronous observe s = some ⟨a.history.length, observe a.history⟩ := by
  simp [synchronous, ready, (rel.ready ready).2]

theorem synchronous_ack_fresh {observe : List (Record P) → D} {s mid t : Machine P}
    {a e events h} (rel : Related s a) (ack : Step (.acknowledge e) s mid)
    (later : Interaction.Events.interpret Step events mid t) (ready : t.cache = some h) :
    ∃ v, synchronous observe t = some v ∧ a.history.length ≤ v.position ∧ e ∈ h := by
  obtain ⟨b,sourceAck,midRel⟩ := ack.simulation rel
  obtain ⟨c,sourceLater,lastRel⟩ := script_simulation _ midRel later
  obtain ⟨mem,suffix,eq⟩ := acknowledged_survives sourceAck sourceLater
  refine ⟨⟨c.history.length,observe c.history⟩,synchronous_correct lastRel ready,?_,?_⟩
  · simp [eq]
  · simpa [(lastRel.ready ready).2] using mem

/-- One projection client is transported by the same refinement as all other
history clients, without reference to log/checkpoint layout or cell encoding. -/
theorem projection_client (events : List (Event P)) (observe : List (Record P) → D)
    (Q : Published D → Prop)
    (source : ∀ a ∈ sourceBehaviors events, Q ⟨a.history.length, observe a.history⟩) :
    ∀ s ∈ targetBehaviors events, ∀ v, synchronous observe s = some v → Q v := by
  apply (history_refinement events).property
    (P := fun a => Q ⟨a.history.length,observe a.history⟩)
    (Q := fun s => ∀ v, synchronous observe s = some v → Q v) source
  intro a s rel property v hv
  cases hc : s.cache with
  | none => simp [synchronous,hc] at hv
  | some h =>
    rw [synchronous_correct rel hc] at hv
    cases hv
    exact property

theorem encoded_projection_client (codec : Codec (Cell P) B)
    (events : List (Event P)) (observe : List (Record P) → D) (Q : Published D → Prop)
    (source : ∀ a ∈ sourceBehaviors events, Q ⟨a.history.length,observe a.history⟩) :
    ∀ s ∈ encodedBehaviors codec events, ∀ v,
      synchronous observe (_root_.Durability.observe codec s) = some v → Q v := by
  apply (encoding_refinement codec events).property
    (P := fun s => ∀ v, synchronous observe s = some v → Q v)
    (Q := fun s => ∀ v, synchronous observe (_root_.Durability.observe codec s) = some v → Q v)
  · exact projection_client events observe Q source
  · intro s t rel property
    exact rel ▸ property

end Durability.Diagnostic

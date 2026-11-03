import Applications.Durability.Clients

namespace Durability

/-- Encoding is optional. This interface asks only for a left inverse on the
admitted cell type, not serializability of every Lean value. -/
structure Codec (C B : Type) where
  encode : C → B
  decode : B → Option C
  roundtrip : ∀ c, decode (encode c) = some c

def decodeHeap {C B : Type} (codec : Codec C B) (s : Heap B) : Heap C :=
  fun i => (s i).bind codec.decode

theorem decode_put {C B : Type} (codec : Codec C B) (s : Heap B) (i : Nat) (c : C) :
    decodeHeap codec (put s i (codec.encode c)) = put (decodeHeap codec s) i c := by
  funext j
  by_cases eq : j = i <;> simp [decodeHeap, put, eq, codec.roundtrip]

structure Encoded (P B : Type) where
  disk : Heap B
  root : Root
  cache : Option (List (Record P))
  active : Option (Record P)
  pending : Option (Plan P)
  buffered : Heap B
  cursor : Option (Cursor P)
  used : Set Nat

def observe {P B : Type} (codec : Codec (Cell P) B) (s : Encoded P B) : Machine P :=
  ⟨decodeHeap codec s.disk, s.root, s.cache, s.active, s.pending,
    decodeHeap codec s.buffered, s.cursor, s.used⟩

inductive EncodedStep {P B : Type} (codec : Codec (Cell P) B) : Event P → Encoded P B → Encoded P B → Prop
  | invoke {s h e} : s.cache = some h → s.active = none → s.pending = none →
      EncodedStep codec (.invoke e) s { s with active := some e }
  | prepare {s h p} : s.cache = some h → s.pending = none →
      p.source = decodeHeap codec s.disk → p.before = h → p.appended = s.active →
      (∀ e, p.appended = some e → Fresh h e) →
      (∀ i c, p.writes i = some c → i ∉ s.used) →
      EncodedStep codec .internal s { s with pending := some p, buffered := (fun _ => none), used := s.used ∪ {i | ∃ c, p.writes i = some c} }
  | write {s p i c} : s.pending = some p → p.writes i = some c →
      EncodedStep codec .internal s { s with buffered := put s.buffered i (codec.encode c) }
  | persist {s p i c} : s.pending = some p → p.writes i = some c →
      s.buffered i = some (codec.encode c) → (s.disk i = none ∨ s.disk i = some (codec.encode c)) →
      EncodedStep codec .internal s { s with disk := put s.disk i (codec.encode c) }
  | publish {s p} : s.pending = some p → Extends p.writes (decodeHeap codec s.disk) →
      EncodedStep codec (match p.appended with | none => .internal | some e => .commit e) s
        { s with root := p.root, cache := some p.after, pending := none, buffered := fun _ => none }
  | acknowledge {s h e} : s.cache = some h → s.active = some e → s.pending = none →
      e ∈ h → EncodedStep codec (.acknowledge e) s { s with active := none }
  | reject {s h e r} : s.cache = some h → s.active = some e → s.pending = none →
      r ∈ h → r.key = e.key → r ≠ e →
      EncodedStep codec (.reject e) s { s with active := none }
  | query {s h} : s.cache = some h → s.active = none → s.pending = none →
      EncodedStep codec (.query h) s s
  | crash {s} : EncodedStep codec .crash s { s with cache := none, active := none, pending := none, buffered := (fun _ => none), cursor := none }
  | startRead {s c} : s.cache = none → s.cursor = none →
      StartRead (decodeHeap codec s.disk) s.root c → EncodedStep codec .internal s { s with cursor := some c }
  | read {s c d} : s.cache = none → s.cursor = some c → Read (decodeHeap codec s.disk) c d →
      EncodedStep codec .internal s { s with cursor := some d }
  | recover {s h} : s.cache = none → s.cursor = some (.done h) →
      EncodedStep codec (.recover h) s { s with cache := some h, cursor := none }
  | reclaim {s h disk'} : s.cache = some h → s.active = none → s.pending = none →
      KeepsRoot (decodeHeap codec s.disk) (decodeHeap codec disk') s.root →
      (∀ i c, disk' i = some c → s.disk i = some c) →
      EncodedStep codec .internal s { s with disk := disk' }

/-- Encoded persistence copies the encoded object, while root publication and
recovery use its checked decoding. The simulation proves those primitive choices
preserve the typed protocol, rather than postulating whole-run refinement. -/
theorem EncodedStep.simulation {P B : Type} {codec : Codec (Cell P) B}
    {s t : Encoded P B} {ev} (step : EncodedStep codec ev s t) :
    Step ev (observe codec s) (observe codec t) := by
  cases step with
  | invoke hc ha hp => exact .invoke hc ha hp
  | prepare hc hp src before app fresh unused => exact .prepare hc hp src before app fresh unused
  | @write s p i c hp hw =>
    simpa [observe, decode_put] using Step.write (s := observe codec s) hp hw
  | @persist s p i c hp hw hb compatible =>
    have buff : decodeHeap codec s.buffered i = some c := by
      simp [decodeHeap, hb, codec.roundtrip]
    have comp : decodeHeap codec s.disk i = none ∨ decodeHeap codec s.disk i = some c := by
      rcases compatible with empty | same
      · left; simp [decodeHeap, empty]
      · right; simp [decodeHeap, same, codec.roundtrip]
    simpa [observe, decode_put] using Step.persist (s := observe codec s) hp hw buff comp
  | publish hp persisted => exact .publish hp persisted
  | acknowledge hc ha hp mem => exact .acknowledge hc ha hp mem
  | reject hc ha hp mem key neq => exact .reject hc ha hp mem key neq
  | query hc ha hp => exact .query hc ha hp
  | crash => exact .crash
  | startRead hc cur start => exact .startRead hc cur start
  | read hc cur rd => exact .read hc cur rd
  | recover hc cur => exact .recover hc cur
  | reclaim hc ha hp keep subset =>
    apply Step.reclaim hc ha hp keep
    intro i c found
    simp only [observe, decodeHeap, Option.bind_eq_some_iff] at found ⊢
    obtain ⟨b, hb, decode⟩ := found
    exact ⟨b, subset i b hb, decode⟩

def encodedInitial {P B : Type} : Encoded P B :=
  ⟨fun _ => none, emptyRoot, some [], none, none, fun _ => none, none, ∅⟩

theorem encoded_script {P B : Type} (codec : Codec (Cell P) B)
    {events : List (Event P)} {s t : Encoded P B}
    (run : Interaction.Events.interpret (EncodedStep codec) events s t) :
    Interaction.Events.interpret Step events (observe codec s) (observe codec t) := by
  induction events generalizing s with
  | nil => cases run; rfl
  | cons e es ih =>
    obtain ⟨mid, first, rest⟩ := run
    exact ⟨observe codec mid, first.simulation, ih rest⟩

def encodedBehaviors {P B : Type} (codec : Codec (Cell P) B) (events : List (Event P)) :
    Set (Encoded P B) := {s | Interaction.Events.interpret (EncodedStep codec) events encodedInitial s}

theorem encoding_refinement {P B : Type} (codec : Codec (Cell P) B) (events : List (Event P)) :
    Interaction.Refines (fun t e => t = observe codec e)
      (targetBehaviors events) (encodedBehaviors codec events) := by
  intro s run
  exact ⟨observe codec s, encoded_script codec run, rfl⟩

theorem encoded_history_refinement {P B : Type} (codec : Codec (Cell P) B)
    (events : List (Event P)) :
    Interaction.Refines (Relation.Comp (fun a t => Related t a)
      (fun t e => t = observe codec e)) (sourceBehaviors events) (encodedBehaviors codec events) :=
  (history_refinement events).trans (encoding_refinement codec events)

/-- The encoded boundary reuses the typed history client unchanged. -/
theorem encoded_history_client {P B : Type} (codec : Codec (Cell P) B)
    (events : List (Event P)) (Q : List (Record P) → Prop)
    (source : ∀ a ∈ sourceBehaviors events, Q a.history) :
    ∀ s ∈ encodedBehaviors codec events, ∀ h, s.cache = some h → Q h := by
  apply (encoding_refinement codec events).property
    (P := fun t => ∀ h, t.cache = some h → Q h)
    (Q := fun s => ∀ h, s.cache = some h → Q h)
    (history_client events Q source)
  intro t s eq property h ready
  subst t
  exact property h ready

theorem encoded_acknowledged_client {P B : Type} (codec : Codec (Cell P) B)
    (before after : List (Event P)) (e : Record P) :
    ∀ s ∈ encodedBehaviors codec (before ++ .acknowledge e :: after),
      ∀ h, s.cache = some h → e ∈ h := by
  apply (encoding_refinement codec _).property
    (P := fun t => ∀ h, t.cache = some h → e ∈ h)
    (Q := fun s => ∀ h, s.cache = some h → e ∈ h)
    (acknowledged_client before after e)
  intro t s eq property h ready
  subst t
  exact property h ready

def encodeHeap {C B : Type} (codec : Codec C B) (s : Heap C) : Heap B :=
  fun i => (s i).map codec.encode

theorem decode_encode {C B : Type} (codec : Codec C B) (s : Heap C) :
    decodeHeap codec (encodeHeap codec s) = s := by
  funext i; cases eq : s i <;> simp [decodeHeap, encodeHeap, eq, codec.roundtrip]

theorem encode_put {C B : Type} (codec : Codec C B) (s : Heap C) (i : Nat) (c : C) :
    encodeHeap codec (put s i c) = put (encodeHeap codec s) i (codec.encode c) := by
  funext j; by_cases eq : j = i <;> simp [encodeHeap, put, eq]

def encodeState {P B : Type} (codec : Codec (Cell P) B) (s : Machine P) : Encoded P B :=
  ⟨encodeHeap codec s.disk, s.root, s.cache, s.active, s.pending,
    encodeHeap codec s.buffered, s.cursor, s.used⟩

theorem observe_encode {P B : Type} (codec : Codec (Cell P) B) (s : Machine P) :
    observe codec (encodeState codec s) = s := by
  cases s; simp [observe, encodeState, decode_encode]

/-- Realizability in the encoded model: both layout executions lift through
primitive encoding, without inventing or dropping crashes. -/
theorem Step.encode {P B : Type} (codec : Codec (Cell P) B) {s t : Machine P} {ev}
    (step : Step ev s t) : EncodedStep codec ev (encodeState codec s) (encodeState codec t) := by
  cases step with
  | invoke hc ha hp => exact .invoke hc ha hp
  | @prepare s h p hc hp src before app fresh unused =>
    apply EncodedStep.prepare hc hp ?_ before app fresh unused
    simpa [encodeState, decode_encode] using src
  | @write s p i c hp hw =>
    simpa [encodeState, encode_put] using
      EncodedStep.write (codec := codec) (s := encodeState codec s) hp hw
  | @persist s p i c hp hw hb compatible =>
    have buff : encodeHeap codec s.buffered i = some (codec.encode c) := by simp [encodeHeap, hb]
    have comp : encodeHeap codec s.disk i = none ∨ encodeHeap codec s.disk i = some (codec.encode c) := by
      rcases compatible with empty | same
      · left; simp [encodeHeap, empty]
      · right; simp [encodeHeap, same]
    simpa [encodeState, encode_put] using
      EncodedStep.persist (codec := codec) (s := encodeState codec s) hp hw buff comp
  | publish hp persisted =>
    apply EncodedStep.publish hp
    simpa [encodeState, decode_encode] using persisted
  | acknowledge hc ha hp mem => exact .acknowledge hc ha hp mem
  | reject hc ha hp mem key neq => exact .reject hc ha hp mem key neq
  | query hc ha hp => exact .query hc ha hp
  | crash => exact .crash
  | startRead hc cur start =>
    apply EncodedStep.startRead hc cur
    simpa [encodeState, decode_encode] using start
  | read hc cur rd =>
    apply EncodedStep.read hc cur
    simpa [encodeState, decode_encode] using rd
  | recover hc cur => exact .recover hc cur
  | reclaim hc ha hp keep subset =>
    apply EncodedStep.reclaim hc ha hp
    · simpa [encodeState, decode_encode] using keep
    · intro i c found
      change (encodeHeap codec _) i = some c at found ⊢
      simp only [encodeHeap, Option.map_eq_some_iff] at found ⊢
      obtain ⟨x, hx, eq⟩ := found
      exact ⟨x, subset i x hx, eq⟩

theorem encode_script {P B : Type} (codec : Codec (Cell P) B)
    {events : List (Event P)} {s t : Machine P}
    (run : Interaction.Events.interpret Step events s t) :
    Interaction.Events.interpret (EncodedStep codec) events (encodeState codec s) (encodeState codec t) := by
  induction events generalizing s with
  | nil => cases run; rfl
  | cons e es ih =>
    obtain ⟨mid, first, rest⟩ := run
    exact ⟨encodeState codec mid, first.encode codec, ih rest⟩

/-- A length-framed finite sequence of natural-number words. This is not a
fixed-width byte codec. Addresses and fields are unbounded natural words. -/
def encodeCell : Cell Nat → List Nat
  | .node none e => [0, e.session, e.id, e.payload]
  | .node (some p) e => [1, p, e.session, e.id, e.payload]
  | .flat e => [2, e.session, e.id, e.payload]
  | .index as => 3 :: as.length :: as

def decodeCell : List Nat → Option (Cell Nat)
  | [0, s, i, p] => some (.node none ⟨s, i, p⟩)
  | [1, prev, s, i, p] => some (.node (some prev) ⟨s, i, p⟩)
  | [2, s, i, p] => some (.flat ⟨s, i, p⟩)
  | 3 :: n :: as => if as.length = n then some (.index as) else none
  | _ => none

def wordCodec : Codec (Cell Nat) (List Nat) where
  encode := encodeCell
  decode := decodeCell
  roundtrip := by
    intro c
    cases c with
    | node prev e => cases prev <;> cases e <;> rfl
    | flat e => cases e; rfl
    | index as => simp [encodeCell, decodeCell]

/-- An incorrect descriptor length is rejected, not silently truncated. -/
theorem malformed_length : wordCodec.decode [3, 2, 9] = none := by decide

end Durability

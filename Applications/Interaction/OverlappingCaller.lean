import Applications.Interaction.OverlappingQueries
import Applications.Interaction.OverlappingStrategies

/-! A reusable two-request client. Context schedules remain external inputs. -/
namespace Interaction.OverlappingCaller
open FiniteStrategies OverlappingStrategies

abbrev arena : Arena := ⟨2⟩
def slot (b : Bool) : Fin arena.slots := if b then 1 else 0
@[simp] theorem slot_inj (a b : Bool) : slot a = slot b ↔ a = b := by
  cases a <;> cases b <;> decide

def relayEvent (s : Strategy arena) : OverlappingQueries.Move → List (Event arena RelayMove)
  | .ask i => [(slot i,.leftAsk),(slot i,.rightAsk)]
  | .reply i b => [(slot i,.rightReply b),(slot i,.leftReply (s.response (slot i) b))]

def relayTrace (s : Strategy arena) (moves : List OverlappingQueries.Move) := moves.flatMap (relayEvent s)

def phase : OverlappingQueries.Status → Phase
  | .pending => .waiting
  | _ => .idle

private theorem native_local (s : Strategy arena) (i : Bool)
    (h : OverlappingQueries.step state m = some next) :
    Path (relayStep (s.response (slot i))) (phase (state i))
      (project (slot i) (relayEvent s m)) (phase (next i)) := by
  cases m with
  | ask j =>
    by_cases hij : j = i
    · subst j
      cases hs : state i <;> simp [OverlappingQueries.step, hs] at h
      all_goals cases h; simp [relayEvent, project, phase, OverlappingQueries.update]
      all_goals exact .cons rfl (.cons rfl .nil)
    · have hslot : slot j ≠ slot i := fun h => hij ((slot_inj j i).mp h)
      cases hs : state j <;> simp [OverlappingQueries.step, hs] at h
      all_goals cases h; simp [relayEvent, project, hslot, OverlappingQueries.update, Ne.symm hij]
      all_goals exact .nil
  | reply j b =>
    cases hs : state j <;> simp [OverlappingQueries.step, hs] at h
    cases h
    by_cases hij : j = i
    · subst j
      simp [relayEvent, project, phase, OverlappingQueries.update, hs]
      exact .cons rfl (.cons (by simp [relayStep]) .nil)
    · have hslot : slot j ≠ slot i := fun h => hij ((slot_inj j i).mp h)
      simp [relayEvent, project, hslot, OverlappingQueries.update, Ne.symm hij]
      exact .nil

private theorem native_path (s : Strategy arena) (i : Bool)
    (h : OverlappingQueries.execute state moves = some next) :
    Path (relayStep (s.response (slot i))) (phase (state i))
      (project (slot i) (relayTrace s moves)) (phase (next i)) := by
  induction moves generalizing state with
  | nil => simp [OverlappingQueries.execute] at h; cases h; exact .nil
  | cons m ms ih =>
    simp only [OverlappingQueries.execute] at h
    cases hm : OverlappingQueries.step state m with
    | none => simp [hm] at h
    | some mid =>
      simp only [hm, Option.bind_some] at h
      have p := (native_local s i hm).append (ih h)
      simpa [relayTrace, List.flatMap_cons, project_append] using p

/-- Every accepted independent native trace produces a legal strategy play,
including a trace ending with either or both requests still pending. -/
theorem relay_legal (s : Strategy arena) (h : OverlappingQueries.Legal moves) :
    s.Play (relayTrace s moves) := by
  obtain ⟨state,h⟩ := h
  intro i
  have hi : i = slot false ∨ i = slot true := by
    simp only [slot, Bool.false_eq_true, ↓reduceIte]
    have := i.isLt
    change i.val < 2 at this
    omega
  rcases hi with rfl | rfl
  · exact ⟨_, native_path s false h⟩
  · exact ⟨_, native_path s true h⟩

/-- The reusable caller works with any two-slot response policy. -/
def caller (s : Strategy arena) (schedule : List (Bool × Bool)) : List (Event arena RelayMove) :=
  relayTrace s (OverlappingQueries.trace schedule)

/-- The actual internal interaction, retaining the intermediate shared channel. -/
def network (s t : Strategy arena) (schedule : List (Bool × Bool)) : List (Event arena WireMove) :=
  translate (fun i => insertMiddle (t.response i)) (caller (s.comp t) schedule)

theorem network_legal (s t : Strategy arena) (h : OverlappingQueries.native schedule = some out) :
    InteractionPlay s t (network s t schedule) := by
  have hp := relay_legal (s.comp t) (OverlappingQueries.native_legal h)
  intro i
  rw [network, project_translate]
  obtain ⟨q,hq⟩ := hp i
  obtain ⟨r,hr,_⟩ := lift_path (f := s.response i) (g := t.response i) hq .idle
  exact ⟨r,hr⟩

theorem network_hides (s t : Strategy arena) (schedule : List (Bool × Bool)) :
    hide (network s t schedule) = caller (s.comp t) schedule :=
  OverlappingStrategies.hide_insert _ _

/-- Decode the exposed service channel. Internal and client events are hidden. -/
def serviceEvent : Event arena RelayMove → List OverlappingQueries.Move
  | (i,.rightAsk) => [.ask (i == slot true)]
  | (i,.rightReply b) => [.reply (i == slot true) b]
  | _ => []

@[simp] theorem decode_slot (i : Bool) : (slot i == slot true) = i := by cases i <;> decide

theorem service_recovery (s : Strategy arena) (moves : List OverlappingQueries.Move) :
    (relayTrace s moves).flatMap serviceEvent = moves := by
  induction moves with
  | nil => rfl
  | cons m ms ih =>
    cases m <;> simp [relayTrace, relayEvent, serviceEvent, ih] at *
    all_goals exact decode_slot _

/-- Observe the actual exposed network service history, retaining pending state.
This evaluator does not call the native client. -/
def run (s t : Strategy arena) (schedule : List (Bool × Bool)) :
    Option OverlappingQueries.Observation :=
  let history := (hide (network s t schedule)).flatMap serviceEvent
  (OverlappingQueries.execute OverlappingQueries.initial history).map
    (fun state => OverlappingQueries.observe state history)

/-- Equality includes invalid schedules, pending state, response order, and result;
it is not just equality of completed Boolean answers. -/
theorem native_comparison (s t : Strategy arena) (schedule : List (Bool × Bool)) :
    run s t schedule = OverlappingQueries.native schedule := by
  simp only [run, network_hides, caller, service_recovery, OverlappingQueries.native]

/-- The two outstanding requests are visible before any service response. -/
theorem requests_overlap (s : Strategy arena) :
    caller s [] = [(slot false,.leftAsk),(slot false,.rightAsk),
      (slot true,.leftAsk),(slot true,.rightAsk)] := rfl

def forwarding : Strategy arena := Strategy.identity arena

theorem pending : run forwarding forwarding [] =
    some ⟨none,.pending,.pending,OverlappingQueries.requests⟩ := by
  rw [native_comparison]; exact OverlappingQueries.both_pending

theorem reply_order_observable :
    run forwarding forwarding [(true,true),(false,false)] ≠
    run forwarding forwarding [(false,false),(true,true)] := by
  simp only [native_comparison]
  exact OverlappingQueries.different_interactions

theorem duplicate_rejected : run forwarding forwarding [(true,true),(true,false)] = none := by
  rw [native_comparison]; exact OverlappingQueries.duplicate_reply_rejected

/-- The client boundary observes answers after the selected strategy policy. -/
def clientEvent : Event arena RelayMove → List OverlappingQueries.Move
  | (i,.leftAsk) => [.ask (i == slot true)]
  | (i,.leftReply b) => [.reply (i == slot true) b]
  | _ => []

def transform (s : Strategy arena) : OverlappingQueries.Move → OverlappingQueries.Move
  | .ask i => .ask i
  | .reply i b => .reply i (s.response (slot i) b)

theorem client_recovery (s : Strategy arena) (moves : List OverlappingQueries.Move) :
    (relayTrace s moves).flatMap clientEvent = moves.map (transform s) := by
  induction moves with
  | nil => rfl
  | cons m ms ih =>
    cases m <;> simp [relayTrace, relayEvent, clientEvent, transform, ih] at *
    all_goals exact decode_slot _

def clientRun (s t : Strategy arena) (schedule : List (Bool × Bool)) :
    Option OverlappingQueries.Observation :=
  let history := (hide (network s t schedule)).flatMap clientEvent
  (OverlappingQueries.execute OverlappingQueries.initial history).map
    (fun state => OverlappingQueries.observe state history)

/-- The caller result comes from the actual client projection. For copycat
forwarding, this agrees with the independently frozen raw-response client. -/
theorem client_native (schedule : List (Bool × Bool)) :
    clientRun forwarding forwarding schedule = OverlappingQueries.native schedule := by
  have ht : transform (forwarding.comp forwarding) = id := by
    funext m
    cases m <;> rfl
  simp only [clientRun, network_hides, caller, client_recovery, ht, List.map_id,
    OverlappingQueries.native]

/-- A nonidentity strategy changes the client answer while leaving the service
answer unchanged. Both boundaries retain the same correlation identifiers. -/
def negate : Strategy arena := ⟨fun _ b => !b⟩

theorem nonidentity_client :
    (clientRun negate forwarding [(true,true),(false,false)]).map
      OverlappingQueries.Observation.left = some (.answered true) := rfl

theorem nonidentity_service :
    (run negate forwarding [(true,true),(false,false)]).map
      OverlappingQueries.Observation.left = some (.answered false) := rfl

end Interaction.OverlappingCaller

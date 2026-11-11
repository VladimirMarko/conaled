import Applications.Interaction.PrefixDiagnostics

/-! Client observations of arbitrary legal wire prefixes. -/
namespace Interaction.PrefixDiagnostics
open FiniteStrategies OverlappingStrategies OverlappingCaller BehavioralCaller OverlappingQueries

/-- Idle internal stages may describe either no use or a completed delivery.
Every propagation phase has a pending client request. -/
def FitsSlot : Stage → Status → Prop
  | .idle, status => status ≠ .pending
  | _, status => status = .pending

def Fits (stages : Stages) (client : State) : Prop :=
  ∀ i : Bool, FitsSlot (stages (slot i)) (client i)

def clientLocal (i : Bool) : WireMove → List Move
  | .aAsk => [.ask i]
  | .aReply b => [.reply i b]
  | _ => []

def clientMoves (event : Event arena WireMove) : List Move :=
  clientLocal (event.1 == slot true) event.2

def clientHistory (wire : Wire) : List Move := wire.flatMap clientMoves

theorem clientHistory_hiding (wire : Wire) :
    clientHistory wire = (hide wire).flatMap clientEvent := by
  induction wire with
  | nil => rfl
  | cons event wire ih =>
    rcases event with ⟨i,m⟩
    cases m <;> simp_all [clientHistory, clientMoves, clientLocal, hide, translate, hideMiddle, clientEvent]

theorem native_execute_append (state : State) (xs ys : List Move) :
    OverlappingQueries.execute state (xs ++ ys) =
      (OverlappingQueries.execute state xs).bind (fun mid => OverlappingQueries.execute mid ys) := by
  induction xs generalizing state with
  | nil => rfl
  | cons m ms ih =>
    simp only [List.cons_append, OverlappingQueries.execute]
    cases h : OverlappingQueries.step state m <;> simp [ih]

/-- The actual wire transition determines either a visible native step or an
empty client projection. Other slots retain their original native state. -/
theorem client_local {f g : Bool → Bool} {p q : Stage} {m : WireMove}
    (state : State) (i : Bool) (align : FitsSlot p (state i))
    (step : wireStep f g p m = some q) :
    ∃ next, OverlappingQueries.execute state (clientLocal i m) = some next ∧
      FitsSlot q (next i) ∧ ∀ j, j ≠ i → next j = state j := by
  cases p <;> cases m <;> cases q <;> cases hs : state i <;>
    simp_all [wireStep, FitsSlot, clientLocal, OverlappingQueries.execute,
      OverlappingQueries.step, OverlappingQueries.update]

theorem slot_surjective (i : Fin arena.slots) : ∃ b, slot b = i := by
  have hi := i.isLt
  change i.val < 2 at hi
  by_cases e : i.val = 0
  · exact ⟨false, Fin.ext e.symm⟩
  · exact ⟨true, Fin.ext (by change 1 = i.val; omega)⟩

/-- One global dispatch step updates exactly the corresponding client slot. -/
theorem client_step (state : State) (align : Fits stages state)
    (step : dispatch s t stages event = some next) :
    ∃ client, OverlappingQueries.execute state (clientMoves event) = some client ∧ Fits next client := by
  rcases event with ⟨j,m⟩
  obtain ⟨i,rfl⟩ := slot_surjective j
  unfold dispatch at step
  cases hs : wireStep (s.response (slot i)) (t.response (slot i)) (stages (slot i)) m with
  | none => simp [hs] at step
  | some q =>
    simp only [hs, Option.map_some, Option.some.injEq] at step
    subst next
    obtain ⟨client, run, hi, other⟩ := client_local state i (align i) hs
    refine ⟨client, ?_, ?_⟩
    · cases i <;> simpa [clientMoves, slot] using run
    · intro j
      by_cases e : j = i
      · subst j; simpa [updateStage] using hi
      · simpa [updateStage, (slot_inj j i).not.mpr e, other j e] using align j

/-- Local visibility/stuttering laws lift to every finite prefix, including
repeated uses of a slot after delivery. -/
theorem client_path (h : Path (dispatch s t) start wire finish)
    (align : Fits start state) :
    ∃ client, OverlappingQueries.execute state (clientHistory wire) = some client ∧ Fits finish client := by
  induction h generalizing state with
  | nil => exact ⟨state, rfl, align⟩
  | cons hs ht ih =>
    obtain ⟨mid, run, hm⟩ := client_step state align hs
    obtain ⟨client, rest, hf⟩ := ih hm
    refine ⟨client, ?_, hf⟩
    change OverlappingQueries.execute state (clientMoves _ ++ clientHistory _) = some client
    rw [native_execute_append, run]
    exact rest

/-- Accepted diagnostic replay never rejects a legal pending external prefix. -/
theorem client_accepted (h : inspect s t wire = some d) :
    ∃ state, OverlappingQueries.execute initial (clientHistory wire) = some state ∧ Fits d.stages state := by
  have paths := (inspect_characterization.mp h).2
  exact client_path (assemble paths) (by intro i; simp [FitsSlot, initial])

theorem external_accepted (h : inspect s t wire = some d) : ∃ out, d.external = some out := by
  obtain ⟨state, run, _⟩ := client_accepted h
  refine ⟨observe state (clientHistory wire), ?_⟩
  rw [projection_history h]
  change (OverlappingQueries.execute initial ((hide wire).flatMap clientEvent)).map _ = _
  rw [← clientHistory_hiding, run]
  rfl

/-- A buffered internal reply still belongs to a pending client request until
A delivery. The proof uses the actual path/native-state alignment. -/
theorem buffered_pending (h : inspect s t wire = some d) (i : Bool) (value : Bool)
    (buffered : d.stages (slot i) = .cAnswered value ∨ d.stages (slot i) = .bAnswered value) :
    ∃ out, d.external = some out ∧ (if i then out.right else out.left) = .pending := by
  obtain ⟨state, run, align⟩ := client_accepted h
  have pending : state i = .pending := by
    have hi := align i
    rcases buffered with buffered | buffered <;> simpa [FitsSlot, buffered] using hi
  refine ⟨observe state (clientHistory wire), ?_, ?_⟩
  · rw [projection_history h]
    change (OverlappingQueries.execute initial ((hide wire).flatMap clientEvent)).map _ = _
    rw [← clientHistory_hiding, run]
    rfl
  · cases i <;> exact pending

/-- Native external state is uniquely determined, even though stage alone cannot
recover it. The original native evaluator supplies this determinism. -/
theorem client_unique
    (h : OverlappingQueries.execute initial (clientHistory wire) = some first)
    (k : OverlappingQueries.execute initial (clientHistory wire) = some second) : first = second :=
  Option.some.inj (h.symm.trans k)

/-- A client-hidden event stutters at that boundary; it need not be hidden at
the relay boundary (for example, a C service reply). -/
theorem client_stutter (hidden : clientMoves event = []) :
    clientHistory (wire ++ [event]) = clientHistory wire := by
  simp [clientHistory, List.flatMap_append, hidden]

theorem external_stutter (hidden : clientMoves event = []) :
    observeWire (wire ++ [event]) = observeWire wire := by
  simp only [observeWire, observeRelay, ← clientHistory_hiding, client_stutter hidden]

theorem visible_step (run : OverlappingQueries.execute initial (clientHistory wire) = some state)
    (visible : clientMoves event = [move])
    (step : OverlappingQueries.step state move = some next) :
    OverlappingQueries.execute initial (clientHistory (wire ++ [event])) = some next := by
  simp only [clientHistory, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  unfold clientHistory at run
  rw [visible, native_execute_append, run]
  simp [OverlappingQueries.execute, step]

/-- The schedule-boundary consumer is recovered without changing its assumptions. -/
theorem caller_recovery (h : inspect negate negate (network negate negate q) = some d) :
    d.external = native q := (projection_history h).trans (implementation_observation q)

/-- Reject malformed wire inputs before projecting externally. -/
def runClient (s t : Strategy arena) (wire : Wire) : Output :=
  (inspect s t wire).bind Detailed.external

theorem runClient_projection (h : inspect s t wire = some d) :
    runClient s t wire = observeWire wire := by
  simp only [runClient, h, Option.bind_some, projection_history h]

theorem caller_rejection (h : native q = none) :
    inspect negate negate (network negate negate q) = none := by
  cases run : inspect negate negate (network negate negate q) with
  | none => rfl
  | some d =>
    obtain ⟨out, valid⟩ := external_accepted run
    have invalid := (caller_recovery run).trans h
    rw [invalid] at valid
    cases valid

/-- Existing schedule semantics, including rejection, are unchanged. -/
theorem runClient_caller (q : List (Bool × Bool)) :
    runClient negate negate (network negate negate q) = native q := by
  cases hn : native q with
  | none => simp only [runClient, caller_rejection hn, Option.bind_none]
  | some out =>
    obtain ⟨d, hd⟩ := (accepted_iff negate negate _).mpr (network_legal _ _ hn)
    exact (runClient_projection hd).trans ((implementation_observation q).trans hn)

end Interaction.PrefixDiagnostics

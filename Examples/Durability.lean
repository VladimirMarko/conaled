import Applications.Durability.ResourceEvents

/-! Checked accepted-history executions and fault cases for #240. -/
namespace Examples.Durability
open _root_.Durability
open Interaction.Events

def first : Record Nat := ⟨7, 10, 4⟩
def second : Record Nat := ⟨7, 11, 9⟩
def conflict : Record Nat := ⟨7, 10, 8⟩

def firstPlan : Plan Nat := appendPlan (fun _ => none) emptyRoot [] (empty_rep _) 0 first rfl
abbrev prepared := prepareState (invokeState (initial : Machine Nat) first) firstPlan
abbrev written := writeState prepared 0 (.node none first)
abbrev durable := persistState written 0 (.node none first)
abbrev committed := publishState durable firstPlan
abbrev accepted := acknowledgeState committed

def appendEvents (e : Record Nat) : List (Event Nat) :=
  [.invoke e, .internal, .internal, .internal, .commit e, .acknowledge e]

theorem first_execution : interpret Step (appendEvents first) initial accepted :=
  append_execution initial [] rfl rfl rfl (empty_rep _) 0 first rfl (by simp [initial])
    (by simp [Fresh])

theorem accepted_rep : Represents accepted.disk accepted.root [first] :=
  append_rep (empty_rep (fun _ => none)) 0 first rfl

/-- Both phases before publication leave the committed history empty, including
when the new cell itself has already become durable. -/
theorem before_commit_crash :
    Represents (crashState written).disk (crashState written).root [] ∧
    Represents (crashState durable).disk (crashState durable).root [] :=
  ⟨empty_rep _, empty_rep _⟩

theorem after_commit_lost_ack : Step .crash committed (crashState committed) ∧
    Represents (crashState committed).disk (crashState committed).root [first] :=
  ⟨.crash, accepted_rep⟩

theorem retry_without_append :
    interpret Step [.invoke first, .acknowledge first] accepted accepted := by
  exact ⟨invokeState accepted first, .invoke rfl rfl rfl,
    accepted, .acknowledge (h := [first]) rfl rfl rfl (by simp), rfl⟩

theorem conflicting_retry_rejects :
    interpret Step [.invoke conflict, .reject conflict] accepted accepted := by
  exact ⟨invokeState accepted conflict, .invoke rfl rfl rfl,
    accepted, .reject (r := first) (h := [first]) rfl rfl rfl (by simp) rfl (by decide), rfl⟩

def cp : Plan Nat := checkpointPlan accepted.disk [first] 10
abbrev copying := prepareState accepted cp
abbrev copied := writeState copying 10 (.flat first)
abbrev partlyRetained := persistState copied 10 (.flat first)
abbrev indexed := writeState partlyRetained 11 (.index [10])
abbrev fullyRetained := persistState indexed 11 (.index [10])
abbrev checkpointed := publishState fullyRetained cp

theorem prepare_checkpoint : Step .internal accepted copying := by
  apply Step.prepare (s := accepted) (p := cp) rfl rfl rfl rfl rfl
  · intro e eq; cases eq
  · intro i c hw
    by_cases ten : i = 10
    · subst i; simp [initial, firstPlan, appendPlan, put]
    by_cases eleven : i = 11
    · subst i; simp [initial, firstPlan, appendPlan, put]
    · simp [cp, checkpointPlan, checkpointWrites, copy, put, ten, eleven] at hw

theorem copy_record : Step .internal copying copied := .write rfl (by decide)
theorem persist_record : Step .internal copied partlyRetained := .persist rfl (by decide) rfl (Or.inl rfl)
theorem copy_index : Step .internal partlyRetained indexed := .write rfl (by decide)
theorem persist_index : Step .internal indexed fullyRetained := .persist rfl (by decide) rfl (Or.inl rfl)

theorem publish_checkpoint : Step .internal fullyRetained checkpointed := by
  apply Step.publish (p := cp) rfl
  intro i c hw
  by_cases ten : i = 10
  · subst i; simpa [cp, checkpointPlan, checkpointWrites, copy, put, addresses, List.range',
      fullyRetained, indexed, partlyRetained, copied, copying] using hw
  by_cases eleven : i = 11
  · subst i; simpa [cp, checkpointPlan, checkpointWrites, copy, put, addresses, List.range',
      fullyRetained, indexed, partlyRetained, copied, copying] using hw
  · simp [cp, checkpointPlan, checkpointWrites, copy, put, ten, eleven] at hw

theorem checkpoint_execution : interpret Step (List.replicate 6 .internal) accepted checkpointed :=
  ⟨copying, prepare_checkpoint, copied, copy_record, partlyRetained, persist_record,
    indexed, copy_index, fullyRetained, persist_index, checkpointed, publish_checkpoint, rfl⟩

theorem checkpoint_representation : Represents checkpointed.disk checkpointed.root [first] := by
  exact ⟨[first], [], .block (as := [10]) (by decide) (.cons (by decide) .nil), .nil, rfl⟩

/-- Interrupted copying preserves the old log, even after a copied cell persists. -/
theorem interrupted_checkpoint :
    Step .crash partlyRetained (crashState partlyRetained) ∧
    Represents (crashState partlyRetained).disk (crashState partlyRetained).root [first] := by
  refine ⟨.crash, ?_⟩
  exact ⟨[], [first], .nil, .snoc (by decide) .nil, rfl⟩

abbrev reclaimed : Machine Nat := { checkpointed with disk := cp.writes }

theorem safe_reclamation : Step .internal checkpointed reclaimed := by
  apply Step.reclaim (s := checkpointed) rfl rfl rfl
  · intro a c needed found
    rcases needed with ⟨i, ptr, ref⟩ | link
    · have iEq : i = 11 := Option.some.inj ptr.symm
      subst i
      rcases ref with rfl | ⟨as, lookup, mem⟩
      · exact found
      · have eq : as = [10] := (Cell.index.inj (Option.some.inj lookup)).symm
        subst as
        have eq : a = 10 := by simpa using mem
        subst a
        exact found
    · cases link
  · intro i c hw
    by_cases ten : i = 10
    · subst i; exact hw
    by_cases eleven : i = 11
    · subst i; exact hw
    · simp [cp, checkpointPlan, checkpointWrites, copy, put, ten, eleven] at hw

/-- Reclaiming the old cell before installing the new root destroys recovery. -/
theorem early_reclamation : ¬ Represents (cp.writes) accepted.root [first] := by
  intro rep
  obtain ⟨pre, tail, hp, ht, eq⟩ := rep
  cases hp
  cases ht with
  | snoc lookup prev => contradiction

abbrev restart := crashState reclaimed
abbrev reading := { restart with cursor := some (Cursor.prefixCells [10] [] none) }
abbrev readRecord := { reading with cursor := some (Cursor.prefixCells [] [first] none) }
abbrev readTail := { readRecord with cursor := some (Cursor.tailCells none [first] []) }
abbrev doneRead := { readTail with cursor := some (Cursor.done [first]) }
abbrev recovered := { doneRead with cache := some [first], cursor := none }

theorem recovery_execution : interpret Step
    [.internal, .internal, .internal, .internal, .recover [first]] restart recovered := by
  exact ⟨reading, .startRead rfl rfl (.checkpoint rfl (by decide)),
    readRecord, .read rfl rfl (.flat (by decide)), readTail, .read rfl rfl .boundary,
    doneRead, .read rfl rfl .finish, recovered, .recover rfl rfl, rfl⟩

/-- Restarting midway loses only the volatile cursor and permits the same scan. -/
theorem repeated_recovery_crash : Step .crash readRecord restart ∧
    interpret Step [.internal, .internal, .internal, .internal, .recover [first]] restart recovered :=
  ⟨.crash, recovery_execution⟩

def afterAck : List (Event Nat) := List.replicate 6 .internal ++ [.internal, .crash] ++
  [.internal, .internal, .internal, .internal, .recover [first]]
def beforeAck : List (Event Nat) := [.invoke first, .internal, .internal, .internal, .commit first]

theorem accepted_recovered_execution :
    interpret Step (beforeAck ++ .acknowledge first :: afterAck) initial recovered := by
  have rest : interpret Step afterAck accepted recovered := by
    rw [afterAck, interpret_append, interpret_append]
    exact ⟨restart, ⟨checkpointed, checkpoint_execution,
      reclaimed, safe_reclamation, restart, Step.crash, rfl⟩, recovery_execution⟩
  have combined : interpret Step (appendEvents first ++ afterAck) initial recovered := by
    rw [interpret_append]
    exact ⟨accepted, first_execution, rest⟩
  exact combined

theorem acknowledged_client_after_recovery : first ∈ ([first] : List (Record Nat)) :=
  acknowledged_client beforeAck afterAck first recovered accepted_recovered_execution [first] rfl

theorem encoded_acknowledged_after_recovery : first ∈ ([first] : List (Record Nat)) :=
  encoded_acknowledged_client wordCodec beforeAck afterAck first
    (encodeState wordCodec recovered) (encode_script wordCodec accepted_recovered_execution) [first] rfl

theorem early_acknowledgment (t : Machine Nat) : ¬ Step (.acknowledge first) written t := by
  have rel : Related written ⟨[], some first, true⟩ := by
    refine { root := empty_rep _, cache := rfl, active := rfl, pending := ?_, cursor := ?_, cursor_offline := ?_, offline_pending := ?_, offline_active := ?_ }
    · intro p hp
      have eq : p = firstPlan := (Option.some.inj hp).symm
      subst p
      refine ⟨rfl, rfl, ?_, ?_, rfl⟩
      · intro i c impossible; cases impossible
      · simp [Fresh]
    · simp [initial]
    · simp [initial]
    · simp
    · simp
  intro step
  obtain ⟨a, spec, rel'⟩ := step.simulation rel
  cases spec with
  | acknowledge online active mem => simp at mem

/-- Actual encoded primitive transitions execute the same checkpoint and recovery. -/
theorem encoded_checkpoint : interpret (EncodedStep wordCodec) (List.replicate 6 .internal)
    (encodeState wordCodec accepted) (encodeState wordCodec checkpointed) :=
  encode_script wordCodec checkpoint_execution

theorem encoded_recovery : interpret (EncodedStep wordCodec)
    [.internal, .internal, .internal, .internal, .recover [first]]
    (encodeState wordCodec restart) (encodeState wordCodec recovered) :=
  encode_script wordCodec recovery_execution

example : (encodeState wordCodec reclaimed).disk 11 = some [3, 1, 10] := rfl
example : wordCodec.decode [3, 2, 10] = none := malformed_length

theorem ready_related (s : Machine Nat) (h : List (Record Nat))
    (rep : Represents s.disk s.root h) (cache : s.cache = some h)
    (active : s.active = none) (pending : s.pending = none) (cursor : s.cursor = none) :
    Related s ⟨h, none, true⟩ := by
  refine { root := rep, cache := cache, active := active, pending := ?_, cursor := ?_, cursor_offline := ?_, offline_pending := ?_, offline_active := ?_ } <;> simp [pending, cursor]

/-- One unchanged order-sensitive client for a log and for a checkpoint/tail.
The worked expectation 49 is the decimal fold of payloads 4 then 9. -/
theorem append_second_client (s : Machine Nat)
    (rep : Represents s.disk s.root [first]) (cache : s.cache = some [first])
    (active : s.active = none) (pending : s.pending = none) (cursor : s.cursor = none)
    (space : s.disk 20 = none) (unused : 20 ∉ s.used) :
    ∃ t, interpret Step (appendEvents second) s t ∧
      t.cache = some [first, second] ∧
      Represents t.disk t.root [first, second] ∧
      ([first, second].foldl (fun n e => n * 10 + e.payload) 0 = 49) ∧
      interpret (EncodedStep wordCodec) (appendEvents second) (encodeState wordCodec s)
        (encodeState wordCodec t) := by
  have run := append_execution s [first] cache active pending rep 20 second space unused
    (by intro r mem; simp only [List.mem_singleton] at mem; subst r; decide)
  obtain ⟨a, spec, rel⟩ := script_simulation _ (ready_related s [first] rep cache active pending cursor) run
  have ready : _ = some [first, second] := rfl
  have hist := (rel.ready ready).2
  have folded := rel.fold ready (fun n e => n * 10 + e.payload) 0
  refine ⟨_, run, ready, ?_, ?_, encode_script wordCodec run⟩
  · exact hist ▸ rel.root
  · rw [← hist] at folded
    exact folded.trans rfl

theorem log_two_records : ∃ t, interpret Step (appendEvents second) accepted t ∧
    t.cache = some [first, second] ∧ Represents t.disk t.root [first, second] ∧
    [first, second].foldl (fun n e => n * 10 + e.payload) 0 = 49 ∧
    interpret (EncodedStep wordCodec) (appendEvents second) (encodeState wordCodec accepted)
      (encodeState wordCodec t) :=
  append_second_client accepted accepted_rep rfl rfl rfl rfl rfl
    (by simp [initial, firstPlan, appendPlan, put])

theorem checkpoint_tail_two_records : ∃ t, interpret Step (appendEvents second) recovered t ∧
    t.cache = some [first, second] ∧ Represents t.disk t.root [first, second] ∧
    [first, second].foldl (fun n e => n * 10 + e.payload) 0 = 49 ∧
    interpret (EncodedStep wordCodec) (appendEvents second) (encodeState wordCodec recovered)
      (encodeState wordCodec t) := by
  apply append_second_client recovered
  · exact ⟨[first], [], .block (as := [10]) rfl (.cons rfl .nil), .nil, rfl⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [initial, cp, checkpointPlan, checkpointWrites, copy, firstPlan, appendPlan, put]

/-- Publishing a tip before its cell persists cannot reconstruct even one record. -/
theorem early_publication : ¬ Represents (fun _ => none : Heap (Cell Nat)) ⟨none, some 0⟩ [first] := by
  rintro ⟨pre, tail, hp, ht, eq⟩
  cases hp
  cases ht with
  | snoc lookup prev => cases lookup

/-- Without retained or external evidence the same reboot observation cannot
answer both the empty execution and the acknowledged one correctly. -/
theorem no_retained_evidence : ¬ ∃ query : Unit → List (Record Nat),
    query () = [] ∧ query () = [first] := by
  rintro ⟨query, empty, one⟩
  rw [empty] at one
  cases one

/-- Local durable updates do not supply the joint transfer invariant. -/
theorem partial_transfer : (9 + 0 : Nat) ≠ 10 ∧ (9 + 1 : Nat) = 10 := by decide

/-- The two balances are payload fields of one immutable retained object. -/
def oldBalances : Record (Nat × Nat) := ⟨1, 0, (10, 0)⟩
def newBalances : Record (Nat × Nat) := ⟨1, 1, (9, 1)⟩
def jointOld : Heap (Cell (Nat × Nat)) := put (fun _ => none) 0 (.node none oldBalances)
def jointNew : Heap (Cell (Nat × Nat)) := put jointOld 1 (.node (some 0) newBalances)

theorem joint_old_rep : Represents jointOld ⟨none, some 0⟩ [oldBalances] :=
  append_rep (empty_rep _) 0 oldBalances rfl

theorem joint_new_rep : Represents jointNew ⟨none, some 1⟩ [oldBalances, newBalances] :=
  append_rep joint_old_rep 1 newBalances rfl

/-- Exclusive atomic root installation selects a complete retained old/new
object. Recovery uniqueness derives the result from the cells; the conclusion
is not assumed as a storage postcondition. Separate roots permit (9,0). -/
theorem shared_root_transfer (root : Root) (h : List (Record (Nat × Nat)))
    (atomic : root = ⟨none, some 0⟩ ∨ root = ⟨none, some 1⟩)
    (recoveredHistory : Represents jointNew root h) :
    (h.foldl (fun _ e => e.payload) (10, 0)).1 +
      (h.foldl (fun _ e => e.payload) (10, 0)).2 = 10 := by
  rcases atomic with rfl | rfl
  · have rep := joint_old_rep.mono (extends_put jointOld 1 (.node (some 0) newBalances) rfl)
    rw [recoveredHistory.unique rep]
    rfl
  · rw [recoveredHistory.unique joint_new_rep]
    rfl

/-- Two independently admitted directed edges form a cycle after union. -/
def edgeAB (a b : Bool) : Prop := a = false ∧ b = true
def edgeBA (a b : Bool) : Prop := a = true ∧ b = false

theorem concurrent_cycle : (¬ ∃ a b c, edgeAB a b ∧ edgeAB b c) ∧
    (¬ ∃ a b c, edgeBA a b ∧ edgeBA b c) ∧
    ∃ a b, (edgeAB a b ∨ edgeBA a b) ∧ (edgeAB b a ∨ edgeBA b a) := by
  constructor
  · simp [edgeAB]
  constructor
  · simp [edgeBA]
  · exact ⟨false, true, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩

/-- The copied record's buffered write and persistence have distinct charges. -/
example : StorageStep [.write] copying copied := .write rfl (by decide)
example : StorageStep [.persist] copied partlyRetained := .persist rfl (by decide) rfl (Or.inl rfl)
example : StorageStep [.readRoot, .readDescriptor] restart reading :=
  .readCheckpointRoot rfl rfl rfl (by decide)
example : StorageStep [.readRecord] reading readRecord := .readFlat (s := reading) (a := 10) (e := first) rfl rfl (by decide)

example (weight : StorageEvent → Nat) :
    weighted weight [.write, .persist, .write, .persist, .installRoot] =
      2 * weight .write + 2 * weight .persist + weight .installRoot := by
  simp [weighted]
  omega

end Examples.Durability

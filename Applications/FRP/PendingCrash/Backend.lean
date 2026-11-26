import Applications.FRP.PendingCrash.Refinement
/-! Agreement of the actual native backend with the selected durable frame,
including prepared-owner provenance until root publication and the exact
comparison with native checkpoint conversion and business suffixes. -/
namespace FRPSpec.PendingCrash
open PendingMigration

def backendView (backend : Migration.Backend) : Migration.Kind × Bool :=
  (backend.kind, backend.logical)

def frameBackendView (frame : Frame) : Migration.Kind × Bool :=
  (frame.kind, frame.logical)

structure BackendAgreement (s : System) : Prop where
  active : s.adapter.active.map backendView = s.adapter.current.map frameBackendView
  prepared : ∀ target, s.adapter.prepared = some target →
    ∃ frame, s.adapter.current = some frame ∧ target.logical = frame.logical

theorem BackendAgreement.initial (kind : Migration.Kind) : BackendAgreement (initialSystem kind) := by
  constructor
  · simp [initialSystem,backendView,frameBackendView,initialFrame]
  · intro target impossible; cases impossible

theorem BackendAgreement.active_eq (s : System) (frame : Frame) (backend : Migration.Backend)
    (agreement : BackendAgreement s) (current : s.adapter.current = some frame)
    (active : s.adapter.active = some backend) :
    backend.kind = frame.kind ∧ backend.logical = frame.logical := by
  simpa [current,active,backendView,frameBackendView] using agreement.active

theorem BackendAgreement.active_exists (s : System) (frame : Frame)
    (agreement : BackendAgreement s) (current : s.adapter.current = some frame) :
    ∃ backend, s.adapter.active = some backend ∧ backend.kind = frame.kind ∧ backend.logical = frame.logical := by
  cases active : s.adapter.active with
  | none => have incompatible := agreement.active; simp [current,active] at incompatible
  | some backend => exact ⟨backend,rfl,agreement.active_eq s frame backend current active⟩

theorem BackendAgreement.congr (s t : System) (agreement : BackendAgreement s)
    (current : t.adapter.current = s.adapter.current)
    (active : t.adapter.active = s.adapter.active)
    (prepared : t.adapter.prepared = s.adapter.prepared) : BackendAgreement t := by
  constructor
  · simpa only [active,current] using agreement.active
  · intro target present
    obtain ⟨frame,found,logical⟩ := agreement.prepared target (prepared ▸ present)
    exact ⟨frame,current.trans found,logical⟩

theorem beginChange_backend (s : System) (command : FrameCommand) (agreement : BackendAgreement s) :
    BackendAgreement (beginChange s command).system := by
  unfold beginChange
  repeat' first | exact agreement | exact ⟨agreement.active,agreement.prepared⟩ | split

theorem crash_backend (s : System) : BackendAgreement (crash s).system := by
  constructor
  · rfl
  · intro target impossible; cases impossible

theorem advance_propose_backend (before after : Frame) (command : FrameCommand)
    (changed : advance before command = .changed after) : propose before command = .changed after := by
  unfold advance at changed
  cases proposed : propose before command <;> simp only [proposed] at changed
  · contradiction
  · contradiction
  · split at changed
    · cases changed; rfl
    · contradiction

theorem advance_tick_backend (before after : Frame)
    (changed : advance before .tickCommit = .changed after) :
    ∃ slot request, before.head = some (slot,request) ∧ request.phase = .confirmed ∧
      after = {(before.update slot {request with phase := .committed}) with logical := request.input} := by
  have proposed := advance_propose_backend before after .tickCommit changed
  simp only [propose] at proposed
  split at proposed
  · contradiction
  · rename_i slot request head
    split at proposed
    · rename_i ready
      cases proposed
      exact ⟨slot,request,head,by simpa using ((Bool.and_eq_true _ _).mp ready).1,rfl⟩
    · contradiction

theorem advance_migration_backend (before after : Frame) (kind : Migration.Kind)
    (changed : advance before (.migrate kind) = .changed after) :
    after = {before with kind := kind} := by
  have proposed := advance_propose_backend before after (.migrate kind) changed
  exact (Decision.changed.inj proposed).symm

theorem applyJournal_tick_selected (s : System) (result : JournalResult s.adapter.journal)
    (record : Durability.Record Frame) (before : Frame) (backend : Migration.Backend)
    (slot : Bool) (request : Request)
    (event : result.event = .commit record) (cause : s.adapter.pendingCause = some .tickCommit)
    (current : s.adapter.current = some before) (active : s.adapter.active = some backend)
    (head : before.head = some (slot,request)) :
    (applyJournal s (.done result)).system.adapter.active =
      some (Migration.evaluate backend request.input).candidate := by
  simp [applyJournal,event,cause,current,active,head]

theorem applyJournal_migration_selected (s : System) (result : JournalResult s.adapter.journal)
    (record : Durability.Record Frame) (kind : Migration.Kind) (old target : Migration.Backend)
    (event : result.event = .commit record) (cause : s.adapter.pendingCause = some (.migrate kind))
    (active : s.adapter.active = some old) (prepared : s.adapter.prepared = some target)
    (kindEq : target.kind = record.payload.kind) (logicalEq : target.logical = record.payload.logical) :
    let after := (applyJournal s (.done result)).system
    after.adapter.active = some target ∧ after.adapter.prepared = none ∧
      after.adapter.retired = old :: s.adapter.retired := by
  simp [applyJournal,event,cause,active,prepared,kindEq,logicalEq]

theorem applyJournal_tick_backend (s : System) (result : JournalResult s.adapter.journal)
    (record : Durability.Record Frame) (before : Frame)
    (agreement : BackendAgreement s) (event : result.event = .commit record)
    (cause : s.adapter.pendingCause = some .tickCommit) (current : s.adapter.current = some before)
    (unprepared : s.adapter.prepared = none)
    (changed : advance before .tickCommit = .changed record.payload) :
    BackendAgreement (applyJournal s (.done result)).system := by
  obtain ⟨backend,active,kindEq,logicalEq⟩ := agreement.active_exists s before current
  obtain ⟨slot,request,head,phase,payload⟩ := advance_tick_backend before record.payload changed
  constructor
  · simp [applyJournal,event,cause,current,active,head,backendView,frameBackendView,payload,
      Frame.update,(Migration.evaluate backend request.input).kind_eq,
      (Migration.evaluate backend request.input).state_eq,kindEq]
  · intro target impossible
    simp [applyJournal,event,cause,current,active,head,unprepared] at impossible

theorem applyJournal_migration_backend (s : System) (result : JournalResult s.adapter.journal)
    (record : Durability.Record Frame) (before : Frame) (kind : Migration.Kind) (target : Migration.Backend)
    (agreement : BackendAgreement s) (event : result.event = .commit record)
    (cause : s.adapter.pendingCause = some (.migrate kind)) (current : s.adapter.current = some before)
    (prepared : s.adapter.prepared = some target) (selectedKind : target.kind = kind)
    (changed : advance before (.migrate kind) = .changed record.payload) :
    BackendAgreement (applyJournal s (.done result)).system := by
  obtain ⟨backend,active,oldKind,oldLogical⟩ := agreement.active_exists s before current
  obtain ⟨frame,found,targetLogical⟩ := agreement.prepared target prepared
  have same : frame = before := Option.some.inj (found.symm.trans current)
  subst frame
  have payload := advance_migration_backend before record.payload kind changed
  constructor
  · simp [applyJournal,event,cause,active,prepared,payload,selectedKind,targetLogical,
      backendView,frameBackendView]
  · intro other impossible
    simp [applyJournal,event,cause,active,prepared,payload,selectedKind,targetLogical] at impossible

theorem applyJournal_recover_backend (s : System) (result : JournalResult s.adapter.journal)
    (history : List (Durability.Record Frame)) (frame : Frame)
    (agreement : BackendAgreement s) (event : result.event = .recover history)
    (validated : (validateMeasured (initialFrame s.adapter.initialKind) (history.map Durability.Record.payload)).1 = some frame)
    (stable : ∀ before, s.adapter.current = some before → frame.logical = before.logical) :
    BackendAgreement (applyJournal s (.done result)).system := by
  constructor
  · simp [applyJournal,event,validated,backendView,frameBackendView]
  · intro target present
    have retained : s.adapter.prepared = some target := by
      simpa [applyJournal,event,validated] using present
    obtain ⟨before,current,logical⟩ := agreement.prepared target retained
    refine ⟨frame,?_,logical.trans (stable before current).symm⟩
    simp [applyJournal,event,validated]


theorem native_prepare_active (active : Migration.Backend) (kind : Migration.Kind)
    (budget : Nat) (allocation validation : Bool) :
    (PendingMigration.step {active := active} (.prepare kind budget allocation validation)).session.active = active := by
  simp only [PendingMigration.step]
  repeat' first | rfl | split

theorem native_prepare_logical (active target : Migration.Backend) (kind : Migration.Kind)
    (budget : Nat) (allocation validation : Bool)
    (selected : (PendingMigration.step {active := active} (.prepare kind budget allocation validation)).session.prepared.map
      (fun prepared => prepared.target) = some target) : target.logical = active.logical := by
  let result := PendingMigration.step ({active := active} : PendingMigration.Session) (.prepare kind budget allocation validation)
  have unchanged : result.session.active = active := native_prepare_active active kind budget allocation validation
  change result.session.prepared.map (fun prepared => prepared.target) = some target at selected
  cases stored : result.session.prepared with
  | none => simp [stored] at selected
  | some prepared =>
    simp only [stored,Option.map_some,Option.some.injEq] at selected
    rw [← selected]
    exact prepared.continuation.trans (congrArg Migration.Backend.logical unchanged)

theorem prepareMigration_backend (s : System) (kind : Migration.Kind) (budget : Nat)
    (allocation validation : Bool) (agreement : BackendAgreement s) :
    BackendAgreement (prepareMigration s kind budget allocation validation).system := by
  unfold prepareMigration
  split
  · exact agreement
  · cases active : s.adapter.active with
    | none => exact agreement
    | some backend =>
      cases current : s.adapter.current with
      | none => have incompatible := agreement.active; simp [active,current] at incompatible
      | some frame =>
        have logical := (agreement.active_eq s frame backend current active).2
        constructor
        · exact agreement.active
        · intro target selected
          have targetLogical := native_prepare_logical backend target kind
            (budget - localReservations s) allocation validation selected
          exact ⟨frame,current,targetLogical.trans logical⟩


theorem receive_backend_unchanged (before after : Frame) (receipt : Receipt)
    (changed : receive before receipt = .changed after) :
    frameBackendView after = frameBackendView before := by
  unfold receive at changed
  repeat' first | split at changed | contradiction
  all_goals cases changed
  all_goals rfl

theorem advance_backend_unchanged (before after : Frame) (command : FrameCommand)
    (changed : advance before command = .changed after)
    (notTick : command ≠ .tickCommit) (notMigration : ∀ kind, command ≠ .migrate kind) :
    frameBackendView after = frameBackendView before := by
  have proposed := advance_propose_backend before after command changed
  cases command with
  | receive receipt => exact receive_backend_unchanged before after receipt proposed
  | tickCommit => exact False.elim (notTick rfl)
  | migrate kind => exact False.elim (notMigration kind rfl)
  | accept input | evaluate | close | release =>
    simp only [propose] at proposed
    repeat' first | split at proposed | contradiction
    all_goals cases proposed
    all_goals rfl

theorem applyJournal_ordinary_backend (s : System) (result : JournalResult s.adapter.journal)
    (record : Durability.Record Frame) (before : Frame) (command : FrameCommand)
    (agreement : BackendAgreement s) (event : result.event = .commit record)
    (cause : s.adapter.pendingCause = some command) (current : s.adapter.current = some before)
    (changed : advance before command = .changed record.payload)
    (notTick : command ≠ .tickCommit) (notMigration : ∀ kind, command ≠ .migrate kind) :
    BackendAgreement (applyJournal s (.done result)).system := by
  have views := advance_backend_unchanged before record.payload command changed notTick notMigration
  have logical : record.payload.logical = before.logical := congrArg Prod.snd views
  have currentActive : s.adapter.active.map backendView = some (frameBackendView record.payload) := by
    rw [agreement.active,current,Option.map_some,views]
  have prepared : ∀ target, s.adapter.prepared = some target →
      ∃ frame, some record.payload = some frame ∧ target.logical = frame.logical := by
    intro target present
    obtain ⟨frame,found,value⟩ := agreement.prepared target present
    have same : frame = before := Option.some.inj (found.symm.trans current)
    subst frame
    exact ⟨record.payload,rfl,value.trans logical.symm⟩
  cases command <;> try contradiction
  case migrate kind => exact False.elim (notMigration kind rfl)
  all_goals constructor
  all_goals first
    | simpa only [applyJournal,event,cause,Option.map_some] using currentActive
    | simpa only [applyJournal,event,cause] using prepared

theorem applyJournal_failed_recover_backend (s : System) (result : JournalResult s.adapter.journal)
    (history : List (Durability.Record Frame)) (event : result.event = .recover history)
    (validated : (validateMeasured (initialFrame s.adapter.initialKind) (history.map Durability.Record.payload)).1 = none)
    (unprepared : s.adapter.prepared = none) : BackendAgreement (applyJournal s (.done result)).system := by
  constructor
  · simp [applyJournal,event,validated]
  · intro target impossible
    simp [applyJournal,event,validated,unprepared] at impossible


def PendingOnline (s : System) : Prop :=
  s.adapter.pendingCause.isSome = true → s.adapter.current.isSome = true

theorem PendingOnline.initial (kind : Migration.Kind) : PendingOnline (initialSystem kind) := by
  intro impossible
  cases impossible

theorem beginChange_pendingOnline (s : System) (command : FrameCommand) (online : PendingOnline s) :
    PendingOnline (beginChange s command).system := by
  unfold beginChange
  repeat' first | exact online | split
  all_goals simp_all [PendingOnline]

theorem applyJournal_pendingOnline (s : System) (attempt : JournalAttempt s.adapter.journal)
    (a : Durability.Abstract Frame) (stable : Frame) (inv : RuntimeInvariant s a stable)
    (online : PendingOnline s) : PendingOnline (applyJournal s attempt).system := by
  cases attempt with
  | failed work => exact online
  | done result =>
    obtain ⟨b,source,relation⟩ := result.native.simulation inv.related
    have recovered := inv.frames.recovered source
    unfold applyJournal
    cases event : result.event <;> simp only [event] at recovered ⊢
    all_goals try exact online
    case commit record => repeat' first | (intro _; rfl) | split
    case acknowledge record => intro impossible; cases impossible
    case recover history =>
      have validated : (validateMeasured (initialFrame s.adapter.initialKind)
          (history.map Durability.Record.payload)).1 = some stable := by
        rw [validateMeasured_eq]; exact recovered
      simp only [validated]
      intro _; rfl

theorem pushLocal_pendingOnline (s : System) (message : Message) (online : PendingOnline s) :
    PendingOnline (pushLocal s message).system := by
  unfold pushLocal
  dsimp only
  split <;> exact online

theorem pushCancellation_pendingOnline (s : System) (identity : Nat) (input : Bool)
    (online : PendingOnline s) : PendingOnline (pushCancellation s identity input).system := by
  unfold pushCancellation
  dsimp only
  split <;> exact online

theorem sendFor_pendingOnline (s : System) (identity : Nat) (command : Send)
    (online : PendingOnline s) : PendingOnline (sendFor s identity command).system := by
  unfold sendFor
  repeat' first | exact online | exact pushLocal_pendingOnline s _ online | exact pushCancellation_pendingOnline s _ _ online | split
  all_goals dsimp only
  all_goals repeat' first | exact online | exact pushLocal_pendingOnline s _ online | exact pushCancellation_pendingOnline s _ _ online | split

theorem handle_pendingOnline (s : System) (online : PendingOnline s) :
    PendingOnline (handle s).system := by
  unfold handle
  split
  · exact online
  · split
    · rename_i receipt rest queueEq
      let queue : LocalQueue := ⟨rest, by have := s.adapter.queue.bounded; rw [queueEq] at this; simp only [List.length_cons] at this; omega⟩
      let popped := {s with adapter := {s.adapter with queue := queue}}
      have poppedOnline : PendingOnline popped := online
      have beginOnline := fun command => beginChange_pendingOnline popped command poppedOnline
      have sendOnline := fun identity command => sendFor_pendingOnline popped identity command poppedOnline
      dsimp only
      repeat' first | exact poppedOnline | exact beginOnline _ | exact sendOnline _ _ | split
    · exact online

theorem step_pendingOnline (s : System) (a : Durability.Abstract Frame) (stable : Frame)
    (command : Command) (inv : RuntimeInvariant s a stable) (online : PendingOnline s) :
    PendingOnline (step s command).system := by
  cases command with
  | «local» action =>
    simp only [step,localCommand]
    repeat' first | exact online | exact beginChange_pendingOnline s _ online | split
  | send second action =>
    simp only [step]
    repeat' first | exact online | exact sendFor_pendingOnline s _ _ online | split
  | storage action =>
    simp only [step,storage]
    split
    · exact online
    · exact applyJournal_pendingOnline s _ a stable inv online
  | crash => intro impossible; cases impossible
  | reconcile =>
    simp only [step,reconcile]
    split
    · exact online
    · exact sendFor_pendingOnline s _ _ online
  | handle => exact handle_pendingOnline s online
  | receive =>
    simp only [step,receiveNetwork]
    split
    · exact online
    · split
      · exact online
      · split <;> exact pushLocal_pendingOnline s _ online
  | submit | drain | network _ | duplicateInbound | duplicateOutbound | dropInbound | dropOutbound |
    rotateInbound | rotateOutbound | prepareMigration _ _ _ _ | cancelMigration | cleanupMigration | inspect =>
    simp only [step,submit,drain,network,duplicateInbound,duplicateOutbound,prepareMigration,cancelMigration,cleanupMigration]
    repeat' first | exact online | split
  | commitMigration =>
    simp only [step,commitMigration]
    split
    · exact online
    · exact beginChange_pendingOnline s _ online

theorem execute_pendingOnline (s : System) (commands : List Command)
    (a : Durability.Abstract Frame) (stable : Frame) (inv : RuntimeInvariant s a stable)
    (online : PendingOnline s) : PendingOnline (execute s commands).system := by
  induction commands generalizing s a stable with
  | nil => exact online
  | cons command commands ih =>
    obtain ⟨b,after,label,next,labelEq,source⟩ := inv.step command
    exact ih (step s command).system b after next (step_pendingOnline s a stable command inv online)

theorem initial_execute_pendingOnline (kind : Migration.Kind) (commands : List Command) :
    PendingOnline (execute (initialSystem kind) commands).system :=
  execute_pendingOnline _ commands _ _ (RuntimeInvariant.initial kind) (PendingOnline.initial kind)

theorem RuntimeInvariant.commit_current_backend {s : System} {a b : Durability.Abstract Frame}
    {stable : Frame} (inv : RuntimeInvariant s a stable) (online : PendingOnline s)
    (record : Durability.Record Frame) (source : Durability.SpecStep (.commit record) a b) :
    s.adapter.current = some stable := by
  obtain ⟨command,cause,changed⟩ := inv.commit_command record source
  have present := online (by simp [cause])
  cases current : s.adapter.current with
  | none => simp [current] at present
  | some frame => have same := inv.current frame current; subst frame; rfl


def StagedBackend (s : System) : FrameCommand → Prop
  | .migrate kind => ∃ target, s.adapter.prepared = some target ∧ target.kind = kind
  | .tickCommit => s.adapter.prepared = none
  | _ => True

def PendingSelection (s : System) (a : Durability.Abstract Frame) : Prop :=
  ∀ record, a.active = some record → record ∉ a.history →
    ∀ command, s.adapter.pendingCause = some command → StagedBackend s command

def SelectionConsistent (s : System) : Prop :=
  ∃ a, Durability.Related s.adapter.journal.machine a ∧ PendingSelection s a

theorem StagedBackend.congr {s t : System} {command : FrameCommand}
    (selected : StagedBackend s command) (prepared : t.adapter.prepared = s.adapter.prepared) :
    StagedBackend t command := by
  cases command <;> first | trivial | simpa only [StagedBackend,prepared] using selected

theorem SelectionConsistent.congr {s t : System} (consistent : SelectionConsistent s)
    (machine : t.adapter.journal.machine = s.adapter.journal.machine)
    (cause : t.adapter.pendingCause = s.adapter.pendingCause)
    (prepared : t.adapter.prepared = s.adapter.prepared) : SelectionConsistent t := by
  obtain ⟨a,related,selected⟩ := consistent
  refine ⟨a,machine ▸ related,?_⟩
  intro record active missing command pending
  exact (selected record active missing command (cause ▸ pending)).congr prepared

theorem SelectionConsistent.initial (kind : Migration.Kind) : SelectionConsistent (initialSystem kind) := by
  refine ⟨Durability.initialAbstract,Durability.related_initial,?_⟩
  intro record impossible
  cases impossible

theorem SelectionConsistent.beginChange {s : System} (consistent : SelectionConsistent s)
    (command : FrameCommand) (staged : StagedBackend s command) :
    SelectionConsistent (beginChange s command).system := by
  obtain ⟨a,related,selection⟩ := consistent
  unfold FRPSpec.PendingCrash.beginChange
  split
  · exact ⟨a,related,selection⟩
  · split
    · exact ⟨a,related,selection⟩
    · split
      · exact ⟨a,related,selection⟩
      · exact ⟨a,related,selection⟩
      · rename_i next changed
        split
        · exact ⟨a,related,selection⟩
        · rename_i result done
          have event := journalInvoke_event _ _ result done
          obtain ⟨b,source,relation⟩ := result.native.simulation related
          refine ⟨b,relation,?_⟩
          rw [event] at source
          cases source
          intro record active missing action pending
          have same : command = action := Option.some.inj pending
          subst action
          exact staged

theorem SelectionConsistent.applyJournal {s : System} (consistent : SelectionConsistent s)
    (attempt : JournalAttempt s.adapter.journal)
    (notInvoke : ∀ result, attempt = .done result → ∀ record, result.event ≠ .invoke record) :
    SelectionConsistent (applyJournal s attempt).system := by
  obtain ⟨a,related,selection⟩ := consistent
  cases attempt with
  | failed work => exact ⟨a,related,selection⟩
  | done result =>
    obtain ⟨b,source,relation⟩ := result.native.simulation related
    refine ⟨b,?_,?_⟩
    · rw [applyJournal_done_machine]; exact relation
    · cases event : result.event <;> rw [event] at source
      case internal => cases source; simpa only [FRPSpec.PendingCrash.applyJournal,event,PendingSelection,StagedBackend] using selection
      case invoke record => exact False.elim (notInvoke result rfl record event)
      case commit record =>
        cases source with
        | commit online active fresh =>
          intro candidate candidateActive missing command pending
          have same : candidate = record := Option.some.inj (candidateActive.symm.trans active)
          subst candidate
          exact False.elim (missing (by simp))
      case acknowledge record => cases source; intro candidate impossible; cases impossible
      case reject record => cases source; intro candidate impossible; cases impossible
      case query history => cases source; simpa only [FRPSpec.PendingCrash.applyJournal,event,PendingSelection,StagedBackend] using selection
      case crash => cases source; intro candidate impossible; cases impossible
      case recover history =>
        cases source with
        | recover offline =>
          have inactive := related.offline_active offline
          intro candidate impossible
          rw [inactive] at impossible
          cases impossible

theorem SelectionConsistent.storage {s : System} (consistent : SelectionConsistent s)
    (command : StorageCommand) : SelectionConsistent (storage s command).system := by
  unfold FRPSpec.PendingCrash.storage
  split
  · exact consistent
  · exact consistent.applyJournal _ (fun result done record => journalStorage_notInvoke s.adapter.journal command record result done)

theorem SelectionConsistent.crash {s : System} (consistent : SelectionConsistent s) :
    SelectionConsistent (crash s).system := by
  obtain ⟨a,related,selection⟩ := consistent
  obtain ⟨b,source,relation⟩ := (journalCrash s.adapter.journal).native.simulation related
  change Durability.SpecStep .crash a b at source
  cases source
  exact ⟨_,relation,by intro record impossible; cases impossible⟩

theorem idle_no_active (s : System) (ready : idle s = true) :
    s.adapter.journal.machine.active = none := by
  simp only [idle,Bool.and_eq_true] at ready
  simpa using ready.1.2

theorem SelectionConsistent.inactive {s t : System} (consistent : SelectionConsistent s)
    (machine : t.adapter.journal.machine = s.adapter.journal.machine)
    (inactive : s.adapter.journal.machine.active = none) : SelectionConsistent t := by
  obtain ⟨a,related,selection⟩ := consistent
  have absent : a.active = none := related.active.symm.trans inactive
  refine ⟨a,machine ▸ related,?_⟩
  intro record impossible
  rw [absent] at impossible
  cases impossible

theorem SelectionConsistent.prepareMigration {s : System} (consistent : SelectionConsistent s)
    (kind : Migration.Kind) (budget : Nat) (allocation validation : Bool) :
    SelectionConsistent (prepareMigration s kind budget allocation validation).system := by
  unfold FRPSpec.PendingCrash.prepareMigration
  split
  · exact consistent
  · rename_i ready
    have idleReady : idle s = true := by simp_all [businessReady]
    cases active : s.adapter.active with
    | none => exact consistent
    | some backend => exact consistent.inactive rfl (idle_no_active s idleReady)

theorem SelectionConsistent.cancelMigration {s : System} (consistent : SelectionConsistent s) :
    SelectionConsistent (cancelMigration s).system := by
  unfold FRPSpec.PendingCrash.cancelMigration
  split
  · exact consistent
  · rename_i ready
    have inactive := idle_no_active s (by simpa using ready)
    split
    · exact consistent
    · exact consistent.inactive rfl inactive

theorem SelectionConsistent.commitMigration {s : System} (consistent : SelectionConsistent s) :
    SelectionConsistent (commitMigration s).system := by
  unfold FRPSpec.PendingCrash.commitMigration
  split
  · exact consistent
  · rename_i target prepared
    exact consistent.beginChange (.migrate target.kind) ⟨target,prepared,rfl⟩

theorem SelectionConsistent.pushLocal {s : System} (consistent : SelectionConsistent s) (message : Message) :
    SelectionConsistent (pushLocal s message).system := by
  unfold FRPSpec.PendingCrash.pushLocal
  dsimp only
  split <;> exact consistent.congr rfl rfl rfl

theorem SelectionConsistent.pushCancellation {s : System} (consistent : SelectionConsistent s)
    (identity : Nat) (input : Bool) : SelectionConsistent (pushCancellation s identity input).system := by
  unfold FRPSpec.PendingCrash.pushCancellation
  dsimp only
  split <;> exact consistent.congr rfl rfl rfl

theorem SelectionConsistent.sendFor {s : System} (consistent : SelectionConsistent s)
    (identity : Nat) (command : Send) : SelectionConsistent (sendFor s identity command).system := by
  unfold FRPSpec.PendingCrash.sendFor
  repeat' first | exact consistent | exact consistent.pushLocal _ | exact consistent.pushCancellation _ _ | split
  all_goals dsimp only
  all_goals repeat' first | exact consistent | exact consistent.pushLocal _ | exact consistent.pushCancellation _ _ | split

theorem SelectionConsistent.handle {s : System} (consistent : SelectionConsistent s) :
    SelectionConsistent (handle s).system := by
  unfold FRPSpec.PendingCrash.handle
  split
  · exact consistent
  · split
    · rename_i receipt rest queueEq
      let queue : LocalQueue := ⟨rest, by have := s.adapter.queue.bounded; rw [queueEq] at this; simp only [List.length_cons] at this; omega⟩
      let popped := {s with adapter := {s.adapter with queue := queue}}
      have poppedConsistent : SelectionConsistent popped := consistent.congr rfl rfl rfl
      have beginSelected := poppedConsistent.beginChange (.receive receipt) trivial
      have sendSelected := fun identity command => poppedConsistent.sendFor identity command
      dsimp only
      repeat' first | exact poppedConsistent | exact beginSelected | exact sendSelected _ _ | split
    · exact consistent


theorem SelectionConsistent.localCommand {s : System} (consistent : SelectionConsistent s)
    (command : FrameCommand) : SelectionConsistent (localCommand s command).system := by
  cases command <;> simp only [FRPSpec.PendingCrash.localCommand]
  all_goals repeat' first | exact consistent | apply consistent.beginChange | split
  all_goals first | trivial | simp_all [StagedBackend,businessReady]

theorem SelectionConsistent.step {s : System} (consistent : SelectionConsistent s) (command : Command) :
    SelectionConsistent (step s command).system := by
  cases command with
  | «local» action => exact consistent.localCommand action
  | send second action =>
    simp only [FRPSpec.PendingCrash.step]
    repeat' first | exact consistent | exact consistent.sendFor _ _ | split
  | storage action => exact consistent.storage action
  | crash => exact consistent.crash
  | reconcile =>
    simp only [FRPSpec.PendingCrash.step,reconcile]
    split
    · exact consistent
    · exact consistent.sendFor _ _
  | handle => exact consistent.handle
  | receive =>
    simp only [FRPSpec.PendingCrash.step,receiveNetwork]
    split
    · exact consistent
    · split
      · exact consistent
      · split
        · exact (consistent.pushLocal _).congr rfl rfl rfl
        · exact consistent.pushLocal _
  | prepareMigration kind budget allocation validation => exact consistent.prepareMigration kind budget allocation validation
  | commitMigration => exact consistent.commitMigration
  | cancelMigration => exact consistent.cancelMigration
  | submit | drain | network _ | duplicateInbound | duplicateOutbound | dropInbound | dropOutbound |
    rotateInbound | rotateOutbound | cleanupMigration | inspect =>
    simp only [FRPSpec.PendingCrash.step,submit,drain,network,duplicateInbound,duplicateOutbound,cleanupMigration]
    repeat' first | exact consistent | split

theorem SelectionConsistent.execute {s : System} (consistent : SelectionConsistent s) (commands : List Command) :
    SelectionConsistent (execute s commands).system := by
  induction commands generalizing s with
  | nil => exact consistent
  | cons command commands ih => exact ih (consistent.step command)

theorem initial_execute_selection (kind : Migration.Kind) (commands : List Command) :
    SelectionConsistent (execute (initialSystem kind) commands).system :=
  (SelectionConsistent.initial kind).execute commands

theorem SelectionConsistent.at_abstract {s : System} {a : Durability.Abstract Frame}
    (consistent : SelectionConsistent s) (related : Durability.Related s.adapter.journal.machine a) :
    PendingSelection s a := by
  obtain ⟨b,other,selection⟩ := consistent
  have history : b.history = a.history := other.root.unique related.root
  have active : b.active = a.active := other.active.symm.trans related.active
  intro record present missing command cause
  exact selection record (by simpa only [active] using present) (by simpa only [history] using missing) command cause

theorem RuntimeInvariant.commit_staged_backend {s : System} {a b : Durability.Abstract Frame}
    {stable : Frame} (inv : RuntimeInvariant s a stable) (consistent : SelectionConsistent s)
    (record : Durability.Record Frame) (source : Durability.SpecStep (.commit record) a b)
    (command : FrameCommand) (cause : s.adapter.pendingCause = some command) : StagedBackend s command := by
  cases source with
  | commit online active fresh =>
    apply consistent.at_abstract inv.related record active _ command cause
    intro member
    exact fresh record member rfl


theorem applyJournal_backend (s : System) (a : Durability.Abstract Frame) (stable : Frame)
    (attempt : JournalAttempt s.adapter.journal) (inv : RuntimeInvariant s a stable)
    (agreement : BackendAgreement s) (online : PendingOnline s) (selection : SelectionConsistent s) :
    BackendAgreement (applyJournal s attempt).system := by
  cases attempt with
  | failed work => exact agreement
  | done result =>
    obtain ⟨b,source,relation⟩ := result.native.simulation inv.related
    have recovery := inv.frames.recovered source
    cases event : result.event <;> rw [event] at source
    case commit record =>
      obtain ⟨command,cause,changed⟩ := inv.commit_command record source
      have current := inv.commit_current_backend online record source
      have staged := inv.commit_staged_backend selection record source command cause
      cases command with
      | migrate kind =>
        obtain ⟨target,prepared,selectedKind⟩ := staged
        exact applyJournal_migration_backend s result record stable kind target agreement event cause current prepared selectedKind changed
      | tickCommit => exact applyJournal_tick_backend s result record stable agreement event cause current staged changed
      | accept input | evaluate | receive receipt | close | release =>
        apply applyJournal_ordinary_backend s result record stable _ agreement event cause current changed
        · intro impossible; cases impossible
        · intro kind impossible; cases impossible
    case recover history =>
      have validated : (validateMeasured (initialFrame s.adapter.initialKind)
          (history.map Durability.Record.payload)).1 = some stable := by
        rw [validateMeasured_eq]
        simpa only [event,RecoveredFrame] using recovery
      exact applyJournal_recover_backend s result history stable agreement event validated
        (fun before current => congrArg Frame.logical (inv.current before current).symm)
    all_goals apply agreement.congr s _
    all_goals simp only [applyJournal,event]

theorem pushLocal_backend (s : System) (message : Message) (agreement : BackendAgreement s) :
    BackendAgreement (pushLocal s message).system := by
  unfold pushLocal
  dsimp only
  split <;> exact agreement.congr s _ rfl rfl rfl

theorem pushCancellation_backend (s : System) (identity : Nat) (input : Bool)
    (agreement : BackendAgreement s) : BackendAgreement (pushCancellation s identity input).system := by
  unfold pushCancellation
  dsimp only
  split <;> exact agreement.congr s _ rfl rfl rfl

theorem sendFor_backend (s : System) (identity : Nat) (command : Send)
    (agreement : BackendAgreement s) : BackendAgreement (sendFor s identity command).system := by
  unfold sendFor
  repeat' first | exact agreement | exact pushLocal_backend s _ agreement | exact pushCancellation_backend s _ _ agreement | split
  all_goals dsimp only
  all_goals repeat' first | exact agreement | exact pushLocal_backend s _ agreement | exact pushCancellation_backend s _ _ agreement | split

theorem handle_backend (s : System) (agreement : BackendAgreement s) : BackendAgreement (handle s).system := by
  unfold handle
  split
  · exact agreement
  · split
    · rename_i receipt rest queueEq
      let queue : LocalQueue := ⟨rest, by have := s.adapter.queue.bounded; rw [queueEq] at this; simp only [List.length_cons] at this; omega⟩
      let popped := {s with adapter := {s.adapter with queue := queue}}
      have poppedAgreement : BackendAgreement popped := agreement.congr s _ rfl rfl rfl
      have beginAgreement := fun command => beginChange_backend popped command poppedAgreement
      have sendAgreement := fun identity command => sendFor_backend popped identity command poppedAgreement
      dsimp only
      repeat' first | exact poppedAgreement | exact poppedAgreement.congr popped _ rfl rfl rfl | exact beginAgreement _ | exact sendAgreement _ _ | split
    · exact agreement

theorem step_backend (s : System) (a : Durability.Abstract Frame) (stable : Frame) (command : Command)
    (inv : RuntimeInvariant s a stable) (agreement : BackendAgreement s)
    (online : PendingOnline s) (selection : SelectionConsistent s) : BackendAgreement (step s command).system := by
  cases command with
  | «local» action =>
    simp only [step,localCommand]
    repeat' first | exact agreement | exact beginChange_backend s _ agreement | split
  | send second action =>
    simp only [step]
    repeat' first | exact agreement | exact sendFor_backend s _ _ agreement | split
  | storage action =>
    simp only [step,storage]
    split
    · exact agreement
    · exact applyJournal_backend s a stable _ inv agreement online selection
  | crash => exact crash_backend s
  | reconcile =>
    simp only [step,reconcile]
    split
    · exact agreement
    · exact sendFor_backend s _ _ agreement
  | handle => exact handle_backend s agreement
  | receive =>
    simp only [step,receiveNetwork]
    split
    · exact agreement
    · split
      · exact agreement
      · split
        · exact (pushLocal_backend s _ agreement).congr _ _ rfl rfl rfl
        · exact pushLocal_backend s _ agreement
  | prepareMigration kind budget allocation validation => exact prepareMigration_backend s kind budget allocation validation agreement
  | commitMigration =>
    simp only [step,commitMigration]
    split
    · exact agreement
    · exact beginChange_backend s _ agreement
  | cancelMigration =>
    simp only [step,cancelMigration]
    split
    · exact agreement
    · split
      · exact agreement
      · exact ⟨agreement.active,by intro target impossible; cases impossible⟩
  | submit | drain | network _ | duplicateInbound | duplicateOutbound | dropInbound | dropOutbound |
    rotateInbound | rotateOutbound | cleanupMigration | inspect =>
    simp only [step,submit,drain,network,duplicateInbound,duplicateOutbound,cleanupMigration]
    repeat' first | exact agreement | exact agreement.congr s _ rfl rfl rfl | split

theorem execute_backend (s : System) (commands : List Command) (a : Durability.Abstract Frame) (stable : Frame)
    (inv : RuntimeInvariant s a stable) (agreement : BackendAgreement s)
    (online : PendingOnline s) (selection : SelectionConsistent s) : BackendAgreement (execute s commands).system := by
  induction commands generalizing s a stable with
  | nil => exact agreement
  | cons command commands ih =>
    obtain ⟨b,after,label,next,labelEq,source⟩ := inv.step command
    exact ih (step s command).system b after next
      (step_backend s a stable command inv agreement online selection)
      (step_pendingOnline s a stable command inv online) (selection.step command)

theorem initial_execute_backend (kind : Migration.Kind) (commands : List Command) :
    BackendAgreement (execute (initialSystem kind) commands).system :=
  execute_backend _ commands _ _ (RuntimeInvariant.initial kind) (BackendAgreement.initial kind)
    (PendingOnline.initial kind) (SelectionConsistent.initial kind)

theorem prepareMigration_selected (s : System) (kind : Migration.Kind) (budget : Nat)
    (active : Migration.Backend) (ready : businessReady s = true)
    (ha : s.adapter.active = some active)
    (space : PendingMigration.preparationSlots {active := active} kind ≤ budget - localReservations s) :
    (prepareMigration s kind budget true true).system.adapter.prepared =
      some (Migration.realize kind active.logical) := by
  let p : Migration.Prepared active :=
    ⟨Migration.realize kind active.logical, Migration.realize_logical _ _⟩
  have hs : PendingMigration.step ({active := active} : PendingMigration.Session)
      (.prepare kind (budget - localReservations s) true true) =
      ⟨{active := active, prepared := some p}, .prepared, none, none, none,
        [.budget, .attempt (p.target.cells + 2), .allocate (p.target.cells + 2),
         .copy p.target.cells, .validate, .release 2]⟩ := by
    simp [PendingMigration.step, Nat.not_lt.mpr space, p, Migration.backend_validates]
  simp only [prepareMigration, ready, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ha]
  exact congrArg (fun o => o.session.prepared.map (fun p => p.target)) hs

theorem prepareMigration_retained (s : System) (kind : Migration.Kind) (budget : Nat)
    (allocationOK validationOK : Bool) :
    let after := (prepareMigration s kind budget allocationOK validationOK).system
    after.adapter.current = s.adapter.current ∧
    after.adapter.active = s.adapter.active ∧
    after.adapter.queue.messages = s.adapter.queue.messages ∧
    after.adapter.journal = s.adapter.journal ∧
    after.inbound = s.inbound ∧ after.outbound = s.outbound := by
  simp only [prepareMigration]
  split
  · exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  · cases ha : s.adapter.active <;> simp [ha, reject]

/-- Exact comparison of the selected native conversion. Pending keyed data and
all traffic are covered separately by prepareMigration_retained. -/
theorem prepareMigration_native_conversion (s : System) (kind : Migration.Kind) (budget : Nat)
    (active : Migration.Backend) (ready : businessReady s = true)
    (ha : s.adapter.active = some active)
    (space : PendingMigration.preparationSlots {active := active} kind ≤ budget - localReservations s) :
    (prepareMigration s kind budget true true).system.adapter.prepared =
      some (PendingMigration.execute {active := active}
        [.prepare kind (budget - localReservations s) true true, .ownershipCommit]).1.active := by
  rw [PendingMigration.prepare_commit _ kind _ rfl space]
  exact prepareMigration_selected s kind budget active ready ha space

/-- Native finite suffix comparison retains the chosen backend continuation;
no equality of independently chosen checkpoint representations is assumed. -/
theorem selected_native_suffix (active : Migration.Backend) (kind : Migration.Kind)
    (budget : Nat) (space : PendingMigration.preparationSlots {active := active} kind ≤ budget)
    (commands : List PendingMigration.Command)
    (business : ∀ c ∈ commands, PendingMigration.Business c) :
    let converted := (PendingMigration.execute {active := active}
      [.prepare kind budget true true,.ownershipCommit]).1
    PendingMigration.checkpoint (PendingMigration.execute converted commands).1 =
      PendingMigration.checkpoint (PendingMigration.execute {active := active} commands).1 ∧
    (PendingMigration.execute converted commands).2 =
      (PendingMigration.execute {active := active} commands).2 := by
  rw [PendingMigration.prepare_commit _ kind budget rfl space]
  exact PendingMigration.transfer_suffix _ kind commands business rfl
/-- A pending selected output is the output of the actual retained native
backend, not merely of a freshly reconstructed frame interpretation. -/
theorem execute_retained_native_output (kind : Migration.Kind) (commands : List Command)
    (frame : Frame) (slot : Bool) (request : Request) (backend : Migration.Backend)
    (current : (execute (initialSystem kind) commands).system.adapter.current = some frame)
    (active : (execute (initialSystem kind) commands).system.adapter.active = some backend)
    (present : frame.requests.get slot = some request)
    (pending : request.phase = .computed ∨ request.phase = .confirmed) :
    request.output = some (Migration.evaluate backend request.input).output := by
  have valid := execute_current_valid kind commands frame current
  have requestValid := (valid.2.2.2.1 slot request (by simp [present])).2.1
  have selected : request.output = some frame.logical := by
    rcases pending with computed | confirmed
    · simp only [FRPSpec.PendingCrash.RequestValid,computed] at requestValid
      exact requestValid.2.1
    · simp only [FRPSpec.PendingCrash.RequestValid,confirmed] at requestValid
      exact requestValid.2.1
  have agreement := (initial_execute_backend kind commands).active_eq _ frame backend current active
  rw [(Migration.evaluate backend request.input).output_eq,agreement.2]
  exact selected
end FRPSpec.PendingCrash

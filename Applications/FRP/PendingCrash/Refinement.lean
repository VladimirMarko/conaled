import Applications.FRP.PendingCrash.Source
/-! Universal source refinement of the concrete pending/crash runtime.
The invariant links the native accepted journal history, the selected frame,
peer terminal evidence and queued traffic. It is established from initialization
and preserved by every command; executable trace-checker success is not assumed. -/
namespace FRPSpec.PendingCrash

theorem validateFrames_append_of_success (initial frame : Frame) (prior suffix : List Frame)
    (valid : validateFrames initial prior = some frame) :
    validateFrames initial (prior ++ suffix) = validateFrames frame suffix := by
  induction prior generalizing initial with
  | nil =>
    simp only [validateFrames] at valid
    split at valid
    · cases valid; rfl
    · contradiction
  | cons next rest ih =>
    simp only [List.cons_append, validateFrames] at valid ⊢
    split at valid
    · rename_i success
      rw [ite_eq_left success]
      exact ih next valid
    · contradiction

theorem validateFrames_append_successor (initial frame next : Frame) (prior : List Frame)
    (valid : validateFrames initial prior = some frame) (allowed : successor frame next = true) :
    validateFrames initial (prior ++ [next]) = some next := by
  rw [validateFrames_append_of_success _ _ _ _ valid]
  simp [validateFrames, allowed, (successor_valid allowed).2]


/-- The stable frame is determined by the complete accepted record sequence.
An active append is either already committed or a genuine next frame. -/
structure DurableFrames (initial : Frame) (a : Durability.Abstract Frame) (stable : Frame) : Prop where
  validated : validateFrames initial (a.history.map Durability.Record.payload) = some stable
  active : ∀ record, a.active = some record →
    record ∈ a.history ∨ successor stable record.payload = true

def permittedInvocation (stable : Frame) : Durability.Event Frame → Prop
  | .invoke record => successor stable record.payload = true
  | _ => True

def publishedFrame (stable : Frame) : Durability.Event Frame → Frame
  | .commit record => record.payload
  | _ => stable

theorem DurableFrames.step {initial stable : Frame} {a b : Durability.Abstract Frame}
    {event : Durability.Event Frame} (frames : DurableFrames initial a stable)
    (step : Durability.SpecStep event a b) (permitted : permittedInvocation stable event) :
    DurableFrames initial b (publishedFrame stable event) := by
  cases step with
  | internal => exact frames
  | invoke online inactive =>
    refine ⟨frames.validated, ?_⟩
    intro other same
    cases Option.some.inj same
    exact Or.inr permitted
  | @commit a record online active fresh =>
    have allowed : successor stable record.payload = true := by
      rcases frames.active record active with member | allowed
      · exact False.elim (fresh record member rfl)
      · exact allowed
    constructor
    · simpa only [List.map_append, List.map_singleton, publishedFrame] using
        validateFrames_append_successor initial stable record.payload
          (a.history.map Durability.Record.payload) frames.validated allowed
    · intro other same
      have equal : record = other := Option.some.inj (active.symm.trans same)
      subst other
      exact Or.inl (List.mem_append.mpr (Or.inr (by simp)))
  | acknowledge online active member | reject online active member key different =>
    exact ⟨frames.validated, by intro record impossible; cases impossible⟩
  | query online inactive => exact frames
  | crash => exact ⟨frames.validated, by intro record impossible; cases impossible⟩
  | recover offline => exact ⟨frames.validated, frames.active⟩

theorem initialFrame_valid (kind : Migration.Kind) : (initialFrame kind).Valid := by
  cases kind <;> decide

theorem DurableFrames.initial (kind : Migration.Kind) :
    DurableFrames (initialFrame kind) Durability.initialAbstract (initialFrame kind) := by
  constructor
  · simp [Durability.initialAbstract, validateFrames, initialFrame_valid]
  · intro record impossible; cases impossible

/-- One native cut preserves validated accepted history. The invocation premise
is discharged at the adapter's checked advance, not by the storage layer. -/
theorem DurableFrames.native_step {initial stable : Frame} {a : Durability.Abstract Frame}
    {s t : Durability.Machine Frame} {event : Durability.Event Frame}
    (frames : DurableFrames initial a stable) (related : Durability.Related s a)
    (step : Durability.Step event s t) (permitted : permittedInvocation stable event) :
    ∃ b, Durability.Related t b ∧ DurableFrames initial b (publishedFrame stable event) := by
  obtain ⟨b, source, relation⟩ := step.simulation related
  exact ⟨b, relation, frames.step source permitted⟩

theorem advance_proposed (f g : Frame) (command : FrameCommand)
    (changed : advance f command = .changed g) :
    propose f command = .changed g ∧ successor f g = true := by
  cases h : propose f command with
  | refused => simp [advance, h] at changed
  | stopped => simp [advance, h] at changed
  | changed next =>
    simp only [advance, h] at changed
    split at changed
    · cases changed; exact ⟨rfl, by assumption⟩
    · contradiction

def StableCurrent (s : System) (stable : Frame) : Prop :=
  ∀ frame, s.adapter.current = some frame → frame = stable

theorem beginChange_current (s : System) (command : FrameCommand) :
    (beginChange s command).system.adapter.current = s.adapter.current := by
  unfold FRPSpec.PendingCrash.beginChange
  repeat' first | rfl | split

theorem journalInvoke_event (journal : Journal) (next : Frame) (result : JournalResult journal)
    (done : journalInvoke journal next = .done result) :
    result.event = .invoke ⟨0,journal.nextAddress,next⟩ := by
  unfold journalInvoke at done
  split at done
  · contradiction
  · split at done
    · split at done
      · cases done; rfl
      · contradiction
    · contradiction

theorem beginChange_permitted (s : System) (stable : Frame) (command : FrameCommand)
    (current : StableCurrent s stable) :
    ∀ event, (beginChange s command).journalEvent = some event →
      permittedInvocation stable event := by
  intro event observed
  unfold beginChange at observed
  split at observed
  · cases observed
  · split at observed
    · cases observed
    · rename_i old present
      have same := current old present
      subst old
      split at observed
      · cases observed
      · cases observed
      · rename_i next changed
        have allowed := (advance_proposed stable next command changed).2
        split at observed
        · cases observed
        · rename_i result done
          cases observed
          rw [journalInvoke_event _ _ result done]
          exact allowed


def recoveredFrame (initial stable : Frame) : Durability.Event Frame → Prop
  | .recover history => validateFrames initial (history.map Durability.Record.payload) = some stable
  | _ => True

theorem DurableFrames.recovered {initial stable : Frame} {a b : Durability.Abstract Frame}
    {event : Durability.Event Frame} (frames : DurableFrames initial a stable)
    (step : Durability.SpecStep event a b) : recoveredFrame initial stable event := by
  cases step <;> first | trivial | exact frames.validated

theorem applyJournal_done_current (s : System) (stable : Frame)
    (result : JournalResult s.adapter.journal) (current : StableCurrent s stable)
    (recover : recoveredFrame (initialFrame s.adapter.initialKind) stable result.event) :
    StableCurrent (applyJournal s (.done result)).system (publishedFrame stable result.event) := by
  intro frame present
  unfold applyJournal at present
  cases event : result.event <;> simp only [event] at present recover ⊢
  all_goals try exact current frame present
  case commit record =>
    repeat' first | split at present | exact (Option.some.inj present).symm
  case recover history =>
    have validated : (validateMeasured (initialFrame s.adapter.initialKind)
        (history.map Durability.Record.payload)).1 = some stable := by
      rw [validateMeasured_eq]
      exact recover
    simp only [validated] at present
    exact (Option.some.inj present).symm


def InvokedBy (s : System) (stable : Frame) (record : Durability.Record Frame) : Prop :=
  ∃ command, s.adapter.pendingCause = some command ∧ advance stable command = .changed record.payload

def PendingConsistent (s : System) (a : Durability.Abstract Frame) (stable : Frame) : Prop :=
  ∀ record, a.active = some record → record ∈ a.history ∨ InvokedBy s stable record

theorem PendingConsistent.initial (kind : Migration.Kind) :
    PendingConsistent (initialSystem kind) Durability.initialAbstract (initialFrame kind) := by
  intro record impossible
  cases impossible

theorem PendingConsistent.congr {s t : System} {a : Durability.Abstract Frame} {stable : Frame}
    (pending : PendingConsistent s a stable) (cause : t.adapter.pendingCause = s.adapter.pendingCause) :
    PendingConsistent t a stable := by
  intro record active
  rcases pending record active with member | ⟨command,current,changed⟩
  · exact Or.inl member
  · exact Or.inr ⟨command,cause.trans current,changed⟩

theorem applyJournal_done_pending {s : System} {a b : Durability.Abstract Frame} {stable : Frame}
    (result : JournalResult s.adapter.journal) (pending : PendingConsistent s a stable)
    (source : Durability.SpecStep result.event a b)
    (notInvoke : ∀ record, result.event ≠ .invoke record) :
    PendingConsistent (applyJournal s (.done result)).system b (publishedFrame stable result.event) := by
  cases event : result.event <;> rw [event] at source
  case internal =>
    cases source
    apply pending.congr
    simp only [applyJournal,event]
  case invoke record => exact False.elim (notInvoke record event)
  case commit record =>
    cases source with
    | commit online active fresh =>
      intro other same
      have equal : record = other := Option.some.inj (active.symm.trans same)
      subst other
      exact Or.inl (List.mem_append.mpr (Or.inr (by simp)))
  case acknowledge record =>
    cases source
    intro other impossible
    cases impossible
  case reject record =>
    cases source
    intro other impossible
    cases impossible
  case query history =>
    cases source
    apply pending.congr
    simp only [applyJournal,event]
  case crash =>
    cases source
    intro other impossible
    cases impossible
  case recover history =>
    cases source
    apply pending.congr
    simp only [applyJournal,event]
    split <;> rfl


def FrameConsistent (s : System) : Prop :=
  ∃ a stable, Durability.Related s.adapter.journal.machine a ∧
    DurableFrames (initialFrame s.adapter.initialKind) a stable ∧ StableCurrent s stable ∧ PendingConsistent s a stable

theorem FrameConsistent.initial (kind : Migration.Kind) : FrameConsistent (initialSystem kind) := by
  refine ⟨Durability.initialAbstract, initialFrame kind, Durability.related_initial,
    DurableFrames.initial kind, ?_, PendingConsistent.initial kind⟩
  intro frame present
  exact (Option.some.inj present).symm

theorem FrameConsistent.congr {s t : System} (consistent : FrameConsistent s)
    (machine : t.adapter.journal.machine = s.adapter.journal.machine)
    (kind : t.adapter.initialKind = s.adapter.initialKind)
    (current : t.adapter.current = s.adapter.current)
    (cause : t.adapter.pendingCause = s.adapter.pendingCause) : FrameConsistent t := by
  obtain ⟨a,stable,related,frames,retained,pending⟩ := consistent
  refine ⟨a,stable,machine ▸ related,kind ▸ frames,?_,pending.congr cause⟩
  intro frame present
  exact retained frame (current ▸ present)

theorem applyJournal_done_kind (s : System) (result : JournalResult s.adapter.journal) :
    (applyJournal s (.done result)).system.adapter.initialKind = s.adapter.initialKind := by
  unfold applyJournal
  cases event : result.event <;> simp only [event]
  all_goals repeat' first | rfl | split

theorem applyJournal_done_machine (s : System) (result : JournalResult s.adapter.journal) :
    (applyJournal s (.done result)).system.adapter.journal.machine = result.journal.machine := by
  unfold applyJournal
  cases event : result.event <;> simp only [event]
  all_goals repeat' first | rfl | split

/-- The actual root publication/reconstruction keeps the same chosen stable
frame as the independent native accepted history. -/
theorem FrameConsistent.applyJournal {s : System} (consistent : FrameConsistent s)
    (attempt : JournalAttempt s.adapter.journal)
    (allowed : ∀ a stable, Durability.Related s.adapter.journal.machine a →
      DurableFrames (initialFrame s.adapter.initialKind) a stable → StableCurrent s stable →
      ∀ result, attempt = .done result → permittedInvocation stable result.event)
    (notInvoke : ∀ result, attempt = .done result → ∀ record, result.event ≠ .invoke record) :
    FrameConsistent (applyJournal s attempt).system := by
  obtain ⟨a,stable,related,frames,current,pending⟩ := consistent
  cases attempt with
  | failed work => exact ⟨a,stable,related,frames,current,pending⟩
  | done result =>
    obtain ⟨b,source,relation⟩ := result.native.simulation related
    have next := frames.step source (allowed a stable related frames current result rfl)
    refine ⟨b,publishedFrame stable result.event,?_,?_,?_,?_⟩
    · rw [applyJournal_done_machine]; exact relation
    · rw [applyJournal_done_kind]; exact next
    · exact applyJournal_done_current s stable result current (frames.recovered source)
    · exact applyJournal_done_pending result pending source (notInvoke result rfl)


theorem FrameConsistent.beginChange {s : System} (consistent : FrameConsistent s)
    (command : FrameCommand) : FrameConsistent (beginChange s command).system := by
  obtain ⟨a,stable,related,frames,current,pending⟩ := consistent
  unfold FRPSpec.PendingCrash.beginChange
  split
  · exact ⟨a,stable,related,frames,current,pending⟩
  · split
    · exact ⟨a,stable,related,frames,current,pending⟩
    · rename_i old present
      have same := current old present
      subst old
      split
      · exact ⟨a,stable,related,frames,current,pending⟩
      · exact ⟨a,stable,related,frames,current,pending⟩
      · rename_i next changed
        have successor := (advance_proposed stable next command changed).2
        split
        · exact ⟨a,stable,related,frames,current,pending⟩
        · rename_i result done
          have event := journalInvoke_event _ _ result done
          obtain ⟨b,source,relation⟩ := result.native.simulation related
          have allowed : permittedInvocation stable result.event := by rw [event]; exact successor
          have extended := frames.step source allowed
          refine ⟨b,stable,relation,?_,current,?_⟩
          · simpa only [event,publishedFrame] using extended
          · rw [event] at source
            cases source
            intro other same
            cases Option.some.inj same
            exact Or.inr ⟨command,rfl,changed⟩

theorem journalStorage_permitted (journal : Journal) (command : StorageCommand) (stable : Frame)
    (result : JournalResult journal)
    (done : journalStep journal (storageCommand command) = .done result) :
    permittedInvocation stable result.event := by
  cases command <;> simp only [storageCommand,journalStep,journalPrepare,journalWrite,
    journalPersist,journalPublish,journalAcknowledge,journalStartRead,journalRead,journalRecover] at done
  all_goals repeat' first | trivial | split at done | cases done
  all_goals change permittedInvocation stable (match _ with | none => .internal | some e => .commit e)
  all_goals split <;> trivial


theorem journalStorage_notInvoke (journal : Journal) (command : StorageCommand) (record : Durability.Record Frame)
    (result : JournalResult journal)
    (done : journalStep journal (storageCommand command) = .done result) :
    result.event ≠ .invoke record := by
  cases command <;> simp only [storageCommand,journalStep,journalPrepare,journalWrite,
    journalPersist,journalPublish,journalAcknowledge,journalStartRead,journalRead,journalRecover] at done
  all_goals repeat' first | (exact fun impossible => by cases impossible) | split at done | cases done
  all_goals change ((match _ with | none => .internal | some e => .commit e) : Durability.Event Frame) ≠ .invoke record
  all_goals split <;> intro impossible <;> cases impossible


theorem FrameConsistent.storage {s : System} (consistent : FrameConsistent s)
    (command : StorageCommand) : FrameConsistent (storage s command).system := by
  unfold FRPSpec.PendingCrash.storage
  split
  · exact consistent
  · apply consistent.applyJournal
    · intro a stable related frames current result done
      exact journalStorage_permitted s.adapter.journal command stable result done
    · intro result done record
      exact journalStorage_notInvoke s.adapter.journal command record result done

theorem FrameConsistent.crash {s : System} (consistent : FrameConsistent s) :
    FrameConsistent (crash s).system := by
  obtain ⟨a,stable,related,frames,current,pending⟩ := consistent
  obtain ⟨b,source,relation⟩ := (journalCrash s.adapter.journal).native.simulation related
  refine ⟨b,stable,relation,frames.step source trivial,?_,?_⟩
  · intro frame impossible; cases impossible
  · cases source
    intro record impossible
    cases impossible

theorem FrameConsistent.pushLocal {s : System} (consistent : FrameConsistent s)
    (message : Message) : FrameConsistent (pushLocal s message).system := by
  dsimp only [FRPSpec.PendingCrash.pushLocal]
  split <;> exact consistent.congr rfl rfl rfl rfl

theorem FrameConsistent.pushCancellation {s : System} (consistent : FrameConsistent s)
    (identity : Nat) (input : Bool) : FrameConsistent (pushCancellation s identity input).system := by
  dsimp only [FRPSpec.PendingCrash.pushCancellation]
  split <;> exact consistent.congr rfl rfl rfl rfl

theorem FrameConsistent.sendFor {s : System} (consistent : FrameConsistent s)
    (identity : Nat) (command : Send) : FrameConsistent (sendFor s identity command).system := by
  unfold FRPSpec.PendingCrash.sendFor
  repeat' first
    | exact consistent
    | exact consistent.pushLocal _
    | exact consistent.pushCancellation _ _
    | split
  all_goals simp only [Option.map]
  all_goals repeat' first | exact consistent | exact consistent.pushLocal _ | exact consistent.pushCancellation _ _ | split

theorem FrameConsistent.localCommand {s : System} (consistent : FrameConsistent s)
    (command : FrameCommand) : FrameConsistent (localCommand s command).system := by
  unfold FRPSpec.PendingCrash.localCommand
  repeat' first | exact consistent | exact consistent.beginChange _ | split
  all_goals dsimp only
  all_goals repeat' first | exact consistent | exact consistent.beginChange _ | split


theorem FrameConsistent.handle {s : System} (consistent : FrameConsistent s) :
    FrameConsistent (handle s).system := by
  unfold FRPSpec.PendingCrash.handle
  repeat' first
    | exact consistent
    | split

  all_goals dsimp only
  all_goals repeat' first
    | exact consistent
    | (apply FrameConsistent.beginChange; exact consistent.congr rfl rfl rfl rfl)
    | (apply FrameConsistent.sendFor; exact consistent.congr rfl rfl rfl rfl)
    | split


theorem FrameConsistent.step {s : System} (consistent : FrameConsistent s) (command : Command) :
    FrameConsistent (step s command).system := by
  cases command with
  | «local» command => exact consistent.localCommand command
  | storage command => exact consistent.storage command
  | crash => exact consistent.crash
  | handle => exact consistent.handle
  | send second command =>
    simp only [FRPSpec.PendingCrash.step]
    repeat' first | exact consistent | exact consistent.sendFor _ _ | split
  | reconcile =>
    simp only [FRPSpec.PendingCrash.step,reconcile]
    split
    · exact consistent
    · exact consistent.sendFor _ _
  | commitMigration =>
    simp only [FRPSpec.PendingCrash.step,commitMigration]
    split
    · exact consistent
    · exact consistent.beginChange _
  | submit | receive | drain | network deliver | duplicateInbound | duplicateOutbound | dropInbound | dropOutbound | rotateInbound | rotateOutbound | prepareMigration target budget allocationOK validationOK | cancelMigration | cleanupMigration | inspect =>
    simp only [FRPSpec.PendingCrash.step,submit,receiveNetwork,drain,network,
      duplicateInbound,duplicateOutbound,prepareMigration,cancelMigration,cleanupMigration]
    all_goals repeat' first | exact consistent | split
    all_goals exact consistent.pushLocal _


theorem FrameConsistent.execute {s : System} (consistent : FrameConsistent s)
    (commands : List Command) : FrameConsistent (execute s commands).system := by
  induction commands generalizing s with
  | nil => exact consistent
  | cons command commands ih => exact ih (consistent.step command)

theorem execute_validated_history (kind : Migration.Kind) (commands : List Command) :
    ∃ a stable,
      Durability.Related (execute (initialSystem kind) commands).system.adapter.journal.machine a ∧
      validateFrames (initialFrame (execute (initialSystem kind) commands).system.adapter.initialKind)
        (a.history.map Durability.Record.payload) = some stable ∧
      StableCurrent (execute (initialSystem kind) commands).system stable := by
  obtain ⟨a,stable,related,frames,current,pending⟩ := (FrameConsistent.initial kind).execute commands
  exact ⟨a,stable,related,frames.validated,current⟩

theorem execute_current_valid (kind : Migration.Kind) (commands : List Command) (frame : Frame)
    (present : (execute (initialSystem kind) commands).system.adapter.current = some frame) : frame.Valid := by
  obtain ⟨a,stable,related,validated,current⟩ := execute_validated_history kind commands
  rw [current frame present]
  exact validateFrames_valid validated





def admissionDelta : FrameCommand → Nat
  | .accept _ => 1
  | _ => 0

theorem propose_nextIdentity (f g : Frame) (command : FrameCommand)
    (changed : propose f command = .changed g) :
    g.nextIdentity = f.nextIdentity + admissionDelta command := by
  cases command <;> simp only [propose, admissionDelta] at changed ⊢
  all_goals try unfold receive at changed
  all_goals repeat' first
    | simp_all [Frame.update]
    | split at changed
  all_goals subst g; rfl

theorem advance_nextIdentity (f g : Frame) (command : FrameCommand)
    (changed : advance f command = .changed g) :
    g.nextIdentity = f.nextIdentity + admissionDelta command :=
  propose_nextIdentity f g command (advance_proposed f g command changed).1

theorem successor_nextIdentity (f g : Frame) (valid : successor f g = true) :
    f.nextIdentity ≤ g.nextIdentity := by
  simp only [successor, Bool.and_eq_true] at valid
  obtain ⟨command, _, changed⟩ := List.any_eq_true.mp valid.2
  have h : propose f command = .changed g := by simpa using changed
  rw [propose_nextIdentity f g command h]
  exact Nat.le_add_right _ _

theorem validateFrames_nextIdentity (f g : Frame) (frames : List Frame)
    (valid : validateFrames f frames = some g) : f.nextIdentity ≤ g.nextIdentity := by
  induction frames generalizing f with
  | nil =>
    simp only [validateFrames] at valid
    split at valid
    · cases valid; exact Nat.le_refl _
    · contradiction
  | cons next rest ih =>
    simp only [validateFrames] at valid
    split at valid
    · exact (successor_nextIdentity f next (by assumption)).trans (ih next valid)
    · contradiction


theorem validateFrames_mem_or_initial (initial stable : Frame) (frames : List Frame)
    (valid : validateFrames initial frames = some stable) : stable = initial ∨ stable ∈ frames := by
  induction frames generalizing initial with
  | nil =>
    simp only [validateFrames] at valid
    split at valid
    · exact Or.inl (Option.some.inj valid).symm
    · contradiction
  | cons next rest ih =>
    simp only [validateFrames] at valid
    split at valid
    · rcases ih next valid with same | member
      · exact Or.inr (by simp [same])
      · exact Or.inr (List.mem_cons_of_mem _ member)
    · contradiction

theorem validateFrames_member_counter (initial stable member : Frame) (frames : List Frame)
    (valid : validateFrames initial frames = some stable) (present : member ∈ frames) :
    member.nextIdentity ≤ stable.nextIdentity := by
  induction frames generalizing initial with
  | nil => simp at present
  | cons next rest ih =>
    simp only [validateFrames] at valid
    split at valid
    · rcases List.mem_cons.mp present with same | present
      · subst member; exact validateFrames_nextIdentity next stable rest valid
      · exact ih next valid present
    · contradiction

/-- Counter monotonicity depends on the validated accepted prefix, even when
comparison states are offline and have no current frame. -/
theorem validated_prefix_counter (beforeKind afterKind : Migration.Kind)
    (before after : Frame) (prior later : List Frame)
    (old : validateFrames (initialFrame beforeKind) prior = some before)
    (new : validateFrames (initialFrame afterKind) later = some after)
    (extendsHistory : prior.IsPrefix later) : before.nextIdentity ≤ after.nextIdentity := by
  rcases validateFrames_mem_or_initial _ _ _ old with same | member
  · simp [same,initialFrame]
  · exact validateFrames_member_counter _ after before later new (extendsHistory.subset member)




def PeerNamesBelow (bound : Nat) (peer : Peer) : Prop :=
  ∀ key entry, (key,entry) ∈ peer → key < bound

theorem PeerNamesBelow.fresh {bound : Nat} {peer : Peer} (names : PeerNamesBelow bound peer) :
    (lookup bound peer).1 = none := by
  induction peer with
  | nil => rfl
  | cons head rest ih =>
    rcases head with ⟨key,entry⟩
    have smaller := names key entry (by simp)
    have different : key ≠ bound := Nat.ne_of_lt smaller
    simp only [lookup,different,↓reduceIte]
    exact ih (fun k e member => names k e (List.mem_cons_of_mem _ member))

theorem PeerNamesBelow.install {bound : Nat} {peer : Peer} (names : PeerNamesBelow bound peer)
    (identity : Nat) (entry : PendingMigration.Ledger) (small : identity < bound) :
    PeerNamesBelow bound (install identity entry peer).1 := by
  induction peer with
  | nil =>
    intro key value member
    simp only [FRPSpec.PendingCrash.install,List.mem_singleton,Prod.mk.injEq] at member
    exact member.1 ▸ small
  | cons head rest ih =>
    rcases head with ⟨key,old⟩
    have tail : PeerNamesBelow bound rest := fun k e member => names k e (List.mem_cons_of_mem _ member)
    unfold FRPSpec.PendingCrash.install
    split
    · intro k e member
      rcases List.mem_cons.mp member with same | member
      · cases same; exact names key old (by simp)
      · exact tail k e member
    · intro k e member
      rcases List.mem_cons.mp member with same | member
      · cases same; exact names key old (by simp)
      · exact ih tail k e member

theorem PeerNamesBelow.peerStep {bound : Nat} {peer : Peer} (names : PeerNamesBelow bound peer)
    (identity : Nat) (command : PeerCommand) (small : identity < bound) :
    PeerNamesBelow bound (peerStep peer identity command).peer := by
  dsimp only [FRPSpec.PendingCrash.peerStep]
  split
  · exact names
  · split
    · exact names
    · exact names.install identity _ small

theorem peerStep_receipt_identity (peer : Peer) (identity : Nat) (command : PeerCommand) :
    (peerStep peer identity command).receipt.identity = identity := by
  dsimp only [FRPSpec.PendingCrash.peerStep]
  split
  · rfl
  · split <;> rfl



open PendingMigration

/-- In-flight traffic is related to the independent source only when it can
still take effect. Old terminal messages need not be erased or reinterpreted. -/
def SourceTraffic (source : DelaySource) (peer : Peer) (identity : Nat)
    (command : PeerCommand) : Prop :=
  match command with
  | .publish input output =>
    (lookup identity peer).1 = some (.reserved input) →
      output = source.state ∧ ∃ rest, source.waiting = (identity,input) :: rest
  | .cancel input =>
    (lookup identity peer).1 = some (.reserved input) →
      ∃ pre post, source.waiting = pre ++ (identity,input) :: post
  | _ => True

/-- This classification is independent of local frames and also covers stale
messages and conflicting retries. -/
theorem peerStep_outcomes (peer : Peer) (identity : Nat) (command : PeerCommand) :
    ((peerStep peer identity command).effect = none ∧
      (peerStep peer identity command).prevented = none) ∨
    (∃ input output, (lookup identity peer).1 = some (.reserved input) ∧
      command = .publish input output ∧
      (peerStep peer identity command).effect = some output ∧
      (peerStep peer identity command).prevented = none) ∨
    (∃ input, (lookup identity peer).1 = some (.reserved input) ∧
      command = .cancel input ∧
      (peerStep peer identity command).effect = none ∧
      (peerStep peer identity command).prevented = some input) := by
  cases h : (lookup identity peer).1 with
  | none => cases command <;> simp [peerStep, h, dispatch]
  | some entry =>
    cases entry with
    | reserved input =>
      cases command with
      | query => simp [peerStep, h, dispatch]
      | reserve other => simp [peerStep, h, dispatch]
      | publish other output =>
        by_cases hi : input = other
        · subst other; simp [peerStep, h, dispatch]
        · simp [peerStep, h, dispatch, hi]
      | cancel other =>
        by_cases hi : input = other
        · subst other; simp [peerStep, h, dispatch]
        · simp [peerStep, h, dispatch, hi]
    | published input output => cases command <;> simp [peerStep, h, dispatch]
    | cancelled input => cases command <;> simp [peerStep, h, dispatch]

/-- Every actual peer-processing step refines the independent source once
legitimacy of its in-flight head has been established by the reachability
invariant. This lemma does not assert that invariant for arbitrary systems. -/
theorem network_source_step (s : System) (source : DelaySource) (deliver : Bool)
    (traffic : ∀ identity command, (identity,command) ∈ s.outbound →
      SourceTraffic source s.peer identity command) :
    ∃ label next, sourceLabel (network s deliver).toLogEntry = some label ∧
      DelayStep label source next := by
  cases h : s.outbound with
  | nil => exact ⟨.internal, source, by simp [network, h, reject, sourceLabel], .internal _⟩
  | cons message rest =>
    rcases message with ⟨identity,command⟩
    have ht := traffic identity command (by simp [h])
    rcases peerStep_outcomes s.peer identity command with hn | he | hc
    · exact ⟨.internal, source, by simp [network, h, sourceLabel, hn.1, hn.2], .internal _⟩
    · obtain ⟨input, output, reserved, rfl, effect, prevented⟩ := he
      obtain ⟨outEq, tail, pending⟩ := ht reserved
      refine ⟨.output identity output, ⟨input,tail⟩, ?_, ?_⟩
      · simp [network, h, sourceLabel, effect, prevented]
      · cases source with
        | mk state waiting =>
          simp only at outEq pending
          subst output; subst waiting
          exact .output state identity input tail
    · obtain ⟨input, reserved, rfl, effect, prevented⟩ := hc
      obtain ⟨pre, post, pending⟩ := ht reserved
      refine ⟨.prevent identity input, ⟨source.state,pre ++ post⟩, ?_, ?_⟩
      · simp [network, h, sourceLabel, effect, prevented]
      · cases source with
        | mk state waiting =>
          simp only at pending
          subst waiting
          exact .prevent state identity input pre post

/-- Terminal evidence remains authenticated by the persistent table. An absent
or reserved response can be arbitrarily old, so it certifies no current state. -/
def ReceiptAuthentic (peer : Peer) (receipt : Receipt) : Prop :=
  match receipt.answer with
  | .published input output | .tooLate input output =>
    (lookup receipt.identity peer).1 = some (.published input output)
  | .prevented input => (lookup receipt.identity peer).1 = some (.cancelled input)
  | _ => True

theorem peerStep_receipt_authentic (peer : Peer) (identity : Nat) (command : PeerCommand) :
    ReceiptAuthentic (peerStep peer identity command).peer
      (peerStep peer identity command).receipt := by
  cases h : (lookup identity peer).1 with
  | none => cases command <;> simp [peerStep, h, dispatch, ReceiptAuthentic]
  | some entry =>
    cases entry with
    | reserved input =>
      cases command with
      | query => simp [peerStep, h, dispatch, ReceiptAuthentic]
      | reserve other =>
        by_cases hi : input = other <;> simp [peerStep, h, dispatch, ReceiptAuthentic, hi]
      | publish other output =>
        by_cases hi : input = other <;> simp [peerStep, h, dispatch, ReceiptAuthentic, hi]
      | cancel other =>
        by_cases hi : input = other <;> simp [peerStep, h, dispatch, ReceiptAuthentic, hi]
    | published input output =>
      cases command with
      | query => simp [peerStep, h, dispatch, ReceiptAuthentic]
      | reserve other =>
        by_cases hi : input = other <;> simp [peerStep, h, dispatch, ReceiptAuthentic, hi]
      | publish other out =>
        by_cases hi : input = other ∧ output = out <;>
          simp [peerStep, h, dispatch, ReceiptAuthentic, hi]
      | cancel other =>
        by_cases hi : input = other <;> simp [peerStep, h, dispatch, ReceiptAuthentic, hi]
    | cancelled input =>
      cases command with
      | query => simp [peerStep, h, dispatch, ReceiptAuthentic]
      | reserve other =>
        by_cases hi : input = other <;> simp [peerStep, h, dispatch, ReceiptAuthentic, hi]
      | publish other out =>
        by_cases hi : input = other <;> simp [peerStep, h, dispatch, ReceiptAuthentic, hi]
      | cancel other =>
        by_cases hi : input = other <;> simp [peerStep, h, dispatch, ReceiptAuthentic, hi]

theorem peerStep_preserves_authentic (peer : Peer) (identity : Nat) (command : PeerCommand)
    (receipt : Receipt) (auth : ReceiptAuthentic peer receipt) :
    ReceiptAuthentic (peerStep peer identity command).peer receipt := by
  rcases receipt with ⟨key,answer⟩
  cases answer <;> simp only [ReceiptAuthentic] at auth ⊢
  all_goals
    by_cases hi : key = identity
    · subst key
      first
      | rw [(peerStep_published _ _ _ _ _ auth).1]; exact auth
      | rw [(peerStep_cancelled _ _ _ _ auth).1]; exact auth
    · rw [peerStep_other _ _ _ _ hi]; exact auth

theorem peerExecute_preserves_authentic (peer : Peer) (commands : List (Nat × PeerCommand))
    (receipt : Receipt) (auth : ReceiptAuthentic peer receipt) :
    ReceiptAuthentic (peerExecute peer commands).peer receipt := by
  induction commands generalizing peer with
  | nil => exact auth
  | cons pair rest ih => exact ih _ (peerStep_preserves_authentic _ _ _ _ auth)

theorem peerExecute_receipts_authentic (peer : Peer) (commands : List (Nat × PeerCommand)) :
    ∀ receipt ∈ (peerExecute peer commands).receipts,
      ReceiptAuthentic (peerExecute peer commands).peer receipt := by
  induction commands generalizing peer with
  | nil => simp [peerExecute]
  | cons pair rest ih =>
    rcases pair with ⟨identity,command⟩
    intro receipt member
    simp only [peerExecute, List.mem_cons] at member
    rcases member with rfl | tail
    · exact peerExecute_preserves_authentic (peerStep peer identity command).peer rest _
        (peerStep_receipt_authentic peer identity command)
    · exact ih _ receipt tail

def pendingEntry (peer : Peer) (request : Request) : Option (Nat × Bool) :=
  match (lookup request.identity peer).1 with
  | some (.published _ _) | some (.cancelled _) => none
  | _ => some (request.identity,request.input)

/-- This mathematical view reads the durable frame and peer to establish a
relation; executable recovery continues to obtain evidence only by replies. -/
def sourceView (frame : Frame) (peer : Peer) : DelaySource :=
  { state := match frame.head with
      | none => frame.logical
      | some (_, request) => match (lookup request.identity peer).1 with
        | some (.published _ _) => request.input
        | _ => frame.logical
    waiting := frame.order.filterMap fun slot =>
      (frame.requests.get slot).bind (pendingEntry peer) }

theorem sourceView_head_reserved (frame : Frame) (peer : Peer) (slot : Bool) (r : Request)
    (head : frame.head = some (slot,r))
    (reserved : (lookup r.identity peer).1 = some (.reserved r.input)) :
    (sourceView frame peer).state = frame.logical ∧
      ∃ rest, (sourceView frame peer).waiting = (r.identity,r.input) :: rest := by
  constructor
  · simp [sourceView, head, reserved]
  · cases ho : frame.order with
    | nil => simp [Frame.head, ho] at head
    | cons first rest =>
      cases hr : frame.requests.get first with
      | none => simp [Frame.head, ho, hr] at head
      | some request =>
        simp [Frame.head, ho, hr] at head
        obtain ⟨rfl,rfl⟩ := head
        simp [sourceView, ho, hr, pendingEntry, reserved]

theorem sourceView_member_reserved (frame : Frame) (peer : Peer) (slot : Bool) (r : Request)
    (member : slot ∈ frame.order) (request : frame.requests.get slot = some r)
    (reserved : (lookup r.identity peer).1 = some (.reserved r.input)) :
    ∃ pre post, (sourceView frame peer).waiting = pre ++ (r.identity,r.input) :: post := by
  apply List.mem_iff_append.mp
  apply List.mem_filterMap.mpr
  exact ⟨slot, member, by simp [request, pendingEntry, reserved]⟩



/-- An old terminal message remains legitimate after its slot has been reused.
A message that can still act must refer to the retained occupied request;
publication additionally names the head and selected old logical state. -/
def FrameTraffic (frame : Frame) (peer : Peer) (identity : Nat) (command : PeerCommand) : Prop :=
  (∃ input output, (lookup identity peer).1 = some (.published input output)) ∨
  (∃ input, (lookup identity peer).1 = some (.cancelled input)) ∨
  ∃ slot request, slot ∈ frame.order ∧ frame.requests.get slot = some request ∧
    request.identity = identity ∧
    match command with
    | .publish input output => input = request.input ∧ output = frame.logical ∧
        frame.head = some (slot,request)
    | .reserve input | .cancel input => input = request.input
    | .query => True

theorem FrameTraffic.sourceTraffic (frame : Frame) (peer : Peer) (identity : Nat)
    (command : PeerCommand) (traffic : FrameTraffic frame peer identity command) :
    SourceTraffic (sourceView frame peer) peer identity command := by
  rcases traffic with published | cancelled | live
  · obtain ⟨input,output,terminal⟩ := published
    cases command <;> simp [SourceTraffic, terminal]
  · obtain ⟨input,terminal⟩ := cancelled
    cases command <;> simp [SourceTraffic, terminal]
  · obtain ⟨slot, request, member, present, identityEq, commandEq⟩ := live
    subst identity
    cases command with
    | query => trivial
    | reserve input => trivial
    | publish input output =>
      obtain ⟨rfl,rfl,head⟩ := commandEq
      intro reserved
      obtain ⟨state,rest,waiting⟩ := sourceView_head_reserved frame peer slot request head reserved
      exact ⟨state.symm,rest,waiting⟩
    | cancel input =>
      subst input
      exact sourceView_member_reserved frame peer slot request member present

theorem network_frame_source_step (s : System) (frame : Frame) (deliver : Bool)
    (traffic : ∀ identity command, (identity,command) ∈ s.outbound →
      FrameTraffic frame s.peer identity command) :
    ∃ label next, sourceLabel (network s deliver).toLogEntry = some label ∧
      DelayStep label (sourceView frame s.peer) next :=
  network_source_step s (sourceView frame s.peer) deliver fun identity command member =>
    FrameTraffic.sourceTraffic _ _ _ _ (traffic identity command member)

theorem pendingEntry_reserve (peer : Peer) (identity : Nat) (input : Bool) (r : Request)
    (absent : (lookup identity peer).1 = none) :
    pendingEntry (install identity (.reserved input) peer).1 r = pendingEntry peer r := by
  by_cases hi : r.identity = identity
  · simp [pendingEntry, hi, absent]
  · simp [pendingEntry, lookup_install_other _ _ _ _ hi]

theorem sourceView_reserve (frame : Frame) (peer : Peer) (identity : Nat) (input : Bool)
    (absent : (lookup identity peer).1 = none) :
    sourceView frame (install identity (.reserved input) peer).1 = sourceView frame peer := by
  apply congrArg₂ DelaySource.mk
  · cases head : frame.head with
    | none => rfl
    | some pair =>
      rcases pair with ⟨slot,r⟩
      by_cases hi : r.identity = identity
      · simp [hi, absent]
      · simp [lookup_install_other _ _ _ _ hi]
  · congr 1
    funext slot
    cases present : frame.requests.get slot with
    | none => rfl
    | some r => exact pendingEntry_reserve peer identity input r absent

/-- A peer transition with no source observation either changes nothing, or
only changes absent to reserved. Neither transition changes source behavior. -/
theorem peerStep_silent_shape (peer : Peer) (identity : Nat) (command : PeerCommand)
    (effect : (peerStep peer identity command).effect = none)
    (prevented : (peerStep peer identity command).prevented = none) :
    (peerStep peer identity command).peer = peer ∨
      ∃ input, (lookup identity peer).1 = none ∧
        (peerStep peer identity command).peer = (install identity (.reserved input) peer).1 := by
  cases h : (lookup identity peer).1 with
  | none =>
    cases command with
    | reserve input => exact Or.inr ⟨input,rfl,by simp [peerStep,h,dispatch]⟩
    | query => simp [peerStep,h,dispatch]
    | publish input output => simp [peerStep,h,dispatch]
    | cancel input => simp [peerStep,h,dispatch]
  | some entry =>
    cases entry with
    | reserved input =>
      cases command with
      | query => simp [peerStep, h, dispatch]
      | reserve other => simp [peerStep, h, dispatch]
      | publish other output =>
        by_cases hi : input = other
        · simp [peerStep, h, dispatch, hi] at effect
        · simp [peerStep, h, dispatch, hi]
      | cancel other =>
        by_cases hi : input = other
        · simp [peerStep, h, dispatch, hi] at prevented
        · simp [peerStep, h, dispatch, hi]
    | published input output => cases command <;> simp [peerStep, h, dispatch]
    | cancelled input => cases command <;> simp [peerStep, h, dispatch]

theorem peerStep_sourceView_stutter (frame : Frame) (peer : Peer) (identity : Nat)
    (command : PeerCommand) (effect : (peerStep peer identity command).effect = none)
    (prevented : (peerStep peer identity command).prevented = none) :
    sourceView frame (peerStep peer identity command).peer = sourceView frame peer := by
  rcases peerStep_silent_shape peer identity command effect prevented with unchanged | reserved
  · rw [unchanged]
  · obtain ⟨input, absent, installed⟩ := reserved
    rw [installed]
    exact sourceView_reserve frame peer identity input absent

theorem pendingSlots_install_other (frame : Frame) (peer : Peer) (identity : Nat)
    (entry : Ledger) (slots : List Bool)
    (separate : ∀ slot ∈ slots, ∀ request ∈ frame.requests.get slot, request.identity ≠ identity) :
    (slots.filterMap fun slot => (frame.requests.get slot).bind
      (pendingEntry (install identity entry peer).1)) =
    (slots.filterMap fun slot => (frame.requests.get slot).bind (pendingEntry peer)) := by
  induction slots with
  | nil => rfl
  | cons slot rest ih =>
    have restEq := ih (by intro other member request present; exact separate other (by simp [member]) request present)
    cases present : frame.requests.get slot with
    | none => simpa [present] using restEq
    | some request =>
      have different := separate slot (by simp) request (by simp [present])
      simp only [List.filterMap_cons, present, Option.bind_some]
      rw [show pendingEntry (install identity entry peer).1 request = pendingEntry peer request by
        simp [pendingEntry, lookup_install_other _ _ _ _ different]]
      cases pendingEntry peer request <;> simp [restEq]

/-- The actual atomic peer publication consumes the ordered source head and
changes its state to the admitted input. The tail keeps every delayed message
and every other pending occurrence; only distinct identities are required. -/
theorem peerStep_sourceView_publish (frame : Frame) (peer : Peer) (slot : Bool)
    (request : Request) (tail : List Bool)
    (order : frame.order = slot :: tail) (present : frame.requests.get slot = some request)
    (reserved : (lookup request.identity peer).1 = some (.reserved request.input))
    (separate : ∀ other ∈ tail, ∀ r ∈ frame.requests.get other, r.identity ≠ request.identity) :
    DelayStep (.output request.identity frame.logical) (sourceView frame peer)
      (sourceView frame (peerStep peer request.identity (.publish request.input frame.logical)).peer) := by
  let remaining := tail.filterMap fun slot => (frame.requests.get slot).bind (pendingEntry peer)
  have before : sourceView frame peer =
      ⟨frame.logical, (request.identity,request.input) :: remaining⟩ := by
    simp [sourceView, Frame.head, order, present, pendingEntry, reserved, remaining]
  have restEq := pendingSlots_install_other frame peer request.identity
    (.published request.input frame.logical) tail separate
  have after : sourceView frame (peerStep peer request.identity
      (.publish request.input frame.logical)).peer = ⟨request.input,remaining⟩ := by
    simp only [peerStep, reserved, dispatch, ite_true]
    simp [sourceView, Frame.head, order, present, pendingEntry, restEq, remaining]
  rw [before,after]
  exact .output frame.logical request.identity request.input remaining

example (kind : Migration.Kind) : sourceView (initialFrame kind) [] = ({} : DelaySource) := rfl

/-- A late conflicting publication for a released lifetime remains present in
the model and stutters, rather than being erased to satisfy a queue invariant. -/
example : FrameTraffic (initialFrame .delay) [(99,.published true false)] 99
    (.publish false true) := by
  left
  exact ⟨true,false,by decide⟩

theorem FrameTraffic.peerStep (frame : Frame) (peer : Peer) (identity changed : Nat)
    (command action : PeerCommand) (traffic : FrameTraffic frame peer identity command) :
    FrameTraffic frame (peerStep peer changed action).peer identity command := by
  rcases traffic with published | cancelled | live
  · obtain ⟨input, output, recorded⟩ := published
    exact Or.inl ⟨input,output,peerStep_preserves_authentic peer changed action
      ⟨identity,.published input output⟩ recorded⟩
  · obtain ⟨input,recorded⟩ := cancelled
    exact Or.inr (Or.inl ⟨input,peerStep_preserves_authentic peer changed action
      ⟨identity,.prevented input⟩ recorded⟩)
  · exact Or.inr (Or.inr live)

theorem FrameTraffic.peerExecute (frame : Frame) (peer : Peer) (identity : Nat)
    (command : PeerCommand) (actions : List (Nat × PeerCommand))
    (traffic : FrameTraffic frame peer identity command) :
    FrameTraffic frame (peerExecute peer actions).peer identity command := by
  induction actions generalizing peer with
  | nil => exact traffic
  | cons action actions ih => exact ih _ (FrameTraffic.peerStep _ _ _ _ _ _ traffic)

theorem sourceView_cancel_state (frame : Frame) (peer : Peer) (identity : Nat) (input : Bool)
    (reserved : (lookup identity peer).1 = some (.reserved input)) :
    (sourceView frame (install identity (.cancelled input) peer).1).state =
      (sourceView frame peer).state := by
  cases head : frame.head with
  | none => simp [sourceView,head]
  | some pair =>
    rcases pair with ⟨slot,r⟩
    by_cases hi : r.identity = identity
    · simp [sourceView,head,hi,reserved]
    · simp [sourceView,head,lookup_install_other _ _ _ _ hi]

theorem peerStep_sourceView_cancel (frame : Frame) (peer : Peer) (slot : Bool)
    (request : Request) (pre post : List Bool)
    (order : frame.order = pre ++ slot :: post) (present : frame.requests.get slot = some request)
    (reserved : (lookup request.identity peer).1 = some (.reserved request.input))
    (separatePre : ∀ other ∈ pre, ∀ r ∈ frame.requests.get other, r.identity ≠ request.identity)
    (separatePost : ∀ other ∈ post, ∀ r ∈ frame.requests.get other, r.identity ≠ request.identity) :
    DelayStep (.prevent request.identity request.input) (sourceView frame peer)
      (sourceView frame (peerStep peer request.identity (.cancel request.input)).peer) := by
  let beforePending := pre.filterMap fun slot => (frame.requests.get slot).bind (pendingEntry peer)
  let afterPending := post.filterMap fun slot => (frame.requests.get slot).bind (pendingEntry peer)
  have before : sourceView frame peer = ⟨(sourceView frame peer).state,
      beforePending ++ (request.identity,request.input) :: afterPending⟩ := by
    apply congrArg₂ DelaySource.mk
    · rfl
    · simp [order, present, pendingEntry, reserved, beforePending, afterPending]
  have beforeEq := pendingSlots_install_other frame peer request.identity
    (.cancelled request.input) pre separatePre
  have afterEq := pendingSlots_install_other frame peer request.identity
    (.cancelled request.input) post separatePost
  have after : sourceView frame (peerStep peer request.identity (.cancel request.input)).peer =
      ⟨(sourceView frame peer).state, beforePending ++ afterPending⟩ := by
    simp only [peerStep, reserved, dispatch, ite_true]
    apply congrArg₂ DelaySource.mk
    · exact sourceView_cancel_state frame peer request.identity request.input reserved
    · simp [order, present, pendingEntry, beforeEq, afterEq, beforePending, afterPending]
  exact (congrArg₂ (DelayStep (.prevent request.identity request.input)) before after).mpr
    (.prevent (sourceView frame peer).state request.identity request.input beforePending afterPending)

def requestProjection (frame : Frame) (slot : Bool) : Option (Nat × Bool) :=
  (frame.requests.get slot).map fun r => (r.identity,r.input)

def projectedSource (logical : Bool) (order : List Bool)
    (slots : Bool → Option (Nat × Bool)) (peer : Peer) : DelaySource :=
  { state := match order.head?.bind slots with
      | none => logical
      | some key => match (lookup key.1 peer).1 with
        | some (.published _ _) => key.2
        | _ => logical
    waiting := order.filterMap fun slot => (slots slot).bind fun key =>
      match (lookup key.1 peer).1 with
      | some (.published _ _) | some (.cancelled _) => none
      | _ => some key }

theorem sourceView_projected (frame : Frame) (peer : Peer) :
    sourceView frame peer = projectedSource frame.logical frame.order (requestProjection frame) peer := by
  apply congrArg₂ DelaySource.mk
  · cases order : frame.order with
    | nil => simp [Frame.head,order]
    | cons slot rest =>
      cases present : frame.requests.get slot <;> simp [Frame.head,order,requestProjection,present]
  · congr 1
    funext slot
    cases present : frame.requests.get slot <;> simp [requestProjection,present,pendingEntry]

theorem sourceView_projection (before after : Frame) (peer : Peer)
    (order : before.order = after.order) (logical : before.logical = after.logical)
    (requests : ∀ slot, requestProjection before slot = requestProjection after slot) :
    sourceView before peer = sourceView after peer := by
  rw [sourceView_projected, sourceView_projected, order, logical, funext requests]

theorem head_order_eq (frame : Frame) (slot : Bool) (request : Request)
    (head : frame.head = some (slot,request)) : frame.order.head? = some slot := by
  cases first : frame.order.head? with
  | none => simp [Frame.head,first] at head
  | some other =>
    cases present : frame.requests.get other with
    | none => simp [Frame.head,first,present] at head
    | some r =>
      simp [Frame.head,first,present] at head
      exact congrArg some head.1

theorem requestProjection_exists (before after : Frame) (slot : Bool) (request : Request)
    (present : before.requests.get slot = some request)
    (projection : requestProjection before slot = requestProjection after slot) :
    ∃ next, after.requests.get slot = some next ∧
      request.identity = next.identity ∧ request.input = next.input := by
  cases target : after.requests.get slot with
  | none => simp [requestProjection,present,target] at projection
  | some next =>
    simp [requestProjection,present,target] at projection
    exact ⟨next,rfl,projection⟩

theorem FrameTraffic.projection (before after : Frame) (peer : Peer) (identity : Nat)
    (command : PeerCommand) (order : before.order = after.order)
    (logical : before.logical = after.logical)
    (requests : ∀ slot, requestProjection before slot = requestProjection after slot)
    (traffic : FrameTraffic before peer identity command) :
    FrameTraffic after peer identity command := by
  rcases traffic with published | cancelled | live
  · exact Or.inl published
  · exact Or.inr (Or.inl cancelled)
  · obtain ⟨slot,request,member,present,identityEq,commandEq⟩ := live
    obtain ⟨next,target,idEq,inputEq⟩ := requestProjection_exists before after slot request
      present (requests slot)
    refine Or.inr (Or.inr ⟨slot,next,order ▸ member,target,idEq.symm.trans identityEq,?_⟩)
    cases command with
    | query => trivial
    | reserve input => exact commandEq.trans inputEq
    | cancel input => exact commandEq.trans inputEq
    | publish input output =>
      obtain ⟨inputMatches,outputMatches,head⟩ := commandEq
      refine ⟨inputMatches.trans inputEq,outputMatches.trans logical,?_⟩
      have first : after.order.head? = some slot := order ▸ head_order_eq before slot request head
      simp [Frame.head,first,target]

theorem frame_valid_identity_separate (frame : Frame) (slot other : Bool)
    (request candidate : Request) (valid : frame.Valid) (different : other ≠ slot)
    (present : frame.requests.get slot = some request)
    (found : candidate ∈ frame.requests.get other) : candidate.identity ≠ request.identity := by
  have distinct := valid.2.2.2.2
  cases slot <;> cases other
  · exact False.elim (different rfl)
  · simp only [Slots.get, Bool.false_eq_true, ite_false] at present
    simp only [Slots.get, ite_true] at found
    exact Ne.symm (distinct request (by simp [present]) candidate found)
  · simp only [Slots.get, ite_true] at present
    simp only [Slots.get, Bool.false_eq_true, ite_false] at found
    exact distinct candidate found request (by simp [present])
  · exact False.elim (different rfl)

theorem frame_valid_separate_around (frame : Frame) (slot : Bool) (request : Request)
    (pre post : List Bool) (valid : frame.Valid)
    (order : frame.order = pre ++ slot :: post)
    (present : frame.requests.get slot = some request) :
    (∀ other ∈ pre, ∀ r ∈ frame.requests.get other, r.identity ≠ request.identity) ∧
    (∀ other ∈ post, ∀ r ∈ frame.requests.get other, r.identity ≠ request.identity) := by
  have nodup : (pre ++ slot :: post).Nodup := order ▸ valid.1
  constructor
  · intro other member r found
    apply frame_valid_identity_separate frame slot other request r valid _ present found
    intro same
    subst other
    exact (List.disjoint_left.mp (List.disjoint_of_nodup_append nodup)) member (by simp)
  · intro other member r found
    apply frame_valid_identity_separate frame slot other request r valid _ present found
    intro same
    subst other
    exact (List.nodup_cons.mp nodup.of_append_right).1 member

/-- Full one-step peer/source simulation with the resulting mathematical view
fixed by the actual post-state. Frame validity supplies occurrence uniqueness;
traffic provenance supplies selected-output and admission-order correctness. -/
theorem network_sourceView_refines (s : System) (frame : Frame) (deliver : Bool)
    (valid : frame.Valid)
    (traffic : ∀ identity command, (identity,command) ∈ s.outbound →
      FrameTraffic frame s.peer identity command) :
    ∃ label, sourceLabel (network s deliver).toLogEntry = some label ∧
      DelayStep label (sourceView frame s.peer) (sourceView frame (network s deliver).system.peer) := by
  cases h : s.outbound with
  | nil => exact ⟨.internal,by simp [network,h,reject,sourceLabel],by simpa [network,h,reject] using DelayStep.internal (sourceView frame s.peer)⟩
  | cons message rest =>
    rcases message with ⟨identity,command⟩
    have ht := traffic identity command (by simp [h])
    rcases peerStep_outcomes s.peer identity command with silent | published | cancelled
    · refine ⟨.internal,by simp [network,h,sourceLabel,silent.1,silent.2],?_⟩
      have unchanged := peerStep_sourceView_stutter frame s.peer identity command silent.1 silent.2
      simpa [network,h,unchanged] using DelayStep.internal (sourceView frame s.peer)
    · obtain ⟨input,output,reserved,rfl,effect,prevented⟩ := published
      refine ⟨.output identity output,by simp [network,h,sourceLabel,effect,prevented],?_⟩
      rcases ht with terminal | terminal | live
      · obtain ⟨x,y,recorded⟩ := terminal; simp [reserved] at recorded
      · obtain ⟨x,recorded⟩ := terminal; simp [reserved] at recorded
      · obtain ⟨slot,request,member,present,idEq,inputEq,outputEq,head⟩ := live
        subst identity; subst input; subst output
        have first := head_order_eq frame slot request head
        cases order : frame.order with
        | nil => simp [order] at first
        | cons other tail =>
          simp [order] at first
          subst other
          have separated := (frame_valid_separate_around frame slot request [] tail valid order present).2
          simpa [network,h] using peerStep_sourceView_publish frame s.peer slot request tail order present reserved separated
    · obtain ⟨input,reserved,rfl,effect,prevented⟩ := cancelled
      refine ⟨.prevent identity input,by simp [network,h,sourceLabel,effect,prevented],?_⟩
      rcases ht with terminal | terminal | live
      · obtain ⟨x,y,recorded⟩ := terminal; simp [reserved] at recorded
      · obtain ⟨x,recorded⟩ := terminal; simp [reserved] at recorded
      · obtain ⟨slot,request,member,present,idEq,inputEq⟩ := live
        subst identity; subst input
        obtain ⟨pre,post,order⟩ := List.mem_iff_append.mp member
        obtain ⟨beforeSeparate,afterSeparate⟩ := frame_valid_separate_around frame slot request pre post valid order present
        simpa [network,h] using peerStep_sourceView_cancel frame s.peer slot request pre post order present reserved beforeSeparate afterSeparate

/-- The peer may already have cancelled or published while the corresponding
local terminal frame is still awaiting persistence. Accepted cannot already
be published: publication requires an earlier durable computed frame. -/
def RequestPeer (peer : Peer) (request : Request) : Prop :=
  let found := (lookup request.identity peer).1
  let live := found = none ∨ found = some (.reserved request.input) ∨
    found = some (.cancelled request.input)
  let published := ∃ output, request.output = some output ∧
    found = some (.published request.input output)
  match request.phase with
  | .accepted => live
  | .computed => live ∨ published
  | .confirmed | .committed => published
  | .cancelled => found = some (.cancelled request.input)

def FramePeer (frame : Frame) (peer : Peer) : Prop :=
  ∀ slot request, request ∈ frame.requests.get slot → RequestPeer peer request

/-- Stronger than the source observation: a message that can still publish
must originate from the durable selected computed head. -/
def PublicationProvenance (frame : Frame) (peer : Peer) (identity : Nat)
    (command : PeerCommand) : Prop :=
  match command with
  | .publish input output =>
    ((lookup identity peer).1 = none ∨ ∃ reserved, (lookup identity peer).1 = some (.reserved reserved)) →
    ∃ slot request, frame.head = some (slot,request) ∧ request.identity = identity ∧
      request.input = input ∧ request.output = some output ∧ request.phase = .computed
  | _ => True

theorem requestPeer_waiting_not_published (peer : Peer) (request : Request)
    (coupled : RequestPeer peer request)
    (waiting : request.phase = .accepted ∨ request.phase = .cancelled)
    (input output : Bool) :
    (lookup request.identity peer).1 ≠ some (.published input output) := by
  rcases waiting with accepted | cancelled
  · simp only [RequestPeer,accepted] at coupled
    rcases coupled with absent | reserved | prevented <;> simp_all
  · simp only [RequestPeer,cancelled] at coupled
    simp [coupled]

theorem FramePeer.initial (kind : Migration.Kind) : FramePeer (initialFrame kind) [] := by
  intro slot request present
  cases slot <;> simp [initialFrame,Slots.get] at present

/-- While the head's peer effect is already published, source state has already
advanced. Installing the same input in the local logical state is a stutter. -/
theorem sourceView_projection_published (before after : Frame) (peer : Peer)
    (order : before.order = after.order)
    (requests : ∀ slot, requestProjection before slot = requestProjection after slot)
    (identity : Nat) (input output : Bool)
    (head : before.order.head?.bind (requestProjection before) = some (identity,input))
    (published : (lookup identity peer).1 = some (.published input output)) :
    sourceView before peer = sourceView after peer := by
  rw [sourceView_projected, sourceView_projected]
  have targetHead : after.order.head?.bind (requestProjection after) = some (identity,input) := by
    rw [← order, ← funext requests]
    exact head
  simp [projectedSource,targetHead,published,order,funext requests]

theorem projectedSource_congr_on_order (logical : Bool) (order : List Bool)
    (before after : Bool → Option (Nat × Bool)) (peer : Peer)
    (equal : ∀ slot ∈ order, before slot = after slot) :
    projectedSource logical order before peer = projectedSource logical order after peer := by
  induction order with
  | nil => rfl
  | cons slot rest ih =>
    have first := equal slot (by simp)
    have tail := ih (by intro other member; exact equal other (by simp [member]))
    have waiting := congrArg DelaySource.waiting tail
    simp only [projectedSource] at waiting ⊢
    rw [List.head?_cons, Option.bind_some, first]
    apply congrArg₂ DelaySource.mk rfl
    simp only [List.filterMap_cons, first]
    cases h : (after slot).bind (fun key => match (lookup key.1 peer).1 with
      | some (.published _ _) | some (.cancelled _) => none
      | _ => some key) <;> simp [waiting]

theorem sourceView_tail_state (frame : Frame) (peer : Peer)
    (valid : frame.Valid) (coupled : FramePeer frame peer) :
    (projectedSource frame.logical frame.order.tail (requestProjection frame) peer).state = frame.logical := by
  cases first : frame.order.tail.head? with
  | none => simp [projectedSource,first]
  | some slot =>
    have member : slot ∈ frame.order.tail := List.mem_of_mem_head? first
    cases present : frame.requests.get slot with
    | none => simp [projectedSource,first,requestProjection,present]
    | some request =>
      have found : request ∈ frame.requests.get slot := by simp [present]
      have phase := (valid.2.2.2.1 slot request found).2.2 member
      have impossible := requestPeer_waiting_not_published peer request (coupled slot request found) phase
      cases recorded : (lookup request.identity peer).1 with
      | none => simp [projectedSource,first,requestProjection,present,recorded]
      | some entry =>
        cases entry with
        | reserved input => simp [projectedSource,first,requestProjection,present,recorded]
        | cancelled input => simp [projectedSource,first,requestProjection,present,recorded]
        | published input output => exact False.elim (impossible input output recorded)

theorem head_request_eq (frame : Frame) (slot : Bool) (request : Request)
    (head : frame.head = some (slot,request)) : frame.requests.get slot = some request := by
  have first := head_order_eq frame slot request head
  cases present : frame.requests.get slot with
  | none => simp [Frame.head,first,present] at head
  | some other =>
    simp [Frame.head,first,present] at head
    exact congrArg some head

theorem sourceView_terminal_head (frame : Frame) (peer : Peer) (slot : Bool) (request : Request)
    (valid : frame.Valid) (coupled : FramePeer frame peer)
    (head : frame.head = some (slot,request)) (finished : terminal request.phase = true) :
    (sourceView frame peer).state = frame.logical ∧ pendingEntry peer request = none := by
  have present := head_request_eq frame slot request head
  have found : request ∈ frame.requests.get slot := by simp [present]
  have wellFormed := (valid.2.2.2.1 slot request found).2.1
  have recorded := coupled slot request found
  cases phase : request.phase <;> simp [terminal,phase] at finished
  case committed =>
    simp only [RequestPeer,phase] at recorded
    obtain ⟨output,selected,published⟩ := recorded
    simp only [requestValid,phase] at wellFormed
    have inputEq : request.input = frame.logical := wellFormed.2.1
    simp [sourceView,head,published,inputEq,pendingEntry]
  case cancelled =>
    simp only [RequestPeer,phase] at recorded
    simp [sourceView,head,recorded,pendingEntry]

theorem requestProjection_release_other (frame : Frame) (slot other : Bool) (different : other ≠ slot) :
    requestProjection {frame with requests := frame.requests.put slot none, order := frame.order.tail} other =
      requestProjection frame other := by
  cases slot <;> cases other <;> simp_all [requestProjection,Slots.get,Slots.put]

theorem sourceView_release (frame : Frame) (peer : Peer) (slot : Bool) (request : Request)
    (valid : frame.Valid) (coupled : FramePeer frame peer)
    (head : frame.head = some (slot,request)) (finished : terminal request.phase = true) :
    sourceView frame peer =
      sourceView {frame with requests := frame.requests.put slot none, order := frame.order.tail} peer := by
  have first := head_order_eq frame slot request head
  have present := head_request_eq frame slot request head
  obtain ⟨state,pending⟩ := sourceView_terminal_head frame peer slot request valid coupled head finished
  cases order : frame.order with
  | nil => simp [order] at first
  | cons other tail =>
    simp [order] at first
    subst other
    have notTail : slot ∉ tail := (List.nodup_cons.mp (order ▸ valid.1)).1
    have after : sourceView {frame with requests := frame.requests.put slot none, order := frame.order.tail} peer =
        projectedSource frame.logical frame.order.tail (requestProjection frame) peer := by
      rw [sourceView_projected]
      apply projectedSource_congr_on_order
      intro other member
      apply requestProjection_release_other
      intro same
      subst other
      exact notTail (by simpa [order] using member)
    rw [order] at after
    rw [after]
    apply congrArg₂ DelaySource.mk
    · simpa only [sourceView,projectedSource,order,List.tail_cons] using state.trans (sourceView_tail_state frame peer valid coupled).symm
    · simp only [order,List.tail_cons,List.filterMap_cons,present,Option.bind_some,pending]
      exact congrArg DelaySource.waiting (sourceView_projected {frame with order := tail} peer)

theorem FramePeer.update (frame : Frame) (peer : Peer) (slot : Bool) (request : Request)
    (coupled : FramePeer frame peer) (next : RequestPeer peer request) :
    FramePeer (frame.update slot request) peer := by
  intro other candidate found
  by_cases same : other = slot
  · subst other
    have equal : request = candidate := by
      cases slot <;> simpa [Frame.update,Slots.get,Slots.put] using found
    subst candidate
    exact next
  · have unchanged : (frame.update slot request).requests.get other = frame.requests.get other := by
      cases slot <;> cases other <;> simp_all [Frame.update,Slots.get,Slots.put]
    exact coupled other candidate (unchanged ▸ found)

theorem find_request_eq (frame : Frame) (identity : Nat) (slot : Bool) (request : Request)
    (found : frame.find identity = some (slot, request)) :
    frame.requests.get slot = some request ∧ request.identity = identity := by
  unfold Frame.find at found
  obtain ⟨actual, _, lookup⟩ := List.exists_of_findSome?_eq_some found
  cases hr : frame.requests.get actual with
  | none => simp [hr] at lookup
  | some value =>
    simp only [hr, Bind.bind, Option.bind] at lookup
    split at lookup
    · simp only [Option.some.injEq, Prod.mk.injEq] at lookup
      rcases lookup with ⟨rfl,rfl⟩
      exact ⟨hr,by assumption⟩
    · contradiction

theorem receive_framePeer (before after : Frame) (peer : Peer) (receipt : Receipt)
    (coupled : FramePeer before peer) (authentic : ReceiptAuthentic peer receipt)
    (changed : receive before receipt = .changed after) : FramePeer after peer := by
  rcases receipt with ⟨identity,answer⟩
  unfold receive at changed
  cases found : before.find identity with
  | none => simp [found] at changed
  | some pair =>
    rcases pair with ⟨slot,request⟩
    obtain ⟨present,idEq⟩ := find_request_eq before identity slot request found
    simp only [found] at changed
    cases answer
    all_goals repeat' first
      | simp_all only [reduceCtorEq, Decision.changed.injEq]
      | split at changed
    all_goals subst after
    all_goals apply FramePeer.update before peer slot _ coupled
    all_goals simp_all [RequestPeer,ReceiptAuthentic]

theorem FramePeer.clear (frame : Frame) (peer : Peer) (slot : Bool)
    (coupled : FramePeer frame peer) :
    FramePeer {frame with requests := frame.requests.put slot none} peer := by
  intro other candidate found
  by_cases same : other = slot
  · subst other
    cases slot <;> simp [Slots.get,Slots.put] at found
  · have unchanged : (frame.requests.put slot none).get other = frame.requests.get other := by
      cases slot <;> cases other <;> simp_all [Slots.get,Slots.put]
    exact coupled other candidate (unchanged ▸ found)

def CommandAuthentic (peer : Peer) : FrameCommand → Prop
  | .receive receipt => ReceiptAuthentic peer receipt
  | _ => True

theorem propose_framePeer (before after : Frame) (peer : Peer) (command : FrameCommand)
    (coupled : FramePeer before peer)
    (fresh : (lookup before.nextIdentity peer).1 = none)
    (authentic : CommandAuthentic peer command)
    (changed : propose before command = .changed after) : FramePeer after peer := by
  cases command with
  | receive receipt => exact receive_framePeer before after peer receipt coupled authentic changed
  | migrate kind => cases changed; exact coupled
  | accept input =>
    simp only [propose] at changed
    repeat' first
      | simp_all only [reduceCtorEq, Decision.changed.injEq]
      | split at changed
    all_goals subst after
    all_goals apply FramePeer.update before peer _ _ coupled
    all_goals simp [RequestPeer,fresh]
  | evaluate | tickCommit | close | release =>
    simp only [propose] at changed
    cases head : before.head with
    | none => simp [head] at changed
    | some pair =>
      rcases pair with ⟨slot,request⟩
      have present := head_request_eq before slot request head
      have recorded := coupled slot request (by simp [present])
      simp only [head] at changed
      split at changed
      · cases changed
        first
        | exact FramePeer.clear before peer slot coupled
        | apply FramePeer.update before peer slot _ coupled
        all_goals simp_all [RequestPeer,Bool.and_eq_true,beq_iff_eq]
      · contradiction

/-- Only actions that can change a live table entry need stronger provenance.
Conflicting retries and terminal messages are handled by the peer itself. -/
def PeerCommandSafe (peer : Peer) (request : Request) : PeerCommand → Prop
  | .reserve input => (lookup request.identity peer).1 = none → input = request.input
  | .publish input output =>
    (lookup request.identity peer).1 = some (.reserved request.input) → input = request.input →
      request.phase = .computed ∧ request.output = some output
  | _ => True

theorem requestPeer_step_same (peer : Peer) (request : Request) (command : PeerCommand)
    (coupled : RequestPeer peer request) (safe : PeerCommandSafe peer request command) :
    RequestPeer (peerStep peer request.identity command).peer request := by
  cases found : (lookup request.identity peer).1 with
  | none =>
    cases command with
    | reserve input =>
      have inputEq := safe found
      subst input
      cases phase : request.phase <;> simp_all [RequestPeer,peerStep,dispatch]
    | query => simpa [peerStep,found,dispatch] using coupled
    | publish input output => simpa [peerStep,found,dispatch] using coupled
    | cancel input => simpa [peerStep,found,dispatch] using coupled
  | some entry =>
    cases entry with
    | published input output =>
      rw [(peerStep_published _ _ _ _ _ found).1]
      exact coupled
    | cancelled input =>
      rw [(peerStep_cancelled _ _ _ _ found).1]
      exact coupled
    | reserved input =>
      have inputEq : input = request.input := by
        cases phase : request.phase <;> simp_all [RequestPeer]
      subst input
      cases command with
      | query => simpa [peerStep,found,dispatch] using coupled
      | reserve other => simpa [peerStep,found,dispatch] using coupled
      | publish other output =>
        by_cases same : request.input = other
        · subst other
          obtain ⟨phase,selected⟩ := safe found rfl
          simp [RequestPeer,phase,selected,peerStep,found,dispatch]
        · simpa [peerStep,found,dispatch,same] using coupled
      | cancel other =>
        by_cases same : request.input = other
        · subst other
          cases phase : request.phase <;> simp_all [RequestPeer,peerStep,dispatch]
        · simpa [peerStep,found,dispatch,same] using coupled

theorem requestPeer_step_other (peer : Peer) (request : Request) (identity : Nat)
    (command : PeerCommand) (coupled : RequestPeer peer request)
    (different : request.identity ≠ identity) :
    RequestPeer (peerStep peer identity command).peer request := by
  unfold RequestPeer at coupled ⊢
  rw [peerStep_other _ _ _ _ different]
  exact coupled

theorem FramePeer.step (frame : Frame) (peer : Peer) (identity : Nat) (command : PeerCommand)
    (coupled : FramePeer frame peer)
    (safe : ∀ slot request, request ∈ frame.requests.get slot → request.identity = identity →
      PeerCommandSafe peer request command) : FramePeer frame (peerStep peer identity command).peer := by
  intro slot request present
  by_cases same : request.identity = identity
  · subst identity
    exact requestPeer_step_same peer request command (coupled slot request present)
      (safe slot request present rfl)
  · exact requestPeer_step_other peer request identity command (coupled slot request present) same

theorem frame_valid_same_identity (frame : Frame) (slot other : Bool)
    (request candidate : Request) (valid : frame.Valid)
    (present : frame.requests.get slot = some request)
    (found : frame.requests.get other = some candidate)
    (sameIdentity : request.identity = candidate.identity) : request = candidate := by
  by_cases same : other = slot
  · subst other
    exact Option.some.inj (present.symm.trans found)
  · exact False.elim ((frame_valid_identity_separate frame slot other request candidate valid same
      present (by simp [found])) sameIdentity.symm)

theorem peerCommandSafe_of_traffic (frame : Frame) (peer : Peer) (identity : Nat)
    (command : PeerCommand) (valid : frame.Valid)
    (traffic : FrameTraffic frame peer identity command)
    (provenance : PublicationProvenance frame peer identity command)
    (slot : Bool) (request : Request) (present : request ∈ frame.requests.get slot)
    (idEq : request.identity = identity) : PeerCommandSafe peer request command := by
  subst identity
  have presentEq : frame.requests.get slot = some request := by simpa using present
  cases command with
  | query => trivial
  | cancel input => trivial
  | reserve input =>
    intro absent
    rcases traffic with published | cancelled | live
    · obtain ⟨x,y,recorded⟩ := published; simp [absent] at recorded
    · obtain ⟨x,recorded⟩ := cancelled; simp [absent] at recorded
    · obtain ⟨other,candidate,member,found,sameIdentity,inputEq⟩ := live
      have same := frame_valid_same_identity frame slot other request candidate valid presentEq found sameIdentity.symm
      subst candidate
      exact inputEq
  | publish input output =>
    intro reserved inputEq
    obtain ⟨other,candidate,head,sameIdentity,inputMatches,selected,phase⟩ :=
      provenance (Or.inr ⟨request.input,reserved⟩)
    have found := head_request_eq frame other candidate head
    have same := frame_valid_same_identity frame slot other request candidate valid presentEq found sameIdentity.symm
    subst candidate
    exact ⟨phase,selected⟩

theorem FramePeer.step_of_traffic (frame : Frame) (peer : Peer) (identity : Nat)
    (command : PeerCommand) (valid : frame.Valid) (coupled : FramePeer frame peer)
    (traffic : FrameTraffic frame peer identity command)
    (provenance : PublicationProvenance frame peer identity command) :
    FramePeer frame (peerStep peer identity command).peer :=
  FramePeer.step frame peer identity command coupled
    (peerCommandSafe_of_traffic frame peer identity command valid traffic provenance)

theorem peerStep_nonterminal_before (peer : Peer) (identity changed : Nat) (action : PeerCommand)
    (after : (lookup identity (peerStep peer changed action).peer).1 = none ∨
      ∃ input, (lookup identity (peerStep peer changed action).peer).1 = some (.reserved input)) :
    (lookup identity peer).1 = none ∨ ∃ input, (lookup identity peer).1 = some (.reserved input) := by
  cases before : (lookup identity peer).1 with
  | none => exact Or.inl rfl
  | some entry =>
    cases entry with
    | reserved input => exact Or.inr ⟨input,rfl⟩
    | published input output =>
      have retained := peerStep_preserves_authentic peer changed action
        ⟨identity,.published input output⟩ before
      change (lookup identity (peerStep peer changed action).peer).1 = some (.published input output) at retained
      simp [retained] at after
    | cancelled input =>
      have retained := peerStep_preserves_authentic peer changed action
        ⟨identity,.prevented input⟩ before
      change (lookup identity (peerStep peer changed action).peer).1 = some (.cancelled input) at retained
      simp [retained] at after

theorem PublicationProvenance.peerStep (frame : Frame) (peer : Peer) (identity changed : Nat)
    (command action : PeerCommand) (provenance : PublicationProvenance frame peer identity command) :
    PublicationProvenance frame (peerStep peer changed action).peer identity command := by
  cases command with
  | reserve input => trivial
  | query => trivial
  | cancel input => trivial
  | publish input output =>
    intro after
    exact provenance (peerStep_nonterminal_before peer identity changed action after)

theorem sourceView_admit (frame : Frame) (peer : Peer) (slot : Bool) (request : Request)
    (valid : frame.Valid) (free : frame.requests.get slot = none)
    (fresh : (lookup request.identity peer).1 = none) :
    DelayStep (.accept request.identity request.input) (sourceView frame peer)
      (sourceView {frame with requests := frame.requests.put slot (some request), order := frame.order ++ [slot], nextIdentity := frame.nextIdentity + 1} peer) := by
  let target := {frame with requests := frame.requests.put slot (some request), order := frame.order ++ [slot], nextIdentity := frame.nextIdentity + 1}
  have notMem : slot ∉ frame.order := by
    intro member
    have occupied := (valid.2.2.1 slot).mp member
    simp [free] at occupied
  have same : ∀ other ∈ frame.order, requestProjection frame other = requestProjection target other := by
    intro other member
    have different : other ≠ slot := by intro eq; subst other; exact notMem member
    cases slot <;> cases other <;> simp_all [requestProjection,target,Slots.get,Slots.put]
  have added : requestProjection target slot = some (request.identity,request.input) := by
    cases slot <;> simp [requestProjection,target,Slots.get,Slots.put]
  have before : sourceView frame peer =
      projectedSource frame.logical frame.order (requestProjection target) peer :=
    (sourceView_projected frame peer).trans (projectedSource_congr_on_order _ _ _ _ _ same)
  have after : sourceView target peer =
      {sourceView frame peer with waiting := (sourceView frame peer).waiting ++ [(request.identity,request.input)]} := by
    rw [sourceView_projected,before]
    change projectedSource frame.logical (frame.order ++ [slot]) (requestProjection target) peer = _
    cases order : frame.order <;> simp [projectedSource,added,fresh,List.filterMap_cons,List.filterMap_append]
    split <;> rfl
  change DelayStep _ _ (sourceView target peer)
  rw [after]
  exact .accept _ _ _

def MessageSafe (frame : Frame) (peer : Peer) : Message → Prop
  | .request identity command => FrameTraffic frame peer identity command ∧
      PublicationProvenance frame peer identity command
  | .reply receipt => ReceiptAuthentic peer receipt

structure TrafficSafe (frame : Frame) (system : System) : Prop where
  owned : ∀ message ∈ system.adapter.queue.messages, MessageSafe frame system.peer message
  outbound : ∀ identity command, (identity,command) ∈ system.outbound →
    FrameTraffic frame system.peer identity command ∧ PublicationProvenance frame system.peer identity command
  inbound : ∀ receipt ∈ system.inbound, ReceiptAuthentic system.peer receipt

theorem MessageSafe.peerStep (frame : Frame) (peer : Peer) (message : Message)
    (identity : Nat) (command : PeerCommand) (safe : MessageSafe frame peer message) :
    MessageSafe frame (peerStep peer identity command).peer message := by
  cases message with
  | request other action => exact ⟨FrameTraffic.peerStep _ _ _ _ _ _ safe.1,
      PublicationProvenance.peerStep _ _ _ _ _ _ safe.2⟩
  | reply receipt => exact peerStep_preserves_authentic _ _ _ _ safe

theorem pushLocal_traffic (s : System) (frame : Frame) (message : Message)
    (safe : TrafficSafe frame s) (incoming : MessageSafe frame s.peer message) :
    TrafficSafe frame (pushLocal s message).system := by
  unfold pushLocal
  dsimp only
  split
  · constructor
    · intro other member
      simp only [List.mem_append,List.mem_singleton] at member
      rcases member with old | rfl
      · exact safe.owned other old
      · exact incoming
    · exact safe.outbound
    · exact safe.inbound
  · exact safe

theorem pushCancellation_traffic (s : System) (frame : Frame) (identity : Nat) (input : Bool)
    (safe : TrafficSafe frame s)
    (reserve : MessageSafe frame s.peer (.request identity (.reserve input)))
    (cancel : MessageSafe frame s.peer (.request identity (.cancel input))) :
    TrafficSafe frame (pushCancellation s identity input).system := by
  unfold pushCancellation
  dsimp only
  split
  · constructor
    · intro other member
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with old | rfl | rfl
      · exact safe.owned other old
      · exact reserve
      · exact cancel
    · exact safe.outbound
    · exact safe.inbound
  · exact safe

theorem requestPeer_nonterminal_computed (peer : Peer) (request : Request)
    (coupled : RequestPeer peer request)
    (live : (lookup request.identity peer).1 = none ∨ ∃ input, (lookup request.identity peer).1 = some (.reserved input))
    (notAccepted : request.phase ≠ .accepted) (_notCancelled : request.phase ≠ .cancelled) :
    request.phase = .computed := by
  rcases live with absent | ⟨input,reserved⟩
  · cases phase : request.phase <;> simp_all [RequestPeer]
  · cases phase : request.phase <;> simp_all [RequestPeer]

theorem occupied_simple_safe (frame : Frame) (peer : Peer) (slot : Bool) (request : Request)
    (valid : frame.Valid) (present : frame.requests.get slot = some request) :
    MessageSafe frame peer (.request request.identity (.reserve request.input)) ∧
    MessageSafe frame peer (.request request.identity (.cancel request.input)) ∧
    MessageSafe frame peer (.request request.identity .query) := by
  have member : slot ∈ frame.order := (valid.2.2.1 slot).mpr (by simp [present])
  refine ⟨⟨Or.inr (Or.inr ⟨slot,request,member,present,rfl,rfl⟩),trivial⟩,
    ⟨Or.inr (Or.inr ⟨slot,request,member,present,rfl,rfl⟩),trivial⟩,
    ⟨Or.inr (Or.inr ⟨slot,request,member,present,rfl,trivial⟩),trivial⟩⟩

theorem occupied_publish_safe (frame : Frame) (peer : Peer) (slot : Bool) (request : Request)
    (output : Bool) (valid : frame.Valid) (coupled : FramePeer frame peer)
    (present : frame.requests.get slot = some request) (first : frame.order.head? = some slot)
    (selected : request.output = some output)
    (notAccepted : request.phase ≠ .accepted) (notCancelled : request.phase ≠ .cancelled) :
    MessageSafe frame peer (.request request.identity (.publish request.input output)) := by
  have member : slot ∈ frame.order := (valid.2.2.1 slot).mpr (by simp [present])
  have found : request ∈ frame.requests.get slot := by simp [present]
  have head : frame.head = some (slot,request) := by simp [Frame.head,first,present]
  have computed := requestPeer_nonterminal_computed peer request (coupled slot request found)
  have sourceOutput : request.phase = .computed → output = frame.logical := by
    intro phase
    have wf := (valid.2.2.2.1 slot request found).2.1
    simp only [requestValid,phase] at wf
    exact Option.some.inj (selected.symm.trans wf.2.1)
  constructor
  · cases recorded : (lookup request.identity peer).1 with
    | none => exact Or.inr (Or.inr ⟨slot,request,member,present,rfl,rfl,
        sourceOutput (computed (Or.inl recorded) notAccepted notCancelled),head⟩)
    | some entry =>
      cases entry with
      | reserved input => exact Or.inr (Or.inr ⟨slot,request,member,present,rfl,rfl,
          sourceOutput (computed (Or.inr ⟨input,recorded⟩) notAccepted notCancelled),head⟩)
      | published input out => exact Or.inl ⟨input,out,recorded⟩
      | cancelled input => exact Or.inr (Or.inl ⟨input,recorded⟩)
  · intro live
    exact ⟨slot,request,head,rfl,rfl,selected,computed live notAccepted notCancelled⟩

theorem sendFor_traffic (s : System) (frame : Frame) (identity : Nat) (command : Send)
    (safe : TrafficSafe frame s) (current : s.adapter.current = some frame)
    (valid : frame.Valid) (coupled : FramePeer frame s.peer) :
    TrafficSafe frame (sendFor s identity command).system := by
  unfold sendFor
  split
  · exact safe
  · simp only [current,Option.bind_some]
    cases found : frame.find identity with
    | none => exact safe
    | some pair =>
      rcases pair with ⟨slot,request⟩
      obtain ⟨present,idEq⟩ := find_request_eq frame identity slot request found
      obtain ⟨reserve,cancel,query⟩ := occupied_simple_safe frame s.peer slot request valid present
      subst identity
      cases command with
      | reserve => exact pushLocal_traffic s frame _ safe reserve
      | query => exact pushLocal_traffic s frame _ safe query
      | cancel =>
        by_cases route : request.routeOpen = true
        · simpa only [route,ite_true] using pushCancellation_traffic s frame _ _ safe reserve cancel
        · simpa [route,reject] using safe
      | publish =>
        by_cases ready : (request.routeOpen && request.phase != Phase.accepted && request.phase != Phase.cancelled && frame.order.head? == some slot) = true
        · simp only [Option.map_some,Option.getD_some,ready,ite_true]
          cases selected : request.output with
          | none => exact safe
          | some output =>
            apply pushLocal_traffic s frame _ safe
            apply occupied_publish_safe frame s.peer slot request output valid coupled present
            all_goals simp_all
        · simpa [ready,reject] using safe

theorem sendFor_traffic_optional (s : System) (frame : Frame) (identity : Nat) (command : Send)
    (safe : TrafficSafe frame s) (current : ∀ retained, s.adapter.current = some retained → retained = frame)
    (valid : frame.Valid) (coupled : FramePeer frame s.peer) :
    TrafficSafe frame (sendFor s identity command).system := by
  cases retained : s.adapter.current with
  | none =>
    unfold sendFor
    split
    · exact safe
    · simpa only [retained,Option.bind_none,reject] using safe
  | some value =>
    have same := current value retained
    subst value
    exact sendFor_traffic s frame identity command safe retained valid coupled

theorem reconcile_traffic (s : System) (frame : Frame) (safe : TrafficSafe frame s)
    (current : ∀ retained, s.adapter.current = some retained → retained = frame)
    (valid : frame.Valid) (coupled : FramePeer frame s.peer) :
    TrafficSafe frame (reconcile s).system := by
  cases first : s.adapter.reconcileOrder.head? with
  | none => simpa only [reconcile,first,reject] using safe
  | some identity => simpa only [reconcile,first] using sendFor_traffic_optional s frame identity .query safe current valid coupled


theorem submit_traffic (s : System) (frame : Frame) (safe : TrafficSafe frame s) :
    TrafficSafe frame (submit s).system := by
  unfold submit
  split
  · exact safe
  · split
    · rename_i identity command rest queueEq
      constructor
      · intro message member
        exact safe.owned message (by rw [queueEq]; exact List.mem_cons_of_mem _ member)
      · intro other action member
        simp only [List.mem_append,List.mem_singleton] at member
        rcases member with old | eq
        · exact safe.outbound other action old
        · cases eq
          exact safe.owned (.request identity command) (by simp [queueEq])
      · exact safe.inbound
    · exact safe

theorem network_traffic (s : System) (frame : Frame) (deliver : Bool)
    (safe : TrafficSafe frame s) : TrafficSafe frame (network s deliver).system := by
  unfold network
  split
  · exact safe
  · rename_i identity command rest outEq
    constructor
    · intro message member
      exact MessageSafe.peerStep frame s.peer message identity command (safe.owned message member)
    · intro other action member
      have prior := safe.outbound other action (by rw [outEq]; exact List.mem_cons_of_mem _ member)
      exact ⟨FrameTraffic.peerStep _ _ _ _ _ _ prior.1,
        PublicationProvenance.peerStep _ _ _ _ _ _ prior.2⟩
    · intro receipt member
      have old : ∀ r ∈ s.inbound, ReceiptAuthentic (peerStep s.peer identity command).peer r :=
        fun r mem => peerStep_preserves_authentic _ _ _ _ (safe.inbound r mem)
      cases deliver
      · exact old receipt member
      · simp only [ite_true,List.mem_append,List.mem_singleton] at member
        rcases member with prior | rfl
        · exact old receipt prior
        · exact peerStep_receipt_authentic _ _ _


theorem pushLocal_peer (s : System) (message : Message) :
    (pushLocal s message).system.peer = s.peer := by
  unfold pushLocal
  dsimp only
  split <;> rfl

theorem receiveNetwork_traffic (s : System) (frame : Frame)
    (safe : TrafficSafe frame s) : TrafficSafe frame (receiveNetwork s).system := by
  unfold receiveNetwork
  split
  · exact safe
  · split
    · exact safe
    · rename_i receipt rest incoming
      have authentic := safe.inbound receipt (by simp [incoming])
      have queued := pushLocal_traffic s frame (.reply receipt) safe authentic
      dsimp only
      split
      · refine ⟨queued.owned,queued.outbound,?_⟩
        intro other member
        rw [pushLocal_peer]
        exact safe.inbound other (by rw [incoming]; exact List.mem_cons_of_mem _ member)
      · exact queued

theorem duplicateInbound_traffic (s : System) (frame : Frame)
    (safe : TrafficSafe frame s) : TrafficSafe frame (duplicateInbound s).system := by
  unfold duplicateInbound
  split
  · exact safe
  · rename_i receipt rest incoming
    refine ⟨safe.owned,safe.outbound,?_⟩
    intro other member
    simp only [List.mem_cons] at member
    rcases member with rfl | old
    · exact safe.inbound other (by simp [incoming])
    · exact safe.inbound other old

theorem duplicateOutbound_traffic (s : System) (frame : Frame)
    (safe : TrafficSafe frame s) : TrafficSafe frame (duplicateOutbound s).system := by
  unfold duplicateOutbound
  split
  · exact safe
  · rename_i message rest outgoing
    refine ⟨safe.owned,?_,safe.inbound⟩
    intro identity command member
    simp only [List.mem_cons] at member
    rcases member with eq | old
    · exact safe.outbound identity command (by rw [outgoing]; exact List.mem_cons.mpr (Or.inl eq))
    · exact safe.outbound identity command old


theorem beginChange_traffic (s : System) (frame : Frame) (command : FrameCommand)
    (safe : TrafficSafe frame s) : TrafficSafe frame (beginChange s command).system := by
  unfold beginChange
  repeat' first | split | exact safe | exact ⟨safe.owned,safe.outbound,safe.inbound⟩

theorem crash_traffic (s : System) (frame : Frame) (safe : TrafficSafe frame s) :
    TrafficSafe frame (crash s).system := by
  exact ⟨by simp [crash],safe.outbound,safe.inbound⟩

theorem drain_traffic (s : System) (frame : Frame) (safe : TrafficSafe frame s) :
    TrafficSafe frame (drain s).system := by
  unfold drain
  split
  · exact safe
  · split
    · exact safe
    · split
      · exact safe
      · refine ⟨?_,safe.outbound,safe.inbound⟩
        intro message member
        exact safe.owned message (List.mem_filter.mp member).1


theorem handle_traffic (s : System) (frame : Frame) (safe : TrafficSafe frame s)
    (current : ∀ retained, s.adapter.current = some retained → retained = frame)
    (valid : frame.Valid) (coupled : FramePeer frame s.peer) :
    TrafficSafe frame (handle s).system := by
  unfold handle
  split
  · exact safe
  · split
    · rename_i receipt rest queueEq
      let queue : LocalQueue := ⟨rest, by have := s.adapter.queue.bounded; rw [queueEq] at this; simp only [List.length_cons] at this; omega⟩
      let popped := {s with adapter := {s.adapter with queue := queue}}
      have poppedSafe : TrafficSafe frame popped := by
        refine ⟨?_,safe.outbound,safe.inbound⟩
        intro message member
        exact safe.owned message (by rw [queueEq]; exact List.mem_cons_of_mem _ member)
      have poppedCurrent : ∀ retained, popped.adapter.current = some retained → retained = frame := current
      have sendSafe := fun identity command => sendFor_traffic_optional popped frame identity command poppedSafe poppedCurrent valid coupled
      have beginSafe := fun command => beginChange_traffic popped frame command poppedSafe
      dsimp only
      repeat' first | split | exact poppedSafe | exact beginSafe _ | exact sendSafe _ _ | exact ⟨poppedSafe.owned,poppedSafe.outbound,poppedSafe.inbound⟩
    · exact safe


def PeerNonterminal (peer : Peer) (identity : Nat) : Prop :=
  (lookup identity peer).1 = none ∨ ∃ input, (lookup identity peer).1 = some (.reserved input)

structure LiveFrameExtension (before after : Frame) (peer : Peer) : Prop where
  requests : ∀ slot request, before.requests.get slot = some request →
    PeerNonterminal peer request.identity →
    ∃ replacement, after.requests.get slot = some replacement ∧
      replacement.identity = request.identity ∧ replacement.input = request.input
  head : ∀ slot request, before.head = some (slot,request) →
    request.phase = .computed → PeerNonterminal peer request.identity →
    ∃ replacement, after.head = some (slot,replacement) ∧
      replacement.identity = request.identity ∧ replacement.input = request.input ∧
      replacement.output = request.output ∧ replacement.phase = .computed ∧ after.logical = before.logical

theorem MessageSafe.extension (before after : Frame) (peer : Peer) (message : Message)
    (valid : after.Valid) (extension : LiveFrameExtension before after peer)
    (safe : MessageSafe before peer message) : MessageSafe after peer message := by
  cases message with
  | reply receipt => exact safe
  | request identity command =>
    have terminalCase : (∃ x y, (lookup identity peer).1 = some (.published x y)) ∨
        (∃ x, (lookup identity peer).1 = some (.cancelled x)) ∨ PeerNonterminal peer identity := by
      cases found : (lookup identity peer).1 with
      | none => exact Or.inr (Or.inr (Or.inl found))
      | some entry =>
        cases entry with
        | reserved input => exact Or.inr (Or.inr (Or.inr ⟨input,found⟩))
        | published input output => exact Or.inl ⟨input,output,rfl⟩
        | cancelled input => exact Or.inr (Or.inl ⟨input,rfl⟩)
    rcases terminalCase with published | cancelled | live
    · refine ⟨Or.inl published,?_⟩
      cases command <;> try trivial
      rcases published with ⟨x,y,found⟩
      intro nonterminal
      rcases nonterminal with absent | ⟨z,reserved⟩ <;> simp_all
    · refine ⟨Or.inr (Or.inl cancelled),?_⟩
      cases command <;> try trivial
      rcases cancelled with ⟨x,found⟩
      intro nonterminal
      rcases nonterminal with absent | ⟨z,reserved⟩ <;> simp_all
    · rcases safe with ⟨traffic,provenance⟩
      have noPublished : ¬ ∃ x y, (lookup identity peer).1 = some (.published x y) := by
        rcases live with absent | ⟨z,reserved⟩
        · simp [absent]
        · simp [reserved]
      have noCancelled : ¬ ∃ x, (lookup identity peer).1 = some (.cancelled x) := by
        rcases live with absent | ⟨z,reserved⟩
        · simp [absent]
        · simp [reserved]
      rcases traffic with published | cancelled | ⟨slot,request,member,present,idEq,detail⟩
      · exact False.elim (noPublished published)
      · exact False.elim (noCancelled cancelled)
      have requestLive : PeerNonterminal peer request.identity := idEq ▸ live
      obtain ⟨replacement,retained,sameId,sameInput⟩ := extension.requests slot request present requestLive
      have ordered : slot ∈ after.order := (valid.2.2.1 slot).mpr (by simp [retained])
      cases command with
      | reserve input => exact ⟨Or.inr (Or.inr ⟨slot,replacement,ordered,retained,sameId.trans idEq,detail.trans sameInput.symm⟩),trivial⟩
      | cancel input => exact ⟨Or.inr (Or.inr ⟨slot,replacement,ordered,retained,sameId.trans idEq,detail.trans sameInput.symm⟩),trivial⟩
      | query => exact ⟨Or.inr (Or.inr ⟨slot,replacement,ordered,retained,sameId.trans idEq,trivial⟩),trivial⟩
      | publish input output =>
        obtain ⟨pubSlot,pubRequest,pubHead,pubId,pubInput,pubOutput,pubPhase⟩ := provenance live
        obtain ⟨next,nextHead,nextId,nextInput,nextOutput,nextPhase,logical⟩ :=
          extension.head pubSlot pubRequest pubHead pubPhase (pubId ▸ live)
        have nextPresent := head_request_eq after pubSlot next nextHead
        have nextOrdered : pubSlot ∈ after.order := (valid.2.2.1 pubSlot).mpr (by simp [nextPresent])
        refine ⟨Or.inr (Or.inr ⟨pubSlot,next,nextOrdered,nextPresent,nextId.trans pubId,?_,?_,nextHead⟩),?_⟩
        · exact (nextInput.trans pubInput).symm
        · exact detail.2.1.trans logical.symm
        · intro _
          exact ⟨pubSlot,next,nextHead,nextId.trans pubId,nextInput.trans pubInput,nextOutput.trans pubOutput,nextPhase⟩

theorem TrafficSafe.extension (before after : Frame) (system : System)
    (valid : after.Valid) (extension : LiveFrameExtension before after system.peer)
    (safe : TrafficSafe before system) : TrafficSafe after system := by
  refine ⟨?_,?_,safe.inbound⟩
  · intro message member
    exact MessageSafe.extension before after system.peer message valid extension (safe.owned message member)
  · intro identity command member
    exact MessageSafe.extension before after system.peer (.request identity command) valid extension (safe.outbound identity command member)


theorem LiveFrameExtension.update (before : Frame) (peer : Peer) (slot : Bool)
    (old replacement : Request) (present : before.requests.get slot = some old)
    (sameId : replacement.identity = old.identity) (sameInput : replacement.input = old.input)
    (preserved : old.phase = .computed → PeerNonterminal peer old.identity →
      replacement.phase = .computed ∧ replacement.output = old.output) :
    LiveFrameExtension before (before.update slot replacement) peer := by
  constructor
  · intro other request found live
    by_cases equal : other = slot
    · subst other
      have eq : request = old := Option.some.inj (found.symm.trans present)
      subst request
      refine ⟨replacement,?_,sameId,sameInput⟩
      cases slot <;> rfl
    · refine ⟨request,?_,rfl,rfl⟩
      cases slot <;> cases other <;> simp_all [Frame.update,Slots.put,Slots.get]
  · intro other request head computed live
    have first := head_order_eq before other request head
    have found := head_request_eq before other request head
    by_cases equal : other = slot
    · subst other
      have eq : request = old := Option.some.inj (found.symm.trans present)
      subst request
      obtain ⟨phase,output⟩ := preserved computed live
      refine ⟨replacement,?_,sameId,sameInput,output,phase,rfl⟩
      cases slot <;> simp [Frame.head,Frame.update,first,Slots.put,Slots.get]
    · refine ⟨request,?_,rfl,rfl,rfl,computed,rfl⟩
      have retained : (before.update slot replacement).requests.get other = some request := by
        cases slot <;> cases other <;> simp_all [Frame.update,Slots.put,Slots.get]
      cases slot <;> cases other <;> simp_all [Frame.head,Frame.update,Slots.get,Slots.put]

theorem receive_liveExtension (before after : Frame) (peer : Peer) (receipt : Receipt)
    (authentic : ReceiptAuthentic peer receipt)
    (changed : receive before receipt = .changed after) : LiveFrameExtension before after peer := by
  rcases receipt with ⟨identity,answer⟩
  unfold receive at changed
  cases found : before.find identity with
  | none => simp [found] at changed
  | some pair =>
    rcases pair with ⟨slot,request⟩
    obtain ⟨present,idEq⟩ := find_request_eq before identity slot request found
    simp only [found] at changed
    cases answer
    all_goals repeat' first
      | simp_all only [reduceCtorEq, Decision.changed.injEq]
      | split at changed
    all_goals subst after
    all_goals apply LiveFrameExtension.update before peer slot request _ present
    all_goals try first | exact idEq.symm | rfl
    all_goals intro computed live
    all_goals rcases live with absent | ⟨input,reserved⟩
    all_goals simp_all [ReceiptAuthentic]


theorem RequestPeer.terminal_not_live (peer : Peer) (request : Request)
    (coupled : RequestPeer peer request) (phase : terminal request.phase = true) :
    ¬ PeerNonterminal peer request.identity := by
  intro live
  rcases live with absent | ⟨input,reserved⟩
  all_goals cases found : request.phase <;> simp_all [terminal,RequestPeer]

theorem LiveFrameExtension.release (before : Frame) (peer : Peer) (slot : Bool)
    (request : Request) (head : before.head = some (slot,request))
    (finished : ¬ PeerNonterminal peer request.identity) :
    LiveFrameExtension before
      {before with requests := before.requests.put slot none, order := before.order.tail} peer := by
  have present := head_request_eq before slot request head
  constructor
  · intro other candidate found live
    have different : other ≠ slot := by
      intro equal
      subst other
      have same := Option.some.inj (found.symm.trans present)
      subst candidate
      exact finished live
    refine ⟨candidate,?_,rfl,rfl⟩
    cases slot <;> cases other <;> simp_all [Slots.put,Slots.get]
  · intro other candidate candidateHead computed live
    have equal := Option.some.inj (candidateHead.symm.trans head)
    have same : candidate = request := congrArg Prod.snd equal
    subst candidate
    exact False.elim (finished live)

theorem LiveFrameExtension.accept (before : Frame) (peer : Peer) (slot : Bool)
    (request : Request) (free : before.requests.get slot = none) :
    LiveFrameExtension before
      {before with requests := before.requests.put slot (some request), order := before.order ++ [slot], nextIdentity := before.nextIdentity + 1} peer := by
  have retained : ∀ other candidate, before.requests.get other = some candidate →
      (before.requests.put slot (some request)).get other = some candidate := by
    intro other candidate found
    have different : other ≠ slot := by intro equal; subst other; simp [free] at found
    cases slot <;> cases other <;> simp_all [Slots.put,Slots.get]
  constructor
  · intro other candidate found _
    exact ⟨candidate,retained other candidate found,rfl,rfl⟩
  · intro other candidate head computed _
    have first := head_order_eq before other candidate head
    have found := head_request_eq before other candidate head
    refine ⟨candidate,?_,rfl,rfl,rfl,computed,rfl⟩
    have orderFirst : (before.order ++ [slot]).head? = some other := by
      cases order : before.order <;> simp_all
    cases slot <;> cases other <;> simp_all [Frame.head,Slots.get,Slots.put]


theorem propose_liveExtension (before after : Frame) (peer : Peer) (command : FrameCommand)
    (coupled : FramePeer before peer) (authentic : CommandAuthentic peer command)
    (changed : propose before command = .changed after) : LiveFrameExtension before after peer := by
  cases command with
  | receive receipt => exact receive_liveExtension before after peer receipt authentic changed
  | migrate kind =>
    cases changed
    constructor
    · intro slot request found _
      exact ⟨request,found,rfl,rfl⟩
    · intro slot request head phase _
      exact ⟨request,head,rfl,rfl,rfl,phase,rfl⟩
  | accept input =>
    simp only [propose] at changed
    repeat' first
      | simp_all only [reduceCtorEq,Decision.changed.injEq]
      | split at changed
    all_goals subst after
    all_goals apply LiveFrameExtension.accept
    all_goals repeat' first | split at * | simp_all
  | evaluate | tickCommit | close | release =>
    simp only [propose] at changed
    cases head : before.head with
    | none => simp [head] at changed
    | some pair =>
      rcases pair with ⟨slot,request⟩
      have present := head_request_eq before slot request head
      have recorded := coupled slot request (by simp [present])
      simp only [head] at changed
      split at changed
      · cases changed
        first
        | apply LiveFrameExtension.release before peer slot request head
          apply RequestPeer.terminal_not_live peer request recorded
          simp_all
        | apply LiveFrameExtension.update before peer slot request _ present
          · rfl
          · rfl
          · intro computed live
            simp_all [terminal]
        | constructor
          · exact (LiveFrameExtension.update before peer slot request {request with phase := .committed}
              present rfl rfl (by intro computed live; simp_all)).requests
          · intro other candidate candidateHead computed live
            have same : candidate = request := congrArg Prod.snd (Option.some.inj (candidateHead.symm.trans head))
            subst candidate
            simp_all
      · contradiction

theorem propose_traffic (before after : Frame) (system : System) (command : FrameCommand)
    (coupled : FramePeer before system.peer) (authentic : CommandAuthentic system.peer command)
    (valid : after.Valid) (changed : propose before command = .changed after)
    (safe : TrafficSafe before system) : TrafficSafe after system :=
  TrafficSafe.extension before after system valid (propose_liveExtension before after system.peer command coupled authentic changed) safe


theorem sourceView_update (frame : Frame) (peer : Peer) (slot : Bool)
    (old replacement : Request) (present : frame.requests.get slot = some old)
    (sameId : replacement.identity = old.identity) (sameInput : replacement.input = old.input) :
    sourceView frame peer = sourceView (frame.update slot replacement) peer := by
  apply sourceView_projection frame (frame.update slot replacement) peer rfl rfl
  intro other
  cases slot <;> cases other <;> simp_all [requestProjection,Frame.update,Slots.put,Slots.get]

theorem receive_sourceView (before after : Frame) (peer : Peer) (receipt : Receipt)
    (changed : receive before receipt = .changed after) : sourceView before peer = sourceView after peer := by
  rcases receipt with ⟨identity,answer⟩
  unfold receive at changed
  cases found : before.find identity with
  | none => simp [found] at changed
  | some pair =>
    rcases pair with ⟨slot,request⟩
    obtain ⟨present,idEq⟩ := find_request_eq before identity slot request found
    simp only [found] at changed
    cases answer
    all_goals repeat' first
      | simp_all only [reduceCtorEq,Decision.changed.injEq]
      | split at changed
    all_goals subst after
    all_goals apply sourceView_update before peer slot request _ present
    all_goals first | exact idEq.symm | rfl

def frameSourceLabel (before : Frame) : FrameCommand → SourceLabel
  | .accept input => .accept before.nextIdentity input
  | _ => .internal

theorem propose_sourceView (before after : Frame) (peer : Peer) (command : FrameCommand)
    (valid : before.Valid) (coupled : FramePeer before peer)
    (fresh : (lookup before.nextIdentity peer).1 = none)
    (changed : propose before command = .changed after) :
    DelayStep (frameSourceLabel before command) (sourceView before peer) (sourceView after peer) := by
  cases command with
  | receive receipt =>
    rw [← receive_sourceView before after peer receipt changed]
    exact .internal _
  | migrate kind => cases changed; exact .internal _
  | accept input =>
    simp only [propose] at changed
    repeat' first
      | simp_all only [reduceCtorEq,Decision.changed.injEq]
      | split at changed
    all_goals subst after
    all_goals apply sourceView_admit before peer _ {identity := before.nextIdentity,input := input} valid _ fresh
    all_goals repeat' first | split at * | simp_all
  | evaluate | close =>
    simp only [propose] at changed
    cases head : before.head with
    | none => simp [head] at changed
    | some pair =>
      rcases pair with ⟨slot,request⟩
      have present := head_request_eq before slot request head
      simp only [head] at changed
      split at changed
      · cases changed
        rw [← sourceView_update before peer slot request _ present]
        · exact .internal _
        all_goals rfl
      · contradiction
  | release =>
    simp only [propose] at changed
    cases head : before.head with
    | none => simp [head] at changed
    | some pair =>
      rcases pair with ⟨slot,request⟩
      simp only [head] at changed
      split at changed
      · cases changed
        rw [← sourceView_release before peer slot request valid coupled head (by simp_all)]
        exact .internal _
      · contradiction
  | tickCommit =>
    simp only [propose] at changed
    cases head : before.head with
    | none => simp [head] at changed
    | some pair =>
      rcases pair with ⟨slot,request⟩
      have present := head_request_eq before slot request head
      have first := head_order_eq before slot request head
      have recorded := coupled slot request (by simp [present])
      simp only [head] at changed
      split at changed
      · rename_i ready
        cases changed
        have phase : request.phase = .confirmed := by simpa using ((Bool.and_eq_true _ _).mp ready).1
        obtain ⟨output,selected,published⟩ : ∃ output, request.output = some output ∧
            (lookup request.identity peer).1 = some (.published request.input output) := by
          simpa only [RequestPeer,phase] using recorded
        let next := {(before.update slot {request with phase := .committed}) with logical := request.input}
        have projections : ∀ other, requestProjection before other = requestProjection next other := by
          intro other
          cases slot <;> cases other <;> simp_all [requestProjection,next,Frame.update,Slots.put,Slots.get]
        have eq := sourceView_projection_published before next peer rfl projections request.identity request.input output
          (by simp [first,requestProjection,present]) published
        change DelayStep .internal (sourceView before peer) (sourceView next peer)
        rw [← eq]
        exact .internal _
      · contradiction


theorem applyJournal_traffic (s : System) (frame : Frame) (attempt : JournalAttempt s.adapter.journal)
    (safe : TrafficSafe frame s) : TrafficSafe frame (applyJournal s attempt).system := by
  cases attempt with
  | failed work => exact safe
  | done result =>
    unfold applyJournal
    cases event : result.event <;> simp only [event]
    all_goals repeat' first | exact ⟨safe.owned,safe.outbound,safe.inbound⟩ | split

theorem localCommand_traffic (s : System) (frame : Frame) (command : FrameCommand)
    (safe : TrafficSafe frame s) : TrafficSafe frame (localCommand s command).system := by
  unfold localCommand
  repeat' first | exact safe | exact beginChange_traffic s frame _ safe | split
  all_goals dsimp only
  all_goals repeat' first | exact safe | exact beginChange_traffic s frame _ safe | split

theorem step_traffic (s : System) (frame : Frame) (command : Command)
    (safe : TrafficSafe frame s)
    (current : ∀ retained, s.adapter.current = some retained → retained = frame)
    (valid : frame.Valid) (coupled : FramePeer frame s.peer) :
    TrafficSafe frame (step s command).system := by
  cases command with
  | «local» action => exact localCommand_traffic s frame action safe
  | send second action =>
    simp only [step]
    repeat' first | exact safe | exact sendFor_traffic_optional s frame _ _ safe current valid coupled | split
  | storage action =>
    simp only [step,storage]
    split
    · exact safe
    · exact applyJournal_traffic s frame _ safe
  | crash => exact crash_traffic s frame safe
  | reconcile => exact reconcile_traffic s frame safe current valid coupled
  | submit => exact submit_traffic s frame safe
  | receive => exact receiveNetwork_traffic s frame safe
  | handle => exact handle_traffic s frame safe current valid coupled
  | drain => exact drain_traffic s frame safe
  | network deliver => exact network_traffic s frame deliver safe
  | duplicateInbound => exact duplicateInbound_traffic s frame safe
  | duplicateOutbound => exact duplicateOutbound_traffic s frame safe
  | dropInbound | rotateInbound =>
    simp only [step]
    split
    · exact safe
    · rename_i receipt rest incoming
      refine ⟨safe.owned,safe.outbound,?_⟩
      intro other member
      apply safe.inbound
      rw [incoming]
      simp_all [or_comm]
  | dropOutbound | rotateOutbound =>
    simp only [step]
    split
    · exact safe
    · rename_i message rest outgoing
      refine ⟨safe.owned,?_,safe.inbound⟩
      intro identity action member
      apply safe.outbound
      rw [outgoing]
      simp_all [or_comm]
  | prepareMigration kind budget allocation validation =>
    simp only [step,prepareMigration]
    repeat' first | exact safe | exact ⟨safe.owned,safe.outbound,safe.inbound⟩ | split
  | commitMigration =>
    simp only [step,commitMigration]
    split
    · exact safe
    · exact beginChange_traffic s frame _ safe
  | cancelMigration =>
    simp only [step,cancelMigration]
    repeat' first | exact safe | exact ⟨safe.owned,safe.outbound,safe.inbound⟩ | split
  | cleanupMigration =>
    simp only [step,cleanupMigration]
    repeat' first | exact safe | exact ⟨safe.owned,safe.outbound,safe.inbound⟩ | split
  | inspect => exact safe

def PendingAuthentic (s : System) : Prop :=
  ∀ command, s.adapter.pendingCause = some command → CommandAuthentic s.peer command

theorem beginChange_pending (s : System) (command : FrameCommand)
    (pending : PendingAuthentic s) (authentic : CommandAuthentic s.peer command) :
    PendingAuthentic (beginChange s command).system := by
  unfold beginChange
  repeat' first | exact pending | split
  all_goals intro other recorded
  all_goals simp_all [CommandAuthentic]

theorem applyJournal_pending (s : System) (attempt : JournalAttempt s.adapter.journal)
    (pending : PendingAuthentic s) : PendingAuthentic (applyJournal s attempt).system := by
  cases attempt with
  | failed work => exact pending
  | done result =>
    unfold applyJournal
    cases event : result.event <;> simp only [event]
    all_goals repeat' first | exact pending | split
    all_goals intro other recorded
    all_goals contradiction

theorem pushLocal_pending (s : System) (message : Message) (pending : PendingAuthentic s) :
    PendingAuthentic (pushLocal s message).system := by
  unfold pushLocal
  dsimp only
  split <;> exact pending

theorem pushCancellation_pending (s : System) (identity : Nat) (input : Bool)
    (pending : PendingAuthentic s) : PendingAuthentic (pushCancellation s identity input).system := by
  unfold pushCancellation
  dsimp only
  split <;> exact pending

theorem sendFor_pending (s : System) (identity : Nat) (command : Send)
    (pending : PendingAuthentic s) : PendingAuthentic (sendFor s identity command).system := by
  unfold sendFor
  repeat' first | exact pending | exact pushLocal_pending s _ pending | exact pushCancellation_pending s _ _ pending | split
  all_goals dsimp only
  all_goals repeat' first | exact pending | exact pushLocal_pending s _ pending | exact pushCancellation_pending s _ _ pending | split

theorem network_pending (s : System) (deliver : Bool) (pending : PendingAuthentic s) :
    PendingAuthentic (network s deliver).system := by
  unfold network
  split
  · exact pending
  · rename_i identity command rest outgoing
    intro action recorded
    have authentic := pending action recorded
    cases action <;> try trivial
    exact peerStep_preserves_authentic _ _ _ _ authentic

theorem handle_pending (s : System) (frame : Frame) (safe : TrafficSafe frame s)
    (pending : PendingAuthentic s) : PendingAuthentic (handle s).system := by
  unfold handle
  split
  · exact pending
  · split
    · rename_i receipt rest queueEq
      let queue : LocalQueue := ⟨rest, by have := s.adapter.queue.bounded; rw [queueEq] at this; simp only [List.length_cons] at this; omega⟩
      let popped := {s with adapter := {s.adapter with queue := queue}}
      have poppedPending : PendingAuthentic popped := pending
      have authentic : CommandAuthentic popped.peer (.receive receipt) :=
        safe.owned (.reply receipt) (by simp [queueEq])
      have beginPending := beginChange_pending popped (.receive receipt) poppedPending authentic
      have sendPending := fun identity command => sendFor_pending popped identity command poppedPending
      dsimp only
      repeat' first | exact poppedPending | exact beginPending | exact sendPending _ _ | split
    · exact pending


theorem step_pending (s : System) (frame : Frame) (command : Command)
    (safe : TrafficSafe frame s) (pending : PendingAuthentic s) :
    PendingAuthentic (step s command).system := by
  cases command with
  | «local» action =>
    simp only [step,localCommand]
    repeat' first | exact pending | apply beginChange_pending s _ pending | split
    all_goals first | trivial | (cases action <;> simp_all [CommandAuthentic])
  | send second action =>
    simp only [step]
    repeat' first | exact pending | exact sendFor_pending s _ _ pending | split
  | storage action =>
    simp only [step,storage]
    split
    · exact pending
    · exact applyJournal_pending s _ pending
  | crash => intro other recorded; simp [step,crash] at recorded
  | reconcile =>
    simp only [step,reconcile]
    split
    · exact pending
    · exact sendFor_pending s _ _ pending
  | submit =>
    simp only [step,submit]
    repeat' first | exact pending | split
  | receive =>
    simp only [step,receiveNetwork]
    split
    · exact pending
    · split
      · exact pending
      · split <;> exact pushLocal_pending s _ pending
  | handle => exact handle_pending s frame safe pending
  | drain =>
    simp only [step,drain]
    repeat' first | exact pending | split
  | network deliver => exact network_pending s deliver pending
  | duplicateInbound | duplicateOutbound =>
    simp only [step,duplicateInbound,duplicateOutbound]
    split <;> exact pending
  | dropInbound | dropOutbound | rotateInbound | rotateOutbound =>
    simp only [step]
    split <;> exact pending
  | prepareMigration kind budget allocation validation =>
    simp only [step,prepareMigration]
    repeat' first | exact pending | split
  | commitMigration =>
    simp only [step,commitMigration]
    split
    · exact pending
    · apply beginChange_pending s _ pending; trivial
  | cancelMigration =>
    simp only [step,cancelMigration]
    repeat' first | exact pending | split
  | cleanupMigration =>
    simp only [step,cleanupMigration]
    split <;> exact pending
  | inspect => exact pending

def StaticFields (before after : System) : Prop :=
  after.peer = before.peer ∧ after.adapter.initialKind = before.adapter.initialKind

theorem beginChange_static (s : System) (command : FrameCommand) :
    StaticFields s (beginChange s command).system := by
  unfold beginChange
  repeat' first | exact ⟨rfl,rfl⟩ | split

theorem pushLocal_static (s : System) (message : Message) : StaticFields s (pushLocal s message).system := by
  unfold pushLocal
  dsimp only
  split <;> exact ⟨rfl,rfl⟩

theorem pushCancellation_static (s : System) (identity : Nat) (input : Bool) :
    StaticFields s (pushCancellation s identity input).system := by
  unfold pushCancellation
  dsimp only
  split <;> exact ⟨rfl,rfl⟩

theorem sendFor_static (s : System) (identity : Nat) (command : Send) :
    StaticFields s (sendFor s identity command).system := by
  unfold sendFor
  repeat' first | exact ⟨rfl,rfl⟩ | exact pushLocal_static s _ | exact pushCancellation_static s _ _ | split
  all_goals dsimp only
  all_goals repeat' first | exact ⟨rfl,rfl⟩ | exact pushLocal_static s _ | exact pushCancellation_static s _ _ | split

theorem handle_static (s : System) : StaticFields s (handle s).system := by
  unfold handle
  split
  · exact ⟨rfl,rfl⟩
  · split
    · rename_i receipt rest queueEq
      let queue : LocalQueue := ⟨rest, by have := s.adapter.queue.bounded; rw [queueEq] at this; simp only [List.length_cons] at this; omega⟩
      let popped := {s with adapter := {s.adapter with queue := queue}}
      have beginStatic := fun command => beginChange_static popped command
      have sendStatic := fun identity command => sendFor_static popped identity command
      dsimp only
      repeat' first | exact ⟨rfl,rfl⟩ | exact beginStatic _ | exact sendStatic _ _ | split
    · exact ⟨rfl,rfl⟩

theorem step_initialKind (s : System) (command : Command) :
    (step s command).system.adapter.initialKind = s.adapter.initialKind := by
  cases command <;> first | exact (handle_static s).2 |
    simp only [step,localCommand,sendFor,storage,crash,reconcile,submit,receiveNetwork,
      drain,network,duplicateInbound,duplicateOutbound,prepareMigration,
      commitMigration,cancelMigration,cleanupMigration,beginChange,applyJournal,pushLocal,pushCancellation]
  all_goals repeat' first | rfl | split
  all_goals dsimp only
  all_goals repeat' first | rfl | split

theorem step_peer (s : System) (command : Command) :
    (step s command).system.peer = match command with
      | .network deliver => (network s deliver).system.peer
      | _ => s.peer := by
  cases command <;> first | exact (handle_static s).1 |
    simp only [step,localCommand,sendFor,storage,crash,reconcile,submit,receiveNetwork,
      drain,duplicateInbound,duplicateOutbound,prepareMigration,
      commitMigration,cancelMigration,cleanupMigration,beginChange,applyJournal,pushLocal,pushCancellation]
  all_goals repeat' first | rfl | split
  all_goals dsimp only
  all_goals repeat' first | rfl | split


theorem lookup_member (peer : Peer) (identity : Nat) (entry : PendingMigration.Ledger)
    (found : (lookup identity peer).1 = some entry) : (identity,entry) ∈ peer := by
  induction peer with
  | nil => cases found
  | cons head rest ih =>
    rcases head with ⟨key,value⟩
    unfold lookup at found
    split at found
    · rename_i same
      subst key
      cases Option.some.inj found
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih found)

theorem FrameTraffic.identity_lt (frame : Frame) (peer : Peer) (identity : Nat) (command : PeerCommand)
    (valid : frame.Valid) (names : PeerNamesBelow frame.nextIdentity peer)
    (traffic : FrameTraffic frame peer identity command) : identity < frame.nextIdentity := by
  rcases traffic with ⟨input,output,published⟩ | ⟨input,cancelled⟩ | ⟨slot,request,member,present,same,command⟩
  · exact names identity _ (lookup_member peer identity _ published)
  · exact names identity _ (lookup_member peer identity _ cancelled)
  · rw [← same]
    exact (valid.2.2.2.1 slot request (by simp [present])).1

theorem observation_counter_monotone (s : System) (o : Observation s.adapter.journal.machine s.peer)
    (a b : Durability.Abstract Frame) (before after : Frame)
    (oldRelation : Durability.Related s.adapter.journal.machine a)
    (newRelation : Durability.Related o.system.adapter.journal.machine b)
    (old : validateFrames (initialFrame s.adapter.initialKind) (a.history.map Durability.Record.payload) = some before)
    (new : validateFrames (initialFrame o.system.adapter.initialKind) (b.history.map Durability.Record.payload) = some after) :
    before.nextIdentity ≤ after.nextIdentity := by
  have grows : a.history.IsPrefix b.history := by
    have native := o.native
    cases event : o.journalEvent with
    | none =>
      simp only [event] at native
      have same := oldRelation.root.unique (native ▸ newRelation.root)
      rw [same]
    | some e =>
      simp only [event] at native
      obtain ⟨c,source,related⟩ := native.simulation oldRelation
      have same := related.root.unique newRelation.root
      obtain ⟨suffix,history⟩ := source.prefix
      exact ⟨suffix,by rw [← same,history]⟩
  exact validated_prefix_counter _ _ before after _ _ old new (grows.map _)



def journalSourceLabel (s : System) : Option (Durability.Event Frame) → SourceLabel
  | some (.commit record) => match s.adapter.pendingCause with
    | some (.accept input) => .accept (record.payload.nextIdentity - 1) input
    | _ => .internal
  | _ => .internal

theorem applyJournal_sourceLabel (s : System) (attempt : JournalAttempt s.adapter.journal) :
    sourceLabel (applyJournal s attempt).toLogEntry =
      some (journalSourceLabel s (applyJournal s attempt).journalEvent) := by
  cases attempt with
  | failed work => rfl
  | done result =>
    unfold applyJournal
    cases event : result.event <;> simp only [event]
    all_goals repeat' first | rfl | split
    all_goals simp_all [journalSourceLabel,sourceLabel]

structure RuntimeInvariant (s : System) (a : Durability.Abstract Frame) (stable : Frame) : Prop where
  related : Durability.Related s.adapter.journal.machine a
  frames : DurableFrames (initialFrame s.adapter.initialKind) a stable
  current : StableCurrent s stable
  pending : PendingConsistent s a stable
  coupled : FramePeer stable s.peer
  traffic : TrafficSafe stable s
  names : PeerNamesBelow stable.nextIdentity s.peer
  authentic : ∀ command, s.adapter.pendingCause = some command → CommandAuthentic s.peer command

theorem RuntimeInvariant.consistent {s : System} {a : Durability.Abstract Frame} {stable : Frame}
    (inv : RuntimeInvariant s a stable) : FrameConsistent s :=
  ⟨a,stable,inv.related,inv.frames,inv.current,inv.pending⟩

theorem RuntimeInvariant.valid {s : System} {a : Durability.Abstract Frame} {stable : Frame}
    (inv : RuntimeInvariant s a stable) : stable.Valid := validateFrames_valid inv.frames.validated


theorem RuntimeInvariant.initial (kind : Migration.Kind) :
    RuntimeInvariant (initialSystem kind) Durability.initialAbstract (initialFrame kind) := by
  constructor
  · exact Durability.related_initial
  · exact DurableFrames.initial kind
  · intro frame present; exact (Option.some.inj present).symm
  · exact PendingConsistent.initial kind
  · intro slot request present
    cases slot <;> simp [initialFrame,PendingMigration.Slots.get] at present
  · constructor <;> intros <;> contradiction
  · intro key entry present; contradiction
  · intro command impossible; cases impossible

def SilentObservation (o : LogEntry) : Prop :=
  sourceLabel o = some .internal ∧ ∀ record, o.journalEvent ≠ some (.commit record)

theorem reject_silent (s : System) (status : Status) (work : List Work) :
    SilentObservation (reject s status work).toLogEntry := by
  exact ⟨rfl,fun _ impossible => by cases impossible⟩

theorem beginChange_silent (s : System) (command : FrameCommand) :
    SilentObservation (beginChange s command).toLogEntry := by
  unfold beginChange
  repeat' first
    | exact ⟨rfl,fun _ impossible => by cases impossible⟩
    | split
  rename_i old present next changed result done
  refine ⟨rfl,?_⟩
  intro record impossible
  have event := journalInvoke_event _ _ result done
  simp only [event] at impossible
  cases impossible

theorem sendFor_silent (s : System) (identity : Nat) (command : Send) :
    SilentObservation (sendFor s identity command).toLogEntry := by
  unfold sendFor
  repeat' first | exact ⟨rfl,fun _ impossible => by cases impossible⟩ | split
  all_goals simp only [Option.map,pushLocal,pushCancellation]
  all_goals repeat' first | exact ⟨rfl,fun _ impossible => by cases impossible⟩ | split

theorem handle_silent (s : System) : SilentObservation (handle s).toLogEntry := by
  unfold handle
  repeat' first
    | exact ⟨rfl,fun _ impossible => by cases impossible⟩
    | split
  all_goals dsimp only
  all_goals repeat' first
    | exact ⟨rfl,fun _ impossible => by cases impossible⟩
    | exact beginChange_silent _ _
    | exact sendFor_silent _ _ _
    | split


theorem RuntimeInvariant.commit_command {s : System} {a b : Durability.Abstract Frame}
    {stable : Frame} (inv : RuntimeInvariant s a stable) (record : Durability.Record Frame)
    (source : Durability.SpecStep (.commit record) a b) :
    ∃ command, s.adapter.pendingCause = some command ∧ advance stable command = .changed record.payload := by
  cases source with
  | commit online active fresh =>
    rcases inv.pending record active with member | invoked
    · exact False.elim (fresh record member rfl)
    · exact invoked

theorem RuntimeInvariant.commit_source {s : System} {a b : Durability.Abstract Frame}
    {stable : Frame} (inv : RuntimeInvariant s a stable) (record : Durability.Record Frame)
    (source : Durability.SpecStep (.commit record) a b) :
    ∃ command, s.adapter.pendingCause = some command ∧
      FramePeer record.payload s.peer ∧
      DelayStep (frameSourceLabel stable command) (sourceView stable s.peer) (sourceView record.payload s.peer) ∧
      journalSourceLabel s (some (.commit record)) = frameSourceLabel stable command := by
  obtain ⟨command,cause,advanced⟩ := inv.commit_command record source
  have proposed := (advance_proposed stable record.payload command advanced).1
  refine ⟨command,cause,?_,?_,?_⟩
  · exact propose_framePeer stable record.payload s.peer command inv.coupled inv.names.fresh
      (inv.authentic command cause) proposed
  · exact propose_sourceView stable record.payload s.peer command inv.valid inv.coupled inv.names.fresh proposed
  · have counter := advance_nextIdentity stable record.payload command advanced
    cases command <;> simp_all [journalSourceLabel,frameSourceLabel,admissionDelta]

theorem step_silent (s : System) (command : Command)
    (notStorage : ∀ c, command ≠ .storage c)
    (notNetwork : ∀ deliver, command ≠ .network deliver) :
    SilentObservation (step s command).toLogEntry := by
  cases command with
  | storage c => exact False.elim (notStorage c rfl)
  | network deliver => exact False.elim (notNetwork deliver rfl)
  | handle => exact handle_silent s
  | «local» c =>
    simp only [step]
    unfold localCommand
    repeat' first
      | exact reject_silent _ _ _
      | exact beginChange_silent _ _
      | split
    all_goals dsimp only
    all_goals repeat' first
      | exact reject_silent _ _ _
      | exact beginChange_silent _ _
      | split
  | send second c =>
    simp only [step]
    repeat' first
      | exact reject_silent _ _ _
      | exact sendFor_silent _ _ _
      | split
  | reconcile =>
    simp only [step]
    unfold reconcile
    split
    · exact reject_silent _ _ _
    · exact sendFor_silent _ _ _
  | commitMigration =>
    simp only [step]
    unfold commitMigration
    split
    · exact reject_silent _ _ _
    · exact beginChange_silent _ _
  | crash => exact ⟨rfl,fun _ impossible => by cases impossible⟩
  | submit | receive | drain | duplicateInbound | duplicateOutbound | dropInbound | dropOutbound | rotateInbound | rotateOutbound | prepareMigration target budget allocationOK validationOK | cancelMigration | cleanupMigration | inspect =>
    simp only [step]
    try simp only [submit, receiveNetwork, drain, duplicateInbound, duplicateOutbound, prepareMigration, cancelMigration, cleanupMigration, pushLocal]
    all_goals repeat' first
      | exact ⟨rfl,fun _ impossible => by cases impossible⟩
      | split

theorem observation_stable_frame (s : System) (o : Observation s.adapter.journal.machine s.peer)
    (a b : Durability.Abstract Frame) (before after : Frame)
    (oldRelation : Durability.Related s.adapter.journal.machine a)
    (newRelation : Durability.Related o.system.adapter.journal.machine b)
    (sameKind : o.system.adapter.initialKind = s.adapter.initialKind)
    (old : validateFrames (initialFrame s.adapter.initialKind) (a.history.map Durability.Record.payload) = some before)
    (new : validateFrames (initialFrame o.system.adapter.initialKind) (b.history.map Durability.Record.payload) = some after) :
    match o.journalEvent with
    | none => after = before
    | some (.commit record) => after = record.payload
    | some _ => after = before := by
  have native := o.native
  rw [sameKind] at new
  cases event : o.journalEvent with
  | none =>
    simp only [event] at native ⊢
    have same := oldRelation.root.unique (native ▸ newRelation.root)
    rw [← same,old] at new
    exact (Option.some.inj new).symm
  | some e =>
    simp only [event] at native ⊢
    obtain ⟨c,source,related⟩ := native.simulation oldRelation
    have same := related.root.unique newRelation.root
    rw [← same] at new
    cases source with
    | commit online active fresh =>
      simp only [List.map_append,List.map_singleton] at new
      rw [validateFrames_append_of_success _ _ _ _ old] at new
      unfold validateFrames at new
      split at new
      · unfold validateFrames at new
        split at new
        · exact (Option.some.inj new).symm
        · contradiction
      · contradiction
    | internal | invoke online inactive | acknowledge online active member | reject online active member key different | query online inactive | crash | recover offline =>
      rw [old] at new
      exact (Option.some.inj new).symm

theorem RuntimeInvariant.network_peer {s : System} {a : Durability.Abstract Frame}
    {stable : Frame} (inv : RuntimeInvariant s a stable) (deliver : Bool) :
    FramePeer stable (network s deliver).system.peer ∧
      PeerNamesBelow stable.nextIdentity (network s deliver).system.peer := by
  cases outbound : s.outbound with
  | nil => simpa [network,outbound,reject] using And.intro inv.coupled inv.names
  | cons message rest =>
    rcases message with ⟨identity,command⟩
    have traffic := inv.traffic.outbound identity command (by simp [outbound])
    simp only [network,outbound]
    exact ⟨FramePeer.step_of_traffic stable s.peer identity command inv.valid inv.coupled traffic.1 traffic.2,
      inv.names.peerStep identity command (FrameTraffic.identity_lt stable s.peer identity command inv.valid inv.names traffic.1)⟩

theorem step_nonnetwork_peer (s : System) (command : Command)
    (notNetwork : ∀ deliver, command ≠ .network deliver) :
    (step s command).system.peer = s.peer := by
  rw [step_peer]
  cases command <;> first | rfl | exact False.elim (notNetwork _ rfl)

theorem step_nonnetwork_label (s : System) (command : Command)
    (notNetwork : ∀ deliver, command ≠ .network deliver) :
    sourceLabel (step s command).toLogEntry =
      some (journalSourceLabel s (step s command).journalEvent) := by
  by_cases storageCase : ∃ c, command = .storage c
  · obtain ⟨c,rfl⟩ := storageCase
    simp only [step,storage]
    split
    · rfl
    · exact applyJournal_sourceLabel _ _
  · have silent := step_silent s command (by simpa using storageCase) notNetwork
    rw [silent.1]
    cases event : (step s command).journalEvent with
    | none => rfl
    | some e =>
      cases e <;> first | rfl | exact False.elim (silent.2 _ event)

theorem RuntimeInvariant.step {s : System} {a : Durability.Abstract Frame}
    {stable : Frame} (inv : RuntimeInvariant s a stable) (command : Command) :
    ∃ b after label, RuntimeInvariant (FRPSpec.PendingCrash.step s command).system b after ∧
      sourceLabel (FRPSpec.PendingCrash.step s command).toLogEntry = some label ∧
      DelayStep label (sourceView stable s.peer) (sourceView after (FRPSpec.PendingCrash.step s command).system.peer) := by
  obtain ⟨b,after,related,frames,current,pending⟩ := inv.consistent.step command
  have valid := validateFrames_valid frames.validated
  have traffic := step_traffic s stable command inv.traffic inv.current inv.valid inv.coupled
  have authentic := step_pending s stable command inv.traffic inv.authentic
  have monotone := observation_counter_monotone s (FRPSpec.PendingCrash.step s command) a b stable after
    inv.related related inv.frames.validated frames.validated
  have selected := observation_stable_frame s (FRPSpec.PendingCrash.step s command) a b stable after
    inv.related related (step_initialKind s command) inv.frames.validated frames.validated
  by_cases isNetwork : ∃ deliver, command = .network deliver
  · obtain ⟨deliver,rfl⟩ := isNetwork
    have noEvent : (FRPSpec.PendingCrash.step s (.network deliver)).journalEvent = none := by
      simp only [FRPSpec.PendingCrash.step,network]
      split <;> rfl
    simp only [noEvent] at selected
    subst after
    obtain ⟨coupled,names⟩ := inv.network_peer deliver
    obtain ⟨label,labelEq,transition⟩ := network_sourceView_refines s stable deliver inv.valid
      (fun id action member => (inv.traffic.outbound id action member).1)
    exact ⟨b,stable,label,⟨related,frames,current,pending,coupled,traffic,names,authentic⟩,labelEq,transition⟩
  · have notNetwork : ∀ deliver, command ≠ .network deliver := by simpa using isNetwork
    have peer := step_nonnetwork_peer s command notNetwork
    have labelEq := step_nonnetwork_label s command notNetwork
    have native := (FRPSpec.PendingCrash.step s command).native
    cases event : (FRPSpec.PendingCrash.step s command).journalEvent with
    | none =>
      simp only [event] at selected
      subst after
      refine ⟨b,stable,.internal,⟨related,frames,current,pending,?_,traffic,?_,authentic⟩,?_,?_⟩
      · simpa only [peer] using inv.coupled
      · simpa only [peer] using inv.names
      · simpa only [event,journalSourceLabel] using labelEq
      · rw [peer]; exact .internal _
    | some e =>
      simp only [event] at native selected
      obtain ⟨c,source,relation⟩ := native.simulation inv.related
      cases e with
      | commit record =>
        subst after
        obtain ⟨action,cause,coupled,transition,label⟩ := inv.commit_source record source
        have proposed : propose stable action = .changed record.payload := by
          obtain ⟨action',cause',advanced'⟩ := inv.commit_command record source
          have eq := Option.some.inj (cause.symm.trans cause')
          subst action'
          exact (advance_proposed _ _ _ advanced').1
        have traffic' : TrafficSafe record.payload (FRPSpec.PendingCrash.step s command).system := by
          apply propose_traffic stable record.payload _ action
          · simpa only [peer] using inv.coupled
          · simpa only [peer] using inv.authentic action cause
          · exact valid
          · exact proposed
          · exact traffic
        refine ⟨b,record.payload,frameSourceLabel stable action,
          ⟨related,frames,current,pending,?_,traffic',?_,authentic⟩,?_,?_⟩
        · simpa only [peer] using coupled
        · rw [peer]
          intro key entry member
          exact Nat.lt_of_lt_of_le (inv.names key entry member) monotone
        · simpa only [event,label] using labelEq
        · simpa only [peer] using transition
      | internal | invoke record | acknowledge record | reject record | query | crash | recover =>
        subst after
        refine ⟨b,stable,.internal,⟨related,frames,current,pending,?_,traffic,?_,authentic⟩,?_,?_⟩
        · simpa only [peer] using inv.coupled
        · simpa only [peer] using inv.names
        · simpa only [event,journalSourceLabel] using labelEq
        · rw [peer]; exact .internal _

theorem RuntimeInvariant.execute {s : System} {a : Durability.Abstract Frame}
    {stable : Frame} (inv : RuntimeInvariant s a stable) (commands : List Command) :
    ∃ b after, RuntimeInvariant (FRPSpec.PendingCrash.execute s commands).system b after ∧
      DelayRun (sourceView stable s.peer) (FRPSpec.PendingCrash.execute s commands).observations
        (sourceView after (FRPSpec.PendingCrash.execute s commands).system.peer) := by
  induction commands generalizing s a stable with
  | nil => exact ⟨a,stable,inv,.nil _⟩
  | cons command commands ih =>
    obtain ⟨b,after,label,next,labelEq,transition⟩ := inv.step command
    obtain ⟨c,final,consistent,run⟩ := ih next
    exact ⟨c,final,consistent,.cons labelEq transition run⟩

/-- Every actual finite runtime execution refines the independent Boolean delay
source, including durable admissions and peer-side terminal transitions. -/
theorem execute_source_refinement (kind : Migration.Kind) (commands : List Command) :
    ∃ final, DelayRun {state := false, waiting := []}
      (execute (initialSystem kind) commands).observations final := by
  obtain ⟨a,frame,consistent,run⟩ := (RuntimeInvariant.initial kind).execute commands
  exact ⟨_,by simpa [sourceView,projectedSource,initialFrame,initialSystem,Frame.head] using run⟩

end FRPSpec.PendingCrash

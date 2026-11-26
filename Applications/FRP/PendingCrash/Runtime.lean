import Applications.FRP.PendingCrash.Journal

/-! A crash-stop adapter with a durable peer and explicit external traffic.
Only the bounded local queue is lost on adapter crash. -/
namespace FRPSpec.PendingCrash
open PendingMigration

inductive Message where
  | request (identity : Nat) (command : PeerCommand)
  | reply (receipt : Receipt)
  deriving DecidableEq, Repr

def Message.identity : Message → Nat
  | .request identity _ => identity
  | .reply receipt => receipt.identity

structure LocalQueue where
  messages : List Message := []
  bounded : messages.length ≤ 4 := by decide

inductive Status where
  | refused | busy | full | queued | sent | handled | staged | stored | acknowledged
  | prepared | migrated | allocationFailure | validationFailure | resourceFailure
  | crashed | reconstructed | stopped | released | inspected
  deriving DecidableEq, Repr

structure Adapter where
  journal : Journal := initialJournal
  initialKind : Migration.Kind := .delay
  current : Option Frame := some (initialFrame .delay)
  active : Option Migration.Backend := some (Migration.realize .delay false)
  prepared : Option Migration.Backend := none
  retired : List Migration.Backend := []
  queue : LocalQueue := {}
  pendingCause : Option FrameCommand := none
  reconcileOrder : List Nat := []
  stopped : Bool := false

/-- External traffic survives adapter crashes. It is distinct from the owned
four-entry queue and from the durable peer receipt table. -/
structure System where
  adapter : Adapter := {}
  peer : Peer := []
  outbound : List (Nat × PeerCommand) := []
  inbound : List Receipt := []

def initialSystem (kind : Migration.Kind := .delay) : System :=
  {adapter := {initialKind := kind, current := some (initialFrame kind), active := some (Migration.realize kind false)}}

structure LogEntry where
  system : System
  status : Status
  journalEvent : Option (Durability.Event Frame) := none
  accepted : Option (Nat × Bool) := none
  effect : Option (Nat × Bool) := none
  prevented : Option (Nat × Bool) := none
  work : List Work := []
  peerCommands : List (Nat × PeerCommand) := []

/-- The certificate concerns the exact journal machine before and after this
operation. It is erased by execution and cannot supply missing peer evidence. -/
structure Observation (before : Durability.Machine Frame) (beforePeer : Peer) extends LogEntry where
  native : match journalEvent with
    | none => system.adapter.journal.machine = before
    | some event => Durability.Step event before system.adapter.journal.machine := by rfl
  peerNative : system.peer = (peerExecute beforePeer peerCommands).peer := by rfl
  peerEffects : effect.toList = (peerExecute beforePeer peerCommands).effects := by rfl

def idle (s : System) : Bool :=
  !s.adapter.stopped && s.adapter.current.isSome &&
    s.adapter.journal.machine.active.isNone && s.adapter.journal.machine.pending.isNone

def businessReady (s : System) : Bool :=
  idle s && s.adapter.prepared.isNone && s.adapter.retired.isEmpty &&
    s.adapter.reconcileOrder.isEmpty

def reject (s : System) (status : Status := .refused) (work : List Work := [.attempt 0]) : Observation s.adapter.journal.machine s.peer :=
  {system := s, status := status, work := work}

def pushLocal (s : System) (message : Message) : Observation s.adapter.journal.machine s.peer :=
  let q := s.adapter.queue
  if h : q.messages.length < 4 then
    {system := {s with adapter := {s.adapter with queue :=
        ⟨q.messages ++ [message], by simp only [List.length_append, List.length_singleton]; omega⟩}}, status := .queued, work := [.messageCheck, .allocate (q.messages.length + 1),
        .copy q.messages.length, .release q.messages.length]}
  else reject s .full [.messageCheck]

/-- Cancellation reserves before submitting its cancel. The pair is enqueued
atomically, so a full queue cannot leave an unreported half-operation. -/
def pushCancellation (s : System) (identity : Nat) (input : Bool) : Observation s.adapter.journal.machine s.peer :=
  let q := s.adapter.queue
  if h : q.messages.length + 2 ≤ 4 then
    {system := {s with adapter := {s.adapter with queue :=
        ⟨q.messages ++ [.request identity (.reserve input), .request identity (.cancel input)],
          by simpa using h⟩}}, status := .queued,
      work := [.messageCheck, .allocate (q.messages.length + 2), .copy q.messages.length, .release q.messages.length]}
  else reject s .full [.messageCheck]

/-- Caller status follows acknowledgment, not invocation or the first cell write. -/
def acknowledgeStatus : Option FrameCommand → Status
  | some (.migrate _) => .migrated
  | _ => .acknowledged

def beginChange (s : System) (command : FrameCommand) : Observation s.adapter.journal.machine s.peer :=
  if !idle s then reject s .busy else
  match s.adapter.current with
  | none => reject s .busy
  | some old => match advance old command with
    | .refused => reject s .refused [.validateFrame]
    | .stopped => {system := {s with adapter := {s.adapter with stopped := true}}, status := .stopped, work := [.validateFrame]}
    | .changed next =>
      match journalInvoke s.adapter.journal next with
      | .failed work => reject s .refused (.validateFrame :: work)
      | .done result =>
        {system := {s with adapter := {s.adapter with journal := result.journal, pendingCause := some command}}, status := .staged, journalEvent := some result.event, work := .validateFrame :: result.work, native := result.native}

/-- Validate exactly the traversed prefix, retaining the failed check in work. -/
def validateMeasured : Frame → List Frame → Option Frame × List Work
  | frame, [] => (if frame.Valid then some frame else none, [.validateFrame])
  | frame, next :: frames =>
    if successor frame next then
      let rest := validateMeasured next frames
      (rest.1, .validateFrame :: rest.2)
    else (none, [.validateFrame])

theorem validateMeasured_eq (frame : Frame) (frames : List Frame) :
    (validateMeasured frame frames).1 = validateFrames frame frames := by
  induction frames generalizing frame with
  | nil => rfl
  | cons next frames ih =>
    by_cases h : successor frame next = true <;> simp [validateMeasured, validateFrames, ih, h]

/-- Reconciliation order is the retained admission order, never table order. -/
def identities (frame : Frame) : List Nat :=
  frame.order.filterMap fun slot => (frame.requests.get slot).map Request.identity

def consumeReconciliation (a : Adapter) (identity : Nat) : Adapter :=
  if a.reconcileOrder.head? = some identity then {a with reconcileOrder := a.reconcileOrder.tail} else a

/-- Native journal results are interpreted only at their actual labeled cut. -/
def applyJournal (s : System) (attempt : JournalAttempt s.adapter.journal) : Observation s.adapter.journal.machine s.peer :=
  match attempt with
  | .failed work => reject s .refused work
  | .done result =>
    let base := {s.adapter with journal := result.journal}
    let default : Observation s.adapter.journal.machine s.peer := {system := {s with adapter := base}, status := .stored, journalEvent := some result.event, work := result.work, native := result.native}
    match result.event with
    | .commit record =>
      let frame := record.payload
      let updated := {base with current := some frame}
      match s.adapter.pendingCause with
      | some (.migrate _) => match s.adapter.prepared, s.adapter.active with
        | some target, some old =>
          if target.kind = frame.kind ∧ target.logical = frame.logical then
            {default with system := {s with adapter := {updated with
              active := some target, prepared := none, retired := old :: s.adapter.retired}}}
          else {default with system := {s with adapter := {updated with stopped := true}}, status := .stopped}
        | _, _ => {default with system := {s with adapter := {updated with stopped := true}}, status := .stopped}
      | some .tickCommit =>
        match s.adapter.active, s.adapter.current.bind Frame.head with
        | some active, some (_, request) =>
          {default with system := {s with adapter := {updated with
            active := some (Migration.evaluate active request.input).candidate}}, work := result.work ++ [.allocate (Migration.evaluate active request.input).candidate.cells,
              .copy active.cells, .release active.cells]}
        | _, _ => {default with system := {s with adapter := {updated with stopped := true}}, status := .stopped}
      | some (.accept input) =>
        {default with system := {s with adapter := updated}, accepted := some (frame.nextIdentity - 1,input)}
      | _ => {default with system := {s with adapter := updated}}
    | .acknowledge _ =>
      let updated := match s.adapter.pendingCause with
        | some (.receive receipt) => {base with reconcileOrder := (consumeReconciliation base receipt.identity).reconcileOrder}
        | _ => base
      {default with system := {s with adapter := {base with pendingCause := none, reconcileOrder := updated.reconcileOrder}}, status := acknowledgeStatus s.adapter.pendingCause}
    | .recover history =>
      let validation := validateMeasured (initialFrame s.adapter.initialKind) (history.map Durability.Record.payload)
      match validation.1 with
      | none => {default with system := {s with adapter := {base with stopped := true, current := none, active := none}}, status := .stopped, work := result.work ++ [.allocate history.length, .copy history.length] ++ validation.2 ++ [.release history.length]}
      | some frame =>
        let active := reconstruct frame
        {default with system := {s with adapter := {base with current := some frame, active := some active, reconcileOrder := identities frame}}, status := .reconstructed, work := result.work ++ [.allocate history.length, .copy history.length] ++ validation.2 ++
            [.release history.length, .allocate active.cells, .convert active.cells]}
    | _ => default

inductive StorageCommand where
  | prepare | write | persist | publish | acknowledge | startRead | read | recover
  deriving DecidableEq, Repr

def storageCommand : StorageCommand → JournalCommand
  | .prepare => .prepare
  | .write => .write
  | .persist => .persist
  | .publish => .publish
  | .acknowledge => .acknowledge
  | .startRead => .startRead
  | .read => .read
  | .recover => .recover

def storage (s : System) (command : StorageCommand) : Observation s.adapter.journal.machine s.peer :=
  if command == .acknowledge && !s.adapter.retired.isEmpty then reject s .busy
  else applyJournal s (journalStep s.adapter.journal (storageCommand command))

/-- A crash ends this incarnation and releases its volatile copies. Outstanding
external submissions and the independent peer are retained unchanged. -/
def crash (s : System) : Observation s.adapter.journal.machine s.peer :=
  let result := journalCrash s.adapter.journal
  let cells := (s.adapter.active.map Migration.Backend.cells).getD 0 +
    (s.adapter.prepared.map Migration.Backend.cells).getD 0 +
    (s.adapter.retired.map Migration.Backend.cells).sum + s.adapter.queue.messages.length
  {system := {s with adapter := {s.adapter with journal := result.journal, current := none, active := none, prepared := none, retired := [], queue := {}, pendingCause := none, reconcileOrder := [], stopped := false}}, status := .crashed, journalEvent := some .crash, work := result.work ++ [.release cells], native := result.native}

/-- Callback retirement scans exactly until the first matching lifetime name,
retaining the work of an unsuccessful full scan as well. -/
def checkMessageIdentity (identity : Nat) : List Message → Bool × List Work
  | [] => (false, [])
  | message :: rest =>
    if message.identity == identity then (true, [.messageCheck])
    else let checked := checkMessageIdentity identity rest
         (checked.1, .messageCheck :: checked.2)

theorem checkMessageIdentity_eq (identity : Nat) (messages : List Message) :
    (checkMessageIdentity identity messages).1 = messages.any (fun m => m.identity == identity) := by
  induction messages with
  | nil => rfl
  | cons message rest ih =>
    simp only [checkMessageIdentity,List.any_cons]
    split <;> simp_all

/-- A physical slot can be reused only after its owned callback queue is empty
of that lifetime identity. External late messages remain identity-keyed. -/
def localCommand (s : System) (command : FrameCommand) : Observation s.adapter.journal.machine s.peer :=
  if !businessReady s then reject s .busy else
  match command with
  | .receive _ | .migrate _ => reject s
  | .release => match s.adapter.current.bind Frame.head with
    | none => reject s
    | some (_, request) =>
      let checked := checkMessageIdentity request.identity s.adapter.queue.messages
      if checked.1 then reject s .busy (checked.2 ++ [.attempt 0])
      else { (beginChange s command) with work := checked.2 ++ (beginChange s command).work }
  | _ => beginChange s command

inductive Send where
  | reserve | query | publish | cancel
  deriving DecidableEq, Repr

def sendFor (s : System) (identity : Nat) (command : Send) : Observation s.adapter.journal.machine s.peer :=
  if !idle s || s.adapter.prepared.isSome then reject s .busy else
  match s.adapter.current.bind (fun frame => frame.find identity) with
  | none => reject s
  | some (slot, request) =>
    let outgoing : Option PeerCommand := match command with
      | .reserve => some (.reserve request.input)
      | .query => some .query
      | .cancel => if request.routeOpen then some (.cancel request.input) else none
      | .publish =>
        if request.routeOpen && request.phase != .accepted && request.phase != .cancelled &&
            (s.adapter.current.map (fun f => f.order.head? == some slot)).getD false then
          request.output.map (PeerCommand.publish request.input)
        else none
    match outgoing with
    | none => reject s
    | some (.cancel input) => pushCancellation s identity input
    | some outgoing => pushLocal s (.request identity outgoing)

/-- Query the next retained identity; receipt dispatch decides any follow-up.
No executable reconciliation path reads the peer table. -/
def reconcile (s : System) : Observation s.adapter.journal.machine s.peer :=
  match s.adapter.reconcileOrder.head? with
  | none => reject s
  | some identity => sendFor s identity .query

/-- External submission is separated from local enqueue and peer publication. -/
def submit (s : System) : Observation s.adapter.journal.machine s.peer :=
  if !idle s || s.adapter.prepared.isSome then reject s .busy else
  match h : s.adapter.queue.messages with
  | .request identity command :: rest =>
    let queue : LocalQueue := ⟨rest, by have := s.adapter.queue.bounded; rw [h] at this; simp only [List.length_cons] at this; omega⟩
    {system := {s with adapter := {s.adapter with queue := queue}, outbound := s.outbound ++ [(identity,command)]}, status := .sent, work := [.messageCheck, .copy s.outbound.length, .allocate (s.outbound.length + 1), .release (s.outbound.length + 1)]}
  | _ => reject s

/-- Processing submitted traffic is allowed while the local adapter is offline.
The peer's one atomic effect/receipt transition is the only business effect. -/
def network (s : System) (deliverReply : Bool) : Observation s.adapter.journal.machine s.peer :=
  match s.outbound with
  | [] => reject s
  | (identity, command) :: rest =>
    let result := peerStep s.peer identity command
    {system := {s with peer := result.peer, outbound := rest, inbound := if deliverReply then s.inbound ++ [result.receipt] else s.inbound}, status := .handled, effect := result.effect.map (fun y => (identity,y)), prevented := result.prevented.map (fun x => (identity,x)), peerCommands := [(identity, command)], peerEffects := by simp [peerExecute, result, Option.toList_map], work := result.work ++ [.messageCheck, .release 1] ++
        (if deliverReply then [.allocate (s.inbound.length + 1), .copy s.inbound.length, .release s.inbound.length] else [])}

def receiveNetwork (s : System) : Observation s.adapter.journal.machine s.peer :=
  if s.adapter.current.isNone || s.adapter.stopped then reject s .busy else
  match s.inbound with
  | [] => reject s
  | receipt :: rest =>
    let result := pushLocal s (.reply receipt)
    if result.status == .queued then
      {result with system := {result.system with inbound := rest}, work := result.work ++ [.release 1]}
    else result

/-- Replays duplicate actual traffic, not caller-supplied forged receipts. -/
def duplicateInbound (s : System) : Observation s.adapter.journal.machine s.peer :=
  match s.inbound with
  | [] => reject s
  | receipt :: _ => {system := {s with inbound := receipt :: s.inbound}, status := .queued, work := [.messageCheck, .copy 1, .allocate 1]}

def duplicateOutbound (s : System) : Observation s.adapter.journal.machine s.peer :=
  match s.outbound with
  | [] => reject s
  | message :: _ => {system := {s with outbound := message :: s.outbound}, status := .queued, work := [.messageCheck, .copy 1, .allocate 1]}

/-- Receipts are consumed from the owned queue. Nonterminal stale answers never
replace selected output or a terminal phase. Recovery obtains evidence here. -/
def handle (s : System) : Observation s.adapter.journal.machine s.peer :=
  if !idle s || s.adapter.prepared.isSome then reject s .busy else
  match h : s.adapter.queue.messages with
  | .reply receipt :: rest =>
    let queue : LocalQueue := ⟨rest, by have := s.adapter.queue.bounded; rw [h] at this; simp only [List.length_cons] at this; omega⟩
    let popped := {s with adapter := {s.adapter with queue := queue}}
    let result : Observation s.adapter.journal.machine s.peer := match popped.adapter.current with
      | none => reject popped
      | some frame => match frame.find receipt.identity with
        | none => reject popped
        | some (_, request) =>
          match advance frame (.receive receipt) with
          | .changed _ | .stopped => beginChange popped (.receive receipt)
          | .refused =>
            let recovering := popped.adapter.reconcileOrder.head? == some receipt.identity
            let finished : Observation s.adapter.journal.machine s.peer := {system := {popped with adapter := {popped.adapter with reconcileOrder := (consumeReconciliation popped.adapter receipt.identity).reconcileOrder}}, status := .handled}
            match receipt.answer with
            | .absent =>
              if recovering && (request.phase == Phase.accepted || request.phase == Phase.computed) then
                sendFor popped receipt.identity .reserve
              else reject popped
            | .reserved input =>
              if recovering && input == request.input then
                if request.phase == Phase.accepted then finished
                else if request.phase == Phase.computed then sendFor popped receipt.identity .publish
                else reject popped
              else reject popped
            | .published input output | .tooLate input output =>
              if recovering && input == request.input && request.output == some output &&
                  (request.phase == Phase.confirmed || request.phase == Phase.committed) then finished
              else reject popped
            | .prevented input =>
              if recovering && input == request.input && request.phase == Phase.cancelled then finished
              else reject popped
            | .conflict => reject popped
    {result with work := [.messageCheck, .release 1] ++ result.work}
  | _ => reject s

/-- Closed identities may drain owned callbacks. External messages remain and
will be rejected by identity after slot reuse. -/
def drain (s : System) : Observation s.adapter.journal.machine s.peer :=
  if !businessReady s then reject s .busy else
  match s.adapter.current.bind Frame.head with
  | none => reject s
  | some (_, request) =>
    if request.routeOpen then reject s else
    let old := s.adapter.queue.messages
    let retained := old.filter (fun m => m.identity != request.identity)
    let queue : LocalQueue := ⟨retained, (List.length_filter_le _ _).trans s.adapter.queue.bounded⟩
    {system := {s with adapter := {s.adapter with queue := queue}}, status := .released, work := List.replicate old.length .messageCheck ++
        [.allocate retained.length, .copy retained.length, .release old.length]}

def transferWork : PendingMigration.TransferEvent → Work
  | .budget => .attempt 0
  | .attempt n => .attempt n
  | .allocate n => .allocate n
  | .copy n => .copy n
  | .validate => .validateFrame
  | .release n => .release n
  | .ownershipCut => .rootPublish

/-- Additional retained local reservations beyond the native preparation
component: append-only journal cells, cached record links, pending copy, cursor,
keyed frame and owned messages. Peer and in-flight network storage are separate. -/
def localReservations (s : System) : Nat :=
  let journal := s.adapter.journal
  let cache := (journal.machine.cache.map List.length).getD 0
  let pending := (journal.machine.pending.map (fun p => p.after.length + 1)).getD 0
  let cursor := match journal.machine.cursor with
    | none => 0
    | some (.prefixCells todo seen _) => todo.length + seen.length
    | some (.tailCells _ pre suffix) => pre.length + suffix.length
    | some (.done history) => history.length
  32 + 48 * journal.cells.length + cache + pending + cursor +
    5 * s.adapter.queue.messages.length + s.adapter.reconcileOrder.length +
    (s.adapter.retired.map Migration.Backend.cells).sum

/-- The native preparation component operates on the actual backend. The keyed
requests and external traffic are retained separately, not projected away in a
claim about the old pending-session validity invariant. -/
def prepareMigration (s : System) (kind : Migration.Kind) (budget : Nat)
    (allocationOK validationOK : Bool) : Observation s.adapter.journal.machine s.peer :=
  if !businessReady s then reject s .busy else
  match s.adapter.active with
  | none => reject s .busy
  | some active =>
    let component : PendingMigration.Session := {active := active}
    let result := PendingMigration.step component (.prepare kind (budget - localReservations s) allocationOK validationOK)
    let status := match result.status with
      | .prepared => Status.prepared
      | .allocationFailure => .allocationFailure
      | .validationFailure => .validationFailure
      | .resourceFailure => .resourceFailure
      | _ => .refused
    {system := {s with adapter := {s.adapter with prepared := result.session.prepared.map (fun p => p.target)}}, status := status, work := result.transfer.flatMap (fun event => match event with
        | .copy cells => [.copy cells, .convert cells]
        | event => [transferWork event])}

def commitMigration (s : System) : Observation s.adapter.journal.machine s.peer :=
  match s.adapter.prepared with
  | none => reject s
  | some target => beginChange s (.migrate target.kind)

def cancelMigration (s : System) : Observation s.adapter.journal.machine s.peer :=
  if !idle s then reject s .busy else
  match s.adapter.prepared with
  | none => reject s
  | some target => {system := {s with adapter := {s.adapter with prepared := none}}, status := .released, work := [.release target.cells]}

/-- Release of the former owner is distinct from durable root publication and
must precede the caller's migrated acknowledgment. -/
def cleanupMigration (s : System) : Observation s.adapter.journal.machine s.peer :=
  match s.adapter.retired with
  | [] => reject s
  | old :: rest => {system := {s with adapter := {s.adapter with retired := rest}}, status := .released, work := [.release old.cells]}

inductive Command where
  | local (command : FrameCommand)
  | send (second : Bool) (command : Send)
  | storage (command : StorageCommand)
  | crash | reconcile | submit | receive | handle | drain
  | network (deliverReply : Bool := true)
  | duplicateInbound | duplicateOutbound | dropInbound | dropOutbound
  | rotateInbound | rotateOutbound
  | prepareMigration (target : Migration.Kind) (budget : Nat := 256)
      (allocationOK validationOK : Bool := true)
  | commitMigration | cancelMigration | cleanupMigration | inspect
  deriving DecidableEq, Repr

def step (s : System) : Command → Observation s.adapter.journal.machine s.peer
  | .local command => localCommand s command
  | .send second command =>
    if !businessReady s then reject s .busy else
    match s.adapter.current with
    | none => reject s
    | some frame => match (if second then frame.order.tail else frame.order).head? with
      | none => reject s
      | some slot => match frame.requests.get slot with
        | none => reject s
        | some request => sendFor s request.identity command
  | .storage command => storage s command
  | .crash => crash s
  | .reconcile => reconcile s
  | .submit => submit s
  | .receive => receiveNetwork s
  | .handle => handle s
  | .drain => drain s
  | .network deliver => network s deliver
  | .duplicateInbound => duplicateInbound s
  | .duplicateOutbound => duplicateOutbound s
  | .dropInbound => match s.inbound with
    | [] => reject s
    | _ :: rest => {system := {s with inbound := rest}, status := .handled, work := [.release 1]}
  | .dropOutbound => match s.outbound with
    | [] => reject s
    | _ :: rest => {system := {s with outbound := rest}, status := .handled, work := [.release 1]}
  | .rotateInbound => match s.inbound with
    | [] => reject s
    | r :: rest => {system := {s with inbound := rest ++ [r]}, status := .handled, work := [.allocate s.inbound.length, .copy s.inbound.length, .release s.inbound.length]}
  | .rotateOutbound => match s.outbound with
    | [] => reject s
    | r :: rest => {system := {s with outbound := rest ++ [r]}, status := .handled, work := [.allocate s.outbound.length, .copy s.outbound.length, .release s.outbound.length]}
  | .prepareMigration target budget allocationOK validationOK =>
      prepareMigration s target budget allocationOK validationOK
  | .commitMigration => commitMigration s
  | .cancelMigration => cancelMigration s
  | .cleanupMigration => cleanupMigration s
  | .inspect => {system := s, status := .inspected}

structure Execution where
  system : System
  observations : List LogEntry

def execute : System → List Command → Execution
  | s, [] => ⟨s, []⟩
  | s, command :: commands =>
    let result := step s command
    let rest := execute result.system commands
    ⟨rest.system, result.toLogEntry :: rest.observations⟩

/-- All local durability events of the composed runtime, without peer effects
or queue traffic being mislabeled as local commits. -/
def Execution.journalEvents (run : Execution) : List (Durability.Event Frame) :=
  run.observations.filterMap LogEntry.journalEvent

theorem execute_native (s : System) (commands : List Command) :
    Interaction.Events.Interpret Durability.Step (execute s commands).journalEvents
      s.adapter.journal.machine (execute s commands).system.adapter.journal.machine := by
  induction commands generalizing s with
  | nil => rfl
  | cons command commands ih =>
    let result := step s command
    have certificate := result.native
    have rest := ih result.system
    cases h : result.journalEvent with
    | none =>
      simp only [h] at certificate
      simp only [result] at h
      simpa only [execute, Execution.journalEvents, List.filterMap_cons,
        result, h, certificate] using rest
    | some event =>
      simp only [h] at certificate
      simp only [result] at h
      simpa only [execute, Execution.journalEvents, List.filterMap_cons, h] using
        (show Interaction.Events.Interpret Durability.Step
          (event :: (execute result.system commands).journalEvents)
          s.adapter.journal.machine (execute result.system commands).system.adapter.journal.machine from
          ⟨result.system.adapter.journal.machine, certificate, rest⟩)

theorem execute_durability (s : System) (commands : List Command)
    (a : Durability.Abstract Frame) (related : Durability.Related s.adapter.journal.machine a) :
    ∃ b, Interaction.Events.Interpret Durability.SpecStep (execute s commands).journalEvents a b ∧
      Durability.Related (execute s commands).system.adapter.journal.machine b :=
  Durability.script_simulation _ related (execute_native s commands)

theorem execute_accepted_prefix (s : System) (commands : List Command)
    (a : Durability.Abstract Frame) (related : Durability.Related s.adapter.journal.machine a) :
    ∃ b suffix, Durability.Related (execute s commands).system.adapter.journal.machine b ∧
      b.history = a.history ++ suffix := by
  obtain ⟨b, run, relation⟩ := execute_durability s commands a related
  obtain ⟨suffix, eq⟩ := Durability.spec_script_prefix run
  exact ⟨b, suffix, relation, eq⟩

theorem execute_acknowledged (s : System) (commands : List Command)
    (a b : Durability.Abstract Frame) (e : Durability.Record Frame)
    (ack : Durability.SpecStep (.acknowledge e) a b)
    (related : Durability.Related s.adapter.journal.machine b) :
    ∃ c suffix, Durability.Related (execute s commands).system.adapter.journal.machine c ∧
      e ∈ c.history ∧ c.history = a.history ++ suffix := by
  obtain ⟨c, run, relation⟩ := execute_durability s commands b related
  obtain ⟨member, suffix, eq⟩ := Durability.acknowledged_survives ack run
  exact ⟨c, suffix, relation, member, eq⟩

theorem peerExecute_append (peer : Peer) (first later : List (Nat × PeerCommand)) :
    (peerExecute peer (first ++ later)).peer = (peerExecute (peerExecute peer first).peer later).peer ∧
    (peerExecute peer (first ++ later)).effects = (peerExecute peer first).effects ++
      (peerExecute (peerExecute peer first).peer later).effects := by
  induction first generalizing peer with
  | nil => simp [peerExecute]
  | cons command commands ih =>
    rcases command with ⟨identity, command⟩
    obtain ⟨hp, he⟩ := ih (peerStep peer identity command).peer
    constructor
    · exact hp
    · simp only [List.cons_append, peerExecute, he, List.append_assoc]

def Execution.peerCommands (run : Execution) : List (Nat × PeerCommand) :=
  run.observations.flatMap LogEntry.peerCommands

def Execution.effects (run : Execution) : List (Nat × Bool) :=
  run.observations.filterMap LogEntry.effect

/-- The composed adapter's external effects are exactly those of the keyed
atomic peer, even through local crashes and duplicated external submissions. -/
theorem execute_peer (s : System) (commands : List Command) :
    (execute s commands).system.peer = (peerExecute s.peer (execute s commands).peerCommands).peer ∧
    (execute s commands).effects = (peerExecute s.peer (execute s commands).peerCommands).effects := by
  induction commands generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons command commands ih =>
    let result := step s command
    have rest := ih result.system
    have composition := peerExecute_append s.peer result.peerCommands
      (execute result.system commands).peerCommands
    rw [← result.peerNative] at composition
    constructor
    · exact rest.1.trans composition.1.symm
    · have hs : (execute s (command :: commands)).effects =
          result.effect.toList ++ (execute result.system commands).effects := by
        cases h : result.effect <;> simp only [result] at h <;>
          simp [execute, Execution.effects, h, result]
      rw [hs, result.peerEffects, rest.2]
      exact composition.2.symm

/-- No lifetime identity can cause two external effects in any finite runtime
execution. This does not assert a fairness or eventual-response guarantee. -/
theorem execute_effects_unique (s : System) (commands : List Command) :
    ((execute s commands).effects.map Prod.fst).Nodup := by
  rw [(execute_peer s commands).2]
  exact peer_effects_unique _ _

end FRPSpec.PendingCrash

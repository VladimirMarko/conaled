import Applications.FRP.PendingRetention.Banks

/-! Closed transport and serialized persistent operations for the bounded
pending service. Commands choose delivery and crashes, but cannot forge a
trusted packet. Execution traces are external observations, not stored history. -/
namespace FRPSpec.PendingRetention
open PendingCrash PendingMigration

inductive Business where
  | reserve | query | cancel | publish
  deriving DecidableEq, Repr

def Business.code : Business → Nat
  | .reserve => 0 | .query => 1 | .cancel => 2 | .publish => 3

inductive LocalCommand where
  | accept (input : Bool)
  | evaluate | tickCommit | close | release
  | migrate (target : Migration.Kind) (allocationOK validationOK : Bool)
  deriving DecidableEq, Repr

def LocalCommand.frameCommand : LocalCommand → FrameCommand
  | .accept x => .accept x
  | .evaluate => .evaluate
  | .tickCommit => .tickCommit
  | .close => .close
  | .release => .release
  | .migrate k _ _ => .migrate k

inductive LocalCause where
  | frame (command : FrameCommand)
  | relinquish (target : Nat)
  | finish (target : Nat)
  deriving DecidableEq, Repr

inductive PeerCause where
  | business (identity : Nat) (command : PeerCommand) (reply : ReplyPacket)
      (effect prevented : Option Bool)
  | floor (target : Nat)
  | deletion (target : Nat)
  deriving DecidableEq, Repr

/-- No trace or proof ledger is part of the machine. The two cause registers
contain only the currently executing operation, not another snapshot. -/
structure System where
  localBank : LocalBanks
  peer : PeerBanks
  localCause : Option LocalCause := none
  peerCause : Option PeerCause := none
  localOut : List RequestPacket := []
  peerIn : List RequestPacket := []
  peerOut : List ReplyPacket := []
  localIn : List ReplyPacket := []
  localDown : Bool := false
  peerDown : Bool := false
  active : Option Migration.Backend := some (Migration.realize .delay false)
  prepared : Option Migration.Backend := none
  former : Option Migration.Backend := none
  retirementScan : Option (Nat × Nat) := none

/-- Charges name work actually requested at this microstep. The numeric fields
are bounded scan/copy counts, not timing estimates or a physical heap claim. -/
inductive Event where
  | check
  | scan (slots : Nat)
  | copy (slots : Nat)
  | allocate (slots : Nat) | release (slots : Nat) | dispatch
  | bank (endpoint : Bool)
  | writeRecord | persistRecord | writeHeader | persistHeader
  | publication (endpoint : Bool)
  | queueCopy | queueDrop | queueRefused
  | reconstruct | convert | validate | cleanup | crash
  deriving DecidableEq, Repr

/-- These events distinguish the bank action from helper traversal/copy work.
They do not price Lean allocation, garbage collection or persistence hardware. -/
def bankEvents {H R : Type} (endpoint : Bool) :
    Option (Durability.SnapshotBanks.Primitive H R) → List Event
  | none => [.check]
  | some (.writeRecord _ _) => [.bank endpoint, .writeRecord]
  | some (.persistRecord _ _) => [.bank endpoint, .persistRecord]
  | some (.writeHeader _) => [.bank endpoint, .writeHeader]
  | some (.persistHeader _) => [.bank endpoint, .persistHeader]
  | some .publish => [.publication endpoint]


/-- The number of predicate visits before the first failed check. -/
def checkedPrefix (test : α → Bool) : List α → Nat
  | [] => 0
  | x :: xs => if test x then 1 + checkedPrefix test xs else 1

/-- A fixed frame validator includes its two request slots. The growing outcome
population is checked separately, including its length traversal. -/
def localGuardWork (cfg : Config) (s : LocalSnapshot) : List Event :=
  [.validate] ++ if !decide s.frame.Valid then [] else
  [.check] ++ if s.frame.nextIdentity > cfg.lifetime then [] else
  [.check] ++ if s.floor > cfg.lifetime then [] else
  [.check] ++ if !(s.pending.all (fun n => n ≤ cfg.lifetime)) then [] else
  [.scan s.outcomes.length,.check] ++ if s.outcomes.length > cfg.outcomeCapacity then [] else
  [.scan (checkedPrefix (fun r => r.identity ≤ cfg.lifetime) s.outcomes)]

def peerGuardWork (cfg : Config) (s : PeerSnapshot) : List Event :=
  [.check] ++ if s.floor > cfg.lifetime then [] else
  [.check] ++ if !(s.pending.all (fun n => n ≤ cfg.lifetime)) then [] else
  [.scan s.entries.length,.check] ++ if s.entries.length > cfg.outcomeCapacity then [] else
  [.scan (checkedPrefix (fun r => r.1 ≤ cfg.lifetime) s.entries)]

/-- Observer instrumentation follows the helper's short-circuit branches.
Constructing this external work trace is not itself charged as service work. -/
def localDecisionWork (cfg : Config) (s : LocalSnapshot) (c : FrameCommand) : List Event :=
  [.check] ++ if s.pending.isSome then [] else
  let accepting := match c with | .accept _ => true | _ => false
  (if accepting then [.check] else []) ++
  if accepting && s.frame.nextIdentity ≥ cfg.lifetime then [] else
  (if accepting then [.scan s.outcomes.length,.check] else []) ++
  if accepting && s.outcomes.length ≥ cfg.outcomeCapacity then [] else
  [.validate] ++ match advance s.frame c with
  | .changed _ =>
    let changedWork := match c with
      | .accept _ => [.copy (s.outcomes.length + 1)]
      | .release => if s.frame.head.isSome then [.scan s.outcomes.length,.copy s.outcomes.length] else []
      | .receive r =>
        let a := match r.answer with | .tooLate x y => Answer.published x y | a => a
        if terminalAnswer a then [.scan s.outcomes.length,.copy s.outcomes.length] else []
      | _ => []
    changedWork ++ match localChangeCore cfg s c with
      | .ok t => localGuardWork cfg t
      | .error _ => []
  | _ => []

def peerWorkEvent : PendingCrash.Work → Event
  | .peerProbe _ => .scan 1
  | .peerWrite _ => .copy 1
  | .allocate n => .allocate n
  | .copy n => .copy n
  | .release n => .release n
  | _ => .check

def peerDecisionWork (cfg : Config) (s : PeerSnapshot) (i : Nat) (c : PeerCommand) : List Event :=
  [.check] ++ if i < s.floor then peerGuardWork cfg s ++ [.check] else
  [.check] ++ if i ≥ cfg.lifetime then [] else
  let r := peerStep s.entries i c
  [.dispatch] ++ r.work.map peerWorkEvent ++ [.scan r.peer.length,.check] ++
  if r.peer.length > cfg.outcomeCapacity then [] else
  peerGuardWork cfg {s with entries := r.peer} ++ [.check]

/-- Schedule lookup traverses the existing target prefix. Record replacement
also traverses/copies its prefix; no hidden operation list is stored. -/
def workerTraversal {H R : Type} (w : Durability.SnapshotBanks.Worker H R) : List Event :=
  [.scan w.target.items.length,.check] ++ if w.busy then
    [.scan (min w.target.items.length (w.cursor.val / 2))] ++
    match Durability.SnapshotBanks.operationAt w.target w.cursor.val with
    | some (.writeRecord i _) => [.scan (min i w.state.buffer.items.length),.copy (min i w.state.buffer.items.length)]
    | some (.persistRecord i _) =>
      let n := min i (w.state.disk.cells (!w.state.disk.selected)).items.length
      [.scan n,.copy n]
    | some (.persistHeader _) => [.copy w.state.buffer.items.length]
    | _ => []
  else []

inductive Observation where
  | idle
  | refused (reason : Refusal)
  | started
  | selected
  | query (result : Query)
  | current (frame : Frame) (floor : Nat) (pending : Option Nat)
  | expired (floor : Nat) (pending : Option Nat)
  | retirementComplete (target : Nat)
  deriving DecidableEq, Repr

structure Result where
  system : System
  observation : Observation := .idle
  label : SourceLabel := .internal
  events : List Event := []

inductive Queue where
  | localOut | peerIn | peerOut | localIn
  deriving DecidableEq, Repr

inductive Command where
  | local (command : LocalCommand)
  | send (identity : Nat) (operation : Business)
  | relinquishBefore (target : Nat)
  | retryRetirement
  | resumeDeletion
  | transferRequest
  | transferReply
  | duplicate (queue : Queue) (index : Nat)
  | drop (queue : Queue)
  | deliverRequest
  | deliverReply
  | progress
  | crashLocal | crashPeer | recoverLocal | recoverPeer
  | cleanup
  | inspect
  | query (identity : Nat)
  | malformed
  deriving DecidableEq, Repr

def initial : System :=
  {localBank := LocalBanks.initial {}, peer := PeerBanks.initial {}}

def controllerIdle (s : System) : Bool :=
  !s.localBank.busy && !s.peer.busy && s.localCause.isNone && s.peerCause.isNone &&
    s.retirementScan.isNone && s.former.isNone

def reject (s : System) (reason : Refusal) (events : List Event := [.check]) : Result :=
  {system := s, observation := .refused reason, events := events}

def pushRequest (cfg : Config) (s : System) (packet : RequestPacket) : Result :=
  if s.localOut.length < cfg.queueCapacity then
    {system := {s with localOut := s.localOut ++ [packet]}, events := [.scan s.localOut.length,.check,.copy (s.localOut.length + 1),.queueCopy]}
  else reject s .full [.scan s.localOut.length,.check,.queueRefused]

def pushReply (cfg : Config) (s : System) (packet : ReplyPacket) : Result :=
  if s.peerOut.length < cfg.queueCapacity then
    {system := {s with peerOut := s.peerOut ++ [packet]}, events := [.scan s.peerOut.length,.check,.copy (s.peerOut.length + 1),.queueCopy]}
  else {system := s, events := [.scan s.peerOut.length,.check,.queueDrop]}

def beginLocal (s : System) (target : LocalSnapshot) (cause : LocalCause) : Result :=
  {system := {s with localBank := s.localBank.begin target, localCause := some cause}, observation := .started, events := [.copy target.outcomes.length,.writeHeader]}

def beginPeer (s : System) (target : PeerSnapshot) (cause : PeerCause) : Result :=
  {system := {s with peer := s.peer.begin target, peerCause := some cause}, observation := .started, events := [.copy target.entries.length,.writeHeader]}

def localStep (cfg : Config) (s : System) (c : LocalCommand) : Result :=
  if !controllerIdle s || s.localDown then reject s .busy else
  let old := s.localBank.selected
  match localChange cfg old c.frameCommand with
  | .error reason => reject s reason (localDecisionWork cfg old c.frameCommand)
  | .ok target =>
    match c with
    | .migrate kind allocationOK validationOK =>
      if !allocationOK then reject s .full (localDecisionWork cfg old c.frameCommand ++ [.check]) else
      let converted := Migration.realize kind old.frame.logical
      if !validationOK || !converted.validate then reject s .invalid (localDecisionWork cfg old c.frameCommand ++ ([.convert,.check] ++ if validationOK then [.validate] else [])) else
      let begun := beginLocal {s with prepared := some converted} target (.frame c.frameCommand)
      {begun with events := localDecisionWork cfg old c.frameCommand ++ [.convert,.check,.validate] ++ begun.events}
    | _ =>
      let begun := beginLocal s target (.frame c.frameCommand)
      {begun with events := localDecisionWork cfg old c.frameCommand ++ begun.events}

/-- A retirement cursor checks one reserved name per step. It stores neither
an interval list nor a second outcome pool. Durable expiry starts only after
all covered names have passed this check. -/
def startRetirement (s : System) (target : Nat) : Result :=
  if !controllerIdle s || s.localDown then reject s .busy else
  let old := s.localBank.selected
  if target ≤ old.floor then
    {system := s, observation := .expired old.floor old.pending, events := [.check]}
  else if old.pending.isSome then reject s .busy else
  if target > old.frame.nextIdentity then reject s .invalid else
  {system := {s with retirementScan := some (target, old.floor)}, observation := .started, events := [.check]}

/-- Counts the same short-circuit search as `outcome`. -/
def outcomeProbes (identity : Nat) : List Outcome → Nat
  | [] => 0
  | r :: rest => if r.identity = identity then 1 else 1 + outcomeProbes identity rest

def scanRetirement (s : System) (target cursor : Nat) : Result :=
  let old := s.localBank.selected
  if cursor < target then
    match outcome old cursor with
    | none => reject {s with retirementScan := none} .unresolved
        [.scan (outcomeProbes cursor old.outcomes)]
    | some r =>
      if r.released && r.answer.any terminalAnswer then
        {system := {s with retirementScan := some (target,cursor+1)}, events := [.scan (outcomeProbes cursor old.outcomes), .check]}
      else reject {s with retirementScan := none} .unresolved
        [.scan (outcomeProbes cursor old.outcomes), .check]
  else beginLocal {s with retirementScan := none}
    {old with floor := target, pending := some target} (.relinquish target)

/-- Number of entry pairs inspected by structural list equality. -/
def equalProbes : List (Nat × Ledger) → List (Nat × Ledger) → Nat
  | [], _ => 0
  | _ :: _, [] => 0
  | x :: xs, y :: ys => if x = y then 1 + equalProbes xs ys else 1

def requestStep (cfg : Config) (s : System) : Result :=
  if !controllerIdle s || s.peerDown then reject s .busy else
  match s.peerIn with
  | [] => reject s .unknown
  | packet :: rest =>
    let consumed := {s with peerIn := rest}
    let old := s.peer.selected
    match packet with
    | .business identity command =>
      if old.pending.isSome then reject s .busy else
      match peerDecision cfg old identity command with
      | .error reason => reject consumed reason (.queueDrop :: peerDecisionWork cfg old identity command)
      | .ok (target,reply,effect,prevented) =>
        let work := [.queueDrop] ++ peerDecisionWork cfg old identity command ++
          [.check,.scan (equalProbes target.entries old.entries)]
        if target = old then
          let sent := pushReply cfg consumed reply
          {sent with events := work ++ sent.events}
        else
          let begun := beginPeer consumed target (.business identity command reply effect prevented)
          {begun with events := work ++ begun.events}
    | .retire target =>
      if old.pending.isSome then reject s .busy else
      if target ≤ old.floor then
        let sent := pushReply cfg consumed (.deleted target)
        {sent with events := .queueDrop :: sent.events}
      else
        let begun := beginPeer consumed {old with floor := target, pending := some target} (.floor target)
        {begun with events := .queueDrop :: begun.events}

def replyStep (cfg : Config) (s : System) : Result :=
  if !controllerIdle s || s.localDown then reject s .busy else
  match s.localIn with
  | [] => reject s .unknown
  | packet :: rest =>
    let consumed := {s with localIn := rest}
    let old := s.localBank.selected
    match packet with
    | .expired _ floor =>
      {system := consumed, observation := .expired floor old.pending, events := [.queueDrop,.check]}
    | .deleted target => match finishRetirement old target with
      | none => reject consumed .invalid [.queueDrop,.check]
      | some next =>
        let begun := beginLocal consumed next (.finish target)
        {begun with events := [.queueDrop,.scan old.outcomes.length,.copy next.outcomes.length] ++ begun.events}
    | .receipt receipt =>
      if receipt.identity < old.floor then
        {system := consumed, observation := .expired old.floor old.pending, events := [.queueDrop,.check]}
      else match localChange cfg old (.receive receipt) with
        | .error reason => reject consumed reason (.queueDrop :: localDecisionWork cfg old (.receive receipt))
        | .ok next =>
          let begun := beginLocal consumed next (.frame (.receive receipt))
          {begun with events := .queueDrop :: (localDecisionWork cfg old (.receive receipt) ++ begun.events)}

def localPublished (s : System) (cause : LocalCause) : Result :=
  let selected := s.localBank.selected
  let base := {s with localCause := none, active := some (reconstruct selected.frame), prepared := none}
  match cause with
  | .frame (.accept x) =>
    {system := base, observation := .selected, label := .accept (selected.frame.nextIdentity - 1) x, events := [.publication false, .reconstruct]}
  | .frame (.migrate _) =>
    {system := {base with active := s.prepared, former := s.active}, observation := .selected, events := [.publication false]}
  | .finish target =>
    {system := base, observation := .retirementComplete target, events := [.publication false, .reconstruct]}
  | _ => {system := base, observation := .selected, events := [.publication false, .reconstruct]}

def peerPublished (cfg : Config) (s : System) (cause : PeerCause) : Result :=
  let base := {s with peerCause := none}
  match cause with
  | .business identity _ reply effect prevented =>
    let sent := pushReply cfg base reply
    {sent with observation := .selected, label := match effect,prevented with
        | some y, _ => .output identity y
        | none, some x => .prevent identity x
        | _, _ => .internal, events := .publication true :: sent.events}
  | .floor _ => {system := base, observation := .selected, events := [.publication true]}
  | .deletion target =>
    let sent := pushReply cfg base (.deleted target)
    {sent with observation := .selected, events := .publication true :: sent.events}

def progress (cfg : Config) (s : System) : Result :=
  if s.localDown && s.peerDown then reject s .busy else
  match s.retirementScan with
  | some (target,cursor) => if s.localDown then reject s .busy
    else scanRetirement s target cursor
  | none =>
    match s.localCause with
    | some cause =>
      if s.localDown then reject s .busy else
      let (banks,published) := s.localBank.progress
      let next := {s with localBank := banks}
      if published then
        let result := localPublished next cause
        {result with events := workerTraversal s.localBank ++ result.events}
      else {system := next, events := workerTraversal s.localBank ++ bankEvents false s.localBank.nextOperation}
    | none => match s.peerCause with
      | some cause =>
        if s.peerDown then reject s .busy else
        let (banks,published) := s.peer.progress
        let next := {s with peer := banks}
        if published then
          let result := peerPublished cfg next cause
          {result with events := workerTraversal s.peer ++ result.events}
        else {system := next, events := workerTraversal s.peer ++ bankEvents true s.peer.nextOperation}
      | none => {system := s, events := [.check]}

/-- Duplication only copies an existing queue element, and consumes capacity. -/
def duplicateList {α : Type} (capacity index : Nat) (items : List α) : Option (List α) := do
  if items.length ≥ capacity then none else do
  let item ← items[index]?
  pure (items ++ [item])

/-- List-backed queue admission charges its traversals, not a constant queue price. -/
def duplicateWork (capacity index : Nat) (items : List α) : List Event :=
  [.scan items.length,.check] ++ if items.length ≥ capacity then [] else
  [.scan (min (index + 1) items.length)] ++
  if index < items.length then [.copy (items.length + 1)] else []

def duplicateQueue (cfg : Config) (s : System) (queue : Queue) (index : Nat) : Result :=
  let next := match queue with
    | .localOut => (duplicateList cfg.queueCapacity index s.localOut).map fun q => {s with localOut := q}
    | .peerIn => (duplicateList cfg.queueCapacity index s.peerIn).map fun q => {s with peerIn := q}
    | .peerOut => (duplicateList cfg.queueCapacity index s.peerOut).map fun q => {s with peerOut := q}
    | .localIn => (duplicateList cfg.queueCapacity index s.localIn).map fun q => {s with localIn := q}
  let work := match queue with
    | .localOut => duplicateWork cfg.queueCapacity index s.localOut
    | .peerIn => duplicateWork cfg.queueCapacity index s.peerIn
    | .peerOut => duplicateWork cfg.queueCapacity index s.peerOut
    | .localIn => duplicateWork cfg.queueCapacity index s.localIn
  match next with
  | none => reject s .full (work ++ [.queueRefused])
  | some t => {system := t, events := work ++ [.queueCopy]}

/-- The two cursor comparisons inspect the stored target lengths. Other
controller fields are scalar; this trace follows the same short circuit. -/
def controllerWork (s : System) : List Event :=
  [.scan s.localBank.target.items.length,.check] ++ if s.localBank.busy then [] else
  [.scan s.peer.target.items.length,.check] ++ if s.peer.busy then [] else
  [.check]

def commandControllerWork (s : System) : Command → List Event
  | .local _ | .send _ _ | .relinquishBefore _ | .retryRetirement | .resumeDeletion
  | .deliverRequest | .deliverReply | .inspect | .query _ => controllerWork s
  | _ => []

def step (cfg : Config) (s : System) : Command → Result := fun command =>
  let result : Result := match command with
    | .local c => localStep cfg s c
    | .send identity operation =>
      if !controllerIdle s || s.localDown || s.localBank.selected.pending.isSome then reject s .busy else
      if identity < s.localBank.selected.floor then
        ⟨s, .expired s.localBank.selected.floor none, .internal, [Event.check]⟩
      else
        let sent := match businessPacket s.localBank.selected identity operation.code with
          | none => reject s .invalid
          | some packet => pushRequest cfg s packet
        {sent with events := [Event.check, Event.scan (outcomeProbes identity s.localBank.selected.outcomes)] ++ sent.events}
    | .relinquishBefore target => startRetirement s target
    | .retryRetirement =>
      if !controllerIdle s || s.localDown then reject s .busy else
      match s.localBank.selected.pending with
      | none => reject s .unknown
      | some target => pushRequest cfg s (.retire target)
    | .resumeDeletion =>
      if !controllerIdle s || s.peerDown then reject s .busy else
      let old := s.peer.selected
      match old.pending with
      | none => reject s .unknown
      | some target =>
        let begun := beginPeer s {old with pending := none, entries := old.entries.filter (fun e => target ≤ e.1)} (.deletion target)
        {begun with events := [.scan old.entries.length,.copy (old.entries.filter (fun e => target ≤ e.1)).length] ++ begun.events}
    | .transferRequest =>
      if s.peerIn.length ≥ cfg.queueCapacity then reject s .full [.scan s.peerIn.length,.check,.queueRefused] else
      match s.localOut with
      | [] => reject s .unknown [.scan s.peerIn.length,.check]
      | packet :: rest =>
        {system := {s with localOut := rest, peerIn := s.peerIn ++ [packet]},
         events := [.scan s.peerIn.length,.check,.copy (s.peerIn.length + 1),.queueCopy]}
    | .transferReply =>
      if s.localIn.length ≥ cfg.queueCapacity then reject s .full [.scan s.localIn.length,.check,.queueRefused] else
      match s.peerOut with
      | [] => reject s .unknown [.scan s.localIn.length,.check]
      | packet :: rest =>
        {system := {s with peerOut := rest, localIn := s.localIn ++ [packet]},
         events := [.scan s.localIn.length,.check,.copy (s.localIn.length + 1),.queueCopy]}
    | .duplicate q i => duplicateQueue cfg s q i
    | .drop q =>
      {system := match q with
        | .localOut => {s with localOut := s.localOut.tail}
        | .peerIn => {s with peerIn := s.peerIn.tail}
        | .peerOut => {s with peerOut := s.peerOut.tail}
        | .localIn => {s with localIn := s.localIn.tail}, events := [.queueDrop]}
    | .deliverRequest => requestStep cfg s
    | .deliverReply => replyStep cfg s
    | .progress => progress cfg s
    | .crashLocal =>
      {system := {s with localBank := s.localBank.crash, localCause := none, localDown := true, active := none, prepared := none, former := none, retirementScan := none}, events := [.crash]}
    | .crashPeer =>
      {system := {s with peer := s.peer.crash, peerCause := none, peerDown := true}, events := [.crash]}
    | .recoverLocal =>
      if s.localDown then
        {system := {s with localDown := false, active := some (reconstruct s.localBank.selected.frame)}, events := [.check, .reconstruct]}
      else reject s .invalid
    | .recoverPeer =>
      if s.peerDown then {system := {s with peerDown := false}, events := [.check]}
      else reject s .invalid
    | .cleanup => {system := {s with former := none}, events := [.cleanup]}
    | .inspect =>
      if s.localDown || !controllerIdle s then reject s .busy else
      {system := s, observation := .current s.localBank.selected.frame s.localBank.selected.floor
        s.localBank.selected.pending, events := [.check]}
    | .query identity =>
      if s.localDown || !controllerIdle s then reject s .busy else
      {system := s, observation := .query (query s.localBank.selected identity), events := [.check, .scan (if identity < s.localBank.selected.floor then 0 else
          outcomeProbes identity s.localBank.selected.outcomes)]}
    | .malformed => reject s .invalid
  {result with events := commandControllerWork s command ++ result.events}

structure Execution where
  system : System
  labels : List SourceLabel := []
  observations : List Observation := []
  events : List Event := []

def execute (cfg : Config) : System → List Command → Execution
  | s, [] => {system := s}
  | s, c :: cs =>
    let first := step cfg s c
    let rest := execute cfg first.system cs
    {system := rest.system, labels := first.label :: rest.labels, observations := first.observation :: rest.observations, events := first.events ++ rest.events}

theorem execute_append (cfg : Config) (s : System) (xs ys : List Command) :
    execute cfg s (xs ++ ys) =
      let first := execute cfg s xs
      let rest := execute cfg first.system ys
      {system := rest.system, labels := first.labels ++ rest.labels, observations := first.observations ++ rest.observations, events := first.events ++ rest.events} := by
  induction xs generalizing s with
  | nil => rfl
  | cons c cs ih => simp [execute, ih, List.append_assoc]

/-- Reachability records executable steps, never an assumed safety property. -/
inductive Reachable (cfg : Config) : System → Prop
  | initial : Reachable cfg initial
  | next {s} : Reachable cfg s → (c : Command) → Reachable cfg (step cfg s c).system

theorem execute_reachable (cfg : Config) (s : System) (cs : List Command)
    (h : Reachable cfg s) : Reachable cfg (execute cfg s cs).system := by
  induction cs generalizing s with
  | nil => exact h
  | cons c cs ih => exact ih _ (.next h c)

end FRPSpec.PendingRetention

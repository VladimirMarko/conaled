import Applications.FRP.PendingCrash.Costs
import Applications.FRP.PendingCrash.Backend

/-! Successful executions and separating failures for the frozen #540 protocol.
The network steps process actual submitted traffic; no receipt is fabricated. -/
namespace FRPSpec.PendingCrash.Examples

abbrev flush : List Command := [.storage .prepare, .storage .write, .storage .persist,
  .storage .publish, .storage .acknowledge]

def change (command : FrameCommand) : List Command := .local command :: flush

def exchange (command : Send) (deliver : Bool := true) : List Command :=
  [.send false command] ++ (if command == .cancel then [.submit, .network false] else []) ++
    [.submit, .network deliver] ++ if deliver then [.receive, .handle] else []

def restart (frames : Nat) : List Command :=
  [.crash, .storage .startRead] ++ List.replicate (frames + 1) (.storage .read) ++ [.storage .recover]

abbrev queryRecovered : List Command := [.reconcile, .submit, .network true, .receive, .handle]

def computed (input : Bool) : List Command :=
  change (.accept input) ++ exchange .reserve ++ change .evaluate

def confirmed (input : Bool) : List Command :=
  computed input ++ exchange .publish ++ flush

def committed (input : Bool) : List Command := confirmed input ++ change .tickCommit

def retire : List Command := change .close ++ [.drain] ++ change .release

def lostPublication : List Command := computed true ++ exchange .publish false ++
  restart 2 ++ queryRecovered ++ flush ++ change .tickCommit

def resumedDelay : List Command := lostPublication ++ retire ++ committed false

def outputs (commands : List Command) : List (Nat × Bool) := (execute (initialSystem .delay) commands).effects

/-- Lost publication acknowledgment does not change the selected false output;
restart queries identity zero, commits it once, then resumes with true. -/
example : outputs resumedDelay = [(0,false), (1,true)] := by decide

example : ((execute (initialSystem .delay) lostPublication).system.adapter.current.map Frame.logical) = some true := by decide +kernel

/-- Acknowledgment loss after root publication leaves the admission visible. -/
def lostAdmission : List Command := [.local (.accept true)] ++ flush.take 4 ++ restart 1

example : ((execute (initialSystem .delay) lostAdmission).system.adapter.current.map Frame.nextIdentity) = some 1 := by decide

example : ((execute (initialSystem .delay) lostAdmission).system.adapter.current.map identities) = some [0] := by decide

example : observedSource {} (execute (initialSystem .delay) resumedDelay) = some ⟨false,[]⟩ := by decide +kernel

def recoveredFrame (commands : List Command) : Option Frame :=
  (execute (initialSystem .delay) commands).system.adapter.current

def cutTrace (staged : List Command) (previousFrames cut : Nat) : List Command :=
  staged ++ flush.take cut ++ restart (previousFrames + if cut < 4 then 0 else 1)

/-- Every write/persist/root-publication cut is exercised for each operation.
The snapshot changes at root publication, not at cell write or persistence. -/
example : (List.range 5).map (fun cut =>
    (recoveredFrame (cutTrace [.local (.accept true)] 0 cut)).map Frame.nextIdentity) =
    [some 0,some 0,some 0,some 0,some 1] := by decide +kernel

def headPhase (frame : Frame) : Option PendingMigration.Phase := frame.head.map (fun p => p.2.phase)

example : (List.range 5).map (fun cut =>
    (recoveredFrame (cutTrace (computed true ++ exchange .publish) 2 cut)).bind headPhase) =
    [some .computed,some .computed,some .computed,some .computed,some .confirmed] := by decide +kernel

example : (List.range 5).map (fun cut =>
    (recoveredFrame (cutTrace (confirmed true ++ [.local .tickCommit]) 3 cut)).map Frame.logical) =
    [some false,some false,some false,some false,some true] := by decide +kernel

def stagedMigration : List Command := computed true ++ [.prepareMigration .redundant, .commitMigration]

example : (List.range 5).map (fun cut =>
    (recoveredFrame (cutTrace stagedMigration 2 cut)).map Frame.kind) =
    [some .delay,some .delay,some .delay,some .delay,some .redundant] := by decide +kernel

/-- Every migration crash cut retains the chosen pending identity, input and
output; only the published backend kind is allowed to change. -/
example : (List.range 5).map (fun cut =>
    (recoveredFrame (cutTrace stagedMigration 2 cut)).bind (fun frame =>
      frame.head.map (fun pair => (pair.2.identity, pair.2.input, pair.2.output)))) =
    List.replicate 5 (some (0,true,some false)) := by decide +kernel

/-- Restart during the journal scan restarts the scan from the durable root. -/
example : (recoveredFrame (computed true ++ [.crash,.storage .startRead,.storage .read] ++ restart 2)).bind headPhase =
    some .computed := by decide +kernel

/-- Failed conversion retains the old owner and every pending field. -/
example : recoveredFrame (computed true ++ [.prepareMigration .redundant 256 false true]) =
    recoveredFrame (computed true) := by decide +kernel

example : (execute (initialSystem .delay) (stagedMigration ++ flush.take 4)).system.adapter.retired.length = 1 := by decide +kernel

example : (execute (initialSystem .delay) (stagedMigration ++ flush.take 4 ++ [.storage .acknowledge])).observations.getLast?.map LogEntry.status =
    some .busy := by decide +kernel

/-- Prevented publication and publication followed by too-late cancellation
have different terminal evidence and different business traces. -/
def preventedFirst : List Command := computed true ++ exchange .cancel ++ flush ++ exchange .publish

example : outputs preventedFirst = [] := by decide +kernel
example : (recoveredFrame preventedFirst).bind headPhase = some .cancelled := by decide +kernel

def publishedFirst : List Command := computed true ++ exchange .publish false ++ exchange .cancel ++ flush

example : outputs publishedFirst = [(0,false)] := by decide +kernel
example : (recoveredFrame publishedFirst).bind headPhase = some .confirmed := by decide +kernel

/-- Peer cancellation survives a crash before the local cancellation frame. -/
def lostCancellation : List Command := computed true ++ exchange .cancel false ++
  restart 2 ++ queryRecovered ++ flush

example : (recoveredFrame lostCancellation).bind headPhase = some .cancelled := by decide +kernel
example : observedSource {} (execute (initialSystem .delay) lostCancellation) = some ⟨false,[]⟩ := by decide +kernel

/-- Repeated evaluation and commit calls after commit do not change state,
selected output or the one peer effect, including after reconstruction. -/
def repeated : List Command := committed true ++ [.local .evaluate,.local .tickCommit] ++
  restart 4 ++ queryRecovered ++ [.local .evaluate,.local .tickCommit]

example : outputs repeated = [(0,false)] := by decide +kernel
example : (recoveredFrame repeated).map Frame.logical = some true := by decide +kernel
example : (recoveredFrame repeated).bind headPhase = some .committed := by decide +kernel

/-- A second admission that has not reached publication is absent after crash;
the existing computed request keeps its identity, order and selected output. -/
def interruptedSecond : List Command := computed true ++ [.local (.accept false)] ++ flush.take 3 ++ restart 2

example : recoveredFrame interruptedSecond = recoveredFrame (computed true) := by decide +kernel

/-- A weaker peer separates effect execution from receipt persistence. A crash
in that gap loses the receipt, and the same retry executes a second effect. -/
structure WeakPeer where
  effects : Nat := 0
  receipt : Bool := false
  volatileReceipt : Bool := false
  deriving DecidableEq, Repr

def weakPublish (p : WeakPeer) : WeakPeer :=
  if p.receipt then p else {p with effects := p.effects + 1, volatileReceipt := true}

def weakCrash (p : WeakPeer) : WeakPeer := {p with volatileReceipt := false}

example : (weakPublish (weakCrash (weakPublish {}))).effects = 2 := by decide

/-- A duplicated old publication remains in external traffic while the first
slot is retired and reused for a fresh identity. -/
def heldPublication : List Command := computed true ++
  [.send false .publish,.submit,.network true,.duplicateInbound,.receive,.handle] ++ flush ++ change .tickCommit

def reusedWithStale : List Command := heldPublication ++ retire ++ change (.accept false) ++
  [.send false .reserve,.submit,.network true,.rotateInbound,.receive,.handle] ++
  change .evaluate ++ [.receive,.handle]

example : (recoveredFrame reusedWithStale).map identities = some [1] := by decide +kernel
example : (recoveredFrame reusedWithStale).bind headPhase = some .computed := by decide +kernel
example : (recoveredFrame reusedWithStale).bind (fun f => f.head.bind (fun p => p.2.output)) = some true := by decide +kernel
example : outputs reusedWithStale = [(0,false)] := by decide +kernel

/-- A retained reservation receipt for the current identity cannot regress a
later confirmed phase or replace its selected false output. -/
def staleReservation : List Command := change (.accept true) ++
  [.send false .reserve,.submit,.network true,.duplicateInbound,.receive,.handle] ++
  change .evaluate ++ [.send false .publish,.submit,.network true,.rotateInbound,.receive,.handle] ++
  flush ++ [.receive,.handle]

example : (recoveredFrame staleReservation).bind headPhase = some .confirmed := by decide +kernel
example : outputs staleReservation = [(0,false)] := by decide +kernel

example : (recoveredFrame (heldPublication ++ [.receive,.handle,.local .evaluate,.local .tickCommit])).bind headPhase =
    some .committed := by decide +kernel
example : (execute (initialSystem .delay) repeated).system.adapter.journal.machine.cache.map List.length =
    some 4 := by decide +kernel

/-- Overlap is visible between root publication and cleanup. A failed
validation executes conversion/allocation/release work but keeps the old frame. -/
example : (execute (initialSystem .delay) (stagedMigration ++ flush.take 4)).system.adapter.active.map Migration.Backend.kind =
    some .redundant := by decide +kernel

example : (execute (initialSystem .delay) (computed true ++ [.prepareMigration .redundant 512 true false])).observations.getLast?.map LogEntry.status =
    some .validationFailure := by decide +kernel

example : (execute (initialSystem .delay) (computed true ++ [.prepareMigration .redundant 512 true false])).cost.allocated >
    (execute (initialSystem .delay) (computed true)).cost.allocated := by decide +kernel

example : (execute (initialSystem .delay) (computed true ++ [.prepareMigration .redundant 512 true false])).cost.released >
    (execute (initialSystem .delay) (computed true)).cost.released := by decide +kernel

example : (storageSize (execute (initialSystem .delay) (stagedMigration ++ flush.take 4)).system).formerOwners > 0 := by decide +kernel

example : (execute (initialSystem .delay) lostPublication).cost.persisted = 4 := by decide +kernel
example : (execute (initialSystem .delay) lostPublication).cost.rootPublications = 4 := by decide +kernel
example : (execute (initialSystem .delay) lostPublication).cost.reconstructed = 3 := by decide +kernel

/-- Storage grows across completed requests even after the two live slots are
released. The persistent peer table and immutable journal are not bounded by 2. -/
example : (execute (initialSystem .delay) resumedDelay).system.peer.length = 2 := by decide +kernel
example : (execute (initialSystem .delay) resumedDelay).system.adapter.journal.cells.length >
    (execute (initialSystem .delay) lostPublication).system.adapter.journal.cells.length := by decide +kernel

/-- The lost-reply/restart scenario and every continuation use the universal
runtime refinement, independently of the closed executable checker examples. -/
example (continuation : List Command) :
    ∃ final, DelayRun {} (execute (initialSystem .delay) (resumedDelay ++ continuation)).observations final :=
  execute_source_refinement .delay _

/-- Stale external replies remain covered after slot reuse, for either backend
and arbitrary subsequent crash/recovery schedules. -/
example (kind : Migration.Kind) (continuation : List Command) :
    ∃ final, DelayRun {} (execute (initialSystem kind) (reusedWithStale ++ continuation)).observations final :=
  execute_source_refinement kind _

/-- Candidate construction is still charged when native validation fails. -/
example : (execute (initialSystem .delay)
    (computed true ++ [.prepareMigration .redundant 512 true false])).cost.converted > 0 := by decide +kernel

/-- Allocation failure precedes candidate materialization. -/
example : (execute (initialSystem .delay)
    (computed true ++ [.prepareMigration .redundant 512 false true])).cost.converted = 0 := by decide +kernel

/-- Persistence without the required buffered write records a failed attempt. -/
example : (execute (initialSystem .delay)
    [.local (.accept true), .storage .prepare, .storage .persist]).cost.attempted > 2 := by decide

example : checkMessageIdentity 3 [.request 3 .query, .request 7 .query] =
    (true,[.messageCheck]) := by decide

example : checkMessageIdentity 5 [.request 3 .query, .request 7 .query] =
    (false,[.messageCheck,.messageCheck]) := by decide

/-- Tick publication materializes the selected replacement before releasing
its previous native owner. Journal history release remains a separate event. -/
example :
    let staged := execute (initialSystem .delay) (confirmed true ++ [.local .tickCommit] ++ flush.take 3)
    let work := (step staged.system (.storage .publish)).work
    Work.allocate 1 ∈ work ∧ Work.release 1 ∈ work := by decide +kernel


/-- Every recovered or committed current frame has an actual native owner with
the same selected kind and continuation, under arbitrary future commands. -/
example (kind : Migration.Kind) (commands : List Command) (frame : Frame)
    (current : (execute (initialSystem kind) commands).system.adapter.current = some frame) :
    ∃ backend, (execute (initialSystem kind) commands).system.adapter.active = some backend ∧
      backend.kind = frame.kind ∧ backend.logical = frame.logical :=
  (initial_execute_backend kind commands).active_exists _ frame current

/-- Preparation retains the exact old owner even when allocation or validation
fails; this statement also retains every pending protocol field and message. -/
example (s : System) (kind : Migration.Kind) (budget : Nat) (allocationOK validationOK : Bool) :
    (prepareMigration s kind budget allocationOK validationOK).system.adapter.active = s.adapter.active :=
  (prepareMigration_retained s kind budget allocationOK validationOK).2.1

end FRPSpec.PendingCrash.Examples

import Applications.FRP.PendingCrash.Source

/-! Source-event accounting and a flattened storage encoding. These quantities
are not elapsed time, physical allocations, filesystem calls or network cost.
Natural-number names have explicit growing binary encodings; no fixed lifetime
memory bound follows from the two slots and four local messages. -/
namespace FRPSpec.PendingCrash

/-- One bit for zero; names never have a zero-sized encoding. -/
def nameBits (n : Nat) : Nat := n.log2 + 1

def receiptBits (r : Receipt) : Nat := nameBits r.identity +
  match r.answer with
  | .absent | .conflict => 3
  | .reserved _ | .prevented _ => 4
  | .published _ _ | .tooLate _ _ => 5

def requestBits (r : Request) : Nat :=
  nameBits r.identity + 1 + 2 + 3 + 1 + (r.receipt.map receiptBits).getD 0 + 1

def frameBits (f : Frame) : Nat :=
  1 + 1 + nameBits f.nextIdentity + f.order.length + 2 +
    ((f.requests.get false).map requestBits).getD 0 +
    ((f.requests.get true).map requestBits).getD 0

def recordBits (r : Durability.Record Frame) : Nat :=
  nameBits r.session + nameBits r.id + frameBits r.payload

def cellBits : Durability.Cell Frame → Nat
  | .node previous record => 2 + 1 + (previous.map nameBits).getD 0 + recordBits record
  | .flat record => 2 + recordBits record
  | .index addresses => 2 + (addresses.map nameBits).sum

def commandBits : PeerCommand → Nat
  | .query => 2
  | .reserve _ | .cancel _ => 3
  | .publish _ _ => 4

def messageBits : Message → Nat
  | .request identity command => 1 + nameBits identity + commandBits command
  | .reply receipt => 1 + receiptBits receipt

def peerEntryBits (entry : Nat × PendingMigration.Ledger) : Nat :=
  nameBits entry.1 + match entry.2 with
  | .reserved _ | .cancelled _ => 3
  | .published _ _ => 4

/-- Every separately owned stable/volatile copy is included. Shared payloads
are charged again in this flattened encoding, so this is not a claim about
Lean's allocator or physical pointer sharing. Unreachable durable cells remain. -/
structure StorageSize where
  journal : Nat
  peer : Nat
  cache : Nat
  pendingBefore : Nat
  pendingAfter : Nat
  buffered : Nat
  reconstruction : Nat
  currentFrame : Nat
  active : Nat
  target : Nat
  formerOwners : Nat
  localMessages : Nat
  externalMessages : Nat
  controls : Nat
  deriving DecidableEq, Repr

def StorageSize.total (s : StorageSize) : Nat :=
  s.journal + s.peer + s.cache + s.pendingBefore + s.pendingAfter + s.buffered +
    s.reconstruction + s.currentFrame + s.active + s.target + s.formerOwners +
    s.localMessages + s.externalMessages + s.controls

def storageSize (s : System) : StorageSize :=
  let j := s.adapter.journal
  let records := fun h : List (Durability.Record Frame) => (h.map recordBits).sum
  {journal := (j.cells.map (fun p => nameBits p.1 + cellBits p.2)).sum,
   peer := (s.peer.map peerEntryBits).sum,
   cache := (j.machine.cache.map records).getD 0,
   pendingBefore := (j.machine.pending.map (fun p => records p.before)).getD 0,
   pendingAfter := (j.machine.pending.map (fun p => records p.after)).getD 0,
   buffered := (j.machine.buffered (j.nextAddress - 1)).map cellBits |>.getD 0,
   reconstruction := match j.machine.cursor with
     | none => 0
     | some (.prefixCells todo seen tail) => (todo.map nameBits).sum + records seen + (tail.map nameBits).getD 0
     | some (.tailCells tip pre suffix) => (tip.map nameBits).getD 0 + records pre + records suffix
     | some (.done history) => records history,
   currentFrame := (s.adapter.current.map frameBits).getD 0,
   active := (s.adapter.active.map Migration.Backend.cells).getD 0,
   target := (s.adapter.prepared.map Migration.Backend.cells).getD 0,
   formerOwners := (s.adapter.retired.map Migration.Backend.cells).sum,
   localMessages := (s.adapter.queue.messages.map messageBits).sum,
   externalMessages := (s.outbound.map (fun p => nameBits p.1 + commandBits p.2)).sum +
     (s.inbound.map receiptBits).sum,
   controls := 16 + nameBits j.nextAddress +
     (j.machine.root.tail.map nameBits).getD 0 + (j.machine.root.checkpoint.map nameBits).getD 0 +
     (j.machine.active.map recordBits).getD 0 + (s.adapter.reconcileOrder.map nameBits).sum}

/-- Categories count the actual emitted source events. Copy/allocation/release
arguments are modeled cells; identity-sensitive scans additionally expose the
binary width of each name they inspect. -/
structure WorkCost where
  checks : Nat := 0
  nameBitsInspected : Nat := 0
  allocated : Nat := 0
  copied : Nat := 0
  released : Nat := 0
  persisted : Nat := 0
  rootPublications : Nat := 0
  reconstructed : Nat := 0
  converted : Nat := 0
  attempted : Nat := 0
  deriving DecidableEq, Repr

def charge (cost : WorkCost) : Work → WorkCost
  | .peerProbe n | .recordCheck n | .cellProbe n =>
      {cost with checks := cost.checks + 1, nameBitsInspected := cost.nameBitsInspected + nameBits n}
  | .peerWrite n | .cellWrite n =>
      {cost with copied := cost.copied + 1, nameBitsInspected := cost.nameBitsInspected + nameBits n}
  | .cellPersist n => {cost with persisted := cost.persisted + 1, nameBitsInspected := cost.nameBitsInspected + nameBits n}
  | .rootPublish => {cost with rootPublications := cost.rootPublications + 1}
  | .validateFrame | .messageCheck => {cost with checks := cost.checks + 1}
  | .reconstruct => {cost with reconstructed := cost.reconstructed + 1}
  | .attempt n => {cost with attempted := cost.attempted + 1 + n}
  | .allocate n => {cost with allocated := cost.allocated + n}
  | .copy n => {cost with copied := cost.copied + n}
  | .release n => {cost with released := cost.released + n}
  | .convert n => {cost with converted := cost.converted + n}

def Execution.work (run : Execution) : List Work := run.observations.flatMap LogEntry.work

def Execution.cost (run : Execution) : WorkCost := run.work.foldl charge {}

/-- Peak flattened retained state includes both migration owners. Transient
within-step copies are separately visible in allocation/release event order. -/
def Execution.retainedPeak (initial : System) (run : Execution) : Nat :=
  run.observations.foldl (fun peak entry => max peak (storageSize entry.system).total)
    (storageSize initial).total

/-- Allocation-event occupancy is measured in modeled cells, separately from
flattened retained bits. Starting occupancy is explicit; releases use saturating
subtraction and every allocation updates the peak before later releases. -/
structure AllocationState where
  live : Nat
  peak : Nat
  deriving DecidableEq, Repr

def allocationStep (state : AllocationState) : Work → AllocationState
  | .allocate n => ⟨state.live + n, max state.peak (state.live + n)⟩
  | .release n => {state with live := state.live - n}
  | _ => state

def Execution.allocationOccupancy (initialCells : Nat) (run : Execution) : AllocationState :=
  run.work.foldl allocationStep ⟨initialCells,initialCells⟩

/-- Even an allocation followed immediately by release remains visible at the
peak. This is the event model, not a claim about a physical allocator. -/
example : ([Work.allocate 3, .release 3].foldl allocationStep ⟨2,2⟩) = ⟨2,5⟩ := by decide

example : nameBits 0 = 1 ∧ nameBits 255 = 8 ∧ nameBits 256 = 9 := by decide

end FRPSpec.PendingCrash

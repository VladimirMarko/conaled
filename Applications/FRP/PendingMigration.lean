import Applications.FRP.MigrationSafety

/-! Bounded, controlled in-process publication peer and pending-work migration.
Every delayed message belongs to the adapter's queue. There is no crash recovery
or admission of arbitrary raw messages after a slot has been released. -/
set_option autoImplicit false
set_option warningAsError true
namespace FRPSpec.PendingMigration
open Migration

inductive Phase where
  | accepted | computed | confirmed | committed | cancelled
  deriving DecidableEq, Repr

structure Request where
  input : Bool
  output : Bool := false
  phase : Phase := .accepted
  routeOpen : Bool := true
  deriving DecidableEq, Repr

inductive Ledger where
  | reserved (input : Bool)
  | published (input output : Bool)
  | cancelled (input : Bool)
  deriving DecidableEq, Repr

inductive Reply where
  | reserved | published | cancelled | conflict
  deriving DecidableEq, Repr

inductive Message where
  | publish (slot input output : Bool)
  | query (slot : Bool)
  | retry (slot input output : Bool)
  | reply (slot : Bool) (answer : Reply)
  deriving DecidableEq, Repr

def Message.slot : Message → Bool
  | .publish s _ _ | .retry s _ _ | .query s | .reply s _ => s

/-- The list representation has a checked physical capacity, including replies. -/
structure Queue where
  messages : List Message
  bounded : messages.length ≤ 4

def Queue.empty : Queue := ⟨[],by decide⟩
def Queue.push (q : Queue) (m : Message) : Option Queue :=
  if h : q.messages.length < 4 then
    some ⟨q.messages ++ [m],by simp only [List.length_append, List.length_singleton]; omega⟩
  else none

def Queue.pop (q : Queue) : Option (Message × Queue) := match h : q.messages with
  | [] => none
  | m :: ms => some (m,⟨ms,by have := q.bounded; rw [h] at this; simp only [List.length_cons] at this; omega⟩)

def Queue.references (q : Queue) (slot : Bool) : Bool :=
  q.messages.any (fun m => m.slot == slot)

/-- Fixed fields avoid a lifetime identity map or hidden allocation history. -/
structure Slots (α : Type) where
  left : Option α := none
  right : Option α := none
  deriving DecidableEq, Repr

def Slots.get {α : Type} (s : Slots α) (i : Bool) : Option α := if i then s.right else s.left

def Slots.put {α : Type} (s : Slots α) (i : Bool) (x : Option α) : Slots α :=
  if i then {s with right := x} else {s with left := x}

/-- A peer operation really installs its result before returning confirmation.
Matching repeats have no effective output; conflicts never overwrite a record. -/
def publish (entry : Option Ledger) (input output : Bool) : Option Ledger × Reply × Option Bool :=
  match entry with
  | some (.reserved x) => if x == input then
      (some (.published input output),.published,some output) else (entry,.conflict,none)
  | some (.published x y) =>
      (entry,if x == input && y == output then .published else .conflict,none)
  | some (.cancelled _) => (entry,.cancelled,none)
  | none => (entry,.conflict,none)

def query (entry : Option Ledger) : Reply := match entry with
  | some (.reserved _) => .reserved
  | some (.published _ _) => .published
  | some (.cancelled _) => .cancelled
  | none => .conflict

structure Session where
  active : Backend
  requests : Slots Request := {}
  peer : Slots Ledger := {}
  /-- Admission order is at most two distinct live slot indices. -/
  order : List Bool := []
  queue : Queue := .empty
  prepared : Option (Prepared active) := none

/-- Public clients construct sessions through admission, not raw identities. -/
def initial (k : Kind := .delay) : Session := ⟨realize k false,{},{},[],.empty,none⟩

inductive Command where
  | accept (input : Bool)
  | evaluate
  | publish | retry (conflict : Bool := false) | queryPeer
  | dispatch (deliver : Bool := true)
  | tickCommit | cancelWork (second : Bool := false) | close | release
  | prepare (target : Kind) (budget : Nat := 256) (allocationOK validationOK : Bool := true)
  | ownershipCommit | cancelMigration | inspect
  deriving DecidableEq, Repr

inductive Status where
  | accepted | evaluated | enqueued | dispatched | confirmed | committed
  | prevented | tooLate | closed | released | prepared | migrated | cancelled
  | busy | full | conflict | refused | allocationFailure | validationFailure | resourceFailure | inspect
  deriving DecidableEq, Repr

/-- Executed logical transfer operations, bounded independently of service age.
The trace is transient observation data, never retained by Session. -/
inductive TransferEvent where
  | budget | attempt (cells : Nat) | allocate (cells : Nat) | copy (cells : Nat)
  | validate | release (cells : Nat) | ownershipCut
  deriving DecidableEq, Repr

structure Outcome where
  session : Session
  status : Status
  accepted : Option Bool := none
  business : Option Bool := none
  cancellation : Option Bool := none
  transfer : List TransferEvent := []

/-- 96 cells reserve command/response framing and fixed controls. -/
def stateSlots (s : Session) : Nat :=
  96 + s.active.cells + 2 * 5 + 2 * 3 + s.order.length + s.queue.messages.length * 5 +
    (s.prepared.map (fun p => p.target.cells)).getD 0

def preparationSlots (s : Session) (target : Kind) : Nat :=
  stateSlots s + (realize target s.active.logical).cells + 2

def reject (s : Session) (status : Status) : Outcome := ⟨s,status,none,none,none,[]⟩

def head (s : Session) (second : Bool := false) : Option (Bool × Request) := do
  let slot ← (if second then s.order.tail else s.order).head?
  let request ← s.requests.get slot
  pure (slot,request)

def update (s : Session) (slot : Bool) (r : Request) : Session :=
  {s with requests := s.requests.put slot (some r)}

def enqueue (s : Session) (r : Request) (m : Message) : Outcome :=
  if !r.routeOpen then reject s .refused
  else match s.queue.push m with
    | none => reject s .full
    | some q => ⟨{s with queue := q},.enqueued,none,none,none,[]⟩

/-- The peer is accessed only here or through the cancellation operation.
Dropping a response never changes the session's knowledge or continuation. -/
def dispatch (s : Session) (deliver : Bool) : Outcome :=
  match s.queue.pop with
  | none => reject s .busy
  | some (m,q) =>
    let base := {s with queue := q}
    match s.requests.get m.slot with
    | none => reject base .refused
    | some r =>
      if !r.routeOpen then reject base .dispatched
      else match m with
      | .reply slot answer =>
        if answer == .published && r.phase == .computed then
          ⟨update base slot {r with phase := .confirmed},.confirmed,none,none,none,[]⟩
        else reject base (if answer == .conflict then .conflict else .dispatched)
      | .publish slot x y | .retry slot x y =>
        let result := publish (s.peer.get slot) x y
        let next := {base with peer := s.peer.put slot result.1}
        let queue := if deliver then (q.push (.reply slot result.2.1)).getD q else q
        ⟨{next with queue := queue},
          if result.2.1 == .conflict then .conflict else .dispatched,none,result.2.2,none,[]⟩
      | .query slot =>
        let queue := if deliver then (q.push (.reply slot (query (s.peer.get slot)))).getD q else q
        ⟨{base with queue := queue},.dispatched,none,none,none,[]⟩

/-- Migration commands are the only commands admitted while a copy is prepared.
The stable peer and complete queue remain under the adapter's ownership. -/
def step (s : Session) (c : Command) : Outcome :=
  match c with
  | .inspect => reject s .inspect
  | .cancelMigration =>
    ⟨{s with prepared := none},.cancelled,none,none,none,
      (s.prepared.map (fun p => [TransferEvent.release p.target.cells])).getD []⟩
  | .ownershipCommit => match s.prepared with
    | none => reject s .busy
    | some p => ⟨⟨p.target,s.requests,s.peer,s.order,s.queue,none⟩,.migrated,none,none,none,
        [.ownershipCut,.release s.active.cells]⟩
  | .prepare target budget allocationOK validationOK =>
    if s.prepared.isSome then reject s .busy
    else if preparationSlots s target > budget then
      ⟨s,.resourceFailure,none,none,none,[.budget]⟩
    else if !allocationOK then
      ⟨s,.allocationFailure,none,none,none,
        [.budget,.attempt ((realize target s.active.logical).cells + 2)]⟩
    else
      let candidate := realize target s.active.logical
      -- Candidate validation forces construction before the modeled injected
      -- validation failure; that branch releases candidate and scratch.
      let traceStart := [TransferEvent.budget,.attempt (candidate.cells + 2),
        .allocate (candidate.cells + 2),.copy candidate.cells,.validate]
      if !candidate.validate || !validationOK then
        ⟨s,.validationFailure,none,none,none,traceStart ++ [.release (candidate.cells + 2)]⟩
      else ⟨{s with prepared := some ⟨candidate,realize_logical _ _⟩},
        .prepared,none,none,none,traceStart ++ [.release 2]⟩
  | _ =>
    if s.prepared.isSome then reject s .busy
    else match c with
    | .accept x =>
      if s.order.length ≥ 2 then reject s .full else
      let free := if (s.requests.get false).isNone then some false
        else if (s.requests.get true).isNone then some true else none
      match free with
      | none => reject s .full
      | some slot =>
        ⟨{s with
          requests := s.requests.put slot (some ⟨x,false,.accepted,true⟩)
          peer := s.peer.put slot (some (.reserved x))
          order := s.order ++ [slot]},.accepted,some x,none,none,[]⟩
    | .dispatch deliver => dispatch s deliver
    | _ => match head s (match c with | .cancelWork second => second | _ => false) with
      | none => reject s .busy
      | some (slot,r) => match c with
        | .evaluate => if r.phase == .accepted then
            let result := Migration.evaluate s.active r.input
            ⟨update s slot {r with output := result.output,phase := .computed},.evaluated,none,none,none,[]⟩
          else reject s .busy
        | .publish => if r.phase == .computed then enqueue s r (.publish slot r.input r.output)
          else reject s .busy
        | .retry conflict => if r.phase == .computed || r.phase == .confirmed || r.phase == .committed then
            enqueue s r (.retry slot (if conflict then !r.input else r.input) r.output)
          else reject s .busy
        | .queryPeer => enqueue s r (.query slot)
        | .tickCommit => if r.phase == .confirmed then
            ⟨{(update s slot {r with phase := .committed}) with
              active := realize s.active.kind r.input,prepared := none},.committed,none,none,none,[]⟩
          else reject s .busy
        | .cancelWork _ => match s.peer.get slot with
          | some (.published _ _) => ⟨s,.tooLate,none,none,some false,[]⟩
          | some (.reserved x) =>
            ⟨{(update s slot {r with phase := .cancelled}) with
              peer := s.peer.put slot (some (.cancelled x))},.prevented,none,none,some true,[]⟩
          | _ => reject s .busy
        | .close => if r.phase == .committed || r.phase == .cancelled then
            ⟨update s slot {r with routeOpen := false},.closed,none,none,none,[]⟩
          else reject s .refused
        | .release => if !r.routeOpen && !s.queue.references slot &&
              (r.phase == .committed || r.phase == .cancelled) then
            ⟨{s with
              requests := s.requests.put slot none
              peer := s.peer.put slot none
              order := s.order.tail},.released,none,none,none,[]⟩
          else reject s .refused
        | _ => reject s .busy

/-- Ghost trace helper; the executable runner retains only Session. -/
def execute : Session → List Command → Session × List Bool
  | s,[] => (s,[])
  | s,c::cs => let o := step s c; let rest := execute o.session cs
              (rest.1,o.business.toList ++ rest.2)

end FRPSpec.PendingMigration

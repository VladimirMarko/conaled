import Applications.FRP.RegionalPendingPlan

/-! Executable changed-cut migration with a stable publication peer and owned
internal deliveries. No user command inserts a raw callback or raw slot token. -/
namespace FRPSpec.Regional.Pending
open Applications.Circuits

structure Wire where
  logical : Bool
  requests : PendingMigration.Slots PendingMigration.Request
  peer : PendingMigration.Slots PendingMigration.Ledger
  order : List Bool
  external : List PendingMigration.Message
  residuals : PendingMigration.Slots Residual
  deliveries : Deliveries
  deriving DecidableEq

def wire (s : Active) : Wire :=
  ⟨s.protocol.active.logical,s.protocol.requests,s.protocol.peer,s.protocol.order,
    s.protocol.queue.messages,s.residuals,s.deliveries⟩

@[simp] theorem convert_wire (s : Active) (cut : Cut) (kind : Migration.Kind) :
    wire (convert s cut kind) = wire s := by
  simp [wire,convert,Active.residuals,PendingMigration.transfer]

/-- Fixed tagged residual stores occupy 22 cells; checked caches add two bits. -/
def retainedCells : Cut → Nat | .checked => 24 | _ => 22

def internalArena : Cut → Nat
  | .fused => jointBody.arena
  | .split => max Indefinite.delay.body.arena (max Circuit.not.arena Circuit.xor.arena)
  | .checked => max Indefinite.delay.body.arena (max Circuit.not.arena Circuit.xor.arena) + 4

/-- Protocol's 192-cell theorem covers its external transitions. Sixteen wrapper
controls, four delivery cells, old/new residual-store overlap, producer/consumer
arenas and eight result/adapter cells are added. -/
def serviceCapacity (cut : Cut) : Nat := 192 + 16 + 4 + 2 * retainedCells cut + max (Rich.arena Rich.code) (internalArena cut) + 8

def transferBase (s : Active) : Nat := PendingMigration.stateSlots s.protocol + 16 + 4 + retainedCells s.cut
/-- Copy the decoded residual store and logical state into a 23-cell scratch. -/
def targetCells (cut : Cut) (kind : Migration.Kind) : Nat := retainedCells cut + (Migration.realize kind false).cells

def transitionPeak (s : Active) (cut : Cut) (kind : Migration.Kind) : Nat :=
  transferBase s + 23 + targetCells cut kind

def requiredCapacity (s : Active) (cut : Cut) (kind : Migration.Kind) : Nat :=
  max (serviceCapacity s.cut) (max (serviceCapacity cut) (transitionPeak s cut kind))

structure Requirements where
  capacity : Nat := 1024
  protocol : Nat := 2
  ordered : Bool := true
  finiteWaits : Bool := true
  deriving DecidableEq, Repr

def supported (r : Requirements) : Prop :=
  r.protocol = 2 ∧ r.ordered = true ∧ r.finiteWaits = true
instance (r : Requirements) : Decidable (supported r) := inferInstanceAs (Decidable (_ ∧ _))

/-- Evidence is indexed by the actual target code, representation and premises. -/
structure Certificate (r : Requirements) (cut : Cut) (kind : Migration.Kind) : Prop where
  assumptions : supported r
  service : serviceCapacity cut ≤ r.capacity
  semantics : ∀ input state, wholeResult cut input state = oracle input state
  representation : ∀ state, (Migration.realize kind state).logical = state

structure Prepared (old : Active) where
  target : Active
  continuation : wire target = wire old
  evidence : ∃ r : Requirements, Certificate r target.cut target.protocol.active.kind ∧
    requiredCapacity old target.cut target.protocol.active.kind ≤ r.capacity

structure Session where
  active : Active
  prepared : Option (Prepared active) := none
  permitted : Bool := true

def initial (cut : Cut := .split) (kind : Migration.Kind := .delay) : Session := ⟨initialActive cut kind,none,true⟩

inductive Status where
  | protocol (status : PendingMigration.Status)
  | produced | deliveredD | deliveredN | joined | completed | drained
  | prepared | migrated | cancelled | frozen | throttled | stale | capacity
  | allocation | validation | unsupported | busy
  deriving DecidableEq, Repr

structure Outcome where
  session : Session
  status : Status
  accepted : Option Bool := none
  business : Option Bool := none
  cancellation : Option Bool := none
  events : List WorkEvent := []

def reject (s : Session) (status : Status) : Outcome := ⟨s,status,none,none,none,[.inspect]⟩

def updateResidual (s : Active) (slot : Bool) (r : Residual) : Active :=
  s.withResiduals (s.residuals.put slot (some r))

def headResidual (s : Active) : Option (Bool × PendingMigration.Request × Residual) := do
  let (slot,r) ← PendingMigration.head s.protocol
  let localState ← s.residuals.get slot
  pure (slot,r,localState)

def producer (s : Session) : Outcome :=
  if s.prepared.isSome then reject s .frozen else
  match headResidual s.active with
  | none => reject s .busy
  | some (slot,r,localState) =>
    if r.phase != .accepted || localState.cached.isSome || localState.cancelled then reject s .busy else
    let d := produce r.input
    let next := updateResidual s.active slot {localState with cached := some d,oldState := s.active.protocol.active.logical}
    ⟨⟨{next with deliveries := ⟨some slot,some slot⟩},none,s.permitted⟩,.produced,none,none,none,[.producer,.copy (retainedCells s.active.cut)]⟩

def deliver (s : Session) (toD : Bool) : Outcome :=
  if s.prepared.isSome then reject s .frozen else
  let cell := if toD then s.active.deliveries.d else s.active.deliveries.n
  match cell with
  | none => reject s .busy
  | some slot =>
    let drained := if toD then {s.active.deliveries with d := none} else {s.active.deliveries with n := none}
    let base := {s.active with deliveries := drained}
    match s.active.residuals.get slot with
    | none => ⟨⟨base,none,s.permitted⟩,.drained,none,none,none,[.retireInternal]⟩
    | some localState =>
      if localState.cancelled then
        ⟨⟨base,none,s.permitted⟩,.drained,none,none,none,[.retireInternal]⟩
      else match localState.cached with
      | none => reject s .busy
      | some d =>
        if toD then
          let result := Indefinite.delay.machine.step (d,localState.oldState)
          let next := updateResidual base slot {localState with dResult := some result.1,candidate := some result.2}
          ⟨⟨next,none,s.permitted⟩,.deliveredD,none,none,none,[.deliverD,.copy (retainedCells s.active.cut)]⟩
        else
          let result := Circuit.not.execute d
          let next := updateResidual base slot {localState with nResult := some result}
          ⟨⟨next,none,s.permitted⟩,.deliveredN,none,none,none,[.deliverN,.copy (retainedCells s.active.cut)]⟩

def join (s : Session) : Outcome :=
  if s.prepared.isSome then reject s .frozen else
  match headResidual s.active with
  | none => reject s .busy
  | some (slot,r,localState) =>
    if r.phase != .accepted || localState.cancelled || s.active.deliveries.references slot then reject s .busy else
    match localState.dResult,localState.nResult,localState.candidate with
    | some d,some n,some _ =>
      let result := Circuit.xor.execute (d,n)
      let p := PendingMigration.update s.active.protocol slot {r with output := result,phase := .computed}
      ⟨⟨{s.active with protocol := p},none,s.permitted⟩,.joined,none,none,none,[.join]⟩
    | _,_,_ => reject s .busy

/-- A complete consumer executor runs only before either consumer has run. A transferred
partial phase uses deliver/join, retaining the completed consumer's result. -/
def whole (s : Session) : Outcome :=
  if s.prepared.isSome then reject s .frozen else
  match headResidual s.active with
  | none => reject s .busy
  | some (slot,r,localState) =>
    if r.phase != .accepted || localState.cancelled || localState.dResult.isSome || localState.nResult.isSome ||
      s.active.deliveries.d != some slot || s.active.deliveries.n != some slot then reject s .busy else
    match localState.cached with
    | none => reject s .busy
    | some d =>
      let result := wholeResult s.active.cut d localState.oldState
      let p := PendingMigration.update s.active.protocol slot {r with output := result.1,phase := .computed}
      let next := updateResidual {s.active with protocol := p,deliveries := {}} slot
        {localState with candidate := some result.2}
      ⟨⟨next,none,s.permitted⟩,.completed,none,none,none,[.consumers s.active.cut (match s.active.cut with | .fused => jointBody.work | _ => Indefinite.delay.body.work + Circuit.not.work + Circuit.xor.work),.copy (retainedCells s.active.cut)]⟩

def accept (s : Session) (input : Bool) : Outcome :=
  if s.prepared.isSome then reject s .frozen else
  let out := PendingMigration.step s.active.protocol (.accept input)
  let base := {s.active with protocol := out.session}
  let next := if out.status == .accepted then
      match out.session.order.getLast? with
      | none => base
      | some slot => updateResidual base slot {}
    else base
  ⟨⟨next,none,s.permitted⟩,.protocol out.status,out.accepted,out.business,out.cancellation,([.protocol (PendingMigration.commandWork s.active.protocol (.accept input)) out.transfer] ++
    if out.status == .accepted then [.copy (retainedCells s.active.cut)] else [])⟩

/-- External commands use the accepted peer implementation directly. Its
business output is already the joined payload stored in the peer ledger. -/
def external (s : Session) (c : PendingMigration.Command) : Outcome :=
  if s.prepared.isSome then reject s .frozen else
  match c with
  | .accept _ | .evaluate | .prepare _ _ _ _ | .ownershipCommit | .cancelMigration => reject s .unsupported
  | _ =>
    let selected := PendingMigration.head s.active.protocol
      (match c with | .cancelWork second => second | _ => false)
    if c == .release && (selected.map (fun p => s.active.deliveries.references p.1)).getD false then
      reject s .busy
    else
      let out := PendingMigration.step s.active.protocol c
      let base := {s.active with protocol := out.session}
      let next := match selected with
        | none => base
        | some (slot,_) =>
          if out.status == .released then base.withResiduals (base.residuals.put slot none)
          else if out.cancellation == some true then
            match base.residuals.get slot with
            | none => base
            | some localState => updateResidual base slot {localState with cancelled := true}
          else base
      ⟨⟨next,none,s.permitted || out.status == .committed⟩,.protocol out.status,
        out.accepted,out.business,out.cancellation,([.protocol (PendingMigration.commandWork s.active.protocol c) out.transfer] ++
        if out.status == .released || out.cancellation == some true then [.copy (retainedCells s.active.cut)] else [])⟩

/-- Deliberately wrong wiring is a checked negative client, not an accepted cut. -/
def swapConsumers (s : Active) : Active :=
  s.withResiduals (mapSlots (fun r => {r with dResult := r.nResult,nResult := r.dResult}) s.residuals)

def prepare (s : Session) (expected target : Cut) (kind : Migration.Kind) (r : Requirements)
    (allocationOK validationOK : Bool := true) (swapped : Bool := false) : Outcome :=
  if s.prepared.isSome then reject s .frozen else
  if !s.permitted then reject s .throttled else
  let attempted : Session := ⟨s.active,none,false⟩
  if expected != s.active.cut then reject attempted .stale else
  if assumptions : supported r then
    if capacity : requiredCapacity s.active target kind ≤ r.capacity then
      if !allocationOK then reject attempted .allocation else
      let converted := convert s.active target kind
      let candidate := if swapped then swapConsumers converted else converted
      let trace := [WorkEvent.allocate (23 + targetCells target kind),.copy 23,.copy (targetCells target kind),.validate]
      if !(decide (wire candidate = wire s.active)) || !validationOK then
        ⟨attempted,.validation,none,none,none,trace ++ [.release (23 + targetCells target kind)]⟩
      else if related : wire candidate = wire s.active then
        let targetBound : serviceCapacity target ≤ r.capacity :=
          (Nat.le_max_left _ _ |>.trans (Nat.le_max_right _ _)).trans capacity
        let cert : Certificate r target kind := ⟨assumptions,targetBound,whole_correct target,Migration.realize_logical kind⟩
        let p : Prepared s.active := ⟨candidate,related,by
          refine ⟨r,?_,?_⟩
          · cases swapped <;> cases kind <;>
              simpa [candidate,converted,convert,swapConsumers,Active.withResiduals,PendingMigration.transfer,Migration.realize,Migration.Backend.kind] using cert
          · cases swapped <;> cases kind <;>
              simpa [candidate,converted,convert,swapConsumers,Active.withResiduals,PendingMigration.transfer,Migration.realize,Migration.Backend.kind] using capacity⟩
        ⟨⟨s.active,some p,false⟩,.prepared,none,none,none,trace ++ [.release 23]⟩
      else ⟨attempted,.validation,none,none,none,trace ++ [.release (23 + targetCells target kind)]⟩
    else reject attempted .capacity
  else reject attempted .unsupported

def commit (s : Session) : Outcome := match s.prepared with
  | none => reject s .busy
  | some p => ⟨⟨p.target,none,false⟩,.migrated,none,none,none,
      [.release (targetCells s.active.cut s.active.protocol.active.kind)]⟩

def cancel (s : Session) : Outcome := match s.prepared with
  | none => reject s .busy
  | some p => ⟨⟨s.active,none,false⟩,.cancelled,none,none,none,
      [.release (targetCells p.target.cut p.target.protocol.active.kind)]⟩

inductive Command where
  | accept (input : Bool) | producer | deliverD | deliverN | join | whole
  | external (command : PendingMigration.Command)
  | prepare (expected target : Cut) (kind : Migration.Kind) (requirements : Requirements)
      (allocationOK validationOK swapped : Bool)
  | commit | cancel

def step (s : Session) : Command → Outcome
  | .accept x => accept s x
  | .producer => producer s
  | .deliverD => deliver s true
  | .deliverN => deliver s false
  | .join => join s
  | .whole => whole s
  | .external c => external s c
  | .prepare e t k r a v swapped => prepare s e t k r a v swapped
  | .commit => commit s
  | .cancel => cancel s

def execute : Session → List Command → Session × List Bool
  | s,[] => (s,[])
  | s,c::cs => let out := step s c; let rest := execute out.session cs
              (rest.1,out.business.toList ++ rest.2)

end FRPSpec.Regional.Pending

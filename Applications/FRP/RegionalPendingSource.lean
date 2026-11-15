import Applications.FRP.RegionalPending

/-! Independent joint source and concrete payload transport to the accepted
bounded delay protocol. Transport is keyed by the retained owner input, never
by an untrusted retry's claimed input. -/
namespace FRPSpec.Regional.Pending

def payload (owner value : Bool) : Bool := Bool.xor value (!owner)
@[simp] theorem payload_involutive (owner value : Bool) :
    payload owner (payload owner value) = value := by cases owner <;> cases value <;> rfl

def ledgerPayload (owner : Bool) : PendingMigration.Ledger → PendingMigration.Ledger
  | .published x y => .published x (payload owner y)
  | .reserved x => .reserved x
  | .cancelled x => .cancelled x

def messagePayload (owner : Bool) : PendingMigration.Message → PendingMigration.Message
  | .publish slot x y => .publish slot x (payload owner y)
  | .retry slot x y => .retry slot x (payload owner y)
  | .query slot => .query slot
  | .reply slot answer => .reply slot answer

/-- Simultaneously transporting retained ledger and proposed payload preserves
confirmation/conflict and transports only an actual effective publication. -/
theorem publication_transport (entry : Option PendingMigration.Ledger) (owner input output : Bool) :
    PendingMigration.publish (entry.map (ledgerPayload owner)) input (payload owner output) =
      let result := PendingMigration.publish entry input output
      (result.1.map (ledgerPayload owner),result.2.1,result.2.2.map (payload owner)) := by
  cases entry with
  | none => rfl
  | some entry =>
    cases entry with
    | reserved x => cases x <;> cases input <;> rfl
    | cancelled x => rfl
    | published x y =>
      cases owner <;> cases input <;> cases output <;> cases x <;> cases y <;> rfl

/-- In particular, flipping the retry input remains a conflict even when the
payload is transformed by the unchanged live owner's mask. -/
theorem conflicting_retry_transport (owner output : Bool) :
    (PendingMigration.publish
      (some (ledgerPayload owner (.published owner output))) (!owner)
      (payload owner output)).2 = (.conflict,none) := by
  cases owner <;> cases output <;> rfl

/-- Accepted-phase output is a dummy; evaluated output is transported using the
retained request input. Retirement removes the whole owner before reuse. -/
def requestPayload (r : PendingMigration.Request) : PendingMigration.Request :=
  {r with output := if r.phase == .accepted then false else payload r.input r.output}

def ownerInput (s : PendingMigration.Session) (slot : Bool) : Bool :=
  ((s.requests.get slot).map (·.input)).getD false

def ownLedger : PendingMigration.Ledger → PendingMigration.Ledger
  | .published x y => .published x (payload x y)
  | .reserved x => .reserved x
  | .cancelled x => .cancelled x

/-- This projection changes only payload interpretation. Admission order,
phase, identity, routes, queue positions and the authoritative backend remain. -/
def delayProjection (s : PendingMigration.Session) : PendingMigration.Session :=
  {s with
    requests := mapSlots requestPayload s.requests
    peer := mapSlots ownLedger s.peer
    queue := ⟨s.queue.messages.map (fun m => messagePayload (ownerInput s m.slot) m),
      by simpa using s.queue.bounded⟩}

@[simp] theorem get_mapSlots {α β : Type} (f : α → β)
    (s : PendingMigration.Slots α) (slot : Bool) :
    (mapSlots f s).get slot = (s.get slot).map f := by cases slot <;> rfl

@[simp] theorem projected_head (s : PendingMigration.Session) (second : Bool := false) :
    PendingMigration.head (delayProjection s) second =
      (PendingMigration.head s second).map (fun p => (p.1,requestPayload p.2)) := by
  simp only [PendingMigration.head,delayProjection,get_mapSlots]
  cases h : (if second then s.order.tail else s.order).head? with
  | none => rfl
  | some slot =>
    cases hr : s.requests.get slot <;> simp [hr]

theorem projection_source (s : PendingMigration.Session) :
    PendingMigration.source (delayProjection s) = PendingMigration.source s := by
  unfold PendingMigration.source
  congr 1
  · simp only [PendingMigration.sourceState,projected_head]
    cases hh : PendingMigration.head s with
    | none => rfl
    | some pair =>
      obtain ⟨slot,r⟩ := pair
      simp only [Option.map_some,delayProjection,get_mapSlots]
      cases hp : s.peer.get slot with
      | none => rfl
      | some ledger => cases ledger <;> rfl
  · simp only [PendingMigration.waiting,delayProjection,get_mapSlots]
    congr 1
    funext slot
    cases hp : s.peer.get slot with
    | none => rfl
    | some ledger => cases ledger <;> rfl

/-- Cached producer and completed consumers agree with the independently
specified fork/join equation. Presence remains separate from the value. -/
def ResidualCorrect (input : Bool) (r : Residual) : Prop :=
  (∀ d, r.cached = some d → d = input) ∧
  (∀ d, r.dResult = some d → d = r.oldState) ∧
  (∀ d, r.nResult = some d → d = !input) ∧
  (∀ d, r.candidate = some d → d = input)

structure Invariant (s : Active) : Prop where
  protocol : PendingMigration.Valid (delayProjection s.protocol)
  residual : ∀ slot request, s.protocol.requests.get slot = some request →
    ∃ r, s.residuals.get slot = some r ∧ ResidualCorrect request.input r
  current : ∀ slot request r, s.protocol.requests.get slot = some request →
    s.residuals.get slot = some r →
    (request.phase = .accepted ∨ request.phase = .computed ∨ request.phase = .confirmed) →
    r.cached.isSome = true → r.oldState = s.protocol.active.logical
  delivery : ∀ slot, s.deliveries.references slot = true →
    ∃ request r, s.protocol.requests.get slot = some request ∧
      s.residuals.get slot = some r ∧ r.cached.isSome = true ∧
      (request.phase = .accepted ∨ request.phase = .cancelled)
  cancellation : ∀ slot request r, s.protocol.requests.get slot = some request →
    s.residuals.get slot = some r → (r.cancelled = true ↔ request.phase = .cancelled)
  cache_head : ∀ slot r, s.residuals.get slot = some r →
    r.cached.isSome = true → s.protocol.order.head? = some slot
  completed_cache : ∀ slot r, s.residuals.get slot = some r →
    (r.dResult.isSome = true ∨ r.nResult.isSome = true ∨ r.candidate.isSome = true) →
    r.cached.isSome = true

@[simp] theorem initial_projection (kind : FRPSpec.Migration.Kind) :
    delayProjection (PendingMigration.initial kind) = PendingMigration.initial kind := by
  simp [delayProjection,PendingMigration.initial,mapSlots,PendingMigration.Queue.empty]

theorem initial_invariant (cut : Cut) (kind : FRPSpec.Migration.Kind) :
    Invariant (initialActive cut kind) := by
  constructor
  · simpa only [initialActive,initial_projection] using PendingMigration.initial_valid kind
  · intro slot request h
    cases slot <;> simp [initialActive,PendingMigration.initial,PendingMigration.Slots.get] at h
  · intro slot request r h
    cases slot <;> simp [initialActive,PendingMigration.initial,PendingMigration.Slots.get] at h
  · intro slot h
    simp [initialActive,Deliveries.references] at h
  · intro slot request r h
    cases slot <;> simp [initialActive,PendingMigration.initial,PendingMigration.Slots.get] at h
  · intro slot r h
    cases slot <;> simp [initialActive,Active.residuals,PendingMigration.Slots.get] at h
  · intro slot r h
    cases slot <;> simp [initialActive,Active.residuals,PendingMigration.Slots.get] at h


@[simp] theorem projection_transfer (s : PendingMigration.Session) (kind : FRPSpec.Migration.Kind) :
    delayProjection (PendingMigration.transfer s kind) =
      PendingMigration.transfer (delayProjection s) kind := rfl

theorem convert_invariant (s : Active) (cut : Cut) (kind : FRPSpec.Migration.Kind)
    (h : Invariant s) : Invariant (convert s cut kind) := by
  constructor
  · simpa only [convert,projection_transfer] using PendingMigration.transfer_valid _ kind h.protocol
  · simpa only [convert,Active.residuals,store_decode_encode,PendingMigration.transfer] using h.residual
  · simpa only [convert,Active.residuals,store_decode_encode,PendingMigration.transfer,FRPSpec.Migration.realize_logical] using h.current
  · simpa only [convert,Active.residuals,store_decode_encode,PendingMigration.transfer] using h.delivery
  · simpa only [convert,Active.residuals,store_decode_encode,PendingMigration.transfer] using h.cancellation
  · simpa only [convert,Active.residuals,store_decode_encode,PendingMigration.transfer] using h.cache_head
  · simpa only [convert,Active.residuals,store_decode_encode,PendingMigration.transfer] using h.completed_cache



structure Source where
  state : Bool
  waiting : List Bool
  deriving DecidableEq, Repr

def source (s : Active) : Source :=
  ⟨PendingMigration.sourceState s.protocol,PendingMigration.waiting s.protocol⟩

/-- Source state advances at effective joined publication. Confirmation and
local commit are silent, and cancellation removes an accepted occurrence. -/
inductive SourceStep : Source → Outcome → Source → Prop where
  | internal (s : Source) (o : Outcome)
      (accepted : o.accepted = none) (published : o.business = none)
      (cancelled : o.cancellation ≠ some true) : SourceStep s o s
  | accept (s : Source) (o : Outcome) (x : Bool)
      (accepted : o.accepted = some x) (published : o.business = none)
      (cancelled : o.cancellation = none) : SourceStep s o ⟨s.state,s.waiting ++ [x]⟩
  | prevent (b x : Bool) (pre post : List Bool) (o : Outcome)
      (accepted : o.accepted = none) (published : o.business = none)
      (cancelled : o.cancellation = some true) :
      SourceStep ⟨b,pre ++ x :: post⟩ o ⟨b,pre ++ post⟩
  | publish (b x : Bool) (xs : List Bool) (o : Outcome)
      (accepted : o.accepted = none) (published : o.business = some (oracle x b).1)
      (cancelled : o.cancellation = none) : SourceStep ⟨b,x::xs⟩ o ⟨x,xs⟩

end FRPSpec.Regional.Pending

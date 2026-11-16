import Applications.FRP.PendingCrash.Refinement

/-! Bounded-service payloads and checked local decisions. Result relinquishment
is a separate owner command; closing a callback never relinquishes a result. -/
namespace FRPSpec.PendingRetention
open PendingCrash PendingMigration

structure Config where
  lifetime : Nat
  outcomeCapacity : Nat
  queueCapacity : Nat
  deriving DecidableEq, Repr

structure Outcome where
  identity : Nat
  input : Bool
  answer : Option Answer := none
  released : Bool := false
  deriving DecidableEq, Repr

structure LocalSnapshot where
  frame : Frame := initialFrame
  floor : Nat := 0
  pending : Option Nat := none
  outcomes : List Outcome := []
  deriving DecidableEq, Repr

structure PeerSnapshot where
  floor : Nat := 0
  pending : Option Nat := none
  entries : Peer := []
  deriving DecidableEq, Repr

inductive RequestPacket where
  | business (identity : Nat) (command : PeerCommand)
  | retire (target : Nat)
  deriving DecidableEq, Repr

inductive ReplyPacket where
  | receipt (receipt : Receipt)
  | expired (identity floor : Nat)
  | deleted (target : Nat)
  deriving DecidableEq, Repr

inductive Refusal where
  | busy | full | exhausted | invalid | unresolved | unknown
  deriving DecidableEq, Repr

inductive Query where
  | expired (floor : Nat)
  | unknown
  | unresolved (input : Bool)
  | terminal (answer : Answer)
  deriving DecidableEq, Repr

def terminalAnswer : Answer → Bool
  | .published _ _ | .prevented _ => true
  | _ => false

def outcome (s : LocalSnapshot) (identity : Nat) : Option Outcome :=
  s.outcomes.find? (fun r => r.identity == identity)

def query (s : LocalSnapshot) (identity : Nat) : Query :=
  if identity < s.floor then .expired s.floor else
  match outcome s identity with
  | none => .unknown
  | some r => match r.answer with
    | none => .unresolved r.input
    | some a => .terminal a

/-- These checks concern finite representation, not provenance or source
semantics. In particular a locally valid frame need not be source related. -/
def LocalBound (cfg : Config) (s : LocalSnapshot) : Prop :=
  s.frame.Valid ∧ s.frame.nextIdentity ≤ cfg.lifetime ∧ s.floor ≤ cfg.lifetime ∧
  (∀ n ∈ s.pending, n ≤ cfg.lifetime) ∧ s.outcomes.length ≤ cfg.outcomeCapacity ∧
  ∀ r ∈ s.outcomes, r.identity ≤ cfg.lifetime

def PeerBound (cfg : Config) (s : PeerSnapshot) : Prop :=
  s.floor ≤ cfg.lifetime ∧ (∀ n ∈ s.pending, n ≤ cfg.lifetime) ∧
  s.entries.length ≤ cfg.outcomeCapacity ∧ ∀ r ∈ s.entries, r.1 ≤ cfg.lifetime

def ReplyBound (cfg : Config) : ReplyPacket → Prop
  | .receipt r => r.identity ≤ cfg.lifetime
  | .expired i f => i ≤ cfg.lifetime ∧ f ≤ cfg.lifetime
  | .deleted t => t ≤ cfg.lifetime

def RequestBound (cfg : Config) : RequestPacket → Prop
  | .business i _ => i ≤ cfg.lifetime
  | .retire t => t ≤ cfg.lifetime

def CommandBound (cfg : Config) : FrameCommand → Prop
  | .receive r => r.identity ≤ cfg.lifetime
  | _ => True

instance (cfg : Config) (s : LocalSnapshot) : Decidable (LocalBound cfg s) := by
  unfold LocalBound; infer_instance
instance (cfg : Config) (s : PeerSnapshot) : Decidable (PeerBound cfg s) := by
  unfold PeerBound; infer_instance
instance (cfg : Config) (r : ReplyPacket) : Decidable (ReplyBound cfg r) := by
  cases r <;> unfold ReplyBound <;> infer_instance
instance (cfg : Config) (r : RequestPacket) : Decidable (RequestBound cfg r) := by
  cases r <;> unfold RequestBound <;> infer_instance
instance (cfg : Config) (r : FrameCommand) : Decidable (CommandBound cfg r) := by
  cases r <;> unfold CommandBound <;> infer_instance

/-- No holes can be hidden by a sparse table: every covered allocated name is
checked separately, and every covered record must be terminal and released. -/
def relinquishable (s : LocalSnapshot) (target : Nat) : Bool :=
  s.floor ≤ target && target ≤ s.frame.nextIdentity &&
    (List.range (target - s.floor)).all fun offset =>
      match outcome s (s.floor + offset) with
      | none => false
      | some r => r.released && r.answer.any terminalAnswer

def relinquish (s : LocalSnapshot) (target : Nat) : Except Refusal LocalSnapshot :=
  if target ≤ s.floor then .ok s else
  if s.pending.isSome then .error .busy else
  if target > s.frame.nextIdentity then .error .invalid else
  if relinquishable s target then .ok {s with floor := target, pending := some target}
  else .error .unresolved

def finishRetirement (s : LocalSnapshot) (target : Nat) : Option LocalSnapshot :=
  if s.pending == some target then
    some {s with pending := none, outcomes := s.outcomes.filter (fun r => target ≤ r.identity)}
  else none

def remember (s : LocalSnapshot) (receipt : Receipt) : LocalSnapshot :=
  let answer := match receipt.answer with
    | .tooLate x y => .published x y
    | a => a
  if terminalAnswer answer then
    {s with outcomes := s.outcomes.map fun r =>
      if r.identity == receipt.identity && r.input == (match answer with
        | .published x _ | .prevented x => x | _ => r.input)
      then {r with answer := some answer} else r}
  else s

/-- The command is internal. Public clients cannot construct a receive edit. -/
def localChangeCore (cfg : Config) (s : LocalSnapshot) (command : FrameCommand) :
    Except Refusal LocalSnapshot :=
  if s.pending.isSome then .error .busy else
  if (match command with | .accept _ => true | _ => false) &&
      s.frame.nextIdentity ≥ cfg.lifetime then .error .exhausted else
  if (match command with | .accept _ => true | _ => false) &&
      s.outcomes.length ≥ cfg.outcomeCapacity then .error .full else
  match advance s.frame command with
  | .changed frame =>
    let result := {s with frame := frame}
    match command with
    | .accept input => .ok {result with outcomes := s.outcomes ++
        [{identity := s.frame.nextIdentity, input := input}]}
    | .release => match s.frame.head with
      | none => .error .invalid
      | some (_,r) => .ok {result with outcomes := s.outcomes.map fun o =>
          if o.identity == r.identity then {o with released := true, answer := r.receipt.map (·.answer)} else o}
    | .receive receipt => .ok (remember result receipt)
    | _ => .ok result
  | _ => .error .invalid

/-- Expiry is checked before dispatch, including before fresh reserve. -/
def peerDecisionCore (cfg : Config) (s : PeerSnapshot) (identity : Nat)
    (command : PeerCommand) : Except Refusal (PeerSnapshot × ReplyPacket × Option Bool × Option Bool) :=
  if identity < s.floor then .ok (s, .expired identity s.floor, none, none) else
  if identity ≥ cfg.lifetime then .error .invalid else
  let result := peerStep s.entries identity command
  if result.peer.length > cfg.outcomeCapacity then .error .full else
  .ok ({s with entries := result.peer}, .receipt result.receipt, result.effect, result.prevented)

def localChange (cfg : Config) (s : LocalSnapshot) (c : FrameCommand) :
    Except Refusal LocalSnapshot :=
  match localChangeCore cfg s c with
  | .error e => .error e
  | .ok t => if LocalBound cfg t then .ok t else .error .invalid

def peerDecision (cfg : Config) (s : PeerSnapshot) (i : Nat) (c : PeerCommand) :
    Except Refusal (PeerSnapshot × ReplyPacket × Option Bool × Option Bool) :=
  match peerDecisionCore cfg s i c with
  | .error e => .error e
  | .ok r => if PeerBound cfg r.1 ∧ ReplyBound cfg r.2.1 then .ok r else .error .invalid

theorem localChange_bound {cfg : Config} {s t : LocalSnapshot} {c : FrameCommand}
    (h : localChange cfg s c = .ok t) : LocalBound cfg t := by
  unfold localChange at h
  split at h <;> try contradiction
  split at h
  · cases h; assumption
  · contradiction

theorem peerDecision_bound {cfg : Config} {s t : PeerSnapshot} {i : Nat} {c : PeerCommand}
    {r : ReplyPacket} {e p : Option Bool}
    (h : peerDecision cfg s i c = .ok (t,r,e,p)) : PeerBound cfg t ∧ ReplyBound cfg r := by
  unfold peerDecision at h
  split at h <;> try contradiction
  split at h
  · cases h; assumption
  · contradiction

/-- Publication authority can only originate from the actual computed head.
Reserve, cancellation and query preserve the admitted identity and input. -/
def businessPacket (s : LocalSnapshot) (identity : Nat) (operation : Nat) :
    Option RequestPacket := do
  if identity < s.floor then none else do
  let record ← outcome s identity
  let command ← match operation with
    | 0 => some (.reserve record.input)
    | 1 => some .query
    | 2 => some (.cancel record.input)
    | 3 => do
      let (_,r) ← s.frame.head
      if r.identity == identity && r.phase == .computed && r.routeOpen then do
        let y ← r.output
        some (.publish r.input y)
      else none
    | _ => none
  pure (.business identity command)

theorem outcome_found {s : LocalSnapshot} {identity : Nat} {r : Outcome}
    (h : outcome s identity = some r) : r ∈ s.outcomes ∧ r.identity = identity :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem businessPacket_bound {cfg : Config} {s : LocalSnapshot} {identity operation : Nat}
    {packet : RequestPacket} (bound : LocalBound cfg s)
    (h : businessPacket s identity operation = some packet) : RequestBound cfg packet := by
  cases found : outcome s identity with
  | none => simp [businessPacket, found] at h
  | some record =>
    have hr := outcome_found found
    have hi : identity ≤ cfg.lifetime := hr.2 ▸ bound.2.2.2.2.2 record hr.1
    unfold businessPacket at h
    simp only [found] at h
    repeat' first | split at h | simp_all [RequestBound]
    all_goals try {subst packet; exact hi}
    all_goals
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨pair, _, h⟩ := h
      split at h
      · simp only [Option.bind_eq_some_iff] at h
        obtain ⟨y, _, h⟩ := h
        simp only [Option.some.injEq] at h
        cases h
        exact hi
      · contradiction

@[simp] theorem peerDecisionCore_expired (cfg : Config) (s : PeerSnapshot)
    (identity : Nat) (command : PeerCommand) (h : identity < s.floor) :
    peerDecisionCore cfg s identity command = .ok (s, .expired identity s.floor, none, none) := by
  simp [peerDecisionCore, h]

@[simp] theorem remember_frame (s : LocalSnapshot) (r : Receipt) :
    (remember s r).frame = s.frame := by
  cases r with
  | mk identity answer => cases answer <;> simp [remember, terminalAnswer]

theorem localChange_frame_valid {cfg : Config} {s t : LocalSnapshot} {c : FrameCommand}
    (h : localChange cfg s c = .ok t) : t.frame.Valid := (localChange_bound h).1

theorem remember_metadata (s : LocalSnapshot) (r : Receipt) :
    (remember s r).floor = s.floor ∧ (remember s r).pending = s.pending := by
  cases r with
  | mk identity answer => cases answer <;> simp [remember, terminalAnswer]

theorem localChange_metadata {cfg : Config} {s t : LocalSnapshot} {c : FrameCommand}
    (h : localChange cfg s c = .ok t) : t.floor = s.floor ∧ t.pending = s.pending := by
  unfold localChange at h
  split at h <;> try contradiction
  next target changed =>
    split at h <;> try contradiction
    cases h
    cases c <;> unfold localChangeCore at changed
    all_goals repeat' first | contradiction | split at changed
    all_goals simp only [Except.ok.injEq] at changed
    all_goals subst t
    all_goals first | exact remember_metadata _ _ | exact ⟨rfl,rfl⟩

example : query {outcomes := [{identity := 0, input := true, answer := some (.published true false), released := true}]} 0 = .terminal (.published true false) := by decide
example : relinquish {frame := {initialFrame with nextIdentity := 1}, outcomes := [{identity := 0, input := true, answer := some (.published true false), released := true}]} 1 = .ok {frame := {initialFrame with nextIdentity := 1}, floor := 1, pending := some 1, outcomes := [{identity := 0, input := true, answer := some (.published true false), released := true}]} := by decide

end FRPSpec.PendingRetention

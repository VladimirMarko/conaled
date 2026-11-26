import Applications.FRP.PendingRetention.Runtime
import Applications.FRP.PendingRetention.Outcomes

/-! Proof-side provenance of the closed pending controller. The lifetime ledger
and bank predecessors below are witnesses, never executable retained history. -/
set_option autoImplicit false
namespace FRPSpec.PendingRetention
open PendingCrash PendingMigration

/-- Retired result names still have genuine lifetime terminal evidence. Control
packets originate only after the owner's durable relinquishment publication. -/
def RequestSafe (frame : Frame) (history : Peer) (floor : Nat) : RequestPacket → Prop
  | .business identity command => MessageSafe frame history (.request identity command)
  | .retire target => target ≤ floor

def ReplySafe (history : Peer) : ReplyPacket → Prop
  | .receipt receipt => ReceiptAuthentic history receipt
  | _ => True

theorem RequestSafe.peerStep {frame : Frame} {history : Peer} {floor : Nat}
    {packet : RequestPacket} (h : RequestSafe frame history floor packet)
    (identity : Nat) (command : PeerCommand) :
    RequestSafe frame (PendingCrash.peerStep history identity command).peer floor packet := by
  cases packet with
  | business i c => exact MessageSafe.peerStep frame history (.request i c) identity command h
  | retire t => exact h

theorem RequestSafe.extension {before after : Frame} {history : Peer} {floor next : Nat}
    {packet : RequestPacket} (h : RequestSafe before history floor packet)
    (valid : after.Valid) (extension : LiveFrameExtension before after history)
    (monotone : floor ≤ next) : RequestSafe after history next packet := by
  cases packet with
  | business i c => exact MessageSafe.extension before after history (.request i c) valid extension h
  | retire t => exact h.trans monotone

theorem ReplySafe.peerStep {history : Peer} {packet : ReplyPacket}
    (h : ReplySafe history packet) (identity : Nat) (command : PeerCommand) :
    ReplySafe (PendingCrash.peerStep history identity command).peer packet := by
  cases packet with
  | receipt r => exact peerStep_preserves_authentic _ _ _ _ h
  | _ => trivial

/-- Existing terminal evidence makes any replay harmless, independently of
whether its live frame slot has since been reused. -/
theorem terminal_message_safe (frame : Frame) (history : Peer) (identity : Nat)
    (command : PeerCommand)
    (terminal : (∃ x y, (lookup identity history).1 = some (.published x y)) ∨
      ∃ x, (lookup identity history).1 = some (.cancelled x)) :
    MessageSafe frame history (.request identity command) := by
  constructor
  · rcases terminal with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · cases command <;> try trivial
    intro nonterminal
    rcases terminal with ⟨x,y,h⟩ | ⟨x,h⟩
    all_goals rcases nonterminal with absent | ⟨v,reserved⟩ <;> simp_all

/-- The sole public publication producer checks the actual computed head, not
an arbitrary caller-provided output or an assumed traffic predicate. -/
theorem computed_message_safe (frame : Frame) (history : Peer) (slot : Bool)
    (request : PendingCrash.Request) (output : Bool) (valid : frame.Valid)
    (head : frame.head = some (slot,request)) (computed : request.phase = .computed)
    (selected : request.output = some output) :
    MessageSafe frame history (.request request.identity (.publish request.input output)) := by
  have present := head_request_eq _ _ _ head
  have member : slot ∈ frame.order := (valid.2.2.1 slot).mpr (by simp [present])
  have wf := (valid.2.2.2.1 slot request (by simp [present])).2.1
  have outputEq : output = frame.logical := by
    simp only [RequestValid, computed] at wf
    exact Option.some.inj (selected.symm.trans wf.2.1)
  refine ⟨Or.inr (Or.inr ⟨slot,request,member,present,rfl,rfl,outputEq,head⟩),?_⟩
  intro _
  exact ⟨slot,request,head,rfl,rfl,selected,computed⟩

/-- Queue copying preserves provenance because the only new item is an item
already present in that same bounded queue. -/
theorem duplicateList_all {α : Type} {P : α → Prop} {capacity index : Nat}
    {items result : List α} (safe : ∀ x ∈ items, P x)
    (changed : duplicateList capacity index items = some result) : ∀ x ∈ result, P x := by
  unfold duplicateList at changed
  split at changed <;> try contradiction
  cases found : items[index]? with
  | none => simp [found] at changed
  | some item =>
    simp only [found, pure] at changed
    cases changed
    intro x member
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · exact safe x old
    · exact safe x (List.mem_of_getElem? found)

theorem businessPacket_safe {s : LocalSnapshot} {history : Peer} {identity operation : Nat}
    {packet : RequestPacket} (valid : s.frame.Valid)
    (simple : ∀ r ∈ s.outcomes,
      MessageSafe s.frame history (.request r.identity (.reserve r.input)) ∧
      MessageSafe s.frame history (.request r.identity (.cancel r.input)) ∧
      MessageSafe s.frame history (.request r.identity .query))
    (produced : businessPacket s identity operation = some packet) :
    RequestSafe s.frame history s.floor packet := by
  cases found : outcome s identity with
  | none => simp [businessPacket, found] at produced
  | some record =>
    have hr := outcome_found found
    have origin := simple record hr.1
    rw [hr.2] at origin
    unfold businessPacket at produced
    simp only [found] at produced
    split at produced
    · simp at produced
    · split at produced
      · cases produced
        exact origin.1
      · cases produced
        exact origin.2.2
      · cases produced
        exact origin.2.1
      · cases head : s.frame.head with
        | none => simp [head] at produced
        | some pair =>
          simp [head] at produced
          obtain ⟨ready,produced⟩ := produced
          simp only [Option.bind_eq_some_iff] at produced
          obtain ⟨output,selected,produced⟩ := produced
          simp only [Option.some.injEq] at produced
          cases produced
          have safe := computed_message_safe s.frame history pair.1 pair.2 output valid head ready.1.2 selected
          simpa only [RequestSafe, ready.1.1] using safe
      · simp at produced

theorem PoolSafe.simple_messages {s : LocalSnapshot} {history : Peer}
    (safe : PoolSafe s.frame history s.outcomes) (valid : s.frame.Valid)
    (r : Outcome) (member : r ∈ s.outcomes) :
    MessageSafe s.frame history (.request r.identity (.reserve r.input)) ∧
    MessageSafe s.frame history (.request r.identity (.cancel r.input)) ∧
    MessageSafe s.frame history (.request r.identity .query) := by
  rcases (safe.safe r member).origin with live | terminal
  · obtain ⟨slot,request,present,identity,input⟩ := live
    have messages := occupied_simple_safe s.frame history slot request valid present
    simpa only [identity,input] using messages
  · have known : (∃ x y, (lookup r.identity history).1 = some (.published x y)) ∨
        ∃ x, (lookup r.identity history).1 = some (.cancelled x) := by
      rcases terminal with cancelled | ⟨output,published⟩
      · exact Or.inr ⟨r.input,cancelled⟩
      · exact Or.inl ⟨r.input,output,published⟩
    exact ⟨terminal_message_safe _ _ _ _ known,
      terminal_message_safe _ _ _ _ known,terminal_message_safe _ _ _ _ known⟩

structure QueuesSafe (s : System) (history : Peer) : Prop where
  localOut : ∀ packet ∈ s.localOut, RequestSafe s.localBank.selected.frame history
    s.localBank.selected.floor packet
  peerIn : ∀ packet ∈ s.peerIn, RequestSafe s.localBank.selected.frame history
    s.localBank.selected.floor packet
  peerOut : ∀ packet ∈ s.peerOut, ReplySafe history packet
  localIn : ∀ packet ∈ s.localIn, ReplySafe history packet

theorem QueuesSafe.initial : QueuesSafe FRPSpec.PendingRetention.initial [] := by
  constructor <;> intro packet h <;> cases h

theorem QueuesSafe.congr {s t : System} {history : Peer} (safe : QueuesSafe s history)
    (frame : t.localBank.selected.frame = s.localBank.selected.frame)
    (floor : t.localBank.selected.floor = s.localBank.selected.floor)
    (lo : t.localOut = s.localOut) (pi : t.peerIn = s.peerIn)
    (po : t.peerOut = s.peerOut) (li : t.localIn = s.localIn) : QueuesSafe t history := by
  constructor
  · simpa only [frame, floor, lo] using safe.localOut
  · simpa only [frame, floor, pi] using safe.peerIn
  · simpa only [po] using safe.peerOut
  · simpa only [li] using safe.localIn

theorem QueuesSafe.peerStep {s : System} {history : Peer} (safe : QueuesSafe s history)
    (identity : Nat) (command : PeerCommand) :
    QueuesSafe s (PendingCrash.peerStep history identity command).peer :=
  ⟨fun p hp => (safe.localOut p hp).peerStep identity command,
   fun p hp => (safe.peerIn p hp).peerStep identity command,
   fun p hp => (safe.peerOut p hp).peerStep identity command,
   fun p hp => (safe.localIn p hp).peerStep identity command⟩

theorem QueuesSafe.pushRequest {s : System} {history : Peer} (cfg : Config)
    (safe : QueuesSafe s history) (packet : RequestPacket)
    (incoming : RequestSafe s.localBank.selected.frame history s.localBank.selected.floor packet) :
    QueuesSafe (FRPSpec.PendingRetention.pushRequest cfg s packet).system history := by
  unfold FRPSpec.PendingRetention.pushRequest
  split
  · refine ⟨?_,safe.peerIn,safe.peerOut,safe.localIn⟩
    intro p hp
    simp only [List.mem_append,List.mem_singleton] at hp
    rcases hp with old | rfl
    · exact safe.localOut p old
    · exact incoming
  · exact safe

theorem QueuesSafe.pushReply {s : System} {history : Peer} (cfg : Config)
    (safe : QueuesSafe s history) (packet : ReplyPacket) (incoming : ReplySafe history packet) :
    QueuesSafe (FRPSpec.PendingRetention.pushReply cfg s packet).system history := by
  unfold FRPSpec.PendingRetention.pushReply
  split
  · refine ⟨safe.localOut,safe.peerIn,?_,safe.localIn⟩
    intro p hp
    simp only [List.mem_append,List.mem_singleton] at hp
    rcases hp with old | rfl
    · exact safe.peerOut p old
    · exact incoming
  · exact safe

theorem QueuesSafe.duplicateQueue {s : System} {history : Peer} (cfg : Config)
    (safe : QueuesSafe s history) (queue : Queue) (index : Nat) :
    QueuesSafe (FRPSpec.PendingRetention.duplicateQueue cfg s queue index).system history := by
  cases queue <;> unfold FRPSpec.PendingRetention.duplicateQueue
  all_goals dsimp only
  all_goals split
  all_goals try exact safe
  all_goals rename_i values found
  all_goals simp only [Option.map_eq_some_iff] at found
  all_goals obtain ⟨items,changed,same⟩ := found
  all_goals cases same
  · exact ⟨duplicateList_all safe.localOut changed,safe.peerIn,safe.peerOut,safe.localIn⟩
  · exact ⟨safe.localOut,duplicateList_all safe.peerIn changed,safe.peerOut,safe.localIn⟩
  · exact ⟨safe.localOut,safe.peerIn,duplicateList_all safe.peerOut changed,safe.localIn⟩
  · exact ⟨safe.localOut,safe.peerIn,safe.peerOut,duplicateList_all safe.localIn changed⟩

theorem QueuesSafe.beginLocal {s : System} {history : Peer} (safe : QueuesSafe s history)
    (target : LocalSnapshot) (cause : LocalCause) :
    QueuesSafe (FRPSpec.PendingRetention.beginLocal s target cause).system history := by
  exact safe.congr (by simp [FRPSpec.PendingRetention.beginLocal]) (by simp [FRPSpec.PendingRetention.beginLocal]) rfl rfl rfl rfl

theorem QueuesSafe.beginPeer {s : System} {history : Peer} (safe : QueuesSafe s history)
    (target : PeerSnapshot) (cause : PeerCause) :
    QueuesSafe (FRPSpec.PendingRetention.beginPeer s target cause).system history :=
  safe.congr rfl rfl rfl rfl rfl rfl

theorem QueuesSafe.transferRequest {s : System} {history : Peer} (cfg : Config)
    (safe : QueuesSafe s history) :
    QueuesSafe (step cfg s .transferRequest).system history := by
  simp only [step]
  split
  · exact safe
  · cases pending : s.localOut with
    | nil => exact safe
    | cons packet rest =>
      refine ⟨?_,?_,safe.peerOut,safe.localIn⟩
      · intro p hp; exact safe.localOut p (by simp [pending,hp])
      · intro p hp
        simp only [List.mem_append,List.mem_singleton] at hp
        rcases hp with old | rfl
        · exact safe.peerIn p old
        · exact safe.localOut p (by simp [pending])

theorem QueuesSafe.transferReply {s : System} {history : Peer} (cfg : Config)
    (safe : QueuesSafe s history) :
    QueuesSafe (step cfg s .transferReply).system history := by
  simp only [step]
  split
  · exact safe
  · cases pending : s.peerOut with
    | nil => exact safe
    | cons packet rest =>
      refine ⟨safe.localOut,safe.peerIn,?_,?_⟩
      · intro p hp; exact safe.peerOut p (by simp [pending,hp])
      · intro p hp
        simp only [List.mem_append,List.mem_singleton] at hp
        rcases hp with old | rfl
        · exact safe.localIn p old
        · exact safe.peerOut p (by simp [pending])

theorem QueuesSafe.drop {s : System} {history : Peer} (cfg : Config)
    (safe : QueuesSafe s history) (queue : Queue) :
    QueuesSafe (step cfg s (.drop queue)).system history := by
  cases queue
  · exact ⟨fun p hp => safe.localOut p (List.mem_of_mem_tail hp),safe.peerIn,safe.peerOut,safe.localIn⟩
  · exact ⟨safe.localOut,fun p hp => safe.peerIn p (List.mem_of_mem_tail hp),safe.peerOut,safe.localIn⟩
  · exact ⟨safe.localOut,safe.peerIn,fun p hp => safe.peerOut p (List.mem_of_mem_tail hp),safe.localIn⟩
  · exact ⟨safe.localOut,safe.peerIn,safe.peerOut,fun p hp => safe.localIn p (List.mem_of_mem_tail hp)⟩

theorem QueuesSafe.crashLocal {s : System} {history : Peer} (cfg : Config)
    (safe : QueuesSafe s history) : QueuesSafe (step cfg s .crashLocal).system history :=
  safe.congr rfl rfl rfl rfl rfl rfl

theorem QueuesSafe.crashPeer {s : System} {history : Peer} (cfg : Config)
    (safe : QueuesSafe s history) : QueuesSafe (step cfg s .crashPeer).system history :=
  safe.congr rfl rfl rfl rfl rfl rfl

theorem QueuesSafe.extension {s t : System} {history : Peer} (safe : QueuesSafe s history)
    (valid : t.localBank.selected.frame.Valid)
    (extension : LiveFrameExtension s.localBank.selected.frame t.localBank.selected.frame history)
    (monotone : s.localBank.selected.floor ≤ t.localBank.selected.floor)
    (lo : t.localOut = s.localOut) (pi : t.peerIn = s.peerIn)
    (po : t.peerOut = s.peerOut) (li : t.localIn = s.localIn) : QueuesSafe t history := by
  constructor
  · intro p hp
    exact (safe.localOut p (lo ▸ hp)).extension valid extension monotone
  · intro p hp
    exact (safe.peerIn p (pi ▸ hp)).extension valid extension monotone
  · simpa only [po] using safe.peerOut
  · simpa only [li] using safe.localIn

/-- Receipt authenticity is retained independently of the physical receipt
pool: delayed genuine replies remain genuine after authorized deletion. -/
def PendingMessagesSafe (s : System) (history : Peer) : Prop :=
  (∀ command, s.localCause = some (.frame command) → CommandAuthentic history command) ∧
  (∀ identity command reply effect prevented,
    s.peerCause = some (.business identity command reply effect prevented) →
    MessageSafe s.localBank.selected.frame history (.request identity command))

def LiveAbove (frame : Frame) (floor : Nat) : Prop :=
  ∀ slot request, request ∈ frame.requests.get slot → floor ≤ request.identity

def ScanSafe (s : System) : Prop :=
  ∀ target cursor, s.retirementScan = some (target,cursor) →
    s.localBank.selected.floor ≤ cursor ∧ cursor ≤ target ∧
    target ≤ s.localBank.selected.frame.nextIdentity ∧
    LiveAbove s.localBank.selected.frame cursor

def RetirementSafe (s : System) : Prop :=
  (∀ target, s.localCause = some (.relinquish target) →
    s.localBank.selected.floor ≤ target ∧
    target ≤ s.localBank.selected.frame.nextIdentity ∧ LiveAbove s.localBank.selected.frame target) ∧
  (∀ target, s.peerCause = some (.floor target) → target ≤ s.localBank.selected.floor)

theorem scan_cursor_live {s : LocalSnapshot} {history : Peer} {cursor : Nat} {r : Outcome}
    (pool : PoolSafe s.frame history s.outcomes) (live : LiveAbove s.frame cursor)
    (found : outcome s cursor = some r) (released : r.released = true) :
    LiveAbove s.frame (cursor + 1) := by
  obtain ⟨member,identity⟩ := outcome_found found
  intro slot request present
  have lower := live slot request present
  have different := (pool.safe r member).released released slot request present
  omega

theorem QueuesSafe.send {s : System} {history : Peer} (cfg : Config)
    (safe : QueuesSafe s history) (pool : PoolSafe s.localBank.selected.frame history
      s.localBank.selected.outcomes) (valid : s.localBank.selected.frame.Valid)
    (identity : Nat) (operation : Business) :
    QueuesSafe (step cfg s (.send identity operation)).system history := by
  simp only [step]
  split
  · exact safe
  · split
    · exact safe
    · split
      · exact safe
      · rename_i packet produced
        exact safe.pushRequest cfg packet (businessPacket_safe valid (pool.simple_messages valid) produced)

/-- The selected retained state is related to an unbounded proof ledger. No
ledger field or copy of it is stored by the executable service. -/
structure RetainedRelation (localState : LocalSnapshot) (peerState : PeerSnapshot)
    (history : Peer) : Prop where
  valid : localState.frame.Valid
  coupled : FramePeer localState.frame history
  names : PeerNamesBelow localState.frame.nextIdentity history
  pool : PoolSafe localState.frame history localState.outcomes
  floors : peerState.floor ≤ localState.floor
  counter : localState.floor ≤ localState.frame.nextIdentity
  live : LiveAbove localState.frame localState.floor
  extension : PeerExtension peerState.floor peerState.entries history
  local_pending : ∀ target ∈ localState.pending, target = localState.floor
  peer_pending : ∀ target ∈ peerState.pending, target = peerState.floor

theorem RetainedRelation.initial : RetainedRelation {} {} [] := by
  refine ⟨initialFrame_valid _,FramePeer.initial _,?_,PoolSafe.initial,
    Nat.le_refl _,Nat.le_refl _,?_,PeerExtension.refl _ _,?_,?_⟩
  · intro i e member; cases member
  · intro slot request member; cases slot <;> simp [initialFrame,Slots.get] at member
  · simp
  · simp

theorem RetainedRelation.localChange {cfg : Config} {s t : LocalSnapshot} {p : PeerSnapshot}
    {history : Peer} (related : RetainedRelation s p history) (command : FrameCommand)
    (authentic : CommandAuthentic history command)
    (changed : localChange cfg s command = .ok t) : RetainedRelation t p history := by
  have metadata := localChange_metadata changed
  have grows : s.frame.nextIdentity ≤ t.frame.nextIdentity := by
    rw [propose_nextIdentity _ _ _ (localChange_proposed changed)]
    omega
  have fresh := related.names.fresh
  refine ⟨localChange_frame_valid changed,
    localChange_framePeer history related.coupled fresh authentic changed,?_,
    related.pool.localChange related.valid related.coupled command authentic changed,
    ?_,?_,?_,related.extension,?_,related.peer_pending⟩
  · intro i e member
    exact (related.names i e member).trans_le grows
  · simpa only [metadata.1] using related.floors
  · simpa only [metadata.1] using related.counter.trans grows
  · rw [metadata.1]
    exact localChange_liveAbove s.floor related.live related.counter changed
  · intro target member
    rw [metadata.1]
    exact related.local_pending target (metadata.2 ▸ member)

theorem RetainedRelation.raise_local {s : LocalSnapshot} {p : PeerSnapshot} {history : Peer}
    (related : RetainedRelation s p history) (target : Nat)
    (monotone : s.floor ≤ target) (counter : target ≤ s.frame.nextIdentity)
    (live : LiveAbove s.frame target) :
    RetainedRelation {s with floor := target,pending := some target} p history :=
  ⟨related.valid,related.coupled,related.names,related.pool,related.floors.trans monotone,
   counter,live,related.extension,by intro t ht; cases ht; rfl,related.peer_pending⟩

theorem RetainedRelation.finish_local {s t : LocalSnapshot} {p : PeerSnapshot} {history : Peer}
    (related : RetainedRelation s p history) (target : Nat)
    (changed : finishRetirement s target = some t) : RetainedRelation t p history := by
  unfold finishRetirement at changed
  split at changed <;> try contradiction
  next matching =>
    have same : s.pending = some target := by simpa using matching
    have floor : target = s.floor := related.local_pending target (by simp [same])
    cases changed
    refine ⟨related.valid,related.coupled,related.names,?_,related.floors,related.counter,
      related.live,related.extension,by simp,related.peer_pending⟩
    exact related.pool.filter target (by simpa only [floor,LiveAbove] using related.live)

theorem RetainedRelation.raise_peer {s : LocalSnapshot} {p : PeerSnapshot} {history : Peer}
    (related : RetainedRelation s p history) (target : Nat)
    (monotone : p.floor ≤ target) (authorized : target ≤ s.floor) :
    RetainedRelation s {p with floor := target,pending := some target} history :=
  ⟨related.valid,related.coupled,related.names,related.pool,authorized,related.counter,
   related.live,related.extension.raise monotone,related.local_pending,
   by intro t ht; cases ht; rfl⟩

theorem RetainedRelation.delete_peer {s : LocalSnapshot} {p : PeerSnapshot} {history : Peer}
    (related : RetainedRelation s p history) (target : Nat)
    (pending : p.pending = some target) :
    RetainedRelation s {p with pending := none,entries := p.entries.filter (fun e => target ≤ e.1)}
      history := by
  have floor := related.peer_pending target (by simp [pending])
  refine ⟨related.valid,related.coupled,related.names,related.pool,related.floors,related.counter,
    related.live,?_,related.local_pending,by simp⟩
  simpa only [floor] using related.extension.filter

theorem RetainedRelation.peerDecision {cfg : Config} {s : LocalSnapshot}
    {p t : PeerSnapshot} {history : Peer} {identity : Nat} {command : PeerCommand}
    {reply : ReplyPacket} {effect prevented : Option Bool}
    (related : RetainedRelation s p history)
    (message : MessageSafe s.frame history (.request identity command))
    (above : p.floor ≤ identity)
    (changed : peerDecision cfg p identity command = .ok (t,reply,effect,prevented)) :
    RetainedRelation s t (PendingCrash.peerStep history identity command).peer := by
  rcases peerDecision_cases changed with expired | performed
  · omega
  · rcases performed with ⟨_,rfl,_,_,_⟩
    refine ⟨related.valid,
      FramePeer.step_of_traffic s.frame history identity command related.valid related.coupled
        message.1 message.2,
      related.names.peerStep identity command
        (FrameTraffic.identity_lt _ _ _ _ related.valid related.names message.1),
      related.pool.peerStep identity command,related.floors,related.counter,related.live,
      related.extension.step identity command above,related.local_pending,related.peer_pending⟩

theorem PeerExtension.authentic {floor : Nat} {retained history : Peer}
    (extension : PeerExtension floor retained history) (receipt : Receipt)
    (above : floor ≤ receipt.identity) (authentic : ReceiptAuthentic retained receipt) :
    ReceiptAuthentic history receipt := by
  rcases receipt with ⟨identity,answer⟩
  cases answer <;> simp only [ReceiptAuthentic] at authentic ⊢
  all_goals exact (extension identity above).symm.trans authentic

theorem peerDecision_reply_unchanged {cfg : Config} {p : PeerSnapshot} {history : Peer}
    {identity : Nat} {command : PeerCommand} {reply : ReplyPacket} {effect prevented : Option Bool}
    (extension : PeerExtension p.floor p.entries history)
    (changed : peerDecision cfg p identity command = .ok (p,reply,effect,prevented)) :
    ReplySafe history reply := by
  rcases peerDecision_cases changed with expired | performed
  · rw [expired.2.2.1]; trivial
  · obtain ⟨above,same,rfl,_,_⟩ := performed
    have sameEntries : p.entries = (peerStep p.entries identity command).peer :=
      congrArg PeerSnapshot.entries same
    have authentic := peerStep_receipt_authentic p.entries identity command
    rw [← sameEntries] at authentic
    exact extension.authentic _ (by simpa only [peerStep_receipt_identity] using above) authentic

theorem QueuesSafe.consume_request {s : System} {history : Peer} (safe : QueuesSafe s history) :
    QueuesSafe {s with peerIn := s.peerIn.tail} history :=
  ⟨safe.localOut,fun p hp => safe.peerIn p (List.mem_of_mem_tail hp),safe.peerOut,safe.localIn⟩

theorem QueuesSafe.consume_reply {s : System} {history : Peer} (safe : QueuesSafe s history) :
    QueuesSafe {s with localIn := s.localIn.tail} history :=
  ⟨safe.localOut,safe.peerIn,safe.peerOut,fun p hp => safe.localIn p (List.mem_of_mem_tail hp)⟩

theorem QueuesSafe.requestStep {s : System} {history : Peer} (cfg : Config)
    (safe : QueuesSafe s history) (extension : PeerExtension s.peer.selected.floor
      s.peer.selected.entries history) :
    QueuesSafe (FRPSpec.PendingRetention.requestStep cfg s).system history := by
  unfold FRPSpec.PendingRetention.requestStep
  split
  · exact safe
  · cases pending : s.peerIn with
    | nil => exact safe
    | cons packet rest =>
      have consumed : QueuesSafe {s with peerIn := rest} history := by
        simpa only [pending,List.tail_cons] using safe.consume_request
      cases packet with
      | business identity command =>
        dsimp only
        split
        · exact safe
        · split
          · exact consumed
          · rename_i target reply effect prevented changed
            split
            · rename_i unchanged
              subst target
              exact consumed.pushReply cfg reply (peerDecision_reply_unchanged extension changed)
            · exact consumed.beginPeer _ _
      | retire target =>
        dsimp only
        split
        · exact safe
        · split
          · exact consumed.pushReply cfg (.deleted target) trivial
          · exact consumed.beginPeer _ _

theorem QueuesSafe.replyStep {s : System} {history : Peer} (cfg : Config)
    (safe : QueuesSafe s history) :
    QueuesSafe (FRPSpec.PendingRetention.replyStep cfg s).system history := by
  unfold FRPSpec.PendingRetention.replyStep
  split
  · exact safe
  · cases pending : s.localIn with
    | nil => exact safe
    | cons packet rest =>
      have consumed : QueuesSafe {s with localIn := rest} history := by
        simpa only [pending,List.tail_cons] using safe.consume_reply
      cases packet with
      | expired i f => exact consumed
      | deleted target =>
        dsimp only
        split
        · exact consumed
        · exact consumed.beginLocal _ _
      | receipt receipt =>
        dsimp only
        split
        · exact consumed
        · split
          · exact consumed
          · exact consumed.beginLocal _ _

/-- A ghost action exists only at the peer's joint receipt/effect selector
publication. The executable service stores neither this action log nor G. -/
def peerAction (s : System) : Command → Option (Nat × PeerCommand)
  | .progress =>
    if s.peerDown || s.localCause.isSome || s.retirementScan.isSome then none else
    match s.peerCause with
    | some (.business identity command _ _ _) =>
      if s.peer.progress.2 then some (identity,command) else none
    | _ => none
  | _ => none

def historyAfter (s : System) (c : Command) (history : Peer) : Peer :=
  match peerAction s c with
  | none => history
  | some (identity,command) => (PendingCrash.peerStep history identity command).peer

def peerActions (cfg : Config) : System → List Command → List (Nat × PeerCommand)
  | _, [] => []
  | s, c :: cs => (peerAction s c).toList ++ peerActions cfg (step cfg s c).system cs

/-- Labels are checked against the independent delay semantics directly.
No old unbounded-runtime log record is fabricated for this relation. -/
inductive SourceRun : DelaySource → List SourceLabel → DelaySource → Prop
  | nil (source) : SourceRun source [] source
  | cons {source mid target label labels} : DelayStep label source mid →
      SourceRun mid labels target → SourceRun source (label :: labels) target

theorem SourceRun.append {source mid target : DelaySource} {xs ys : List SourceLabel}
    (first : SourceRun source xs mid) (rest : SourceRun mid ys target) :
    SourceRun source (xs ++ ys) target := by
  induction first with
  | nil => exact rest
  | cons head _ ih => exact .cons head (ih rest)

/-- Any invariant proved by the actual one-command executor propagates to the
same arbitrary finite execution. This helper adds no semantic assumption to
that executor; callers must separately establish initialization and preservation. -/
theorem execute_induction (cfg : Config) (P : System → Peer → Prop)
    (preserved : ∀ s history c, P s history →
      P (step cfg s c).system (historyAfter s c history))
    (s : System) (history : Peer) (cs : List Command) (valid : P s history) :
    P (execute cfg s cs).system (peerExecute history (peerActions cfg s cs)).peer := by
  induction cs generalizing s history with
  | nil => exact valid
  | cons c cs ih =>
    have next := preserved s history c valid
    have tail := ih (step cfg s c).system (historyAfter s c history) next
    cases action : peerAction s c with
    | none => simpa [execute, peerActions, action, historyAfter, peerExecute] using tail
    | some pair =>
      rcases pair with ⟨identity,command⟩
      simpa [execute, peerActions, action, historyAfter, peerExecute] using tail

end FRPSpec.PendingRetention

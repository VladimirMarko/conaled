import Applications.FRP.PendingRetention.Model

/-! Retained peer observations and the source relation for bounded pending work. -/
namespace FRPSpec.PendingRetention
open PendingCrash

/-- Deleting only older names leaves every retained lookup unchanged. -/
theorem lookup_filter_ge (peer : Peer) (floor identity : Nat) (kept : floor ≤ identity) :
    (lookup identity (peer.filter (fun entry => floor ≤ entry.1))).1 =
      (lookup identity peer).1 := by
  induction peer with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨key,value⟩
    by_cases retained : floor ≤ key
    · simp only [List.filter_cons, decide_eq_true retained, ↓reduceIte]
      by_cases same : key = identity
      · simp [lookup, same]
      · simp [lookup, same, ih]
    · have different : key ≠ identity := by intro same; subst key; exact retained kept
      simp [List.filter, retained, lookup, different, ih]

/-- The independent source observes only the entries named by occupied slots. -/
theorem sourceView_lookup_congr (frame : Frame) (left right : Peer)
    (same : ∀ slot request, request ∈ frame.requests.get slot →
      (lookup request.identity left).1 = (lookup request.identity right).1) :
    sourceView frame left = sourceView frame right := by
  apply congrArg₂ DelaySource.mk
  · cases head : frame.head with
    | none => rfl
    | some pair =>
      rcases pair with ⟨slot,request⟩
      have present := head_request_eq frame slot request head
      simp only [same slot request (by simp [present])]
  · congr 1
    funext slot
    cases present : frame.requests.get slot with
    | none => rfl
    | some request => simp [pendingEntry, same slot request (by simp [present])]

theorem sourceView_filter_ge (frame : Frame) (peer : Peer) (floor : Nat)
    (live : ∀ slot request, request ∈ frame.requests.get slot → floor ≤ request.identity) :
    sourceView frame (peer.filter (fun entry => floor ≤ entry.1)) = sourceView frame peer := by
  apply sourceView_lookup_congr
  intro slot request present
  exact lookup_filter_ge peer floor request.identity (live slot request present)

/-- The proof-side lifetime ledger agrees with every still-actionable name.
It is not part of the executable snapshot or its storage bound. -/
def PeerExtension (floor : Nat) (retained history : Peer) : Prop :=
  ∀ identity, floor ≤ identity →
    (lookup identity retained).1 = (lookup identity history).1

theorem PeerExtension.refl (floor : Nat) (peer : Peer) : PeerExtension floor peer peer :=
  fun _ _ => rfl

theorem PeerExtension.raise {floor next : Nat} {retained history : Peer}
    (extension : PeerExtension floor retained history) (monotone : floor ≤ next) :
    PeerExtension next retained history :=
  fun identity above => extension identity (monotone.trans above)

theorem PeerExtension.filter {floor : Nat} {retained history : Peer}
    (extension : PeerExtension floor retained history) :
    PeerExtension floor (retained.filter (fun entry => floor ≤ entry.1)) history := by
  intro identity above
  rw [lookup_filter_ge retained floor identity above]
  exact extension identity above

theorem lookup_peerStep_self (peer : Peer) (identity : Nat) (command : PeerCommand) :
    (lookup identity (peerStep peer identity command).peer).1 =
      (dispatch (lookup identity peer).1 command).1 := by
  cases found : (lookup identity peer).1 with
  | none => cases command <;> simp [peerStep, found, dispatch]
  | some entry =>
    cases entry <;> cases command <;> simp [peerStep, found, dispatch]
    all_goals split <;> simp_all

theorem PeerExtension.step {floor : Nat} {retained history : Peer}
    (extension : PeerExtension floor retained history) (identity : Nat)
    (command : PeerCommand) (above : floor ≤ identity) :
    PeerExtension floor (peerStep retained identity command).peer
      (peerStep history identity command).peer := by
  intro other kept
  by_cases same : other = identity
  · subst other
    rw [lookup_peerStep_self, lookup_peerStep_self, extension identity above]
  · rw [peerStep_other _ _ _ _ same, peerStep_other _ _ _ _ same]
    exact extension other kept

theorem PeerExtension.effect {floor : Nat} {retained history : Peer}
    (extension : PeerExtension floor retained history) (identity : Nat)
    (command : PeerCommand) (above : floor ≤ identity) :
    (peerStep retained identity command).effect = (peerStep history identity command).effect := by
  rw [peerStep_effect, peerStep_effect, extension identity above]

theorem PeerExtension.source {floor : Nat} {retained history : Peer}
    (extension : PeerExtension floor retained history) (frame : Frame)
    (live : ∀ slot request, request ∈ frame.requests.get slot → floor ≤ request.identity) :
    sourceView frame retained = sourceView frame history := by
  apply sourceView_lookup_congr
  intro slot request present
  exact extension request.identity (live slot request present)

/-- Successful bounded edits still use the existing checked frame transition. -/
theorem localChange_proposed {cfg : Config} {s t : LocalSnapshot} {c : FrameCommand}
    (changed : localChange cfg s c = .ok t) :
    propose s.frame c = .changed t.frame := by
  have core : localChangeCore cfg s c = .ok t := by
    unfold localChange at changed
    split at changed <;> try contradiction
    split at changed <;> try contradiction
    cases changed
    assumption
  cases advanced : advance s.frame c with
  | refused | stopped =>
    cases c <;> simp only [localChangeCore, advanced] at core
    all_goals repeat' split at core
    all_goals contradiction
  | changed frame =>
    have proposed := (advance_proposed _ _ _ advanced).1
    have same : t.frame = frame := by
      cases c <;> simp only [localChangeCore, advanced] at core
      all_goals repeat' split at core
      all_goals first | contradiction | (cases core; simp)
    rw [same]
    exact proposed

theorem localChange_sourceView {cfg : Config} {s t : LocalSnapshot} {c : FrameCommand}
    (history : Peer) (valid : s.frame.Valid) (coupled : FramePeer s.frame history)
    (fresh : (lookup s.frame.nextIdentity history).1 = none)
    (changed : localChange cfg s c = .ok t) :
    DelayStep (frameSourceLabel s.frame c) (sourceView s.frame history)
      (sourceView t.frame history) :=
  propose_sourceView s.frame t.frame history c valid coupled fresh
    (localChange_proposed changed)

theorem localChange_framePeer {cfg : Config} {s t : LocalSnapshot} {c : FrameCommand}
    (history : Peer) (coupled : FramePeer s.frame history)
    (fresh : (lookup s.frame.nextIdentity history).1 = none)
    (authentic : CommandAuthentic history c)
    (changed : localChange cfg s c = .ok t) : FramePeer t.frame history :=
  propose_framePeer s.frame t.frame history c coupled fresh authentic
    (localChange_proposed changed)

/-- Successful peer decisions either reject an expired name without dispatch,
or perform exactly the existing peer operation at a retained name. -/
theorem peerDecision_cases {cfg : Config} {s t : PeerSnapshot} {identity : Nat}
    {command : PeerCommand} {reply : ReplyPacket} {effect prevented : Option Bool}
    (changed : peerDecision cfg s identity command = .ok (t,reply,effect,prevented)) :
    (identity < s.floor ∧ t = s ∧ reply = .expired identity s.floor ∧
      effect = none ∧ prevented = none) ∨
    (s.floor ≤ identity ∧ t = {s with entries := (peerStep s.entries identity command).peer} ∧
      reply = .receipt (peerStep s.entries identity command).receipt ∧
      effect = (peerStep s.entries identity command).effect ∧
      prevented = (peerStep s.entries identity command).prevented) := by
  unfold peerDecision at changed
  split at changed <;> try contradiction
  split at changed <;> try contradiction
  cases changed
  rename_i result core _
  unfold peerDecisionCore at core
  split at core
  · cases core
    exact .inl ⟨by assumption,rfl,rfl,rfl,rfl⟩
  · rename_i retained
    split at core <;> try contradiction
    dsimp only at core
    split at core <;> try contradiction
    cases core
    exact .inr ⟨Nat.le_of_not_lt retained,rfl,rfl,rfl,rfl⟩

theorem PeerExtension.receipt {floor : Nat} {retained history : Peer}
    (extension : PeerExtension floor retained history) (identity : Nat)
    (command : PeerCommand) (above : floor ≤ identity) :
    (peerStep retained identity command).receipt = (peerStep history identity command).receipt := by
  simp only [peerStep, extension identity above]
  split <;> first | rfl | (split <;> rfl)

theorem PeerExtension.prevented {floor : Nat} {retained history : Peer}
    (extension : PeerExtension floor retained history) (identity : Nat)
    (command : PeerCommand) (above : floor ≤ identity) :
    (peerStep retained identity command).prevented = (peerStep history identity command).prevented := by
  simp only [peerStep, extension identity above]
  split <;> first | rfl | (split <;> rfl)

/-- A published lifetime name cannot execute again, whether its retained
record still exists or its identity has already crossed the rejection floor. -/
theorem peerDecision_no_reexecution {cfg : Config} {s t : PeerSnapshot} {history : Peer}
    {identity : Nat} {command : PeerCommand} {reply : ReplyPacket}
    {effect prevented : Option Bool} (x y : Bool)
    (extension : PeerExtension s.floor s.entries history)
    (published : (lookup identity history).1 = some (.published x y))
    (changed : peerDecision cfg s identity command = .ok (t,reply,effect,prevented)) :
    effect = none := by
  rcases peerDecision_cases changed with expired | performed
  · exact expired.2.2.2.1
  · rw [performed.2.2.2.1, extension.effect identity command performed.1]
    exact (peerStep_published history identity x y command published).2

/-- Cancellation remains terminal after receipt compaction too. -/
theorem peerDecision_preserves_prevention {cfg : Config} {s t : PeerSnapshot} {history : Peer}
    {identity : Nat} {command : PeerCommand} {reply : ReplyPacket}
    {effect prevented : Option Bool} (x : Bool)
    (extension : PeerExtension s.floor s.entries history)
    (cancelled : (lookup identity history).1 = some (.cancelled x))
    (changed : peerDecision cfg s identity command = .ok (t,reply,effect,prevented)) :
    effect = none := by
  rcases peerDecision_cases changed with expired | performed
  · exact expired.2.2.2.1
  · rw [performed.2.2.2.1, extension.effect identity command performed.1]
    exact (peerStep_cancelled history identity x command cancelled).2

def peerSourceLabel (peer : Peer) (identity : Nat) (command : PeerCommand) : SourceLabel :=
  match (peerStep peer identity command).effect, (peerStep peer identity command).prevented with
  | some output, _ => .output identity output
  | none, some input => .prevent identity input
  | none, none => .internal

/-- The raw peer operation inherits the independent delay-source step. The old
network wrapper is used only to reuse its theorem, not as the new controller. -/
theorem peerStep_source (frame : Frame) (peer : Peer) (identity : Nat) (command : PeerCommand)
    (valid : frame.Valid) (traffic : FrameTraffic frame peer identity command) :
    DelayStep (peerSourceLabel peer identity command) (sourceView frame peer)
      (sourceView frame (peerStep peer identity command).peer) := by
  let system : PendingCrash.System := {peer := peer, outbound := [(identity,command)]}
  obtain ⟨label, observed, source⟩ := network_sourceView_refines system frame false valid (by
    intro i c member
    have same : (i,c) = (identity,command) := by simpa [system] using member
    cases same
    exact traffic)
  have labelEq : label = peerSourceLabel peer identity command := by
    cases effect : (peerStep peer identity command).effect <;>
      cases prevented : (peerStep peer identity command).prevented <;>
      simpa [network,system,sourceLabel,Observation.toLogEntry,effect,prevented,peerSourceLabel]
        using observed.symm
  simpa only [labelEq,system,network] using source

theorem peerStep_source_coupled (frame : Frame) (peer : Peer) (identity : Nat)
    (command : PeerCommand) (valid : frame.Valid) (coupled : FramePeer frame peer)
    (message : MessageSafe frame peer (.request identity command)) :
    FramePeer frame (peerStep peer identity command).peer ∧
    DelayStep (peerSourceLabel peer identity command) (sourceView frame peer)
      (sourceView frame (peerStep peer identity command).peer) :=
  ⟨FramePeer.step_of_traffic frame peer identity command valid coupled message.1 message.2,
    peerStep_source frame peer identity command valid message.1⟩

end FRPSpec.PendingRetention

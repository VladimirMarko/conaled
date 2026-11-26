import Applications.FRP.PendingRetention.Refinement

/-! Retained outcomes are tied to live requests or immutable lifetime evidence.
The history argument is a proof witness, never an executable pool field. -/
namespace FRPSpec.PendingRetention
open PendingCrash
open PendingMigration (Slots)

def OutcomeLive (frame : Frame) (o : Outcome) : Prop :=
  ∃ slot request, frame.requests.get slot = some request ∧
    request.identity = o.identity ∧ request.input = o.input

def OutcomeTerminal (history : Peer) (o : Outcome) : Prop :=
  (lookup o.identity history).1 = some (.cancelled o.input) ∨
    ∃ output, (lookup o.identity history).1 = some (.published o.input output)

structure OutcomeSafe (frame : Frame) (history : Peer) (o : Outcome) : Prop where
  origin : OutcomeLive frame o ∨ OutcomeTerminal history o
  released : o.released = true → ∀ slot request, request ∈ frame.requests.get slot →
    request.identity ≠ o.identity
  authentic : ∀ answer ∈ o.answer, terminalAnswer answer = true ∧
    ReceiptAuthentic history ⟨o.identity,answer⟩

structure PoolSafe (frame : Frame) (history : Peer) (outcomes : List Outcome) : Prop where
  safe : ∀ o ∈ outcomes, OutcomeSafe frame history o
  covered : ∀ slot request, request ∈ frame.requests.get slot →
    ∃ o ∈ outcomes, o.identity = request.identity ∧ o.input = request.input
  below : ∀ o ∈ outcomes, o.identity < frame.nextIdentity

theorem OutcomeTerminal.peerStep {history : Peer} {o : Outcome}
    (h : OutcomeTerminal history o) (identity : Nat) (command : PeerCommand) :
    OutcomeTerminal (peerStep history identity command).peer o := by
  rcases h with cancelled | ⟨output,published⟩
  · exact Or.inl (peerStep_preserves_authentic history identity command
      ⟨o.identity,.prevented o.input⟩ cancelled)
  · exact Or.inr ⟨output,peerStep_preserves_authentic history identity command
      ⟨o.identity,.published o.input output⟩ published⟩

theorem OutcomeSafe.peerStep {frame : Frame} {history : Peer} {o : Outcome}
    (h : OutcomeSafe frame history o) (identity : Nat) (command : PeerCommand) :
    OutcomeSafe frame (peerStep history identity command).peer o := by
  refine ⟨h.origin.imp_right (fun t => t.peerStep identity command),h.released,?_⟩
  intro answer ha
  exact ⟨(h.authentic answer ha).1,
    peerStep_preserves_authentic _ _ _ _ (h.authentic answer ha).2⟩

theorem PoolSafe.peerStep {frame : Frame} {history : Peer} {outcomes : List Outcome}
    (h : PoolSafe frame history outcomes) (identity : Nat) (command : PeerCommand) :
    PoolSafe frame (peerStep history identity command).peer outcomes :=
  ⟨fun o ho => (h.safe o ho).peerStep identity command,h.covered,h.below⟩

theorem PoolSafe.initial : PoolSafe (initialFrame kind) [] [] := by
  refine ⟨by simp,?_,by simp⟩
  intro slot request hr
  cases slot <;> simp [initialFrame,Slots.get] at hr

theorem PoolSafe.filter {frame : Frame} {history : Peer} {outcomes : List Outcome}
    (h : PoolSafe frame history outcomes) (floor : Nat)
    (live : ∀ slot request, request ∈ frame.requests.get slot → floor ≤ request.identity) :
    PoolSafe frame history (outcomes.filter (fun o => floor ≤ o.identity)) := by
  refine ⟨fun o ho => h.safe o (List.mem_of_mem_filter ho),?_,
    fun o ho => h.below o (List.mem_of_mem_filter ho)⟩
  intro slot request hr
  obtain ⟨o,ho,hi,hx⟩ := h.covered slot request hr
  exact ⟨o,List.mem_filter.mpr ⟨ho,by simpa [hi] using live slot request hr⟩,hi,hx⟩

/-- A terminal valid frame already carries the exact receipt to retain at release. -/
theorem terminal_request_receipt (state : Bool) (history : Peer) (request : Request)
    (valid : RequestValid state request) (coupled : RequestPeer history request)
    (done : terminal request.phase = true) :
    ∃ answer, request.receipt = some ⟨request.identity,answer⟩ ∧
      terminalAnswer answer = true ∧ ReceiptAuthentic history ⟨request.identity,answer⟩ := by
  cases phase : request.phase <;> simp [terminal,phase] at done
  · simp only [RequestValid,phase] at valid
    simp only [RequestPeer,phase] at coupled
    obtain ⟨output,present,receipt⟩ := valid.2.2
    obtain ⟨selected,selection,recorded⟩ := coupled
    have same : output = selected := Option.some.inj (present.symm.trans selection)
    subst selected
    exact ⟨.published request.input output,receipt,rfl,recorded⟩
  · simp only [RequestValid,phase] at valid
    exact ⟨.prevented request.input,valid.2,rfl,by simpa only [ReceiptAuthentic,RequestPeer,phase] using coupled⟩

theorem PoolSafe.released_not_live {frame : Frame} {history : Peer} {outcomes : List Outcome}
    (h : PoolSafe frame history outcomes) {o : Outcome} (ho : o ∈ outcomes)
    (released : o.released = true) {slot : Bool} {request : Request}
    (hr : request ∈ frame.requests.get slot) : request.identity ≠ o.identity :=
  (h.safe o ho).released released slot request hr

theorem PoolSafe.map_answer {frame : Frame} {history : Peer} {outcomes : List Outcome}
    (h : PoolSafe frame history outcomes) (predicate : Outcome → Bool) (answer : Answer)
    (terminal : terminalAnswer answer = true)
    (auth : ∀ o ∈ outcomes, predicate o = true → ReceiptAuthentic history ⟨o.identity,answer⟩) :
    PoolSafe frame history (outcomes.map fun o => if predicate o then {o with answer := some answer} else o) := by
  refine ⟨?_,?_,?_⟩
  · intro o ho
    obtain ⟨old,hold,rfl⟩ := List.mem_map.mp ho
    split
    · rename_i hp
      exact ⟨(h.safe old hold).origin,(h.safe old hold).released,
        by intro a ha; cases ha; exact ⟨terminal,auth old hold hp⟩⟩
    · exact h.safe old hold
  · intro slot request hr
    obtain ⟨o,ho,hi,hx⟩ := h.covered slot request hr
    refine ⟨if predicate o then {o with answer := some answer} else o,
      List.mem_map.mpr ⟨o,ho,rfl⟩,?_,?_⟩ <;> split <;> assumption
  · intro o ho
    obtain ⟨old,hold,rfl⟩ := List.mem_map.mp ho
    split <;> exact h.below old hold

theorem PoolSafe.remember {s : LocalSnapshot} {history : Peer}
    (h : PoolSafe s.frame history s.outcomes) (receipt : Receipt)
    (auth : ReceiptAuthentic history receipt) :
    PoolSafe (remember s receipt).frame history (remember s receipt).outcomes := by
  rw [remember_frame]
  rcases receipt with ⟨identity,answer⟩
  cases answer <;> dsimp [FRPSpec.PendingRetention.remember,terminalAnswer] <;> try exact h
  all_goals
    apply h.map_answer
    · rfl
    · intro o ho hp
      have hi : o.identity = identity := by
        simp only [Bool.and_eq_true,beq_iff_eq] at hp
        exact hp.1
      simpa [hi,ReceiptAuthentic] using auth

/-- Equality of occupied identity/input pairs ignores phase and evidence fields. -/
def SameNames (before after : Frame) : Prop :=
  ∀ slot, (before.requests.get slot).map (fun r => (r.identity,r.input)) =
    (after.requests.get slot).map (fun r => (r.identity,r.input))

theorem SameNames.request {before after : Frame} (same : SameNames before after)
    {slot : Bool} {request : Request} (present : after.requests.get slot = some request) :
    ∃ old, before.requests.get slot = some old ∧ old.identity = request.identity ∧ old.input = request.input := by
  have eq : (before.requests.get slot).map (fun r => (r.identity,r.input)) =
      some (request.identity,request.input) := (same slot).trans (by simp [present])
  obtain ⟨old,ho,he⟩ := Option.map_eq_some_iff.mp eq
  exact ⟨old,ho,(Prod.mk.inj he).1,(Prod.mk.inj he).2⟩

theorem SameNames.symm {before after : Frame} (same : SameNames before after) : SameNames after before :=
  fun slot => (same slot).symm

theorem OutcomeLive.names {before after : Frame} {o : Outcome}
    (same : SameNames before after) (h : OutcomeLive before o) : OutcomeLive after o := by
  obtain ⟨slot,request,hr,hi,hx⟩ := h
  obtain ⟨next,hn,hni,hnx⟩ := same.symm.request hr
  exact ⟨slot,next,hn,hni.trans hi,hnx.trans hx⟩

theorem PoolSafe.names {before after : Frame} {history : Peer} {outcomes : List Outcome}
    (h : PoolSafe before history outcomes) (same : SameNames before after)
    (counter : before.nextIdentity ≤ after.nextIdentity) : PoolSafe after history outcomes := by
  refine ⟨?_,?_,fun o ho => (h.below o ho).trans_le counter⟩
  · intro o ho
    refine ⟨(h.safe o ho).origin.imp_left (OutcomeLive.names same),?_,(h.safe o ho).authentic⟩
    intro released slot request hr
    obtain ⟨old,hold,hi,hx⟩ := same.request (by simpa using hr)
    rw [←hi]
    exact (h.safe o ho).released released slot old (by simp [hold])
  · intro slot request hr
    obtain ⟨old,hold,hi,hx⟩ := same.request (by simpa using hr)
    obtain ⟨o,ho,oi,ox⟩ := h.covered slot old (by simp [hold])
    exact ⟨o,ho,oi.trans hi,ox.trans hx⟩


theorem SameNames.update (frame : Frame) (slot : Bool) (old next : Request)
    (present : frame.requests.get slot = some old)
    (identity : next.identity = old.identity) (input : next.input = old.input) :
    SameNames frame (frame.update slot next) := by
  intro other
  by_cases eq : other = slot
  · subst other
    cases slot <;> simp_all [Frame.update,Slots.get,Slots.put]
  · cases slot <;> cases other <;> simp_all [Frame.update,Slots.get,Slots.put]

theorem receive_sameNames (before after : Frame) (receipt : Receipt)
    (changed : receive before receipt = .changed after) : SameNames before after := by
  rcases receipt with ⟨identity,answer⟩
  unfold receive at changed
  cases found : before.find identity with
  | none => simp [found] at changed
  | some pair =>
    rcases pair with ⟨slot,request⟩
    have present := (find_request_eq before identity slot request found).1
    simp only [found] at changed
    cases answer
    all_goals repeat' first
      | simp_all only [reduceCtorEq,Decision.changed.injEq]
      | split at changed
    all_goals subst after
    all_goals exact SameNames.update before slot request _ present rfl rfl

theorem propose_sameNames (before after : Frame) (command : FrameCommand)
    (notAccept : ∀ input, command ≠ .accept input) (notRelease : command ≠ .release)
    (changed : propose before command = .changed after) : SameNames before after := by
  cases command with
  | accept input => exact False.elim (notAccept input rfl)
  | release => exact False.elim (notRelease rfl)
  | receive receipt => exact receive_sameNames before after receipt changed
  | migrate kind => cases changed; exact fun _ => rfl
  | evaluate | tickCommit | close =>
    simp only [propose] at changed
    cases head : before.head with
    | none => simp [head] at changed
    | some pair =>
      rcases pair with ⟨slot,request⟩
      have present := head_request_eq before slot request head
      simp only [head] at changed
      split at changed
      · cases changed
        exact SameNames.update before slot request _ present rfl rfl
      · contradiction


theorem PoolSafe.accept {frame : Frame} {history : Peer} {outcomes : List Outcome}
    (h : PoolSafe frame history outcomes) (slot input : Bool)
    (free : frame.requests.get slot = none) :
    PoolSafe {frame with
      requests := frame.requests.put slot (some {identity := frame.nextIdentity,input := input})
      order := frame.order ++ [slot]
      nextIdentity := frame.nextIdentity + 1} history
      (outcomes ++ [{identity := frame.nextIdentity,input := input}]) := by
  let next : Request := {identity := frame.nextIdentity,input := input}
  have get (other : Bool) : (frame.requests.put slot (some next)).get other =
      if other = slot then some next else frame.requests.get other :=
    PendingMigration.slots_get_put _ _ _ _
  refine ⟨?_,?_,?_⟩
  · intro o ho
    rcases List.mem_append.mp ho with ho | ho
    · have safe := h.safe o ho
      refine ⟨?_,?_,safe.authentic⟩
      · rcases safe.origin with live | terminal
        · obtain ⟨other,request,hr,hi,hx⟩ := live
          have ne : other ≠ slot := by intro eq; subst other; simp [free] at hr
          exact Or.inl ⟨other,request,by simpa [next,get,ne] using hr,hi,hx⟩
        · exact Or.inr terminal
      · intro released other request hr
        by_cases eq : other = slot
        · subst other
          have he : request = next := by symm; simpa [next,get] using hr
          subst request
          have bound := h.below o ho
          dsimp [next]
          omega
        · apply safe.released released other request
          simpa [next,get,eq] using hr
    · have eq := List.mem_singleton.mp ho
      subst o
      refine ⟨Or.inl ⟨slot,next,by simp [next,get],rfl,rfl⟩,by simp,by simp⟩
  · intro other request hr
    by_cases eq : other = slot
    · subst other
      have he : request = next := by symm; simpa [next,get] using hr
      subst request
      exact ⟨⟨frame.nextIdentity,input,none,false⟩,by simp,rfl,rfl⟩
    · have old : request ∈ frame.requests.get other := by simpa [next,get,eq] using hr
      obtain ⟨o,ho,hi,hx⟩ := h.covered other request old
      exact ⟨o,List.mem_append_left _ ho,hi,hx⟩
  · intro o ho
    rcases List.mem_append.mp ho with ho | ho
    · exact Nat.lt_succ_of_lt (h.below o ho)
    · cases List.mem_singleton.mp ho
      exact Nat.lt_succ_self _


theorem terminal_request (history : Peer) (request : Request)
    (coupled : RequestPeer history request) (done : terminal request.phase = true) :
    OutcomeTerminal history ⟨request.identity,request.input,none,false⟩ := by
  cases phase : request.phase <;> simp [terminal,phase] at done
  · simp only [RequestPeer,phase] at coupled
    obtain ⟨output,_,found⟩ := coupled
    exact Or.inr ⟨output,found⟩
  · exact Or.inl (by simpa only [ReceiptAuthentic,RequestPeer,phase] using coupled)

theorem PoolSafe.release {frame : Frame} {history : Peer} {outcomes : List Outcome}
    (h : PoolSafe frame history outcomes) (valid : frame.Valid)
    (slot : Bool) (request : Request) (present : frame.requests.get slot = some request)
    (coupled : RequestPeer history request) (done : terminal request.phase = true) :
    PoolSafe {frame with requests := frame.requests.put slot none,order := frame.order.tail} history
      (outcomes.map fun o => if o.identity == request.identity then {o with released := true, answer := request.receipt.map (·.answer)} else o) := by
  have remaining (other : Bool) (r : Request)
      (hr : r ∈ (frame.requests.put slot none).get other) :
      r ∈ frame.requests.get other ∧ r.identity ≠ request.identity := by
    by_cases eq : other = slot
    · subst other
      simp at hr
    · have old : r ∈ frame.requests.get other := by simpa [PendingMigration.slots_get_put,eq] using hr
      exact ⟨old,frame_valid_identity_separate frame slot other request r valid eq present old⟩
  have terminal := terminal_request history request coupled done
  have origin (o : Outcome) (ho : o ∈ outcomes) :
      OutcomeLive {frame with requests := frame.requests.put slot none,order := frame.order.tail} o ∨
        OutcomeTerminal history o := by
    rcases (h.safe o ho).origin with live | terminal
    · obtain ⟨other,r,hr,hi,hx⟩ := live
      by_cases eq : other = slot
      · subst other
        have he : r = request := Option.some.inj (hr.symm.trans present)
        subst r
        exact Or.inr (by simpa [OutcomeTerminal,hi,hx] using terminal)
      · exact Or.inl ⟨other,r,by simpa [PendingMigration.slots_get_put,eq] using hr,hi,hx⟩
    · exact Or.inr terminal
  refine ⟨?_,?_,?_⟩
  · intro o ho
    obtain ⟨old,hold,rfl⟩ := List.mem_map.mp ho
    split
    · rename_i same
      have same : old.identity = request.identity := by simpa using same
      refine ⟨origin old hold,?_,?_⟩
      · intro _ other r hr
        simpa [same] using (remaining other r hr).2
      · obtain ⟨answer,receipt,terminal,authentic⟩ := terminal_request_receipt frame.logical
          history request ((valid.2.2.2.1 slot request (by simp [present])).2.1) coupled done
        intro a ha
        simp only [receipt,Option.map_some,Option.mem_some_iff] at ha
        subst a
        exact ⟨terminal,by simpa only [same] using authentic⟩
    · refine ⟨origin old hold,?_,(h.safe old hold).authentic⟩
      intro released other r hr
      exact (h.safe old hold).released released other r (remaining other r hr).1
  · intro other r hr
    obtain ⟨o,ho,hi,hx⟩ := h.covered other r (remaining other r hr).1
    refine ⟨if o.identity == request.identity then {o with released := true, answer := request.receipt.map (·.answer)} else o,
      List.mem_map.mpr ⟨o,ho,rfl⟩,?_,?_⟩ <;> split <;> assumption
  · intro o ho
    obtain ⟨old,hold,rfl⟩ := List.mem_map.mp ho
    split <;> exact h.below old hold


theorem remember_outcomes_eq (s t : LocalSnapshot) (receipt : Receipt)
    (same : s.outcomes = t.outcomes) :
    (FRPSpec.PendingRetention.remember s receipt).outcomes =
      (FRPSpec.PendingRetention.remember t receipt).outcomes := by
  rcases receipt with ⟨identity,answer⟩
  cases answer <;> simp [FRPSpec.PendingRetention.remember,terminalAnswer,same]


def changedOutcomes (s : LocalSnapshot) : FrameCommand → List Outcome
  | .accept input => s.outcomes ++ [⟨s.frame.nextIdentity,input,none,false⟩]
  | .release => match s.frame.head with
    | none => s.outcomes
    | some (_,r) => s.outcomes.map fun o => if o.identity == r.identity then {o with released := true, answer := r.receipt.map (·.answer)} else o
  | .receive receipt => (FRPSpec.PendingRetention.remember s receipt).outcomes
  | _ => s.outcomes

theorem localChange_outcomes {cfg : Config} {s t : LocalSnapshot} {c : FrameCommand}
    (changed : localChange cfg s c = .ok t) : t.outcomes = changedOutcomes s c := by
  have core : localChangeCore cfg s c = .ok t := by
    unfold localChange at changed
    split at changed <;> try contradiction
    split at changed <;> try contradiction
    cases changed
    assumption
  cases advanced : advance s.frame c with
  | refused | stopped =>
    cases c <;> simp only [localChangeCore,advanced] at core
    all_goals repeat' split at core
    all_goals contradiction
  | changed frame =>
    cases c <;> simp only [localChangeCore,advanced] at core
    all_goals repeat' split at core
    all_goals first | contradiction | (cases core; try rfl)
    all_goals try simp_all only [changedOutcomes]
    all_goals exact remember_outcomes_eq _ _ _ rfl


theorem PoolSafe.propose_accept {before after : Frame} {history : Peer} {outcomes : List Outcome}
    (h : PoolSafe before history outcomes) (input : Bool)
    (changed : propose before (.accept input) = .changed after) :
    PoolSafe after history (outcomes ++ [⟨before.nextIdentity,input,none,false⟩]) := by
  simp only [propose] at changed
  repeat' first | split at changed | contradiction
  all_goals cases changed
  all_goals apply h.accept
  all_goals
    rename_i free slot found
    split at found
    · cases found; simpa using ‹(before.requests.get false).isNone = true›
    · split at found
      · cases found; simpa using ‹(before.requests.get true).isNone = true›
      · contradiction

theorem PoolSafe.localChange {cfg : Config} {s t : LocalSnapshot} {history : Peer}
    (h : PoolSafe s.frame history s.outcomes) (valid : s.frame.Valid)
    (coupled : FramePeer s.frame history) (command : FrameCommand)
    (auth : CommandAuthentic history command)
    (changed : localChange cfg s command = .ok t) : PoolSafe t.frame history t.outcomes := by
  have proposed := localChange_proposed changed
  have counter : s.frame.nextIdentity ≤ t.frame.nextIdentity := by
    rw [propose_nextIdentity s.frame t.frame command proposed]
    omega
  rw [localChange_outcomes changed]
  cases command with
  | accept input => exact h.propose_accept input proposed
  | release =>
    cases head : s.frame.head with
    | none => simp [propose,head] at proposed
    | some pair =>
      rcases pair with ⟨slot,request⟩
      have present := head_request_eq s.frame slot request head
      simp only [propose,head] at proposed
      split at proposed
      · rename_i done
        have eq := Decision.changed.inj proposed
        rw [←eq]
        simp only [changedOutcomes,head]
        apply h.release valid slot request present (coupled slot request (by simp [present]))
        simp only [Bool.and_eq_true] at done
        exact done.1
      · contradiction
  | receive receipt =>
    have remembered := h.remember receipt auth
    rw [remember_frame] at remembered
    exact remembered.names (propose_sameNames _ _ _ (by simp) (by simp) proposed) counter
  | evaluate | tickCommit | close | migrate target =>
    exact h.names (propose_sameNames _ _ _ (by simp) (by simp) proposed) counter


theorem relinquishable_record {s : LocalSnapshot} {target identity : Nat}
    (checked : relinquishable s target = true) (lower : s.floor ≤ identity)
    (upper : identity < target) :
    ∃ o ∈ s.outcomes, o.identity = identity ∧ o.released = true ∧
      ∃ answer ∈ o.answer, terminalAnswer answer = true := by
  simp only [relinquishable,Bool.and_eq_true,decide_eq_true_eq] at checked
  have visit := List.all_eq_true.mp checked.2 (identity - s.floor)
    (List.mem_range.mpr (by omega))
  have eq : s.floor + (identity - s.floor) = identity := by omega
  rw [eq] at visit
  cases found : outcome s identity with
  | none => simp [found] at visit
  | some o =>
    simp only [found,Bool.and_eq_true] at visit
    obtain ⟨ho,hi⟩ := outcome_found found
    refine ⟨o,ho,hi,visit.1,?_⟩
    cases ha : o.answer with
    | none => simp [ha] at visit
    | some answer => exact ⟨answer,by simp,by simpa [ha] using visit.2⟩

theorem PoolSafe.relinquishable_live {s : LocalSnapshot} {history : Peer}
    (h : PoolSafe s.frame history s.outcomes) (target : Nat)
    (checked : relinquishable s target = true)
    (old : ∀ slot request, request ∈ s.frame.requests.get slot → s.floor ≤ request.identity) :
    ∀ slot request, request ∈ s.frame.requests.get slot → target ≤ request.identity := by
  intro slot request hr
  by_contra below
  obtain ⟨o,ho,hi,released,_⟩ := relinquishable_record checked (old slot request hr) (by omega)
  exact (h.safe o ho).released released slot request hr hi.symm

theorem PoolSafe.relinquish {s t : LocalSnapshot} {history : Peer}
    (h : PoolSafe s.frame history s.outcomes) (target : Nat)
    (changed : relinquish s target = .ok t) : PoolSafe t.frame history t.outcomes := by
  unfold FRPSpec.PendingRetention.relinquish at changed
  repeat' split at changed
  all_goals first | contradiction | (cases changed; exact h)

theorem PoolSafe.finishRetirement {s t : LocalSnapshot} {history : Peer}
    (h : PoolSafe s.frame history s.outcomes) (target : Nat)
    (live : ∀ slot request, request ∈ s.frame.requests.get slot → target ≤ request.identity)
    (changed : finishRetirement s target = some t) : PoolSafe t.frame history t.outcomes := by
  unfold FRPSpec.PendingRetention.finishRetirement at changed
  split at changed
  · cases changed
    exact h.filter target live
  · contradiction


theorem propose_live_above (before after : Frame) (command : FrameCommand) (floor : Nat)
    (live : ∀ slot request, request ∈ before.requests.get slot → floor ≤ request.identity)
    (counter : floor ≤ before.nextIdentity) (changed : propose before command = .changed after) :
    ∀ slot request, request ∈ after.requests.get slot → floor ≤ request.identity := by
  by_cases accept : ∃ input, command = .accept input
  · obtain ⟨input,rfl⟩ := accept
    simp only [propose] at changed
    repeat' first | split at changed | contradiction
    all_goals cases changed
    all_goals intro slot request present
    all_goals simp only [PendingMigration.slots_get_put] at present
    all_goals split at present
    all_goals first
      | (simp only [Option.mem_some_iff] at present; cases present; exact counter)
      | exact live slot request present
  · by_cases release : command = .release
    · subst command
      simp only [propose] at changed
      cases head : before.head with
      | none => simp [head] at changed
      | some pair =>
        rcases pair with ⟨slot,request⟩
        simp only [head] at changed
        split at changed
        · cases changed
          intro other r present
          simp only [PendingMigration.slots_get_put] at present
          split at present
          · simp at present
          · exact live other r present
        · contradiction
    · have same := propose_sameNames before after command
        (fun input eq => accept ⟨input,eq⟩) release changed
      intro slot request present
      obtain ⟨old,ho,hi,_⟩ := same.request (by simpa using present)
      rw [←hi]
      exact live slot old (by simp [ho])

theorem localChange_live_above {cfg : Config} {s t : LocalSnapshot} {command : FrameCommand}
    (floor : Nat)
    (live : ∀ slot request, request ∈ s.frame.requests.get slot → floor ≤ request.identity)
    (counter : floor ≤ s.frame.nextIdentity) (changed : localChange cfg s command = .ok t) :
    ∀ slot request, request ∈ t.frame.requests.get slot → floor ≤ request.identity :=
  propose_live_above _ _ _ floor live counter (localChange_proposed changed)

/-- This form consumes a cursor's already checked prefix without materializing
an interval list in the runtime. -/
theorem PoolSafe.checked_prefix_live {s : LocalSnapshot} {history : Peer}
    (h : PoolSafe s.frame history s.outcomes) (target : Nat)
    (checked : ∀ identity, s.floor ≤ identity → identity < target →
      ∃ o ∈ s.outcomes, o.identity = identity ∧ o.released = true)
    (old : ∀ slot request, request ∈ s.frame.requests.get slot → s.floor ≤ request.identity) :
    ∀ slot request, request ∈ s.frame.requests.get slot → target ≤ request.identity := by
  intro slot request present
  by_contra below
  obtain ⟨o,ho,hi,released⟩ := checked request.identity (old slot request present) (by omega)
  exact (h.safe o ho).released released slot request present hi.symm


namespace OutcomeExamples

def config : Config := ⟨4,3,1⟩
def accepted : LocalSnapshot :=
  {frame := {initialFrame with
      requests := {left := some {identity := 0,input := true}}
      order := [false]
      nextIdentity := 1}
   outcomes := [⟨0,true,none,false⟩]}

/-- A fresh actual bounded admission creates both occupied coverage and its
reserved outcome; no receipt or terminal origin is assumed. -/
theorem accepted_pool : PoolSafe accepted.frame [] accepted.outcomes :=
  PoolSafe.localChange (cfg := config) (s := {}) PoolSafe.initial (by decide) (FramePeer.initial .delay)
    (.accept true) trivial (by decide)

def terminalRequest : Request :=
  ⟨0,true,some false,some ⟨0,.published true false⟩,.committed,false⟩
def publishedHistory : Peer := [(0,.published true false)]
def beforeRelease : LocalSnapshot :=
  {frame := {initialFrame with
      logical := true
      requests := {left := some terminalRequest}
      order := [false]
      nextIdentity := 1}
   outcomes := [⟨0,true,some (.published true false),false⟩]}
def afterRelease : LocalSnapshot :=
  {frame := {initialFrame with logical := true,nextIdentity := 1}
   outcomes := [⟨0,true,some (.published true false),true⟩]}

theorem beforeRelease_pool : PoolSafe beforeRelease.frame publishedHistory beforeRelease.outcomes := by
  refine ⟨?_,?_,?_⟩
  · intro o ho
    simp only [beforeRelease,List.mem_singleton] at ho
    subst o
    refine ⟨Or.inl ⟨false,terminalRequest,rfl,rfl,rfl⟩,by simp,?_⟩
    intro answer ha
    cases ha
    exact ⟨rfl,rfl⟩
  · intro slot request hr
    cases slot
    · have eq : request = terminalRequest := by simpa [beforeRelease,Slots.get,eq_comm] using hr
      subst request
      exact ⟨⟨0,true,some (.published true false),false⟩,by simp [beforeRelease],rfl,rfl⟩
    · simp [beforeRelease,Slots.get] at hr
  · intro o ho
    simp only [beforeRelease,List.mem_singleton] at ho
    subst o
    decide

theorem beforeRelease_peer : FramePeer beforeRelease.frame publishedHistory := by
  intro slot request hr
  cases slot
  · have eq : request = terminalRequest := by simpa [beforeRelease,Slots.get,eq_comm] using hr
    subst request
    exact ⟨false,rfl,rfl⟩
  · simp [beforeRelease,Slots.get] at hr

/-- Release drops the live slot, not the retained result or its terminal origin. -/
theorem released_pool : PoolSafe afterRelease.frame publishedHistory afterRelease.outcomes :=
  beforeRelease_pool.localChange (cfg := config) (by decide) beforeRelease_peer .release trivial (by decide)

example : query afterRelease 0 = .terminal (.published true false) := by decide
example : relinquishable accepted 1 = false := by decide
example : relinquishable afterRelease 1 = true := by decide
example (slot : Bool) (request : Request) (present : request ∈ afterRelease.frame.requests.get slot) :
    1 ≤ request.identity :=
  released_pool.relinquishable_live 1 (by decide) (fun _ _ _ => Nat.zero_le _) slot request present

end OutcomeExamples


end FRPSpec.PendingRetention

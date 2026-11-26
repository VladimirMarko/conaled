import Applications.FRP.PendingRetention.Outcomes

namespace FRPSpec.PendingRetention
open PendingCrash
set_option autoImplicit false

/-- Retained names have one observation record. A record that has left the
live frame retains a terminal answer until explicit relinquishment. -/
structure PoolObserved (frame : Frame) (floor : Nat) (outcomes : List Outcome) : Prop where
  unique : (outcomes.map Outcome.identity).Nodup
  covered : ∀ identity, floor ≤ identity → identity < frame.nextIdentity →
    ∃ record ∈ outcomes, record.identity = identity
  status : ∀ record ∈ outcomes, OutcomeLive frame record ∨ record.released = true
  completed : ∀ record ∈ outcomes, record.released = true →
    ∃ answer, record.answer = some answer ∧ terminalAnswer answer = true

theorem PoolObserved.initial (kind : Migration.Kind) :
    PoolObserved (initialFrame kind) 0 [] := by
  constructor <;> simp [initialFrame]

theorem PoolObserved.names {before after : Frame} {floor : Nat} {outcomes : List Outcome}
    (h : PoolObserved before floor outcomes) (same : SameNames before after)
    (counter : after.nextIdentity = before.nextIdentity) : PoolObserved after floor outcomes := by
  exact ⟨h.unique,by simpa only [counter] using h.covered,
    fun record member => (h.status record member).imp_left (OutcomeLive.names same),h.completed⟩

theorem PoolObserved.map {before after : Frame} {floor : Nat} {outcomes : List Outcome}
    (h : PoolObserved before floor outcomes) (f : Outcome → Outcome)
    (counter : after.nextIdentity = before.nextIdentity)
    (identity : ∀ record ∈ outcomes, (f record).identity = record.identity)
    (status : ∀ record ∈ outcomes, OutcomeLive after (f record) ∨ (f record).released = true)
    (complete : ∀ record ∈ outcomes, (f record).released = true →
      ∃ answer, (f record).answer = some answer ∧ terminalAnswer answer = true) :
    PoolObserved after floor (outcomes.map f) := by
  refine ⟨?_,?_,?_,?_⟩
  · have names : (outcomes.map f).map Outcome.identity = outcomes.map Outcome.identity := by
      rw [List.map_map]
      exact List.map_congr_left identity
    rw [names]
    exact h.unique
  · intro name lower upper
    obtain ⟨record,member,equal⟩ := h.covered name lower (counter ▸ upper)
    exact ⟨f record,List.mem_map.mpr ⟨record,member,rfl⟩,(identity record member).trans equal⟩
  · intro record member
    obtain ⟨old,oldMember,rfl⟩ := List.mem_map.mp member
    exact status old oldMember
  · intro record member
    obtain ⟨old,oldMember,rfl⟩ := List.mem_map.mp member
    exact complete old oldMember

theorem PoolObserved.raise_local {frame : Frame} {floor target : Nat} {outcomes : List Outcome}
    (h : PoolObserved frame floor outcomes) (increasing : floor ≤ target) :
    PoolObserved frame target outcomes :=
  ⟨h.unique,fun name lower upper => h.covered name (increasing.trans lower) upper,h.status,h.completed⟩

theorem PoolObserved.filter {frame : Frame} {floor : Nat} {outcomes : List Outcome}
    (h : PoolObserved frame floor outcomes) :
    PoolObserved frame floor (outcomes.filter fun record => floor ≤ record.identity) := by
  refine ⟨?_,?_,?_,?_⟩
  · exact List.Nodup.sublist (List.Sublist.map Outcome.identity List.filter_sublist) h.unique
  · intro name lower upper
    obtain ⟨record,member,equal⟩ := h.covered name lower upper
    exact ⟨record,List.mem_filter.mpr ⟨member,by simpa [equal] using lower⟩,equal⟩
  · intro record member
    exact h.status record (List.mem_filter.mp member).1
  · intro record member
    exact h.completed record (List.mem_filter.mp member).1

theorem remember_floor (s : LocalSnapshot) (receipt : Receipt) :
    (remember s receipt).floor = s.floor := by
  unfold FRPSpec.PendingRetention.remember
  split <;> dsimp only <;> split <;> rfl

theorem PoolObserved.map_answer {frame : Frame} {floor : Nat} {outcomes : List Outcome}
    (h : PoolObserved frame floor outcomes) (answer : Answer) (predicate : Outcome → Bool)
    (terminal : terminalAnswer answer = true) :
    PoolObserved frame floor (outcomes.map fun record =>
      if predicate record then {record with answer := some answer} else record) := by
  apply h.map (after := frame) _ rfl
  · intro record member; split <;> rfl
  · intro record member; split <;> exact h.status record member
  · intro record member
    split
    · intro _; exact ⟨answer,rfl,terminal⟩
    · exact h.completed record member

theorem PoolObserved.remember {s : LocalSnapshot}
    (h : PoolObserved s.frame s.floor s.outcomes) (receipt : Receipt) :
    PoolObserved (remember s receipt).frame (remember s receipt).floor (remember s receipt).outcomes := by
  rw [remember_frame,remember_floor]
  rcases receipt with ⟨identity,answer⟩
  cases answer <;> dsimp [FRPSpec.PendingRetention.remember,terminalAnswer] <;> try exact h
  all_goals apply h.map_answer; rfl

theorem PoolObserved.accept {frame : Frame} {floor : Nat} {outcomes : List Outcome}
    (h : PoolObserved frame floor outcomes) (below : ∀ o ∈ outcomes, o.identity < frame.nextIdentity)
    (slot input : Bool) (free : frame.requests.get slot = none) :
    PoolObserved {frame with
      requests := frame.requests.put slot (some {identity := frame.nextIdentity,input := input})
      order := frame.order ++ [slot]
      nextIdentity := frame.nextIdentity + 1} floor
      (outcomes ++ [{identity := frame.nextIdentity,input := input}]) := by
  let next : Request := {identity := frame.nextIdentity,input := input}
  have get (other : Bool) : (frame.requests.put slot (some next)).get other =
      if other = slot then some next else frame.requests.get other :=
    PendingMigration.slots_get_put _ _ _ _
  refine ⟨?_,?_,?_,?_⟩
  · simp only [List.map_append,List.map_cons,List.map_nil,List.nodup_append]
    refine ⟨h.unique,by simp,?_⟩
    intro name member other singleton
    obtain ⟨record,oldMember,rfl⟩ := List.mem_map.mp member
    have equal : other = frame.nextIdentity := by simpa using singleton
    have bound := below record oldMember
    simpa [equal] using Nat.ne_of_lt bound
  · intro name lower upper
    by_cases fresh : name = frame.nextIdentity
    · exact ⟨⟨frame.nextIdentity,input,none,false⟩,by simp,by simpa using fresh.symm⟩
    · obtain ⟨record,member,equal⟩ := h.covered name lower (by dsimp at upper; omega)
      exact ⟨record,List.mem_append_left _ member,equal⟩
  · intro record member
    rcases List.mem_append.mp member with member | member
    · rcases h.status record member with live | released
      · obtain ⟨other,request,present,identity,value⟩ := live
        have different : other ≠ slot := by intro equal; subst other; simp [free] at present
        exact Or.inl ⟨other,request,by simpa [next,get,different] using present,identity,value⟩
      · exact Or.inr released
    · cases List.mem_singleton.mp member
      exact Or.inl ⟨slot,next,by simp [next,get],rfl,rfl⟩
  · intro record member released
    rcases List.mem_append.mp member with member | member
    · exact h.completed record member released
    · cases List.mem_singleton.mp member
      contradiction

theorem PoolObserved.release {frame : Frame} {floor : Nat} {outcomes : List Outcome}
    {history : Peer} (h : PoolObserved frame floor outcomes) (valid : frame.Valid)
    (slot : Bool) (request : Request) (present : frame.requests.get slot = some request)
    (coupled : RequestPeer history request) (done : terminal request.phase = true) :
    PoolObserved {frame with requests := frame.requests.put slot none,order := frame.order.tail} floor
      (outcomes.map fun o => if o.identity == request.identity then
        {o with released := true, answer := request.receipt.map (·.answer)} else o) := by
  apply h.map (after := {frame with requests := frame.requests.put slot none,order := frame.order.tail}) _ rfl
  · intro record member; split <;> rfl
  · intro record member
    split
    · exact Or.inr rfl
    · rename_i different
      rcases h.status record member with live | released
      · obtain ⟨other,r,found,identity,value⟩ := live
        have otherSlot : other ≠ slot := by
          intro equal; subst other
          have equal : r = request := Option.some.inj (found.symm.trans present)
          subst r
          simp [identity] at different
        exact Or.inl ⟨other,r,by simpa [PendingMigration.slots_get_put,otherSlot] using found,identity,value⟩
      · exact Or.inr released
  · intro record member
    split
    · intro _
      obtain ⟨answer,receipt,terminal,_⟩ := terminal_request_receipt frame.logical
        history request ((valid.2.2.2.1 slot request (by simp [present])).2.1) coupled done
      exact ⟨answer,by simp [receipt],terminal⟩
    · exact h.completed record member

theorem PoolObserved.propose_accept {before after : Frame} {floor : Nat} {outcomes : List Outcome}
    (h : PoolObserved before floor outcomes) (below : ∀ o ∈ outcomes, o.identity < before.nextIdentity)
    (input : Bool) (changed : propose before (.accept input) = .changed after) :
    PoolObserved after floor (outcomes ++ [⟨before.nextIdentity,input,none,false⟩]) := by
  simp only [propose] at changed
  repeat' first | split at changed | contradiction
  all_goals cases changed
  all_goals apply h.accept below
  all_goals
    rename_i free slot found
    split at found
    · cases found; simpa using ‹(before.requests.get false).isNone = true›
    · split at found
      · cases found; simpa using ‹(before.requests.get true).isNone = true›
      · contradiction

theorem PoolObserved.localChange {cfg : Config} {s t : LocalSnapshot} {history : Peer}
    (h : PoolObserved s.frame s.floor s.outcomes) (pool : PoolSafe s.frame history s.outcomes)
    (valid : s.frame.Valid) (coupled : FramePeer s.frame history) (command : FrameCommand)
    (changed : localChange cfg s command = .ok t) : PoolObserved t.frame t.floor t.outcomes := by
  have proposed := localChange_proposed changed
  have counter := propose_nextIdentity s.frame t.frame command proposed
  rw [localChange_outcomes changed,(localChange_metadata changed).1]
  cases command with
  | accept input => exact h.propose_accept pool.below input proposed
  | release =>
    cases head : s.frame.head with
    | none => simp [propose,head] at proposed
    | some pair =>
      rcases pair with ⟨slot,request⟩
      have present := head_request_eq s.frame slot request head
      simp only [propose,head] at proposed
      split at proposed
      · rename_i done
        have equal := Decision.changed.inj proposed
        rw [←equal]
        simp only [changedOutcomes,head]
        apply h.release valid slot request present (coupled slot request (by simp [present]))
        simp only [Bool.and_eq_true] at done
        exact done.1
      · contradiction
  | receive receipt =>
    have remembered := h.remember receipt
    rw [remember_frame,remember_floor] at remembered
    have same := propose_sameNames _ _ _ (by simp) (by simp) proposed
    apply remembered.names same
    simpa [admissionDelta] using counter
  | evaluate | tickCommit | close | migrate target =>
    apply h.names (propose_sameNames _ _ _ (by simp) (by simp) proposed)
    simpa [admissionDelta] using counter

theorem PoolObserved.finishRetirement {s t : LocalSnapshot} {target : Nat}
    (h : PoolObserved s.frame s.floor s.outcomes)
    (pending : ∀ target ∈ s.pending, target = s.floor)
    (finished : finishRetirement s target = some t) : PoolObserved t.frame t.floor t.outcomes := by
  unfold FRPSpec.PendingRetention.finishRetirement at finished
  split at finished
  · rename_i matched
    have equal : s.pending = some target := by simpa using matched
    have floor := pending target (by simp [equal])
    cases finished
    simpa only [floor] using h.filter
  · contradiction

/-- Every allocated name above the explicit retirement floor remains known. -/
theorem PoolObserved.query_known {s : LocalSnapshot} (h : PoolObserved s.frame s.floor s.outcomes)
    (identity : Nat) (lower : s.floor ≤ identity) (upper : identity < s.frame.nextIdentity) :
    query s identity ≠ .unknown := by
  obtain ⟨record,member,equal⟩ := h.covered identity lower upper
  have found : (outcome s identity).isSome = true := by
    simpa [outcome,List.find?_isSome] using
      (show ∃ r ∈ s.outcomes, (r.identity == identity) = true from ⟨record,member,by simp [equal]⟩)
  cases result : outcome s identity with
  | none => simp [result] at found
  | some record => cases answer : record.answer <;> simp [query,result,answer,Nat.not_lt.mpr lower]

/-- A retained name that is no longer live keeps a terminal observation. -/
theorem PoolObserved.query_completed {s : LocalSnapshot}
    (h : PoolObserved s.frame s.floor s.outcomes) (identity : Nat)
    (lower : s.floor ≤ identity) (upper : identity < s.frame.nextIdentity)
    (notLive : ∀ record ∈ s.outcomes, record.identity = identity → ¬OutcomeLive s.frame record) :
    ∃ answer, query s identity = .terminal answer ∧ terminalAnswer answer = true := by
  cases found : outcome s identity with
  | none => exact False.elim (h.query_known identity lower upper (by simp [query,found,Nat.not_lt.mpr lower]))
  | some record =>
    obtain ⟨member,equal⟩ := outcome_found found
    have released := (h.status record member).resolve_left (notLive record member equal)
    obtain ⟨answer,present,terminal⟩ := h.completed record member released
    exact ⟨answer,by simp [query,found,present,Nat.not_lt.mpr lower],terminal⟩

theorem PoolSafe.query_authentic {s : LocalSnapshot} {history : Peer} {identity : Nat} {answer : Answer}
    (safe : PoolSafe s.frame history s.outcomes) (lower : s.floor ≤ identity)
    (result : query s identity = .terminal answer) : ReceiptAuthentic history ⟨identity,answer⟩ := by
  cases found : outcome s identity with
  | none => simp [query,found,Nat.not_lt.mpr lower] at result
  | some record =>
    obtain ⟨member,equal⟩ := outcome_found found
    cases stored : record.answer with
    | none => simp [query,found,stored,Nat.not_lt.mpr lower] at result
    | some value =>
      have same : value = answer := by simpa [query,found,stored,Nat.not_lt.mpr lower] using result
      subst value
      simpa only [equal] using ((safe.safe record member).authentic answer (by simp [stored])).2

namespace ObservationExamples
open OutcomeExamples

/-- A terminal head can exist before any query result was remembered. -/
def unremembered : LocalSnapshot :=
  {beforeRelease with outcomes := [⟨0,true,none,false⟩]}

theorem unremembered_observed :
    PoolObserved unremembered.frame unremembered.floor unremembered.outcomes := by
  refine ⟨by decide,?_,?_,?_⟩
  · intro identity lower upper
    have equal : identity = 0 := by change identity < 1 at upper; omega
    subst identity
    exact ⟨⟨0,true,none,false⟩,by simp [unremembered],rfl⟩
  · intro record member
    have equal : record = ⟨0,true,none,false⟩ := by simpa [unremembered] using member
    subst record
    exact Or.inl ⟨false,terminalRequest,rfl,rfl,rfl⟩
  · intro record member
    have equal : record = ⟨0,true,none,false⟩ := by simpa [unremembered] using member
    subst record
    simp

theorem release_populates_answer : localChange config unremembered .release = .ok afterRelease := by decide

theorem released_observed : PoolObserved afterRelease.frame afterRelease.floor afterRelease.outcomes := by
  exact unremembered_observed.release (by decide) false terminalRequest rfl
    (by exact ⟨false,rfl,rfl⟩ : RequestPeer publishedHistory terminalRequest) rfl

example : query afterRelease 0 ≠ .unknown := released_observed.query_known 0 (by decide) (by decide)
example : query afterRelease 0 = .terminal (.published true false) := by decide
example : query {afterRelease with floor := 1} 0 = .expired 1 := by decide

end ObservationExamples
end FRPSpec.PendingRetention

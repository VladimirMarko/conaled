import Applications.FRP.RegionalPendingSource

/-! External peer transitions transport joined payloads through the bounded
ordered protocol. Accepted request outputs are unobservable dummy fields. -/
namespace FRPSpec.Regional.Pending
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 200000

private def eraseAccepted (r : PendingMigration.Request) : PendingMigration.Request :=
  {r with output := if r.phase == .accepted then false else r.output}

private def eraseSession (s : PendingMigration.Session) : PendingMigration.Session :=
  {s with requests := mapSlots eraseAccepted s.requests}

private theorem erase_slot (b : Bool) (r : Option PendingMigration.Request)
    (p : Option PendingMigration.Ledger) :
    PendingMigration.SlotValid b (r.map eraseAccepted) p ↔ PendingMigration.SlotValid b r p := by
  cases r with
  | none => rfl
  | some r =>
    cases p with
    | none => rfl
    | some p => cases h : r.phase <;> simp [PendingMigration.SlotValid,eraseAccepted,h]

private theorem erase_message (s : PendingMigration.Session)
    (slots : ∀ slot, PendingMigration.SlotValid s.active.logical (s.requests.get slot) (s.peer.get slot))
    (m : PendingMigration.Message) :
    PendingMigration.MessageValid (eraseSession s) m ↔ PendingMigration.MessageValid s m := by
  unfold PendingMigration.MessageValid
  simp only [eraseSession,get_mapSlots]
  cases hr : s.requests.get m.slot with
  | none => simp
  | some r =>
    have hs := slots m.slot
    rw [hr] at hs
    cases hp : s.peer.get m.slot with
    | none => simp [hp,PendingMigration.SlotValid] at hs
    | some p =>
      rw [hp] at hs
      cases m <;> cases phase : r.phase <;>
        simp_all [eraseAccepted,PendingMigration.SlotValid,PendingMigration.Message.slot]

private theorem erase_valid (s : PendingMigration.Session) :
    PendingMigration.Valid (eraseSession s) ↔ PendingMigration.Valid s := by
  constructor
  · intro h
    have slots : ∀ slot, PendingMigration.SlotValid s.active.logical (s.requests.get slot) (s.peer.get slot) := by
      intro slot
      exact (erase_slot _ _ _).mp (by simpa [eraseSession] using h.slots slot)
    refine ⟨h.order,?_,slots,?_,?_⟩
    · intro slot
      simpa [eraseSession] using h.occupied slot
    · intro slot member r hr
      have ht := h.tail slot member (eraseAccepted r) (by simp [eraseSession,hr])
      simpa [eraseAccepted] using ht
    · intro m hm
      exact (erase_message s slots m).mp (h.messages m hm)
  · intro h
    refine ⟨h.order,?_,?_,?_,?_⟩
    · intro slot
      simpa [eraseSession] using h.occupied slot
    · intro slot
      simpa only [eraseSession,get_mapSlots] using (erase_slot _ _ _).mpr (h.slots slot)
    · intro slot member r hr
      simp only [eraseSession,get_mapSlots,Option.map_eq_some_iff] at hr
      obtain ⟨original,ho,rfl⟩ := hr
      simpa [eraseAccepted] using h.tail slot member original ho
    · intro m hm
      exact (erase_message s h.slots m).mpr (h.messages m hm)

private def uniformRequest (r : PendingMigration.Request) : PendingMigration.Request :=
  {r with output := payload r.input r.output}

private def uniformProjection (s : PendingMigration.Session) : PendingMigration.Session :=
  {s with
    requests := mapSlots uniformRequest s.requests
    peer := mapSlots ownLedger s.peer
    queue := ⟨s.queue.messages.map (fun m => messagePayload (ownerInput s m.slot) m),
      by simpa using s.queue.bounded⟩}

private theorem erase_uniform (s : PendingMigration.Session) :
    eraseSession (uniformProjection s) = delayProjection s := by
  have req : mapSlots eraseAccepted (mapSlots uniformRequest s.requests) =
      mapSlots requestPayload s.requests := by
    cases s.requests with
    | mk first second =>
      cases first <;> cases second <;>
        simp [mapSlots,eraseAccepted,uniformRequest,requestPayload]
  simp only [eraseSession,uniformProjection,delayProjection,req]

/-- Uniform transport is equivalent to the public invariant even though accepted
outputs differ. No cancelled or published payload is discarded by this lemma. -/
private theorem uniform_valid (s : PendingMigration.Session) :
    PendingMigration.Valid (uniformProjection s) ↔ PendingMigration.Valid (delayProjection s) := by
  rw [← erase_uniform]
  exact (erase_valid _).symm

private theorem uniform_head (s : PendingMigration.Session) (second : Bool := false) :
    PendingMigration.head (uniformProjection s) second =
      (PendingMigration.head s second).map (fun p => (p.1,uniformRequest p.2)) := by
  simp only [PendingMigration.head,uniformProjection,get_mapSlots]
  cases h : (if second then s.order.tail else s.order).head? with
  | none => rfl
  | some slot => cases hr : s.requests.get slot <;> simp [hr]

private theorem uniform_source (s : PendingMigration.Session) :
    PendingMigration.source (uniformProjection s) = PendingMigration.source s := by
  unfold PendingMigration.source
  congr 1
  · simp only [PendingMigration.sourceState,uniform_head]
    cases hh : PendingMigration.head s with
    | none => rfl
    | some pair =>
      obtain ⟨slot,r⟩ := pair
      simp only [Option.map_some,uniformProjection,get_mapSlots]
      cases hp : s.peer.get slot with
      | none => rfl
      | some ledger => cases ledger <;> rfl
  · simp only [PendingMigration.waiting,uniformProjection,get_mapSlots]
    congr 1
    funext slot
    cases hp : s.peer.get slot with
    | none => rfl
    | some ledger => cases ledger <;> rfl

private theorem map_put {α β : Type} (f : α → β) (s : PendingMigration.Slots α)
    (slot : Bool) (v : Option α) :
    mapSlots f (s.put slot v) = (mapSlots f s).put slot (v.map f) := by
  cases slot <;> rfl

private theorem owner_update (s : PendingMigration.Session) (slot : Bool)
    (r q : PendingMigration.Request) (hr : s.requests.get slot = some r) (hi : q.input = r.input)
    (a : Bool) : ownerInput (PendingMigration.update s slot q) a = ownerInput s a := by
  by_cases eq : a = slot
  · subst a; simp [ownerInput,PendingMigration.update,hr,hi]
  · simp [ownerInput,PendingMigration.update,PendingMigration.slots_get_put,eq]

private theorem uniform_update (s : PendingMigration.Session) (slot : Bool)
    (r q : PendingMigration.Request) (hr : s.requests.get slot = some r) (hi : q.input = r.input) :
    uniformProjection (PendingMigration.update s slot q) =
      PendingMigration.update (uniformProjection s) slot (uniformRequest q) := by
  have owners : ownerInput (PendingMigration.update s slot q) = ownerInput s := by
    funext a; exact owner_update s slot r q hr hi a
  simp only [uniformProjection,PendingMigration.update,map_put,Option.map_some]
  congr 1
  congr 1
  apply List.map_congr_left
  intro m hm
  exact congrArg (fun f => messagePayload (f m.slot) m) owners

private def LocalCommand : PendingMigration.Command → Prop
  | .publish | .retry _ | .queryPeer | .tickCommit | .cancelWork _ | .close | .release | .inspect => True
  | _ => False

private def mapQueue (owner : Bool → Bool) (q : PendingMigration.Queue) : PendingMigration.Queue :=
  ⟨q.messages.map (fun m => messagePayload (owner m.slot) m),by simpa using q.bounded⟩

private theorem uniform_peer (s : PendingMigration.Session) (slot : Bool)
    (p : Option PendingMigration.Ledger) :
    uniformProjection {s with peer := s.peer.put slot p} =
      {(uniformProjection s) with peer := (uniformProjection s).peer.put slot (p.map ownLedger)} := by
  simp only [uniformProjection,map_put]
  rfl

private theorem uniform_queue (s : PendingMigration.Session) (q : PendingMigration.Queue) :
    uniformProjection {s with queue := q} =
      {(uniformProjection s) with queue := mapQueue (ownerInput s) q} := rfl

private theorem uniform_commit (s : PendingMigration.Session) (input : Bool) :
    uniformProjection {s with active := Migration.realize s.active.kind input,prepared := none} =
      {(uniformProjection s) with active := Migration.realize s.active.kind input,prepared := none} := rfl

private theorem mapQueue_push (owner : Bool → Bool) (q : PendingMigration.Queue) (m : PendingMigration.Message) :
    (mapQueue owner q).push (messagePayload (owner m.slot) m) =
      (q.push m).map (mapQueue owner) := by
  by_cases h : q.messages.length < 4 <;>
    simp [PendingMigration.Queue.push,mapQueue,h,List.map_append]

private def uniformOutcome (o : PendingMigration.Outcome) : PendingMigration.Outcome :=
  {o with session := uniformProjection o.session}

private theorem uniform_enqueue (s : PendingMigration.Session) (r : PendingMigration.Request)
    (m : PendingMigration.Message) :
    uniformOutcome (PendingMigration.enqueue s r m) =
      PendingMigration.enqueue (uniformProjection s) (uniformRequest r)
        (messagePayload (ownerInput s m.slot) m) := by
  unfold PendingMigration.enqueue
  simp only [uniformRequest]
  split <;> simp only [*]
  · rfl
  · change uniformOutcome (match s.queue.push m with
      | none => PendingMigration.reject s .full
      | some q => ⟨{s with queue := q},.enqueued,none,none,none,[]⟩) = _
    have eq := mapQueue_push (ownerInput s) s.queue m
    change (uniformProjection s).queue.push (messagePayload (ownerInput s m.slot) m) = _ at eq
    rw [eq]
    cases h : s.queue.push m <;> rfl

private theorem uniform_peer_get (s : PendingMigration.Session) (slot : Bool) :
    (uniformProjection s).peer.get slot = (s.peer.get slot).map ownLedger := get_mapSlots _ _ _

private theorem uniform_commit_state (s : PendingMigration.Session) (slot : Bool)
    (r : PendingMigration.Request) (hr : s.requests.get slot = some r) :
    uniformProjection {(PendingMigration.update s slot {r with phase := .committed}) with
      active := Migration.realize s.active.kind r.input,prepared := none} =
    {(PendingMigration.update (uniformProjection s) slot {(uniformRequest r) with phase := .committed}) with
      active := Migration.realize s.active.kind r.input,prepared := none} := by
  exact congrArg (fun t : PendingMigration.Session =>
    {t with active := Migration.realize s.active.kind r.input,prepared := none})
    (uniform_update s slot r {r with phase := .committed} hr rfl)

private theorem uniform_prevention (s : PendingMigration.Session) (slot : Bool)
    (r : PendingMigration.Request) (x : Bool) (hr : s.requests.get slot = some r) :
    uniformProjection {(PendingMigration.update s slot {r with phase := .cancelled}) with
      peer := s.peer.put slot (some (.cancelled x))} =
    {(PendingMigration.update (uniformProjection s) slot {(uniformRequest r) with phase := .cancelled}) with
      peer := (uniformProjection s).peer.put slot (some (.cancelled x))} := by
  have hu := congrArg (fun t : PendingMigration.Session =>
    {t with peer := (uniformProjection s).peer.put slot (some (.cancelled x))})
    (uniform_update s slot r {r with phase := .cancelled} hr rfl)
  simpa only [uniformProjection,PendingMigration.update,map_put,Option.map_some,ownLedger,ownerInput,uniformRequest] using hu

private theorem uniform_retirement (s : PendingMigration.Session) (slot : Bool)
    (hq : s.queue.references slot = false) :
    uniformProjection {s with requests := s.requests.put slot none,peer := s.peer.put slot none,order := s.order.tail} =
    {(uniformProjection s) with requests := (uniformProjection s).requests.put slot none,peer := (uniformProjection s).peer.put slot none,order := s.order.tail} := by
  simp only [uniformProjection,map_put,Option.map_none]
  congr 1
  congr 1
  apply List.map_congr_left
  intro m hm
  have ne : m.slot ≠ slot := by
    have all := List.any_eq_false.mp hq m hm
    simpa using all
  simp [ownerInput,PendingMigration.slots_get_put,ne]

private theorem uniform_references (s : PendingMigration.Session) (slot : Bool) :
    (uniformProjection s).queue.references slot = s.queue.references slot := by
  simp only [PendingMigration.Queue.references,uniformProjection,List.any_map]
  congr 1
  funext m
  cases m <;> rfl

private theorem uniform_local (s : PendingMigration.Session) (c : PendingMigration.Command)
    (hc : LocalCommand c) (hp : s.prepared = none) :
    uniformOutcome (PendingMigration.step s c) = PendingMigration.step (uniformProjection s) c := by
  have hprepared : (uniformProjection s).prepared = none := hp
  cases c <;> simp only [LocalCommand] at hc
  all_goals try contradiction
  all_goals dsimp only [PendingMigration.step]
  all_goals try simp only [hp,hprepared,Option.isSome_none,Bool.false_eq_true,↓reduceIte,uniform_head]
  all_goals try rfl
  all_goals split <;> try simp only [*,Option.map_none,Option.map_some]
  all_goals try rfl
  all_goals rename_i slot r hh
  all_goals
    have hr : s.requests.get slot = some r := by
      first | exact (PendingMigration.head_fields s slot r hh).2
            | exact PendingMigration.selected_request s _ slot r hh
  all_goals try simp only [uniformRequest,uniform_peer_get,uniform_references]
  all_goals cases pe : s.peer.get slot <;>
    try (rename_i ledger; have _ : PendingMigration.Ledger := ledger; cases ledger)
  all_goals try simp only [pe,Option.map_none,Option.map_some,ownLedger]
  all_goals repeat' first | (split <;> try simp only [*]) | dsimp only
  all_goals try rfl
  all_goals simp_all [uniform_enqueue,messagePayload,PendingMigration.Message.slot,ownerInput,uniformRequest,ownLedger]
  all_goals dsimp only [uniformOutcome]
  all_goals try rw [uniform_commit_state s slot r hr]
  all_goals try rw [uniform_prevention s slot r _ hr]
  all_goals try rw [uniform_update s slot r {r with routeOpen := false} hr rfl]
  all_goals try rfl
  all_goals
    have hq : s.queue.references slot = false := by simp_all
    have hu := congrArg (fun t : PendingMigration.Session =>
      (⟨t,.released,none,none,none,[]⟩ : PendingMigration.Outcome)) (uniform_retirement s slot hq)
    simpa only [uniformProjection,hp] using hu

private theorem local_valid (s : PendingMigration.Session) (c : PendingMigration.Command)
    (hc : LocalCommand c) (hp : s.prepared = none)
    (hs : PendingMigration.Valid (delayProjection s)) :
    PendingMigration.Valid (delayProjection (PendingMigration.step s c).session) := by
  apply (uniform_valid _).mp
  have transported := PendingMigration.step_valid (uniformProjection s) c ((uniform_valid s).mpr hs)
  rw [← uniform_local s c hc hp] at transported
  exact transported

private theorem message_slot (owner : Bool) (m : PendingMigration.Message) :
    (messagePayload owner m).slot = m.slot := by cases m <;> rfl

private theorem mapQueue_pop (owner : Bool → Bool) (q : PendingMigration.Queue) :
    (mapQueue owner q).pop = q.pop.map (fun p =>
      (messagePayload (owner p.1.slot) p.1,mapQueue owner p.2)) := by
  cases q with
  | mk messages bounded => cases messages <;> rfl

private def ledgerInput : PendingMigration.Ledger → Bool
  | .reserved x | .published x _ | .cancelled x => x

private theorem peer_owned (s : PendingMigration.Session) (slot : Bool)
    (r : PendingMigration.Request) (hs : PendingMigration.Valid (uniformProjection s))
    (hr : s.requests.get slot = some r) (entry : PendingMigration.Ledger)
    (hp : s.peer.get slot = some entry) : ledgerInput entry = r.input := by
  have law := hs.slots slot
  simp only [uniformProjection,get_mapSlots,hr,hp,Option.map_some] at law
  cases entry <;> cases phase : r.phase <;>
    simp_all [PendingMigration.SlotValid,uniformRequest,ownLedger,ledgerInput]

private theorem owned_publication (s : PendingMigration.Session) (slot : Bool)
    (r : PendingMigration.Request) (hs : PendingMigration.Valid (uniformProjection s))
    (hr : s.requests.get slot = some r) (x y : Bool) :
    PendingMigration.publish ((uniformProjection s).peer.get slot) x (payload r.input y) =
      let result := PendingMigration.publish (s.peer.get slot) x y
      (result.1.map ownLedger,result.2.1,result.2.2.map (payload r.input)) := by
  rw [uniform_peer_get]
  cases hp : s.peer.get slot with
  | none => rfl
  | some entry =>
    have owner := peer_owned s slot r hs hr entry hp
    cases entry with
    | reserved a =>
      change a = r.input at owner
      subst a
      cases h : r.input <;> cases x <;> cases y <;> rfl
    | published a b =>
      change a = r.input at owner
      subst a
      cases h : r.input <;> cases x <;> cases y <;> cases b <;> rfl
    | cancelled a => rfl

private def outputOwner (s : PendingMigration.Session) : Bool :=
  ((PendingMigration.head s).map (fun p => p.2.input)).getD false

private def publicationTransport (s : PendingMigration.Session) (o : PendingMigration.Outcome) : PendingMigration.Outcome :=
  {uniformOutcome o with business := o.business.map (payload (outputOwner s))}

private theorem queued_owner (s : PendingMigration.Session) (m : PendingMigration.Message)
    (hm : m ∈ s.queue.messages) (hs : PendingMigration.Valid (uniformProjection s)) :
    ∃ r, s.requests.get m.slot = some r ∧ PendingMigration.head s = some (m.slot,r) := by
  have valid := hs.messages (messagePayload (ownerInput s m.slot) m)
    (List.mem_map.mpr ⟨m,hm,rfl⟩)
  obtain ⟨ho,q,hq,_⟩ := valid
  simp only [message_slot] at ho hq
  simp only [uniformProjection,get_mapSlots,Option.map_eq_some_iff] at hq
  obtain ⟨r,hr,rfl⟩ := hq
  exact ⟨r,hr,by simp [PendingMigration.head,uniformProjection] at ho; simp [PendingMigration.head,ho,hr]⟩

private theorem uniform_request_get (s : PendingMigration.Session) (slot : Bool) :
    (uniformProjection s).requests.get slot = (s.requests.get slot).map uniformRequest := get_mapSlots _ _ _

private theorem mapQueue_response (owner : Bool → Bool) (q : PendingMigration.Queue)
    (slot : Bool) (answer : PendingMigration.Reply) (deliver : Bool) :
    mapQueue owner (if deliver then (q.push (.reply slot answer)).getD q else q) =
      (if deliver then ((mapQueue owner q).push (.reply slot answer)).getD (mapQueue owner q)
        else mapQueue owner q) := by
  cases deliver
  · rfl
  · have hp := mapQueue_push owner q (.reply slot answer)
    simp only [messagePayload] at hp
    simp only [↓reduceIte,hp]
    cases q.push (.reply slot answer) <;> rfl

private theorem uniform_query (s : PendingMigration.Session) (slot : Bool) :
    PendingMigration.query ((uniformProjection s).peer.get slot) = PendingMigration.query (s.peer.get slot) := by
  rw [uniform_peer_get]
  cases s.peer.get slot with
  | none => rfl
  | some ledger => cases ledger <;> rfl

private theorem uniform_dispatch (s : PendingMigration.Session) (deliver : Bool)
    (hs : PendingMigration.Valid (uniformProjection s)) :
    publicationTransport s (PendingMigration.dispatch s deliver) =
      PendingMigration.dispatch (uniformProjection s) deliver := by
  have pop := mapQueue_pop (ownerInput s) s.queue
  change (uniformProjection s).queue.pop = _ at pop
  unfold PendingMigration.dispatch
  rw [pop]
  cases hp : s.queue.pop with
  | none => rfl
  | some pair =>
    obtain ⟨m,q⟩ := pair
    have messages := PendingMigration.popped_messages s.queue m q hp
    obtain ⟨r,hr,hh⟩ := queued_owner s m (by simp [messages]) hs
    have owner : ownerInput s m.slot = r.input := by simp [ownerInput,hr]
    have outOwner : outputOwner s = r.input := by simp [outputOwner,hh]
    simp only [Option.map_some,message_slot,uniform_request_get,hr,uniformRequest]
    split <;> try simp only [*]
    · rfl
    · cases m <;> simp only [messagePayload,owner]
      all_goals simp only [PendingMigration.Message.slot] at hr hh owner
      all_goals try simp only [owned_publication s _ r hs hr]
      all_goals try rw [uniform_query]
      case reply slot answer =>
        split <;> try simp only [*]
        · dsimp only [publicationTransport,uniformOutcome]
          rw [uniform_update {s with queue := q} slot r {r with phase := .confirmed} hr rfl]
          rfl
        · rfl
      all_goals dsimp only [publicationTransport,uniformOutcome]
      all_goals try rfl
      all_goals simp only [outOwner]
      all_goals try simp only [owned_publication s _ r hs hr]
      all_goals try simp only [uniformProjection,map_put,ownerInput]
      all_goals congr 1
      all_goals congr 1
      all_goals exact mapQueue_response (ownerInput s) q _ _ deliver

private def liftSource (s : PendingMigration.Source) : Source := ⟨s.state,s.waiting⟩

private theorem lift_step (a b : PendingMigration.Source) (p : PendingMigration.Outcome)
    (o : Outcome) (mask : Bool) (h : PendingMigration.SourceStep a p b)
    (ha : o.accepted = p.accepted) (hc : o.cancellation = p.cancellation)
    (hb : p.business = o.business.map (payload mask))
    (owner : o.business.isSome = true → a.waiting.head? = some mask) :
    SourceStep (liftSource a) o (liftSource b) := by
  cases h with
  | internal a p accept publish cancel =>
    have empty : o.business = none := by simpa [publish] using hb.symm
    exact .internal _ _ (ha.trans accept) empty (by simpa [hc] using cancel)
  | accept a p x accept publish cancel =>
    have empty : o.business = none := by simpa [publish] using hb.symm
    exact .accept _ _ x (ha.trans accept) empty (hc.trans cancel)
  | prevent b x pre post p accept publish cancel =>
    have empty : o.business = none := by simpa [publish] using hb.symm
    exact .prevent b x pre post o (ha.trans accept) empty (hc.trans cancel)
  | publish b x xs p accept publish cancel =>
    cases output : o.business with
    | none => simp [output,publish] at hb
    | some y =>
      have eq : x = mask := by simpa using owner (by simp [output])
      subst mask
      have payloadEq : b = payload x y := by simpa [publish,output] using hb
      have result : y = (oracle x b).1 := by
        rw [payloadEq]
        exact (payload_involutive x y).symm
      exact .publish b x xs o (ha.trans accept) (by simpa [result] using output) (hc.trans cancel)

private theorem publication_waiting (s : PendingMigration.Session) (slot : Bool)
    (r : PendingMigration.Request) (x y result : Bool)
    (hs : PendingMigration.Valid (uniformProjection s))
    (hr : s.requests.get slot = some r) (hh : PendingMigration.head s = some (slot,r))
    (hb : (PendingMigration.publish (s.peer.get slot) x y).2.2 = some result) :
    (PendingMigration.source s).waiting.head? = some (outputOwner s) := by
  have ho := (PendingMigration.head_fields s slot r hh).1
  have order := List.eq_cons_of_mem_head? ho
  cases hp : s.peer.get slot with
  | none => simp [PendingMigration.publish,hp] at hb
  | some entry =>
    have own := peer_owned s slot r hs hr entry hp
    cases entry with
    | reserved input =>
      change input = r.input at own
      simp only [PendingMigration.source,PendingMigration.waiting]
      rw [order]
      simp [hp,outputOwner,hh,own]
    | published input output => simp [PendingMigration.publish,hp] at hb
    | cancelled input => simp [PendingMigration.publish,hp] at hb

private theorem dispatch_owner (s : PendingMigration.Session) (deliver : Bool)
    (hs : PendingMigration.Valid (uniformProjection s))
    (nonempty : (PendingMigration.dispatch s deliver).business.isSome = true) :
    (PendingMigration.source s).waiting.head? = some (outputOwner s) := by
  cases output : (PendingMigration.dispatch s deliver).business with
  | none => simp [output] at nonempty
  | some y =>
    unfold PendingMigration.dispatch at output
    cases hp : s.queue.pop with
    | none => simp [hp,PendingMigration.reject] at output
    | some pair =>
      obtain ⟨m,q⟩ := pair
      have messages := PendingMigration.popped_messages s.queue m q hp
      obtain ⟨r,hr,hh⟩ := queued_owner s m (by simp [messages]) hs
      simp only [hp,hr] at output
      split at output
      · simp [PendingMigration.reject] at output
      · cases m with
        | publish slot x value => exact publication_waiting s slot r x value y hs hr hh output
        | retry slot x value => exact publication_waiting s slot r x value y hs hr hh output
        | query slot => simp at output
        | reply slot answer =>
          dsimp only at output
          split at output <;> simp [PendingMigration.reject] at output

private theorem dispatch_valid (s : PendingMigration.Session) (deliver : Bool)
    (hs : PendingMigration.Valid (delayProjection s)) :
    PendingMigration.Valid (delayProjection (PendingMigration.dispatch s deliver).session) := by
  apply (uniform_valid _).mp
  have h := (PendingMigration.dispatch_source (uniformProjection s) deliver ((uniform_valid s).mpr hs)).1
  rw [← uniform_dispatch s deliver ((uniform_valid s).mpr hs)] at h
  exact h

private theorem local_no_output (s : PendingMigration.Session) (c : PendingMigration.Command)
    (hc : LocalCommand c) : (PendingMigration.step s c).business = none := by
  cases c <;> simp only [LocalCommand] at hc
  all_goals try contradiction
  all_goals dsimp only [PendingMigration.step,PendingMigration.enqueue,PendingMigration.reject]
  all_goals repeat' first | rfl | split | dsimp only [PendingMigration.enqueue,PendingMigration.reject]

private theorem transport_refines (s : PendingMigration.Session) (p : PendingMigration.Outcome)
    (o : Outcome)
    (h : PendingMigration.SourceStep (PendingMigration.source (uniformProjection s))
      (publicationTransport s p) (PendingMigration.source (uniformProjection p.session)))
    (ha : o.accepted = p.accepted) (hb : o.business = p.business)
    (hc : o.cancellation = p.cancellation)
    (owner : p.business.isSome = true → (PendingMigration.source s).waiting.head? = some (outputOwner s)) :
    SourceStep (liftSource (PendingMigration.source s)) o
      (liftSource (PendingMigration.source p.session)) := by
  rw [uniform_source,uniform_source] at h
  exact lift_step _ _ _ o (outputOwner s) h ha hc (by simp [publicationTransport,hb])
    (by simpa [hb] using owner)

private theorem local_refines (s : PendingMigration.Session) (c : PendingMigration.Command)
    (hc : LocalCommand c) (hp : s.prepared = none)
    (hs : PendingMigration.Valid (delayProjection s)) (o : Outcome)
    (ha : o.accepted = (PendingMigration.step s c).accepted)
    (hb : o.business = (PendingMigration.step s c).business)
    (hx : o.cancellation = (PendingMigration.step s c).cancellation) :
    SourceStep (liftSource (PendingMigration.source s)) o
      (liftSource (PendingMigration.source (PendingMigration.step s c).session)) := by
  have refined := PendingMigration.step_refines (uniformProjection s) c ((uniform_valid s).mpr hs)
  rw [← uniform_local s c hc hp] at refined
  have empty := local_no_output s c hc
  have eq : publicationTransport s (PendingMigration.step s c) = uniformOutcome (PendingMigration.step s c) := by
    simp [publicationTransport,uniformOutcome,empty]
  exact transport_refines s (PendingMigration.step s c) o
    (by simpa only [eq,uniformOutcome] using refined) ha hb hx (by simp [empty])

private theorem dispatch_refines (s : PendingMigration.Session) (deliver : Bool)
    (hs : PendingMigration.Valid (delayProjection s)) (o : Outcome)
    (ha : o.accepted = (PendingMigration.dispatch s deliver).accepted)
    (hb : o.business = (PendingMigration.dispatch s deliver).business)
    (hc : o.cancellation = (PendingMigration.dispatch s deliver).cancellation) :
    SourceStep (liftSource (PendingMigration.source s)) o
      (liftSource (PendingMigration.source (PendingMigration.dispatch s deliver).session)) := by
  have valid := (uniform_valid s).mpr hs
  have refined := (PendingMigration.dispatch_source (uniformProjection s) deliver valid).2
  rw [← uniform_dispatch s deliver valid] at refined
  exact transport_refines s (PendingMigration.dispatch s deliver) o refined ha hb hc
    (dispatch_owner s deliver valid)

/-- The actual protocol commands permitted by the fork/join wrapper. -/
def ExternalCommand : PendingMigration.Command → Prop
  | .accept _ | .evaluate | .prepare _ _ _ _ | .ownershipCommit | .cancelMigration => False
  | _ => True

theorem external_command_valid (s : PendingMigration.Session) (c : PendingMigration.Command)
    (hc : ExternalCommand c) (hp : s.prepared = none)
    (hs : PendingMigration.Valid (delayProjection s)) :
    PendingMigration.Valid (delayProjection (PendingMigration.step s c).session) := by
  cases c <;> simp only [ExternalCommand] at hc
  all_goals try contradiction
  case dispatch deliver =>
    simpa only [PendingMigration.step,hp,Option.isSome_none,Bool.false_eq_true,↓reduceIte] using dispatch_valid s deliver hs
  all_goals exact local_valid s _ (by trivial) hp hs

theorem external_command_refines (s : PendingMigration.Session) (c : PendingMigration.Command)
    (hc : ExternalCommand c) (hp : s.prepared = none)
    (hs : PendingMigration.Valid (delayProjection s)) (o : Outcome)
    (ha : o.accepted = (PendingMigration.step s c).accepted)
    (hb : o.business = (PendingMigration.step s c).business)
    (hx : o.cancellation = (PendingMigration.step s c).cancellation) :
    SourceStep ⟨PendingMigration.sourceState s,PendingMigration.waiting s⟩ o
      ⟨PendingMigration.sourceState (PendingMigration.step s c).session,
        PendingMigration.waiting (PendingMigration.step s c).session⟩ := by
  cases c <;> simp only [ExternalCommand] at hc
  all_goals try contradiction
  case dispatch deliver =>
    simp only [PendingMigration.step,hp,Option.isSome_none,Bool.false_eq_true,↓reduceIte] at ha hb hx ⊢
    exact dispatch_refines s deliver hs o ha hb hx
  all_goals exact local_refines s _ (by trivial) hp hs o ha hb hx

private theorem source_ite (p : Prop) [Decidable p] (a b : Active) :
    source (if p then a else b) = (if p then source a else source b) := by split <;> rfl

private theorem source_residuals (a : Active) (r : PendingMigration.Slots Residual) :
    source (a.withResiduals r) = source a := rfl

private theorem source_option {α : Type} (o : Option α) (a : Active) (f : α → Active) :
    source (match o with | none => a | some x => f x) =
      (match o with | none => source a | some x => source (f x)) := by cases o <;> rfl

private theorem source_update (a : Active) (slot : Bool) (r : Residual) :
    source (updateResidual a slot r) = source a := rfl

private theorem option_const {α β : Type} (o : Option α) (b : β) :
    (match o with | none => b | some _ => b) = b := by cases o <;> rfl

private theorem source_cancellation (a : Active) (slot : Bool) :
    source (match a.residuals.get slot with
      | none => a
      | some r => updateResidual a slot {r with cancelled := true}) = source a := by
  cases a.residuals.get slot <;> rfl

private def releaseBlocked (s : Session) (c : PendingMigration.Command) : Bool :=
  c == .release && ((PendingMigration.head s.active.protocol
    (match c with | .cancelWork second => second | _ => false)).map
    (fun p => s.active.deliveries.references p.1)).getD false

private theorem external_fields (s : Session) (c : PendingMigration.Command)
    (hc : ExternalCommand c) (hp : s.prepared.isSome = false)
    (hb : releaseBlocked s c = false) :
    (source (external s c).session.active,(external s c).accepted,
      (external s c).business,(external s c).cancellation) =
    (liftSource (PendingMigration.source (PendingMigration.step s.active.protocol c).session),
      (PendingMigration.step s.active.protocol c).accepted,
      (PendingMigration.step s.active.protocol c).business,
      (PendingMigration.step s.active.protocol c).cancellation) := by
  cases c <;> simp only [ExternalCommand] at hc
  all_goals try contradiction
  all_goals dsimp only [releaseBlocked] at hb
  all_goals dsimp only [external]
  all_goals simp only [hp,hb,Bool.false_eq_true,↓reduceIte]
  all_goals repeat' first | rfl | split | dsimp only [source,updateResidual,Active.withResiduals]

/-- The public wrapper preserves the independent source step, including busy
internal-reference refusal, unsupported commands, and frozen preparation. -/
theorem external_refines (s : Session) (c : PendingMigration.Command)
    (hs : Invariant s.active) (hp : s.active.protocol.prepared = none) :
    SourceStep (source s.active) (external s c) (source (external s c).session.active) := by
  by_cases frozen : s.prepared.isSome = true
  · have eq : external s c = reject s .frozen := by simp [external,frozen]
    rw [eq]
    exact .internal _ _ rfl rfl (by simp [reject])
  have free : s.prepared.isSome = false := by simpa using frozen
  by_cases hc : ExternalCommand c
  · by_cases hb : releaseBlocked s c = true
    · have eq : external s c = reject s .busy := by
        cases c <;> simp only [ExternalCommand] at hc
        all_goals try contradiction
        all_goals dsimp only [releaseBlocked] at hb
        all_goals dsimp only [external]
        all_goals simp only [free,hb,Bool.false_eq_true,↓reduceIte]
      rw [eq]
      exact .internal _ _ rfl rfl (by simp [reject])
    · have fields := external_fields s c hc free (by simpa using hb)
      have target := congrArg Prod.fst fields
      dsimp only at target
      rw [target]
      apply external_command_refines s.active.protocol c hc hp hs.protocol
      · exact congrArg (fun x => x.2.1) fields
      · exact congrArg (fun x => x.2.2.1) fields
      · exact congrArg (fun x => x.2.2.2) fields
  · have eq : external s c = reject s .unsupported := by
      cases c <;> simp only [ExternalCommand] at hc
      all_goals try contradiction
      all_goals simp [external,free]
    rw [eq]
    exact .internal _ _ rfl rfl (by simp [reject])

/-- Projected ordered-peer validity is established for every public external
operation; residual ownership is tracked separately in the joint invariant. -/
theorem external_projected_valid (s : Session) (c : PendingMigration.Command)
    (hs : Invariant s.active) (hp : s.active.protocol.prepared = none) :
    PendingMigration.Valid (delayProjection (external s c).session.active.protocol) := by
  by_cases hc : ExternalCommand c
  · have raw := external_command_valid s.active.protocol c hc hp hs.protocol
    cases c <;> simp only [ExternalCommand] at hc
    all_goals try contradiction
    all_goals dsimp only [external]
    all_goals repeat' first | (split <;> try simp only [*]) | dsimp only
    all_goals first
      | exact hs.protocol
      | simpa only [updateResidual,Active.withResiduals] using raw
  · cases c <;> simp only [ExternalCommand] at hc
    all_goals try contradiction
    all_goals dsimp only [external]
    all_goals split <;> exact hs.protocol

private def livePhase (p : PendingMigration.Phase) : Prop :=
  p = .accepted ∨ p = .computed ∨ p = .confirmed

private def deliveryPhase (p : PendingMigration.Phase) : Prop := p = .accepted ∨ p = .cancelled

private def Aligned (r q : PendingMigration.Request) : Prop :=
  r.input = q.input ∧ (livePhase q.phase → livePhase r.phase) ∧
    (deliveryPhase r.phase → deliveryPhase q.phase) ∧ (r.phase = .cancelled ↔ q.phase = .cancelled)

private theorem aligned_refl (r : PendingMigration.Request) : Aligned r r :=
  ⟨rfl,id,id,Iff.rfl⟩

private theorem metadata_current (s t : Active) (hs : Invariant s)
    (valid : PendingMigration.Valid (delayProjection t.protocol))
    (order : s.protocol.order = t.protocol.order)
    (residuals : s.residuals = t.residuals) (deliveries : s.deliveries = t.deliveries)
    (forward : ∀ slot r, s.protocol.requests.get slot = some r →
      ∃ q, t.protocol.requests.get slot = some q ∧ Aligned r q)
    (backward : ∀ slot q, t.protocol.requests.get slot = some q →
      ∃ r, s.protocol.requests.get slot = some r ∧ Aligned r q)
    (current : ∀ slot q localState, t.protocol.requests.get slot = some q →
      t.residuals.get slot = some localState → livePhase q.phase →
      localState.cached.isSome = true → localState.oldState = t.protocol.active.logical) : Invariant t := by
  constructor
  · exact valid
  · intro slot q hq
    obtain ⟨r,hr,aligned⟩ := backward slot q hq
    obtain ⟨localState,hlocal,correct⟩ := hs.residual slot r hr
    exact ⟨localState,residuals ▸ hlocal,aligned.1 ▸ correct⟩
  · exact current
  · intro slot refs
    obtain ⟨r,localState,hr,hl,cached,phase⟩ := hs.delivery slot (deliveries ▸ refs)
    obtain ⟨q,hq,aligned⟩ := forward slot r hr
    exact ⟨q,localState,hq,residuals ▸ hl,cached,aligned.2.2.1 phase⟩
  · intro slot q localState hq hl
    obtain ⟨r,hr,aligned⟩ := backward slot q hq
    exact (hs.cancellation slot r localState hr (residuals ▸ hl)).trans aligned.2.2.2
  · intro slot r hr cached
    rw [← order]
    exact hs.cache_head slot r (residuals ▸ hr) cached
  · intro slot r hr completed
    exact hs.completed_cache slot r (residuals ▸ hr) completed

private theorem metadata_preserved (s t : Active) (hs : Invariant s)
    (valid : PendingMigration.Valid (delayProjection t.protocol))
    (logical : s.protocol.active.logical = t.protocol.active.logical)
    (order : s.protocol.order = t.protocol.order)
    (residuals : s.residuals = t.residuals) (deliveries : s.deliveries = t.deliveries)
    (forward : ∀ slot r, s.protocol.requests.get slot = some r →
      ∃ q, t.protocol.requests.get slot = some q ∧ Aligned r q)
    (backward : ∀ slot q, t.protocol.requests.get slot = some q →
      ∃ r, s.protocol.requests.get slot = some r ∧ Aligned r q) : Invariant t := by
  apply metadata_current s t hs valid order residuals deliveries forward backward
  intro slot q localState hq hl phase cached
  obtain ⟨r,hr,aligned⟩ := backward slot q hq
  exact (hs.current slot r localState hr (residuals ▸ hl) (aligned.2.1 phase) cached).trans logical

private theorem protocol_metadata_preserved (s : Active) (p : PendingMigration.Session)
    (hs : Invariant s) (valid : PendingMigration.Valid (delayProjection p))
    (logical : s.protocol.active.logical = p.active.logical)
    (order : s.protocol.order = p.order) (requests : s.protocol.requests = p.requests) :
    Invariant {s with protocol := p} := by
  apply metadata_preserved s {s with protocol := p} hs valid logical order rfl rfl
  · intro slot r hr
    exact ⟨r,requests ▸ hr,aligned_refl r⟩
  · intro slot r hr
    exact ⟨r,requests ▸ hr,aligned_refl r⟩

private theorem request_metadata_preserved (s : Active) (slot : Bool)
    (r q : PendingMigration.Request) (hs : Invariant s)
    (hr : s.protocol.requests.get slot = some r) (aligned : Aligned r q)
    (valid : PendingMigration.Valid (delayProjection (PendingMigration.update s.protocol slot q))) :
    Invariant {s with protocol := PendingMigration.update s.protocol slot q} := by
  apply metadata_preserved s {s with protocol := PendingMigration.update s.protocol slot q} hs valid rfl rfl rfl rfl
  · intro a old ho
    by_cases eq : a = slot
    · subst a; rw [hr] at ho; cases ho
      exact ⟨q,by simp [PendingMigration.update],aligned⟩
    · exact ⟨old,by simpa [PendingMigration.update,PendingMigration.slots_get_put,eq] using ho,aligned_refl old⟩
  · intro a new hn
    by_cases eq : a = slot
    · subst a
      simp only [PendingMigration.update,PendingMigration.slots_get_put_same,Option.some.injEq] at hn
      subst new
      exact ⟨r,hr,aligned⟩
    · exact ⟨new,by simpa [PendingMigration.update,PendingMigration.slots_get_put,eq] using hn,aligned_refl new⟩

private theorem request_metadata_queued (s : Active) (queue : PendingMigration.Queue) (slot : Bool)
    (r q : PendingMigration.Request) (hs : Invariant s)
    (hr : s.protocol.requests.get slot = some r) (aligned : Aligned r q)
    (valid : PendingMigration.Valid (delayProjection (PendingMigration.update {s.protocol with queue := queue} slot q))) :
    Invariant {s with protocol := PendingMigration.update {s.protocol with queue := queue} slot q} := by
  apply metadata_preserved s {s with protocol := PendingMigration.update {s.protocol with queue := queue} slot q} hs valid rfl rfl rfl rfl
  · intro a old ho
    by_cases eq : a = slot
    · subst a; rw [hr] at ho; cases ho
      exact ⟨q,by simp [PendingMigration.update],aligned⟩
    · exact ⟨old,by simpa [PendingMigration.update,PendingMigration.slots_get_put,eq] using ho,aligned_refl old⟩
  · intro a new hn
    by_cases eq : a = slot
    · subst a
      simp only [PendingMigration.update,PendingMigration.slots_get_put_same,Option.some.injEq] at hn
      subst new
      exact ⟨r,hr,aligned⟩
    · exact ⟨new,by simpa [PendingMigration.update,PendingMigration.slots_get_put,eq] using hn,aligned_refl new⟩

private theorem commit_metadata (s : Active) (slot : Bool) (r : PendingMigration.Request)
    (hs : Invariant s) (hh : PendingMigration.head s.protocol = some (slot,r))
    (phase : r.phase = .confirmed)
    (valid : PendingMigration.Valid (delayProjection (PendingMigration.logicalCommit s.protocol slot r))) :
    Invariant {s with protocol := PendingMigration.logicalCommit s.protocol slot r} := by
  obtain ⟨ho,hr⟩ := PendingMigration.head_fields s.protocol slot r hh
  have aligned : Aligned r {r with phase := .committed} := by
    simp [Aligned,livePhase,deliveryPhase,phase]
  apply metadata_current s {s with protocol := PendingMigration.logicalCommit s.protocol slot r}
    hs valid rfl rfl rfl
  · intro a old hold
    by_cases eq : a = slot
    · subst a; rw [hr] at hold; cases hold
      exact ⟨{r with phase := .committed},by simp [PendingMigration.logicalCommit,PendingMigration.update],aligned⟩
    · exact ⟨old,by simpa [PendingMigration.logicalCommit,PendingMigration.update,
        PendingMigration.slots_get_put,eq] using hold,aligned_refl old⟩
  · intro a new hnew
    by_cases eq : a = slot
    · subst a
      simp only [PendingMigration.logicalCommit,PendingMigration.update,
        PendingMigration.slots_get_put_same,Option.some.injEq] at hnew
      subst new
      exact ⟨r,hr,aligned⟩
    · exact ⟨new,by simpa [PendingMigration.logicalCommit,PendingMigration.update,
        PendingMigration.slots_get_put,eq] using hnew,aligned_refl new⟩
  · intro a new localState hnew hlocal live cached
    have head := hs.cache_head a localState hlocal cached
    have eq : a = slot := Option.some.inj (head.symm.trans ho)
    subst a
    simp only [PendingMigration.logicalCommit,PendingMigration.update,
      PendingMigration.slots_get_put_same,Option.some.injEq] at hnew
    subst new
    simp [livePhase] at live

private theorem cancel_metadata (s : Active) (slot : Bool) (r : PendingMigration.Request)
    (localState : Residual) (hs : Invariant s)
    (hr : s.protocol.requests.get slot = some r) (hl : s.residuals.get slot = some localState)
    (valid : PendingMigration.Valid (delayProjection (PendingMigration.prevention s.protocol slot r))) :
    Invariant (updateResidual {s with protocol := PendingMigration.prevention s.protocol slot r}
      slot {localState with cancelled := true}) := by
  obtain ⟨old,hold,correct⟩ := hs.residual slot r hr
  rw [hl] at hold
  cases hold
  constructor
  · exact valid
  · intro a q hq
    by_cases eq : a = slot
    · subst a
      simp only [updateResidual,Active.withResiduals,PendingMigration.prevention,PendingMigration.update,
        PendingMigration.slots_get_put_same,Option.some.injEq] at hq
      subst q
      refine ⟨{localState with cancelled := true},?_,correct⟩
      simp [updateResidual]
    · have oldq : s.protocol.requests.get a = some q := by
        simpa [updateResidual,Active.withResiduals,PendingMigration.prevention,PendingMigration.update,
          PendingMigration.slots_get_put,eq] using hq
      obtain ⟨work,hw,law⟩ := hs.residual a q oldq
      exact ⟨work,by simpa [updateResidual,Active.residuals,Active.withResiduals,store_decode_encode,PendingMigration.slots_get_put,eq] using hw,law⟩
  · intro a q work hq hw phase cached
    by_cases eq : a = slot
    · subst a
      simp only [updateResidual,Active.withResiduals,PendingMigration.prevention,PendingMigration.update,
        PendingMigration.slots_get_put_same,Option.some.injEq] at hq
      subst q
      simp at phase
    · apply hs.current a q work _ _ phase cached
      · simpa [updateResidual,Active.withResiduals,PendingMigration.prevention,PendingMigration.update,
          PendingMigration.slots_get_put,eq] using hq
      · simpa [updateResidual,Active.residuals,Active.withResiduals,store_decode_encode,PendingMigration.slots_get_put,eq] using hw
  · intro a refs
    obtain ⟨q,work,hq,hw,cached,phase⟩ := hs.delivery a refs
    by_cases eq : a = slot
    · subst a
      rw [hr] at hq; cases hq
      rw [hl] at hw; cases hw
      refine ⟨{r with phase := .cancelled},{localState with cancelled := true},?_,?_,cached,Or.inr rfl⟩
      · simp [updateResidual,Active.withResiduals,PendingMigration.prevention,PendingMigration.update]
      · simp [updateResidual]
    · refine ⟨q,work,?_,?_,cached,phase⟩
      · simpa [updateResidual,Active.withResiduals,PendingMigration.prevention,PendingMigration.update,
          PendingMigration.slots_get_put,eq] using hq
      · simpa [updateResidual,Active.residuals,Active.withResiduals,store_decode_encode,PendingMigration.slots_get_put,eq] using hw
  · intro a q work hq hw
    by_cases eq : a = slot
    · subst a
      simp only [updateResidual,Active.withResiduals,PendingMigration.prevention,PendingMigration.update,
        PendingMigration.slots_get_put_same,Option.some.injEq] at hq
      subst q
      simp only [updateResidual,with_residuals,PendingMigration.slots_get_put_same,Option.some.injEq] at hw
      subst work
      simp
    · apply hs.cancellation a q work
      · simpa [updateResidual,Active.withResiduals,PendingMigration.prevention,PendingMigration.update,
          PendingMigration.slots_get_put,eq] using hq
      · simpa [updateResidual,Active.residuals,Active.withResiduals,store_decode_encode,PendingMigration.slots_get_put,eq] using hw
  · intro a work hw cached
    by_cases eq : a = slot
    · subst a
      simp only [updateResidual,with_residuals,PendingMigration.slots_get_put_same,Option.some.injEq] at hw
      subst work
      exact hs.cache_head slot localState hl cached
    · apply hs.cache_head a work _ cached
      simpa [updateResidual,Active.residuals,Active.withResiduals,store_decode_encode,PendingMigration.slots_get_put,eq] using hw
  · intro a work hw completed
    by_cases eq : a = slot
    · subst a
      simp only [updateResidual,with_residuals,PendingMigration.slots_get_put_same,Option.some.injEq] at hw
      subst work
      exact hs.completed_cache slot localState hl completed
    · apply hs.completed_cache a work _ completed
      simpa [updateResidual,Active.residuals,Active.withResiduals,store_decode_encode,PendingMigration.slots_get_put,eq] using hw

private theorem retirement_metadata (s : Active) (slot : Bool) (r : PendingMigration.Request)
    (hs : Invariant s) (hh : PendingMigration.head s.protocol = some (slot,r))
    (empty : s.deliveries.references slot = false)
    (valid : PendingMigration.Valid (delayProjection (PendingMigration.retirement s.protocol slot))) :
    Invariant (({s with protocol := PendingMigration.retirement s.protocol slot} : Active).withResiduals
      (s.residuals.put slot none)) := by
  have ho := (PendingMigration.head_fields s.protocol slot r hh).1
  constructor
  · exact valid
  · intro a q hq
    by_cases eq : a = slot
    · subst a
      simp [Active.withResiduals,PendingMigration.retirement] at hq
    · have oldq : s.protocol.requests.get a = some q := by
        simpa [Active.withResiduals,PendingMigration.retirement,PendingMigration.slots_get_put,eq] using hq
      obtain ⟨work,hw,law⟩ := hs.residual a q oldq
      exact ⟨work,by simpa [PendingMigration.slots_get_put,eq] using hw,law⟩
  · intro a q work hq hw phase cached
    by_cases eq : a = slot
    · subst a
      simp [Active.withResiduals,PendingMigration.retirement] at hq
    · apply hs.current a q work _ _ phase cached
      · simpa [Active.withResiduals,PendingMigration.retirement,PendingMigration.slots_get_put,eq] using hq
      · simpa [PendingMigration.slots_get_put,eq] using hw
  · intro a refs
    have ne : a ≠ slot := by intro eq; subst a; simp [Active.withResiduals,empty] at refs
    obtain ⟨q,work,hq,hw,cached,phase⟩ := hs.delivery a refs
    refine ⟨q,work,?_,?_,cached,phase⟩
    · simpa [Active.withResiduals,PendingMigration.retirement,PendingMigration.slots_get_put,ne] using hq
    · simpa [PendingMigration.slots_get_put,ne] using hw
  · intro a q work hq hw
    by_cases eq : a = slot
    · subst a
      simp [Active.withResiduals,PendingMigration.retirement] at hq
    · apply hs.cancellation a q work
      · simpa [Active.withResiduals,PendingMigration.retirement,PendingMigration.slots_get_put,eq] using hq
      · simpa [PendingMigration.slots_get_put,eq] using hw
  · intro a work hw cached
    by_cases eq : a = slot
    · subst a; simp at hw
    · have old : s.residuals.get a = some work := by simpa [PendingMigration.slots_get_put,eq] using hw
      have head := hs.cache_head a work old cached
      exact False.elim (eq (Option.some.inj (head.symm.trans ho)))
  · intro a work hw completed
    by_cases eq : a = slot
    · subst a; simp at hw
    · apply hs.completed_cache a work _ completed
      simpa [PendingMigration.slots_get_put,eq] using hw

private theorem dispatch_metadata (s : Active) (deliver : Bool) (hs : Invariant s)
    (valid : PendingMigration.Valid (delayProjection (PendingMigration.dispatch s.protocol deliver).session)) :
    Invariant {s with protocol := (PendingMigration.dispatch s.protocol deliver).session} := by
  unfold PendingMigration.dispatch at valid ⊢
  cases hp : s.protocol.queue.pop with
  | none =>
    simpa only [hp,PendingMigration.reject] using hs
  | some pair =>
    obtain ⟨m,q⟩ := pair
    have messages := PendingMigration.popped_messages s.protocol.queue m q hp
    obtain ⟨r,hr,hh⟩ := queued_owner s.protocol m (by simp [messages]) ((uniform_valid _).mpr hs.protocol)
    simp only [hp,hr] at valid ⊢
    split <;> simp only [*] at valid ⊢
    · exact protocol_metadata_preserved s _ hs valid rfl rfl rfl
    · cases m with
      | publish slot x y => exact protocol_metadata_preserved s _ hs valid rfl rfl rfl
      | retry slot x y => exact protocol_metadata_preserved s _ hs valid rfl rfl rfl
      | query slot => exact protocol_metadata_preserved s _ hs valid rfl rfl rfl
      | reply slot answer =>
        dsimp only at valid ⊢
        split <;> simp only [*] at valid ⊢
        · rename_i condition
          have both : answer = .published ∧ r.phase = .computed := by simpa using condition
          have phase := both.2
          apply request_metadata_queued s q slot r {r with phase := .confirmed} hs hr _ valid
          simp [Aligned,livePhase,deliveryPhase,phase]
        · exact protocol_metadata_preserved s _ hs valid rfl rfl rfl

private theorem dispatch_control (s : PendingMigration.Session) (deliver : Bool) :
    (PendingMigration.dispatch s deliver).cancellation = none ∧
      (PendingMigration.dispatch s deliver).status ≠ .released := by
  unfold PendingMigration.dispatch
  repeat' first | (constructor <;> trivial) | split | dsimp only [PendingMigration.reject]

set_option backward.dsimp.instances true in
private theorem external_dispatch_invariant (s : Session) (deliver : Bool)
    (hs : Invariant s.active) (hp : s.active.protocol.prepared = none) :
    Invariant (external s (.dispatch deliver)).session.active := by
  have valid := dispatch_valid s.active.protocol deliver hs.protocol
  have control := dispatch_control s.active.protocol deliver
  by_cases frozen : s.prepared.isSome = true
  · simpa only [external,frozen,↓reduceIte,reject] using hs
  · have raw : PendingMigration.step s.active.protocol (.dispatch deliver) =
        PendingMigration.dispatch s.active.protocol deliver := by simp [PendingMigration.step,hp]
    have status : ((PendingMigration.dispatch s.active.protocol deliver).status == .released) = false := by
      simpa using control.2
    have cancellation : ((PendingMigration.dispatch s.active.protocol deliver).cancellation == some true) = false := by
      simp [control.1]
    simp only [external,frozen,↓reduceIte,raw,status,cancellation]
    cases h : PendingMigration.head s.active.protocol false <;>
      simpa [h,raw,control.1,control.2] using dispatch_metadata s.active deliver hs valid

set_option backward.dsimp.instances true in
/-- Every external event preserves internal ownership and retained producer /
consumer work as well as the ordered-peer invariant. -/
theorem external_invariant (s : Session) (c : PendingMigration.Command)
    (hs : Invariant s.active) (hp : s.active.protocol.prepared = none) :
    Invariant (external s c).session.active := by
  by_cases hc : ExternalCommand c
  · have valid := external_command_valid s.active.protocol c hc hp hs.protocol
    cases c with
    | dispatch deliver => exact external_dispatch_invariant s deliver hs hp
    | _ =>
      simp only [ExternalCommand] at hc
      all_goals try contradiction
      all_goals dsimp only [external,PendingMigration.step] at valid ⊢
      all_goals split
      all_goals first
      | exact hs
      | try simp only [hp,Option.isSome_none,Bool.false_eq_true,↓reduceIte] at valid ⊢
        repeat' first
          | exact hs
          | (split <;> try simp only [*] at valid ⊢)
          | dsimp only [PendingMigration.enqueue,PendingMigration.reject,reject] at valid ⊢
        all_goals simp_all [beq_iff_eq,PendingMigration.enqueue,PendingMigration.reject,reject]
        all_goals try exact protocol_metadata_preserved s.active _ hs valid rfl rfl rfl
        all_goals first
        | rename_i frozen hh phase
          exact commit_metadata s.active _ _ hs hh phase valid
        | rename_i frozen hh phase
          apply request_metadata_preserved s.active _ _ _ hs
            (PendingMigration.head_fields _ _ _ hh).2 _ valid
          simp [Aligned,livePhase,deliveryPhase]
        | rename_i frozen empty hh phase
          simpa only [PendingMigration.retirement,hp,Active.residuals] using
            retirement_metadata s.active _ _ hs hh empty
              (by simpa only [PendingMigration.retirement,hp] using valid)
        | rename_i frozen hh peer hlocal
          have hr := PendingMigration.selected_request s.active.protocol _ _ _ hh
          have owner := peer_owned s.active.protocol _ _ ((uniform_valid _).mpr hs.protocol) hr _ peer
          dsimp only [ledgerInput] at owner
          rw [owner] at valid ⊢
          obtain ⟨work,hw,law⟩ := hs.residual _ _ hr
          first
          | have absent : s.active.residuals.get _ = none := hlocal
            rw [hw] at absent
            contradiction
          | apply cancel_metadata s.active _ _ _ hs hr _ valid
            exact hlocal
  · cases c <;> simp only [ExternalCommand] at hc
    all_goals try contradiction
    all_goals dsimp only [external]
    all_goals split <;> exact hs

end FRPSpec.Regional.Pending

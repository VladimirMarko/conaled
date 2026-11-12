import Applications.FRP.PendingMigrationSafety

/-! Independent delay source and the invariant needed to connect protocol
transitions to it. Source requests have no backend, slot, peer, or callback. -/
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace FRPSpec.PendingMigration

structure Source where
  state : Bool
  waiting : List Bool
  deriving DecidableEq, Repr

/-- Source cancellation removes the selected accepted occurrence before its
transition. Effective publication consumes the oldest remaining occurrence. -/
inductive SourceStep : Source → Outcome → Source → Prop
  | internal (a : Source) (o : Outcome)
      (noAccept : o.accepted = none) (noOutput : o.business = none)
      (noCancellation : o.cancellation ≠ some true) : SourceStep a o a
  | accept (a : Source) (o : Outcome) (x : Bool)
      (accepted : o.accepted = some x) (noOutput : o.business = none)
      (noCancellation : o.cancellation = none) :
      SourceStep a o ⟨a.state,a.waiting ++ [x]⟩
  | prevent (b x : Bool) (pre post : List Bool) (o : Outcome)
      (noAccept : o.accepted = none) (noOutput : o.business = none)
      (prevented : o.cancellation = some true) :
      SourceStep ⟨b,pre ++ x :: post⟩ o ⟨b,pre ++ post⟩
  | publish (b x : Bool) (xs : List Bool) (o : Outcome)
      (noAccept : o.accepted = none) (output : o.business = some b)
      (noCancellation : o.cancellation = none) :
      SourceStep ⟨b,x :: xs⟩ o ⟨x,xs⟩

/-- Protocol-internal confirmation/commit does not advance this source twice.
It advances at the peer effect; the backend may still await confirmation. -/
def sourceState (s : Session) : Bool := match head s with
  | some (slot,r) => match s.peer.get slot with
    | some (.published _ _) => r.input
    | _ => s.active.logical
  | none => s.active.logical

def waiting (s : Session) : List Bool := s.order.filterMap fun slot =>
  match s.peer.get slot with
  | some (.reserved x) => some x
  | _ => none

def source (s : Session) : Source := ⟨sourceState s,waiting s⟩

/-- The first publication, not its confirmation, advances the source. -/
def SlotValid (b : Bool) (request : Option Request) (entry : Option Ledger) : Prop :=
  match request,entry with
  | none,none => True
  | some r,some ledger =>
    (r.routeOpen = false → r.phase = .committed ∨ r.phase = .cancelled) ∧
    match r.phase with
    | .accepted => ledger = .reserved r.input
    | .computed => r.output = b ∧
        (ledger = .reserved r.input ∨ ledger = .published r.input r.output)
    | .confirmed => r.output = b ∧ ledger = .published r.input r.output
    | .committed => r.input = b ∧ ledger = .published r.input r.output
    | .cancelled => ledger = .cancelled r.input
  | _,_ => False

def MessageValid (s : Session) (m : Message) : Prop :=
  s.order.head? = some m.slot ∧ ∃ r, s.requests.get m.slot = some r ∧
    match m with
    | .publish _ _ y | .retry _ _ y => y = r.output ∧ r.phase ≠ .accepted
    | .reply _ .published => s.peer.get m.slot = some (.published r.input r.output)
    | _ => True

/-- Full live-state invariant: slots are precisely the admission-order entries;
only its head may compute; every delayed event belongs to that head. -/
structure Valid (s : Session) : Prop where
  order : s.order.Nodup
  occupied : ∀ slot, slot ∈ s.order ↔ (s.requests.get slot).isSome = true
  slots : ∀ slot, SlotValid s.active.logical (s.requests.get slot) (s.peer.get slot)
  tail : ∀ slot ∈ s.order.tail, ∀ r, s.requests.get slot = some r →
    r.phase = .accepted ∨ r.phase = .cancelled
  messages : ∀ m ∈ s.queue.messages, MessageValid s m

@[simp] theorem slots_get_put_same {α : Type} (s : Slots α) (slot : Bool) (x : Option α) :
    (s.put slot x).get slot = x := by cases slot <;> rfl

@[simp] theorem slots_get_put_other {α : Type} (s : Slots α) (slot : Bool) (x : Option α) :
    (s.put slot x).get (!slot) = s.get (!slot) := by cases slot <;> rfl

theorem initial_valid (k : Migration.Kind) : Valid (initial k) := by
  constructor
  · simp [initial]
  · intro slot; cases slot <;> simp [initial, Slots.get]
  · intro slot; cases slot <;> simp [initial, Slots.get, SlotValid]
  · simp [initial]
  · simp [initial, Queue.empty]

theorem initial_source (k : Migration.Kind) : source (initial k) = ⟨false,[]⟩ := by
  cases k <;> rfl

theorem transfer_source (s : Session) (k : Migration.Kind) :
    source (transfer s k) = source s := by
  simp only [source, sourceState, head, transfer, waiting, Migration.realize_logical]

theorem transfer_valid (s : Session) (k : Migration.Kind) (h : Valid s) :
    Valid (transfer s k) := by
  rcases h with ⟨a,b,c,d,e⟩
  exact ⟨a,b,by simpa only [transfer, Migration.realize_logical] using c,d,e⟩

theorem head_occupied (s : Session) (h : Valid s) (slot : Bool)
    (hh : s.order.head? = some slot) : ∃ r, s.requests.get slot = some r := by
  have member : slot ∈ s.order := List.mem_of_mem_head? hh
  have present := (h.occupied slot).mp member
  cases hr : s.requests.get slot with
  | none => simp [hr] at present
  | some r => exact ⟨r,rfl⟩

/-- There is no external callback list when no admission head exists. -/
theorem empty_order_queue (s : Session) (h : Valid s) (ho : s.order = []) :
    s.queue.messages = [] := by
  cases hq : s.queue.messages with
  | nil => rfl
  | cons m ms =>
    have hm := (h.messages m (by simp [hq])).1
    simp [ho] at hm

/-- All event kinds refer to the admission head; after closing and draining it,
release cannot leave traffic that later aliases a reused slot. -/
theorem released_queue_empty (s : Session) (h : Valid s) (slot : Bool) (r : Request)
    (hh : head s = some (slot,r)) (released : (step s .release).status = .released) :
    s.queue.messages = [] := by
  have absent := (release_excludes s slot r hh released).2
  have ho : s.order.head? = some slot := by
    unfold head at hh
    cases hx : s.order.head? with
    | none => simp [hx] at hh
    | some a =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hh
      rw [hx] at hh
      cases hr : s.requests.get a with
      | none => simp [hr] at hh
      | some value => simp [hr] at hh; exact hh.1 ▸ rfl
  cases hq : s.queue.messages with
  | nil => rfl
  | cons m ms =>
    have mem : m ∈ s.queue.messages := by simp [hq]
    have hm := (h.messages m mem).1
    have eqslot : m.slot = slot := Option.some.inj (hm.symm.trans ho)
    exact False.elim (absent m mem eqslot)

/-- A live bounded checkpoint cannot contain more occupied identities than the
physical two-slot carrier. Quarantined requests still count as occupied. -/
theorem valid_bounded (s : Session) (h : Valid s) : s.order.length ≤ 2 := by
  simpa using h.order.length_le_card

/-- Under the reachable-state invariant, a new peer effect is the next delay
output. This statement uses the independent source state, not local knowledge
of a publication confirmation. -/
theorem publication_source (s : Session) (hs : Valid s) (slot x y output : Bool)
    (hm : MessageValid s (.publish slot x y))
    (he : (publish (s.peer.get slot) x y).2.2 = some output) :
    output = sourceState s := by
  rcases hm with ⟨ho,r,hr,hy,hphase⟩
  simp only [Message.slot] at ho hr
  have hv := hs.slots slot
  rw [hr] at hv
  cases hl : s.peer.get slot with
  | none => simp [publish, hl] at he
  | some ledger =>
    cases ledger with
    | published a b => simp [publish, hl] at he
    | cancelled a => simp [publish, hl] at he
    | reserved a =>
      simp only [publish, hl] at he
      split at he
      · simp only [Option.some.injEq] at he
        have hh : head s = some (slot,r) := by simp [head, ho, hr]
        simp only [sourceState, hh, hl]
        rw [hl] at hv
        cases hp : r.phase <;> simp_all [SlotValid]
      · contradiction

/-- Once a peer effect is installed, every subsequent matching retry has no
business effect, independently of whether its confirmation was delivered. -/
theorem publication_once (entry : Option Ledger) (x y output : Bool)
    (h : (publish entry x y).2.2 = some output) :
    publish (publish entry x y).1 x y = ((publish entry x y).1,.published,none) := by
  cases entry with
  | none => simp [publish] at h
  | some entry =>
    cases entry with
    | published a b => simp [publish] at h
    | cancelled a => simp [publish] at h
    | reserved a =>
      cases a <;> cases x <;> cases y <;> simp_all [publish]

/-- Source meaning and its live-state invariant ignore migration scratch and
physical representation. They retain the entire protocol checkpoint. -/
theorem checkpoint_source {s t : Session} (h : checkpoint s = checkpoint t) :
    source s = source t := by
  have hb := congrArg Checkpoint.logical h
  have hr := congrArg Checkpoint.requests h
  have hp := congrArg Checkpoint.peer h
  have ho := congrArg Checkpoint.order h
  simp only [checkpoint] at hb hr hp ho
  simp only [source, sourceState, waiting, head, hr, hp, ho, hb]

theorem checkpoint_valid {s t : Session} (h : checkpoint s = checkpoint t)
    (hs : Valid s) : Valid t := by
  have hb := congrArg Checkpoint.logical h
  have hr := congrArg Checkpoint.requests h
  have hp := congrArg Checkpoint.peer h
  have ho := congrArg Checkpoint.order h
  have hq := congrArg Checkpoint.queue h
  simp only [checkpoint] at hb hr hp ho hq
  rcases hs with ⟨a,b,c,d,e⟩
  constructor
  · simpa only [ho] using a
  · simpa only [ho,hr] using b
  · simpa only [hb,hr,hp] using c
  · simpa only [ho,hr] using d
  · simpa only [MessageValid,ho,hr,hp,hq] using e

/-- Enqueuing an already validated head event preserves both the source and
all live-state obligations; refusal leaves them unchanged. -/
theorem enqueue_source (s : Session) (r : Request) (m : Message) :
    source (enqueue s r m).session = source s := by
  unfold enqueue
  repeat' first | split | rfl

theorem queue_push_members (q : Queue) (m : Message) (q' : Queue)
    (h : q.push m = some q') : q'.messages = q.messages ++ [m] := by
  unfold Queue.push at h
  split at h
  · cases h; rfl
  · contradiction

theorem enqueue_valid (s : Session) (r : Request) (m : Message)
    (hs : Valid s) (hm : MessageValid s m) : Valid (enqueue s r m).session := by
  unfold enqueue
  split
  · exact hs
  · split
    · exact hs
    · rename_i q hq
      have he := queue_push_members s.queue m q hq
      refine ⟨hs.order,hs.occupied,hs.slots,hs.tail,?_⟩
      intro event hmem
      simp only [he,List.mem_append,List.mem_singleton] at hmem
      rcases hmem with hmem | hmem
      · exact hs.messages event hmem
      · subst event; exact hm

/-- Migration changes representation and scratch ownership, never the
accepted-order delay checkpoint or its externally observed transition. -/
theorem migration_checkpoint (s : Session) (c : Command) (hc : ¬ Business c) :
    checkpoint (step s c).session = checkpoint s ∧
    (step s c).accepted = none ∧ (step s c).business = none ∧
      (step s c).cancellation = none := by
  cases c <;> simp only [Business,not_true_eq_false] at hc
  case cancelMigration => exact ⟨rfl,rfl,rfl,rfl⟩
  case ownershipCommit =>
    simp only [step]
    split
    · exact ⟨rfl,rfl,rfl,rfl⟩
    · rename_i p hp
      exact ⟨by simpa only [checkpoint] using
        congrArg (fun b => Checkpoint.mk b s.requests s.peer s.order s.queue) p.continuation,
        rfl,rfl,rfl⟩
  case prepare target budget alloc valid =>
    simp only [step]
    repeat' first | split | exact ⟨rfl,rfl,rfl,rfl⟩

theorem migration_valid (s : Session) (c : Command) (hc : ¬ Business c)
    (hs : Valid s) : Valid (step s c).session :=
  checkpoint_valid (migration_checkpoint s c hc).1.symm hs

theorem migration_source_step (s : Session) (c : Command) (hc : ¬ Business c) :
    SourceStep (source s) (step s c) (source (step s c).session) := by
  obtain ⟨h,ha,hb,hc⟩ := migration_checkpoint s c hc
  rw [checkpoint_source h]
  exact .internal _ _ ha hb (by simp [hc])

@[simp] theorem slots_get_put {α : Type} (s : Slots α) (slot other : Bool)
    (x : Option α) : (s.put slot x).get other = if other = slot then x else s.get other := by
  cases slot <;> cases other <;> rfl

/-- The state update used by successful admission. -/
def admission (s : Session) (slot x : Bool) : Session :=
  {s with requests := s.requests.put slot (some ⟨x,false,.accepted,true⟩)
          peer := s.peer.put slot (some (.reserved x))
          order := s.order ++ [slot]}

theorem admission_valid (s : Session) (slot x : Bool) (hs : Valid s)
    (free : s.requests.get slot = none) : Valid (admission s slot x) := by
  have absent : slot ∉ s.order := by
    intro h
    have hp := (hs.occupied slot).mp h
    simp [free] at hp
  constructor
  · change (s.order ++ [slot]).Nodup
    rw [List.nodup_append]
    refine ⟨hs.order,by simp,?_⟩
    intro a ha b hb eq
    simp only [List.mem_singleton] at hb
    exact absent ((eq.trans hb) ▸ ha)
  · intro a
    by_cases ha : a = slot
    · subst a; simp [admission]
    · simp [admission,ha,hs.occupied a]
  · intro a
    by_cases ha : a = slot
    · subst a; simp [admission,SlotValid]
    · simpa only [admission,slots_get_put,ite_eq_right ha] using hs.slots a
  · intro a ha r hr
    by_cases eq : a = slot
    · subst a
      simp only [admission,slots_get_put_same,Option.some.injEq] at hr
      subst r; exact Or.inl rfl
    · have old : a ∈ s.order.tail := by
        cases ho : s.order with
        | nil => simp [admission,ho] at ha
        | cons b bs => simpa [admission,ho,eq] using ha
      apply hs.tail a old r
      simpa only [admission,slots_get_put,ite_eq_right eq] using hr
  · intro m hm
    have old := hs.messages m hm
    have member : m.slot ∈ s.order := List.mem_of_mem_head? old.1
    have ne : m.slot ≠ slot := by intro eq; exact absent (eq ▸ member)
    have hn : s.order ≠ [] := by intro eq; simp [eq] at member
    simpa [MessageValid,admission,ne,List.head?_append_of_ne_nil _ hn] using old

theorem admission_source (s : Session) (slot x : Bool) (hs : Valid s)
    (free : s.requests.get slot = none) :
    source (admission s slot x) = ⟨(source s).state,(source s).waiting ++ [x]⟩ := by
  have absent : slot ∉ s.order := by
    intro h
    have hp := (hs.occupied slot).mp h
    simp [free] at hp
  have maps : s.order.filterMap (fun a => match (s.peer.put slot (some (.reserved x))).get a with
        | some (.reserved y) => some y | _ => none) = waiting s := by
    apply List.filterMap_congr
    intro a ha
    have ne : a ≠ slot := by intro eq; exact absent (eq ▸ ha)
    simp only [slots_get_put,ite_eq_right ne]
  have hw : waiting (admission s slot x) = waiting s ++ [x] := by
    simp only [waiting,admission,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,
      slots_get_put_same]
    exact congrArg (fun xs => xs ++ [x]) maps
  have hb : sourceState (admission s slot x) = sourceState s := by
    cases ho : s.order with
    | nil => simp [sourceState,head,admission,ho]
    | cons a as =>
      have ne : a ≠ slot := by intro eq; apply absent; simp [ho,eq]
      cases hr : s.requests.get a <;> simp [sourceState,head,admission,ho,ne,hr]
  exact congrArg₂ Source.mk hb hw

theorem rejected_source (s : Session) (status : Status) (hs : Valid s) :
    Valid (reject s status).session ∧
    SourceStep (source s) (reject s status) (source (reject s status).session) :=
  ⟨hs,.internal _ _ rfl rfl (by simp [reject])⟩

theorem admitted_source (s : Session) (slot x : Bool) (hs : Valid s)
    (free : s.requests.get slot = none) :
    Valid (admission s slot x) ∧
    SourceStep (source s) ⟨admission s slot x,.accepted,some x,none,none,[]⟩
      (source (admission s slot x)) := by
  refine ⟨admission_valid s slot x hs free,?_⟩
  rw [admission_source s slot x hs free]
  exact .accept _ _ x rfl rfl rfl

theorem accept_source (s : Session) (x : Bool) (hs : Valid s) :
    Valid (step s (.accept x)).session ∧
    SourceStep (source s) (step s (.accept x)) (source (step s (.accept x)).session) := by
  simp only [step]
  split
  · exact rejected_source _ _ hs
  · split
    · exact rejected_source _ _ hs
    · split
      · exact rejected_source _ _ hs
      · rename_i slot heq
        apply admitted_source s slot x hs
        split at heq
        · rename_i hf
          have eq : false = slot := Option.some.inj heq
          rw [← eq]
          exact Option.isNone_iff_eq_none.mp hf
        · split at heq
          · rename_i ht
            have eq : true = slot := Option.some.inj heq
            rw [← eq]
            exact Option.isNone_iff_eq_none.mp ht
          · contradiction

theorem head_fields (s : Session) (slot : Bool) (r : Request)
    (h : head s = some (slot,r)) :
    s.order.head? = some slot ∧ s.requests.get slot = some r := by
  unfold head at h
  simp only [Bool.false_eq_true,↓reduceIte] at h
  cases ho : s.order.head? with
  | none => simp [ho] at h
  | some a =>
    rw [ho] at h
    cases hr : s.requests.get a with
    | none => simp [hr] at h
    | some q =>
      simp [hr] at h
      obtain ⟨rfl,rfl⟩ := h
      exact ⟨rfl,hr⟩

theorem head_not_tail (s : Session) (hs : Valid s) (slot : Bool)
    (ho : s.order.head? = some slot) : slot ∉ s.order.tail := by
  cases he : s.order with
  | nil => simp [he] at ho
  | cons a as =>
    simp only [he,List.head?_cons,Option.some.injEq] at ho
    subst a
    have hn := hs.order
    rw [he,List.nodup_cons] at hn
    simpa only [he,List.tail_cons] using hn.1

/-- Replacing the head leaves admission order and all untouched slots intact.
The caller supplies the new local ledger and delayed-event obligations. -/
theorem head_update_valid (s : Session) (slot : Bool) (r n : Request) (hs : Valid s)
    (hh : head s = some (slot,r))
    (slotLaw : SlotValid s.active.logical (some n) (s.peer.get slot))
    (events : ∀ m ∈ s.queue.messages, MessageValid (update s slot n) m) :
    Valid (update s slot n) := by
  obtain ⟨ho,hr⟩ := head_fields s slot r hh
  have hn := head_not_tail s hs slot ho
  refine ⟨hs.order,?_,?_,?_,events⟩
  · intro a
    by_cases eq : a = slot
    · subst a
      have hm : slot ∈ s.order := List.mem_of_mem_head? ho
      simp [update,hm]
    · simpa only [update,slots_get_put,ite_eq_right eq] using hs.occupied a
  · intro a
    by_cases eq : a = slot
    · subst a; simpa only [update,slots_get_put_same] using slotLaw
    · simpa only [update,slots_get_put,ite_eq_right eq] using hs.slots a
  · intro a ha q hq
    have ne : a ≠ slot := by intro eq; exact hn (eq ▸ ha)
    exact hs.tail a ha q (by simpa only [update,slots_get_put,ite_eq_right ne] using hq)

theorem head_update_source (s : Session) (slot : Bool) (r n : Request)
    (hh : head s = some (slot,r)) (hi : n.input = r.input) :
    source (update s slot n) = source s := by
  obtain ⟨ho,hr⟩ := head_fields s slot r hh
  have hu : head (update s slot n) = some (slot,n) := by simp [head,update,ho]
  apply congrArg₂ Source.mk
  · unfold sourceState
    rw [hu,hh]
    dsimp only [update]
    rw [hi]
  · rfl

theorem evaluate_head_valid (s : Session) (slot : Bool) (r : Request) (hs : Valid s)
    (hh : head s = some (slot,r)) (phase : r.phase = .accepted) :
    Valid (update s slot {r with output := s.active.logical, phase := .computed}) := by
  obtain ⟨ho,hr⟩ := head_fields s slot r hh
  have hv := hs.slots slot
  rw [hr] at hv
  have ledger : s.peer.get slot = some (.reserved r.input) := by
    cases hp : s.peer.get slot with
    | none => simp [hp,SlotValid] at hv
    | some entry =>
      simp only [SlotValid,hp,phase] at hv
      exact congrArg some hv.2
  have route : r.routeOpen = true := by
    cases hroute : r.routeOpen
    · have h := hv
      simp [ledger,SlotValid,phase,hroute] at h
    · rfl
  apply head_update_valid s slot r _ hs hh
  · simp [SlotValid,ledger,route]
  · intro m hm
    obtain ⟨hhead,q,hq,law⟩ := hs.messages m hm
    have eqslot : m.slot = slot := Option.some.inj (hhead.symm.trans ho)
    rw [eqslot,hr] at hq
    cases hq
    cases m with
    | publish a x y => simp_all [Message.slot]
    | retry a x y => simp_all [Message.slot]
    | query a =>
      simp only [Message.slot] at eqslot
      subst a
      simp [MessageValid,Message.slot,update,ho]
    | reply a answer =>
      simp only [Message.slot] at eqslot
      subst a
      cases answer <;> simp_all [MessageValid,Message.slot,update]

theorem enqueued_source (s : Session) (r : Request) (m : Message)
    (hs : Valid s) (hm : MessageValid s m) :
    Valid (enqueue s r m).session ∧
    SourceStep (source s) (enqueue s r m) (source (enqueue s r m).session) := by
  refine ⟨enqueue_valid s r m hs hm,?_⟩
  rw [enqueue_source]
  apply SourceStep.internal
  all_goals unfold enqueue; repeat' first | split | rfl | simp [reject]

theorem query_source (s : Session) (hs : Valid s) :
    Valid (step s .queryPeer).session ∧
    SourceStep (source s) (step s .queryPeer) (source (step s .queryPeer).session) := by
  simp only [step]
  split
  · exact rejected_source _ _ hs
  · split
    · exact rejected_source _ _ hs
    · rename_i slot r hh
      obtain ⟨ho,hr⟩ := head_fields s slot r hh
      apply enqueued_source _ _ _ hs
      exact ⟨ho,r,hr,True.intro⟩

theorem publish_source (s : Session) (hs : Valid s) :
    Valid (step s .publish).session ∧
    SourceStep (source s) (step s .publish) (source (step s .publish).session) := by
  simp only [step]
  split
  · exact rejected_source _ _ hs
  · split
    · exact rejected_source _ _ hs
    · rename_i slot r hh
      obtain ⟨ho,hr⟩ := head_fields s slot r hh
      split
      · rename_i phase
        apply enqueued_source _ _ _ hs
        refine ⟨ho,r,hr,rfl,?_⟩
        have hp : r.phase = .computed := by simpa using phase
        simp [hp]
      · exact rejected_source _ _ hs

theorem evaluate_source (s : Session) (hs : Valid s) :
    Valid (step s .evaluate).session ∧
    SourceStep (source s) (step s .evaluate) (source (step s .evaluate).session) := by
  simp only [step]
  split
  · exact rejected_source _ _ hs
  · split
    · exact rejected_source _ _ hs
    · rename_i slot r hh
      split
      · rename_i phase
        simp only [evaluate_output]
        refine ⟨evaluate_head_valid s slot r hs hh (by simpa using phase),?_⟩
        rw [head_update_source s slot r {r with output := s.active.logical,phase := .computed} hh rfl]
        exact .internal _ _ rfl rfl (by simp)
      · exact rejected_source _ _ hs

theorem retry_source (s : Session) (conflict : Bool) (hs : Valid s) :
    Valid (step s (.retry conflict)).session ∧
    SourceStep (source s) (step s (.retry conflict)) (source (step s (.retry conflict)).session) := by
  simp only [step]
  split
  · exact rejected_source _ _ hs
  · split
    · exact rejected_source _ _ hs
    · rename_i slot r hh
      obtain ⟨ho,hr⟩ := head_fields s slot r hh
      split
      · rename_i phase
        apply enqueued_source _ _ _ hs
        refine ⟨ho,r,hr,rfl,?_⟩
        cases hp : r.phase <;> simp_all
      · exact rejected_source _ _ hs

theorem close_head_valid (s : Session) (slot : Bool) (r : Request) (hs : Valid s)
    (hh : head s = some (slot,r)) (terminal : r.phase = .committed ∨ r.phase = .cancelled) :
    Valid (update s slot {r with routeOpen := false}) := by
  obtain ⟨ho,hr⟩ := head_fields s slot r hh
  apply head_update_valid s slot r _ hs hh
  · have hv := hs.slots slot
    rw [hr] at hv
    cases hp : s.peer.get slot with
    | none => simp [hp,SlotValid] at hv
    | some entry =>
      simp only [SlotValid,hp] at hv ⊢
      exact ⟨fun _ => terminal,hv.2⟩
  · intro m hm
    obtain ⟨hhead,q,hq,law⟩ := hs.messages m hm
    have eqslot : m.slot = slot := Option.some.inj (hhead.symm.trans ho)
    rw [eqslot,hr] at hq
    cases hq
    refine ⟨hhead,{r with routeOpen := false},?_,?_⟩
    · simp [update,eqslot]
    · cases m <;> exact law

theorem close_source (s : Session) (hs : Valid s) :
    Valid (step s .close).session ∧
    SourceStep (source s) (step s .close) (source (step s .close).session) := by
  simp only [step]
  split
  · exact rejected_source _ _ hs
  · split
    · exact rejected_source _ _ hs
    · rename_i slot r hh
      split
      · rename_i phase
        refine ⟨close_head_valid s slot r hs hh (by simpa using phase),?_⟩
        rw [head_update_source s slot r {r with routeOpen := false} hh rfl]
        exact .internal _ _ rfl rfl (by simp)
      · exact rejected_source _ _ hs

theorem reserved_input (s : Session) (slot x : Bool) (r : Request) (hs : Valid s)
    (hr : s.requests.get slot = some r) (hp : s.peer.get slot = some (.reserved x)) :
    x = r.input := by
  have hv := hs.slots slot
  cases phase : r.phase <;> simp_all [SlotValid]

def prevention (s : Session) (slot : Bool) (r : Request) : Session :=
  {(update s slot {r with phase := .cancelled}) with
    peer := s.peer.put slot (some (.cancelled r.input))}

theorem prevention_valid (s : Session) (slot : Bool) (r : Request) (hs : Valid s)
    (hr : s.requests.get slot = some r) (hp : s.peer.get slot = some (.reserved r.input)) :
    Valid (prevention s slot r) := by
  refine ⟨hs.order,?_,?_,?_,?_⟩
  · intro a
    by_cases eq : a = slot
    · subst a
      have hm := (hs.occupied slot).mpr (by simp [hr])
      simp [prevention,update,hm]
    · simpa only [prevention,update,slots_get_put,ite_eq_right eq] using hs.occupied a
  · intro a
    by_cases eq : a = slot
    · subst a; simp [prevention,update,SlotValid]
    · simpa only [prevention,update,slots_get_put,ite_eq_right eq] using hs.slots a
  · intro a ha q hq
    by_cases eq : a = slot
    · subst a
      simp only [prevention,update,slots_get_put_same,Option.some.injEq] at hq
      subst q; exact Or.inr rfl
    · apply hs.tail a ha q
      simpa only [prevention,update,slots_get_put,ite_eq_right eq] using hq
  · intro m hm
    obtain ⟨ho,q,hq,law⟩ := hs.messages m hm
    by_cases eq : m.slot = slot
    · rw [eq,hr] at hq
      cases hq
      refine ⟨ho,{r with phase := .cancelled},?_,?_⟩
      · simp [prevention,update,eq]
      · cases m with
        | publish a x y => exact ⟨law.1,by simp⟩
        | retry a x y => exact ⟨law.1,by simp⟩
        | query a => trivial
        | reply a answer =>
          cases answer <;> simp_all [Message.slot,prevention,update]
    · refine ⟨ho,q,?_,?_⟩
      · simpa only [prevention,update,slots_get_put,ite_eq_right eq] using hq
      · cases m with
        | publish a x y => exact law
        | retry a x y => exact law
        | query a => trivial
        | reply a answer =>
          cases answer <;> simp_all [Message.slot,prevention,update]

theorem prevention_state (s : Session) (slot : Bool) (r : Request)
    (hr : s.requests.get slot = some r) (hp : s.peer.get slot = some (.reserved r.input)) :
    sourceState (prevention s slot r) = sourceState s := by
  cases ho : s.order.head? with
  | none => simp [sourceState,head,prevention,update,ho]
  | some a =>
    by_cases eq : a = slot
    · subst a; simp [sourceState,head,prevention,update,ho,hr,hp]
    · cases hq : s.requests.get a <;> simp [sourceState,head,prevention,update,ho,hq,eq]

theorem prevention_source (s : Session) (slot : Bool) (r : Request) (hs : Valid s)
    (hr : s.requests.get slot = some r) (hp : s.peer.get slot = some (.reserved r.input)) :
    SourceStep (source s) ⟨prevention s slot r,.prevented,none,none,some true,[]⟩
      (source (prevention s slot r)) := by
  have member := (hs.occupied slot).mpr (by simp [hr])
  obtain ⟨pre,post,order⟩ := List.mem_iff_append.mp member
  have nodup := hs.order
  rw [order,List.nodup_append] at nodup
  have prefree : slot ∉ pre := by
    intro h
    exact nodup.2.2 slot h slot (by simp) rfl
  have postfree : slot ∉ post := (List.nodup_cons.mp nodup.2.1).1
  let pending := fun a => match s.peer.get a with
    | some (.reserved x) => some x | _ => none
  have mapEq : ∀ xs : List Bool, slot ∉ xs →
      xs.filterMap (fun a => match (prevention s slot r).peer.get a with
        | some (.reserved x) => some x | _ => none) = xs.filterMap pending := by
    intro xs absent
    apply List.filterMap_congr
    intro a ha
    have ne : a ≠ slot := by intro eq; exact absent (eq ▸ ha)
    simp [pending,prevention,slots_get_put,ne]
  have old : waiting s = pre.filterMap pending ++ r.input :: post.filterMap pending := by
    simp [waiting,order,pending,hp]
  have new : waiting (prevention s slot r) = pre.filterMap pending ++ post.filterMap pending := by
    change (s.order.filterMap _) = _
    rw [order,List.filterMap_append,List.filterMap_cons]
    simp only [prevention,slots_get_put_same]
    exact congrArg₂ List.append (mapEq pre prefree) (mapEq post postfree)
  change SourceStep ⟨sourceState s,waiting s⟩ _
    ⟨sourceState (prevention s slot r),waiting (prevention s slot r)⟩
  rw [old,new,prevention_state s slot r hr hp]
  exact .prevent _ _ _ _ _ rfl rfl rfl

theorem selected_request (s : Session) (second slot : Bool) (r : Request)
    (h : head s second = some (slot,r)) : s.requests.get slot = some r := by
  unfold head at h
  cases ho : (if second then s.order.tail else s.order).head? with
  | none => simp [ho] at h
  | some a =>
    rw [ho] at h
    cases hr : s.requests.get a with
    | none => simp [hr] at h
    | some q =>
      simp [hr] at h
      obtain ⟨rfl,rfl⟩ := h
      exact hr

theorem cancel_source (s : Session) (second : Bool) (hs : Valid s) :
    Valid (step s (.cancelWork second)).session ∧
    SourceStep (source s) (step s (.cancelWork second))
      (source (step s (.cancelWork second)).session) := by
  simp only [step]
  split
  · exact rejected_source _ _ hs
  · split
    · exact rejected_source _ _ hs
    · rename_i slot r hh
      have hr := selected_request s second slot r hh
      cases hp : s.peer.get slot with
      | none => exact rejected_source _ _ hs
      | some entry =>
        cases entry with
        | cancelled x => exact rejected_source _ _ hs
        | published x y => exact ⟨hs,.internal _ _ rfl rfl (by simp)⟩
        | reserved x =>
          have eq := reserved_input s slot x r hs hr hp
          subst x
          exact ⟨prevention_valid s slot r hs hr hp,prevention_source s slot r hs hr hp⟩

theorem other_slot_tail (s : Session) (hs : Valid s) (slot a : Bool) (q : Request)
    (ho : s.order.head? = some slot) (ne : a ≠ slot) (hq : s.requests.get a = some q) :
    a ∈ s.order.tail := by
  have mem := (hs.occupied a).mpr (by simp [hq])
  cases he : s.order with
  | nil => simp [he] at ho
  | cons b bs =>
    simp only [he,List.head?_cons,Option.some.injEq] at ho
    subst b
    simpa [he,ne] using mem

def logicalCommit (s : Session) (slot : Bool) (r : Request) : Session :=
  {(update s slot {r with phase := .committed}) with
    active := Migration.realize s.active.kind r.input,prepared := none}

theorem commit_head_valid (s : Session) (slot : Bool) (r : Request) (hs : Valid s)
    (hh : head s = some (slot,r)) (phase : r.phase = .confirmed) :
    Valid (logicalCommit s slot r) := by
  obtain ⟨ho,hr⟩ := head_fields s slot r hh
  have hv := hs.slots slot
  rw [hr] at hv
  have ledger : s.peer.get slot = some (.published r.input r.output) := by
    cases hp : s.peer.get slot with
    | none => simp [hp,SlotValid] at hv
    | some entry =>
      simp only [SlotValid,hp,phase] at hv
      exact congrArg some hv.2.2
  refine ⟨hs.order,?_,?_,?_,?_⟩
  · intro a
    by_cases eq : a = slot
    · subst a
      have mem := List.mem_of_mem_head? ho
      simp [logicalCommit,update,mem]
    · simpa only [logicalCommit,update,slots_get_put,ite_eq_right eq] using hs.occupied a
  · intro a
    by_cases eq : a = slot
    · subst a; simp [logicalCommit,update,SlotValid,ledger]
    · simp only [logicalCommit,update,slots_get_put,ite_eq_right eq,Migration.realize_logical]
      have old := hs.slots a
      cases hq : s.requests.get a with
      | none =>
        cases hp : s.peer.get a <;> simp_all [SlotValid]
      | some q =>
        have tail := hs.tail a (other_slot_tail s hs slot a q ho eq hq) q hq
        cases hp : s.peer.get a <;> rcases tail with ha | hc <;> simp_all [SlotValid]
  · intro a ha q hq
    have ne : a ≠ slot := by intro eq; exact head_not_tail s hs slot ho (eq ▸ ha)
    exact hs.tail a ha q (by simpa only [logicalCommit,update,slots_get_put,ite_eq_right ne] using hq)
  · intro m hm
    obtain ⟨hhead,q,hq,law⟩ := hs.messages m hm
    have eqslot : m.slot = slot := Option.some.inj (hhead.symm.trans ho)
    rw [eqslot,hr] at hq
    cases hq
    refine ⟨hhead,{r with phase := .committed},?_,?_⟩
    · simp [logicalCommit,update,eqslot]
    · cases m with
      | publish a x y => exact ⟨law.1,by simp⟩
      | retry a x y => exact ⟨law.1,by simp⟩
      | query a => trivial
      | reply a answer => cases answer <;> exact law

theorem commit_head_source (s : Session) (slot : Bool) (r : Request) (hs : Valid s)
    (hh : head s = some (slot,r)) (phase : r.phase = .confirmed) :
    source (logicalCommit s slot r) = source s := by
  obtain ⟨ho,hr⟩ := head_fields s slot r hh
  have hv := hs.slots slot
  have ledger : s.peer.get slot = some (.published r.input r.output) := by
    cases hp : s.peer.get slot with
    | none => simp [hr,hp,SlotValid] at hv
    | some entry =>
      simp only [hr,SlotValid,hp,phase] at hv
      exact congrArg some hv.2.2
  simp [source,sourceState,head,logicalCommit,update,waiting,ho,hr,ledger]

theorem commit_source (s : Session) (hs : Valid s) :
    Valid (step s .tickCommit).session ∧
    SourceStep (source s) (step s .tickCommit) (source (step s .tickCommit).session) := by
  simp only [step]
  split
  · exact rejected_source _ _ hs
  · split
    · exact rejected_source _ _ hs
    · rename_i slot r hh
      split
      · rename_i phase
        have hp : r.phase = .confirmed := by simpa using phase
        refine ⟨commit_head_valid s slot r hs hh hp,?_⟩
        change SourceStep (source s) _ (source (logicalCommit s slot r))
        rw [commit_head_source s slot r hs hh hp]
        exact .internal _ _ rfl rfl (by simp)
      · exact rejected_source _ _ hs

def retirement (s : Session) (slot : Bool) : Session :=
  {s with requests := s.requests.put slot none,peer := s.peer.put slot none,order := s.order.tail}

theorem retirement_valid (s : Session) (slot : Bool) (r : Request) (hs : Valid s)
    (hh : head s = some (slot,r)) (empty : s.queue.messages = []) :
    Valid (retirement s slot) := by
  obtain ⟨ho,hr⟩ := head_fields s slot r hh
  have order := List.eq_cons_of_mem_head? ho
  have hn := head_not_tail s hs slot ho
  refine ⟨hs.order.tail,?_,?_,?_,?_⟩
  · intro a
    by_cases eq : a = slot
    · subst a; simp [retirement,hn]
    · have old := hs.occupied a
      nth_rw 1 [order] at old
      simpa [retirement,eq] using old
  · intro a
    by_cases eq : a = slot
    · subst a; simp [retirement,SlotValid]
    · simpa only [retirement,slots_get_put,ite_eq_right eq] using hs.slots a
  · intro a ha q hq
    have mem : a ∈ s.order.tail := List.mem_of_mem_tail ha
    have ne : a ≠ slot := by intro eq; exact hn (eq ▸ mem)
    exact hs.tail a mem q (by simpa only [retirement,slots_get_put,ite_eq_right ne] using hq)
  · intro m hm; simp [retirement,empty] at hm

theorem retirement_source (s : Session) (slot : Bool) (r : Request) (hs : Valid s)
    (hh : head s = some (slot,r)) (terminal : r.phase = .committed ∨ r.phase = .cancelled) :
    source (retirement s slot) = source s := by
  obtain ⟨ho,hr⟩ := head_fields s slot r hh
  have order := List.eq_cons_of_mem_head? ho
  have hn := head_not_tail s hs slot ho
  have hv := hs.slots slot
  have oldstate : sourceState s = s.active.logical := by
    clear order
    simp only [sourceState,hh]
    cases hp : s.peer.get slot <;> rcases terminal with ht | ht <;> simp_all [SlotValid]
  have newstate : sourceState (retirement s slot) = s.active.logical := by
    clear order
    cases htail : s.order.tail.head? with
    | none => simp [sourceState,head,retirement,htail]
    | some a =>
      have mem : a ∈ s.order.tail := List.mem_of_mem_head? htail
      have ne : a ≠ slot := by intro eq; exact hn (eq ▸ mem)
      obtain ⟨q,hq⟩ : ∃ q, s.requests.get a = some q := by
        have present := (hs.occupied a).mp (List.mem_of_mem_tail mem)
        cases he : s.requests.get a with
        | none => simp [he] at present
        | some q => exact ⟨q,rfl⟩
      have tail := hs.tail a mem q hq
      have valid := hs.slots a
      cases hp : s.peer.get a <;> rcases tail with ht | ht <;>
        simp_all [sourceState,head,retirement,SlotValid]
  have maps : s.order.tail.filterMap (fun a => match (s.peer.put slot none).get a with
      | some (.reserved x) => some x | _ => none) =
      s.order.tail.filterMap (fun a => match s.peer.get a with
      | some (.reserved x) => some x | _ => none) := by
    apply List.filterMap_congr
    intro a ha
    have ne : a ≠ slot := by intro eq; exact hn (eq ▸ ha)
    simp [ne]
  have waitingEq : waiting (retirement s slot) = waiting s := by
    change s.order.tail.filterMap _ = s.order.filterMap _
    simp only [retirement]
    rw [maps]
    nth_rw 2 [order]
    clear order
    cases hp : s.peer.get slot <;> rcases terminal with ht | ht <;> simp_all [SlotValid]
  exact congrArg₂ Source.mk (newstate.trans oldstate.symm) waitingEq

theorem release_source (s : Session) (hs : Valid s) :
    Valid (step s .release).session ∧
    SourceStep (source s) (step s .release) (source (step s .release).session) := by
  simp only [step]
  split
  · exact rejected_source _ _ hs
  · rename_i unprepared
    split
    · exact rejected_source _ _ hs
    · rename_i slot r hh
      split
      · rename_i allowed
        have status : (step s .release).status = .released := by
          simp [step,unprepared,hh,allowed]
        have terminal : r.phase = .committed ∨ r.phase = .cancelled := by
          have h := allowed
          simp only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at h
          exact h.2
        refine ⟨retirement_valid s slot r hs hh (released_queue_empty s hs slot r hh status),?_⟩
        change SourceStep (source s) _ (source (retirement s slot))
        rw [retirement_source s slot r hs hh terminal]
        exact .internal _ _ rfl rfl (by simp)
      · exact rejected_source _ _ hs

theorem queue_valid (s : Session) (q : Queue) (hs : Valid s)
    (events : ∀ m ∈ q.messages, MessageValid s m) : Valid {s with queue := q} :=
  ⟨hs.order,hs.occupied,hs.slots,hs.tail,events⟩

theorem queue_source (s : Session) (q : Queue) : source {s with queue := q} = source s := rfl

theorem popped_messages (q : Queue) (m : Message) (rest : Queue)
    (h : q.pop = some (m,rest)) : q.messages = m :: rest.messages := by
  unfold Queue.pop at h
  split at h
  · contradiction
  · rename_i first tail heq
    cases h; exact heq

theorem reply_queue_valid (s : Session) (q : Queue) (reply : Message) (deliver : Bool)
    (hs : Valid s) (hq : ∀ m ∈ q.messages, MessageValid s m)
    (hr : MessageValid s reply) :
    Valid {s with queue := if deliver then (q.push reply).getD q else q} := by
  apply queue_valid _ _ hs
  cases deliver
  · exact hq
  · cases hp : q.push reply with
    | none => exact hq
    | some next =>
      intro m hm
      have messages := queue_push_members q reply next hp
      simp only [↓reduceIte,hp,Option.getD_some,messages,List.mem_append,
        List.mem_singleton] at hm
      rcases hm with hm | hm
      · exact hq m hm
      · subst m; exact hr

theorem published_ledger (s : Session) (slot x y : Bool) (r : Request) (hs : Valid s)
    (hr : s.requests.get slot = some r) (hp : s.peer.get slot = some (.published x y)) :
    x = r.input ∧ y = r.output := by
  have hv := hs.slots slot
  cases phase : r.phase <;> simp_all [SlotValid]

theorem query_reply_valid (s : Session) (slot : Bool) (r : Request) (hs : Valid s)
    (ho : s.order.head? = some slot) (hr : s.requests.get slot = some r) :
    MessageValid s (.reply slot (query (s.peer.get slot))) := by
  refine ⟨ho,r,hr,?_⟩
  cases hp : s.peer.get slot with
  | none => trivial
  | some entry =>
    cases entry with
    | reserved x => trivial
    | cancelled x => trivial
    | published x y =>
      obtain ⟨rfl,rfl⟩ := published_ledger s slot x y r hs hr hp
      exact hp

def publicationState (s : Session) (slot : Bool) (r : Request) : Session :=
  {s with peer := s.peer.put slot (some (.published r.input r.output))}

theorem publication_valid (s : Session) (slot : Bool) (r : Request) (hs : Valid s)
    (hh : head s = some (slot,r)) (phase : r.phase = .computed)
    (hp : s.peer.get slot = some (.reserved r.input)) : Valid (publicationState s slot r) := by
  obtain ⟨ho,hr⟩ := head_fields s slot r hh
  have hv := hs.slots slot
  simp only [SlotValid,hr,hp,phase] at hv
  refine ⟨hs.order,hs.occupied,?_,hs.tail,?_⟩
  · intro a
    by_cases eq : a = slot
    · subst a; simpa [publicationState,SlotValid,hr,phase] using And.intro hv.1 hv.2.1
    · simpa only [publicationState,slots_get_put,ite_eq_right eq] using hs.slots a
  · intro m hm
    obtain ⟨hhead,q,hq,law⟩ := hs.messages m hm
    have eqslot : m.slot = slot := Option.some.inj (hhead.symm.trans ho)
    rw [eqslot,hr] at hq
    cases hq
    refine ⟨hhead,r,by simpa only [publicationState,eqslot] using hr,?_⟩
    cases m with
    | publish a x y => exact law
    | retry a x y => exact law
    | query a => trivial
    | reply a answer =>
      cases answer <;> simp_all [Message.slot,publicationState]

theorem publication_source_step (s : Session) (slot : Bool) (r : Request) (hs : Valid s)
    (hh : head s = some (slot,r)) (phase : r.phase = .computed)
    (hp : s.peer.get slot = some (.reserved r.input)) (o : Outcome)
    (ha : o.accepted = none) (hb : o.business = some r.output) (hc : o.cancellation = none) :
    SourceStep (source s) o (source (publicationState s slot r)) := by
  obtain ⟨ho,hr⟩ := head_fields s slot r hh
  have hv := hs.slots slot
  simp only [hr,hp,SlotValid,phase] at hv
  have output := hv.2.1
  have order := List.eq_cons_of_mem_head? ho
  have hn := head_not_tail s hs slot ho
  let tail := s.order.tail.filterMap fun a => match s.peer.get a with
    | some (.reserved x) => some x | _ => none
  have oldwaiting : waiting s = r.input :: tail := by
    unfold waiting
    rw [order,List.filterMap_cons]
    simp only [hp,Option.map_some,Option.getD_some]
    rfl
  have newwaiting : waiting (publicationState s slot r) = tail := by
    change s.order.filterMap _ = _
    rw [order,List.filterMap_cons]
    simp only [publicationState,slots_get_put_same]
    apply List.filterMap_congr
    intro a ha
    have ne : a ≠ slot := by intro eq; exact hn (eq ▸ ha)
    simp [ne]
  have oldstate : sourceState s = s.active.logical := by simp [sourceState,hh,hp]
  have newstate : sourceState (publicationState s slot r) = r.input := by
    simp [sourceState,head,publicationState,ho,hr]
  change SourceStep ⟨sourceState s,waiting s⟩ o
    ⟨sourceState (publicationState s slot r),waiting (publicationState s slot r)⟩
  rw [oldwaiting,newwaiting,oldstate,newstate]
  exact .publish _ _ _ _ ha (by simpa only [output] using hb) hc

theorem confirmation_valid (s : Session) (slot : Bool) (r : Request) (hs : Valid s)
    (hh : head s = some (slot,r)) (phase : r.phase = .computed)
    (ledger : s.peer.get slot = some (.published r.input r.output)) :
    Valid (update s slot {r with phase := .confirmed}) := by
  obtain ⟨ho,hr⟩ := head_fields s slot r hh
  apply head_update_valid s slot r _ hs hh
  · have hv := hs.slots slot
    simpa [hr,ledger,phase,SlotValid] using hv
  · intro m hm
    obtain ⟨hhead,q,hq,law⟩ := hs.messages m hm
    have eqslot : m.slot = slot := Option.some.inj (hhead.symm.trans ho)
    rw [eqslot,hr] at hq
    cases hq
    refine ⟨hhead,{r with phase := .confirmed},?_,?_⟩
    · simp [update,eqslot]
    · cases m with
      | publish a x y => exact ⟨law.1,by simp⟩
      | retry a x y => exact ⟨law.1,by simp⟩
      | query a => trivial
      | reply a answer => cases answer <;> exact law

@[simp] theorem slots_put_get {α : Type} (s : Slots α) (slot : Bool) :
    s.put slot (s.get slot) = s := by cases s; cases slot <;> rfl

def peerState (s : Session) (slot x y : Bool) : Session :=
  {s with peer := s.peer.put slot (publish (s.peer.get slot) x y).1}

theorem peer_publication (s : Session) (slot x y : Bool) (r : Request) (hs : Valid s)
    (hh : head s = some (slot,r)) (hy : y = r.output) (phase : r.phase ≠ .accepted)
    (o : Outcome) (ha : o.accepted = none)
    (hb : o.business = (publish (s.peer.get slot) x y).2.2) (hc : o.cancellation = none) :
    Valid (peerState s slot x y) ∧
    SourceStep (source s) o (source (peerState s slot x y)) ∧
    MessageValid (peerState s slot x y) (.reply slot (publish (s.peer.get slot) x y).2.1) := by
  obtain ⟨ho,hr⟩ := head_fields s slot r hh
  subst y
  have hv := hs.slots slot
  cases hp : s.peer.get slot with
  | none => simp [hr,hp,SlotValid] at hv
  | some entry =>
    cases entry with
    | reserved a =>
      have eq := reserved_input s slot a r hs hr hp
      subst a
      have computed : r.phase = .computed := by cases ht : r.phase <;> simp_all [SlotValid]
      by_cases matchInput : r.input = x
      · subst x
        have state : peerState s slot r.input r.output = publicationState s slot r := by
          simp [peerState,publicationState,publish,hp]
        rw [state]
        refine ⟨publication_valid s slot r hs hh computed hp,
          publication_source_step s slot r hs hh computed hp o ha (by simpa [publish,hp] using hb) hc,?_⟩
        simp only [publish,hp,beq_self_eq_true,↓reduceIte]
        exact ⟨ho,r,hr,by simp [publicationState,Message.slot]⟩
      · have state : peerState s slot x r.output = s := by
          simp only [peerState,publish,hp]
          simp only [beq_eq_false_iff_ne.mpr matchInput,Bool.false_eq_true,↓reduceIte]
          rw [← hp,slots_put_get]
        rw [state]
        refine ⟨hs,.internal _ _ ha (by simpa [publish,hp,matchInput] using hb) (by simp [hc]),?_⟩
        simp [publish,hp,matchInput,MessageValid,Message.slot,ho,hr]
    | published a b =>
      obtain ⟨rfl,rfl⟩ := published_ledger s slot a b r hs hr hp
      have state : peerState s slot x r.output = s := by
        simp only [peerState,publish,hp]
        rw [← hp,slots_put_get]
      rw [state]
      refine ⟨hs,.internal _ _ ha (by simpa [publish,hp] using hb) (by simp [hc]),?_⟩
      simp only [publish,hp]
      split <;> simp [MessageValid,Message.slot,ho,hr,hp]
    | cancelled a =>
      have state : peerState s slot x r.output = s := by
        simp only [peerState,publish,hp]
        rw [← hp,slots_put_get]
      rw [state]
      refine ⟨hs,.internal _ _ ha (by simpa [publish,hp] using hb) (by simp [hc]),?_⟩
      exact ⟨ho,r,hr,True.intro⟩

def publicationOutcome (s : Session) (slot x y : Bool) (deliver : Bool) : Outcome :=
  let result := publish (s.peer.get slot) x y
  let queue := if deliver then (s.queue.push (.reply slot result.2.1)).getD s.queue else s.queue
  ⟨{peerState s slot x y with queue := queue},
    if result.2.1 == .conflict then .conflict else .dispatched,none,result.2.2,none,[]⟩

theorem publication_outcome_source (s : Session) (slot x y : Bool) (r : Request)
    (deliver : Bool) (hs : Valid s) (hh : head s = some (slot,r))
    (hy : y = r.output) (phase : r.phase ≠ .accepted) :
    Valid (publicationOutcome s slot x y deliver).session ∧
    SourceStep (source s) (publicationOutcome s slot x y deliver)
      (source (publicationOutcome s slot x y deliver).session) := by
  obtain ⟨hv,hstep,hm⟩ := peer_publication s slot x y r hs hh hy phase
    (publicationOutcome s slot x y deliver) rfl rfl rfl
  refine ⟨?_,hstep⟩
  exact reply_queue_valid (peerState s slot x y) s.queue
    (.reply slot (publish (s.peer.get slot) x y).2.1) deliver hv hv.messages hm

theorem dispatch_source (s : Session) (deliver : Bool) (hs : Valid s) :
    Valid (dispatch s deliver).session ∧
    SourceStep (source s) (dispatch s deliver) (source (dispatch s deliver).session) := by
  unfold dispatch
  cases hp : s.queue.pop with
  | none => exact rejected_source _ _ hs
  | some pair =>
    obtain ⟨m,q⟩ := pair
    have messages := popped_messages s.queue m q hp
    have hm := hs.messages m (by simp [messages])
    have baseValid : Valid {s with queue := q} := queue_valid s q hs (by
      intro event member
      exact hs.messages event (by simp [messages,member]))
    obtain ⟨ho,r,hr,law⟩ := hm
    dsimp only
    rw [hr]
    dsimp only
    split
    · exact rejected_source _ _ baseValid
    · cases m with
      | publish slot x y =>
        have hh : head {s with queue := q} = some (slot,r) := by
          simp only [Message.slot] at ho hr
          simp [head,ho,hr]
        exact publication_outcome_source {s with queue := q} slot x y r deliver
          baseValid hh law.1 law.2
      | retry slot x y =>
        have hh : head {s with queue := q} = some (slot,r) := by
          simp only [Message.slot] at ho hr
          simp [head,ho,hr]
        exact publication_outcome_source {s with queue := q} slot x y r deliver
          baseValid hh law.1 law.2
      | query slot =>
        simp only [Message.slot] at ho hr
        refine ⟨reply_queue_valid {s with queue := q} q
          (.reply slot (query (s.peer.get slot))) deliver baseValid baseValid.messages
          (query_reply_valid _ slot r baseValid ho hr),?_⟩
        exact .internal _ _ rfl rfl (by simp)
      | reply slot answer =>
        simp only [Message.slot] at ho hr
        have hh : head {s with queue := q} = some (slot,r) := by simp [head,ho,hr]
        dsimp only
        split
        · rename_i condition
          have hc : answer = .published ∧ r.phase = .computed := by simpa using condition
          obtain ⟨rfl,phase⟩ := hc
          have ledger : s.peer.get slot = some (.published r.input r.output) := law
          refine ⟨confirmation_valid _ slot r baseValid hh phase ledger,?_⟩
          rw [head_update_source {s with queue := q} slot r {r with phase := .confirmed} hh rfl]
          exact .internal _ _ rfl rfl (by simp)
        · exact rejected_source _ _ baseValid

/-- Every actual command preserves the live-state invariant and performs one
independent source transition, including refusal and migration stuttering. -/
theorem step_source (s : Session) (c : Command) (hs : Valid s) :
    Valid (step s c).session ∧
    SourceStep (source s) (step s c) (source (step s c).session) := by
  cases c with
  | inspect => exact rejected_source _ _ hs
  | accept x => exact accept_source s x hs
  | evaluate => exact evaluate_source s hs
  | publish => exact publish_source s hs
  | retry conflict => exact retry_source s conflict hs
  | queryPeer => exact query_source s hs
  | tickCommit => exact commit_source s hs
  | cancelWork second => exact cancel_source s second hs
  | close => exact close_source s hs
  | release => exact release_source s hs
  | dispatch deliver =>
    simp only [step]
    split
    · exact rejected_source _ _ hs
    · exact dispatch_source s deliver hs
  | prepare target budget alloc validate =>
    exact ⟨migration_valid _ _ (by simp [Business]) hs,migration_source_step _ _ (by simp [Business])⟩
  | ownershipCommit =>
    exact ⟨migration_valid _ _ (by simp [Business]) hs,migration_source_step _ _ (by simp [Business])⟩
  | cancelMigration =>
    exact ⟨migration_valid _ _ (by simp [Business]) hs,migration_source_step _ _ (by simp [Business])⟩

theorem step_valid (s : Session) (c : Command) (hs : Valid s) : Valid (step s c).session :=
  (step_source s c hs).1

theorem step_refines (s : Session) (c : Command) (hs : Valid s) :
    SourceStep (source s) (step s c) (source (step s c).session) := (step_source s c hs).2

theorem execute_valid (s : Session) (cs : List Command) (hs : Valid s) :
    Valid (execute s cs).1 := by
  induction cs generalizing s with
  | nil => exact hs
  | cons c cs ih => exact ih _ (step_valid s c hs)

/-- A ghost source execution records all acceptance/cancellation/publication
observations. Neither the public adapter nor Source retains this trace. -/
inductive SourceRun : Source → List Outcome → Source → Prop
  | nil (a : Source) : SourceRun a [] a
  | cons {a b c : Source} {o : Outcome} {os : List Outcome}
      (step : SourceStep a o b) (rest : SourceRun b os c) : SourceRun a (o::os) c

def sourceOutputs (os : List Outcome) : List Bool := os.filterMap Outcome.business

def sourceAcceptances (os : List Outcome) : List Bool := os.filterMap Outcome.accepted

def sourceCancellations (os : List Outcome) : Nat :=
  (os.filter fun o => o.cancellation == some true).length

theorem source_step_balance {a b : Source} {o : Outcome} (h : SourceStep a o b) :
    b.waiting.length + o.business.toList.length +
      (if o.cancellation = some true then 1 else 0) =
    a.waiting.length + o.accepted.toList.length := by
  cases h with
  | internal a o ha ho hc => simp [ha,ho,hc]
  | accept a o x ha ho hc => simp [ha,ho,hc]
  | prevent b x pre post o ha ho hc => simp [ha,ho,hc,List.length_append]; omega
  | publish b x xs o ha ho hc => simp [ha,ho,hc]

theorem source_run_balance {a b : Source} {os : List Outcome} (h : SourceRun a os b) :
    b.waiting.length + (sourceOutputs os).length + sourceCancellations os =
      a.waiting.length + (sourceAcceptances os).length := by
  induction h with
  | nil => simp [sourceOutputs,sourceAcceptances,sourceCancellations]
  | @cons a mid b o os hs hr ih =>
    have hb := source_step_balance hs
    simp only [sourceOutputs,sourceAcceptances,sourceCancellations,List.filterMap_cons,
      List.filter_cons] at *
    cases ha : o.accepted <;> cases ho : o.business <;>
      by_cases hc : o.cancellation = some true <;>
      simp_all [List.length_cons,Option.toList]
    all_goals omega

/-- A complete command trace is ghost data; operational state remains bounded. -/
def executionTrace : Session → List Command → List Outcome
  | _, [] => []
  | s, c::cs => let o := step s c; o :: executionTrace o.session cs

theorem executionTrace_outputs (s : Session) (cs : List Command) :
    sourceOutputs (executionTrace s cs) = (execute s cs).2 := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    simp only [executionTrace,sourceOutputs,List.filterMap_cons,execute]
    have h := ih (step s c).session
    unfold sourceOutputs at h
    rw [h]
    cases (step s c).business <;> rfl

/-- Trace lifting composes a supplied local simulation; it does not assume the
final output trace or successful publication schedule. -/
theorem source_trace_of_step (s : Session) (cs : List Command)
    (preserves : ∀ t c, Valid t → Valid (step t c).session)
    (refines : ∀ t c, Valid t → SourceStep (source t) (step t c) (source (step t c).session))
    (hs : Valid s) : SourceRun (source s) (executionTrace s cs) (source (execute s cs).1) := by
  induction cs generalizing s with
  | nil => exact .nil _
  | cons c cs ih => exact .cons (refines s c hs) (ih _ (preserves s c hs))

/-- Full finite-trace refinement of the executable transition function. No
fairness assumption is needed: unresolved work remains in Source.waiting. -/
theorem execution_refines (s : Session) (cs : List Command) (hs : Valid s) :
    SourceRun (source s) (executionTrace s cs) (source (execute s cs).1) :=
  source_trace_of_step s cs step_valid step_refines hs

theorem initial_execution_refines (k : Migration.Kind) (cs : List Command) :
    SourceRun ⟨false,[]⟩ (executionTrace (initial k) cs) (source (execute (initial k) cs).1) := by
  simpa only [initial_source] using execution_refines (initial k) cs (initial_valid k)

/-- Each accepted occurrence is still pending, was effectively published once,
or was prevented. Confirmation and retries do not consume another occurrence. -/
theorem execution_no_loss (s : Session) (cs : List Command) (hs : Valid s) :
    (waiting (execute s cs).1).length + (execute s cs).2.length +
      sourceCancellations (executionTrace s cs) =
    (waiting s).length + (sourceAcceptances (executionTrace s cs)).length := by
  have h := source_run_balance (execution_refines s cs hs)
  simpa only [source,executionTrace_outputs] using h

theorem initial_no_loss (k : Migration.Kind) (cs : List Command) :
    (waiting (execute (initial k) cs).1).length + (execute (initial k) cs).2.length +
      sourceCancellations (executionTrace (initial k) cs) =
    (sourceAcceptances (executionTrace (initial k) cs)).length := by
  simpa only [waiting,initial,List.filterMap_nil,List.length_nil,Nat.zero_add] using
    execution_no_loss (initial k) cs (initial_valid k)

/-- Accepted slot identities remain unique, including cancelled or completed
requests that have not yet retired their callbacks. -/
theorem reachable_owners (k : Migration.Kind) (cs : List Command) :
    (execute (initial k) cs).1.order.Nodup ∧
    ∀ slot, slot ∈ (execute (initial k) cs).1.order ↔
      ((execute (initial k) cs).1.requests.get slot).isSome = true := by
  have h := execute_valid (initial k) cs (initial_valid k)
  exact ⟨h.order,h.occupied⟩

end FRPSpec.PendingMigration

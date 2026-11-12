import Applications.FRP.RegionalPending

/-! Pending ownership, preparation and continuation across actual cut changes. -/
namespace FRPSpec.Regional.Pending
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 40000

def Business : Command → Prop
  | .prepare _ _ _ _ _ _ _ | .commit | .cancel => False
  | _ => True

theorem prepare_preserves (s : Session) (e t : Cut) (k : Migration.Kind) (r : Requirements)
    (a v bad : Bool) : (prepare s e t k r a v bad).session.active = s.active := by
  unfold prepare
  repeat' first | rfl | split | dsimp only

theorem commit_preserves (s : Session) : wire (commit s).session.active = wire s.active := by
  cases h : s.prepared with
  | none => simp [commit,h,reject]
  | some p => simpa only [commit,h] using p.continuation

theorem cancel_preserves (s : Session) : (cancel s).session.active = s.active := by
  cases h : s.prepared <;> simp [cancel,h,reject]

theorem prepared_freezes (s : Session) (c : Command) (hc : Business c)
    (hp : s.prepared.isSome = true) :
    (step s c).session = s ∧ (step s c).business = none := by
  cases c <;> simp only [Business] at hc
  all_goals simp [step,accept,producer,deliver,join,whole,external,hp,reject]

theorem attempt_consumes (s : Session) (e t : Cut) (k : Migration.Kind) (r : Requirements)
    (a v bad : Bool) (hp : s.prepared.isSome = false) (permit : s.permitted = true) :
    (prepare s e t k r a v bad).session.permitted = false := by
  simp only [prepare,hp,permit,Bool.not_true,Bool.false_eq_true,↓reduceIte]
  repeat' first | rfl | dsimp only | split

theorem no_repeat_attempt (s : Session) (e t : Cut) (k : Migration.Kind) (r : Requirements)
    (a v bad : Bool) (hp : s.prepared.isSome = false) (permit : s.permitted = false) :
    (prepare s e t k r a v bad).session = s ∧ (prepare s e t k r a v bad).status = .throttled := by
  simp [prepare,hp,permit,reject]

theorem producer_once (s : Session) (slot : Bool) (r : PendingMigration.Request) (work : Residual)
    (hh : headResidual s.active = some (slot,r,work)) (cached : work.cached.isSome = true) :
    (producer s).session = s := by
  unfold producer
  split
  · rfl
  · simp [hh,cached,reject]

theorem empty_delivery_stutters (s : Session) (toD : Bool)
    (empty : (if toD then s.active.deliveries.d else s.active.deliveries.n) = none) :
    (deliver s toD).session = s := by
  unfold deliver
  split
  · rfl
  · simp only [empty]; rfl

/-- No internal callback can outlive slot reuse: release checks these two owned
cells as well as the external queue's route/terminal/reference checks. -/
theorem internal_blocks_release (s : Session) (slot : Bool) (r : PendingMigration.Request)
    (hh : PendingMigration.head s.active.protocol = some (slot,r))
    (refs : s.active.deliveries.references slot = true) :
    (external s .release).session = s := by
  unfold external
  split
  · rfl
  · simp [hh,refs,reject]

theorem producer_transfer (s : Active) (cut : Cut) (kind : Migration.Kind) (slot : Bool) :
    ((convert s cut kind).residuals.get slot).map Residual.cached =
      (s.residuals.get slot).map Residual.cached ∧
    (convert s cut kind).deliveries = s.deliveries := by
  constructor
  · rw [convert_residuals]
  · rfl

/-- Confirmation loss and publication-before-commit are part of the complete
wire checkpoint. Neither phase is reconstructed from a fresh peer. -/
theorem peer_transfer (s : Active) (cut : Cut) (kind : Migration.Kind) :
    (convert s cut kind).protocol.peer = s.protocol.peer ∧
    (convert s cut kind).protocol.requests = s.protocol.requests ∧
    (convert s cut kind).protocol.queue = s.protocol.queue ∧
    (convert s cut kind).protocol.order = s.protocol.order := ⟨rfl,rfl,rfl,rfl⟩

/-- Peer retry idempotence applies to the joined payload itself. -/
theorem joined_retry (input joined : Bool) :
    PendingMigration.publish (some (.published input joined)) input joined =
      (some (.published input joined),.published,none) := PendingMigration.retry_idempotent input joined

/-- Normalization retains the complete checkpoint while selecting a fixed
reference representation. It does not initialize or replay the computation. -/
def normalizeActive (s : Active) : Active :=
  ⟨.split,PendingMigration.canonical s.protocol,s.residuals,s.deliveries⟩

def normalize (s : Session) : Session := ⟨normalizeActive s.active,none,true⟩

@[simp] theorem normalize_wire (s : Active) : wire (normalizeActive s) = wire s := rfl

/-- Control statuses are representation-independent as well as business frames. -/
theorem protocol_status (s : PendingMigration.Session) (c : PendingMigration.Command)
    (hc : PendingMigration.Business c) (hp : s.prepared = none) :
    (PendingMigration.step s c).status = (PendingMigration.step (PendingMigration.canonical s) c).status := by
  cases c <;> simp only [PendingMigration.Business] at hc
  all_goals simp only [PendingMigration.step,PendingMigration.canonical,hp,
    Option.isSome_none,Bool.false_eq_true,↓reduceIte]
  all_goals repeat' first
    | simp_all [PendingMigration.reject,PendingMigration.update,PendingMigration.enqueue,
        PendingMigration.dispatch,PendingMigration.head]
    | split

/-- The wrapper consumes this existing complete-checkpoint contract rather than
assuming that equal outputs imply equal outstanding peer obligations. -/
theorem protocol_fields (s : PendingMigration.Session) (c : PendingMigration.Command)
    (hc : PendingMigration.Business c) (hp : s.prepared = none) :
    PendingMigration.checkpoint (PendingMigration.step s c).session =
      PendingMigration.checkpoint (PendingMigration.step (PendingMigration.canonical s) c).session ∧
    (PendingMigration.step s c).status = (PendingMigration.step (PendingMigration.canonical s) c).status ∧
    PendingMigration.observations (PendingMigration.step s c) =
      PendingMigration.observations (PendingMigration.step (PendingMigration.canonical s) c) :=
  ⟨(PendingMigration.step_checkpoint s c hc hp).1,protocol_status s c hc hp,
    (PendingMigration.step_checkpoint s c hc hp).2⟩

@[simp] theorem normalized_residuals (s : Active) : (normalizeActive s).residuals = s.residuals := rfl

/-- Local work updates commute with normalization, including the actual stored
checked/fused cache representations. -/
theorem update_normalize (s : Active) (slot : Bool) (r : Residual) :
    normalizeActive (updateResidual s slot r) = updateResidual (normalizeActive s) slot r := by
  simp [normalizeActive,updateResidual,Active.withResiduals,Active.residuals]


def observation (o : Outcome) : Wire × Status × Option Bool × Option Bool × Option Bool :=
  (wire o.session.active,o.status,o.accepted,o.business,o.cancellation)

@[simp] theorem headResidual_normalize (s : Active) : headResidual (normalizeActive s) = headResidual s := rfl

@[simp] theorem normalized_deliveries (s : Active) : (normalizeActive s).deliveries = s.deliveries := rfl
@[simp] theorem normalized_protocol (s : Active) : (normalizeActive s).protocol = PendingMigration.canonical s.protocol := rfl

theorem producer_normalize (s : Session)  (hp : s.prepared = none) :
    observation (producer s) = observation (producer (normalize s)) := by
  simp only [producer,normalize,hp,Option.isSome_none,Bool.false_eq_true,↓reduceIte,
    headResidual_normalize,normalized_residuals,normalized_deliveries,normalized_protocol]
  simp only [observation]
  repeat' first
    | (split <;> try simp only [*])
    | dsimp only
  all_goals simp_all [observation,wire,normalizeActive,reject,updateResidual,Active.withResiduals,
    Active.residuals,PendingMigration.canonical,PendingMigration.update,whole_correct]

theorem deliver_normalize (s : Session) (d : Bool) (hp : s.prepared = none) :
    observation (deliver s d) = observation (deliver (normalize s) d) := by
  simp only [deliver,normalize,hp,Option.isSome_none,Bool.false_eq_true,↓reduceIte,
    headResidual_normalize,normalized_residuals,normalized_deliveries,normalized_protocol]
  simp only [observation]
  repeat' first
    | (split <;> try simp only [*])
    | dsimp only
  all_goals simp_all [observation,wire,normalizeActive,reject,updateResidual,Active.withResiduals,
    Active.residuals,PendingMigration.canonical,PendingMigration.update,whole_correct]

theorem join_normalize (s : Session)  (hp : s.prepared = none) :
    observation (join s) = observation (join (normalize s)) := by
  simp only [join,normalize,hp,Option.isSome_none,Bool.false_eq_true,↓reduceIte,
    headResidual_normalize,normalized_residuals,normalized_deliveries,normalized_protocol]
  simp only [observation]
  repeat' first
    | (split <;> try simp only [*])
    | dsimp only
  all_goals simp_all [observation,wire,normalizeActive,reject,updateResidual,Active.withResiduals,
    Active.residuals,PendingMigration.canonical,PendingMigration.update,whole_correct]

theorem whole_normalize (s : Session)  (hp : s.prepared = none) :
    observation (whole s) = observation (whole (normalize s)) := by
  simp only [whole,normalize,hp,Option.isSome_none,Bool.false_eq_true,↓reduceIte,
    headResidual_normalize,normalized_residuals,normalized_deliveries,normalized_protocol]
  simp only [observation]
  repeat' first
    | (split <;> try simp only [*])
    | dsimp only
  all_goals simp_all [observation,wire,normalizeActive,reject,updateResidual,Active.withResiduals,
    Active.residuals,PendingMigration.canonical,PendingMigration.update,whole_correct]

theorem accept_normalize (s : Session) (x : Bool) (hp : s.prepared = none)
    (hi : s.active.protocol.prepared = none) :
    observation (accept s x) = observation (accept (normalize s) x) := by
  obtain ⟨fields,status,obs⟩ := protocol_fields s.active.protocol (.accept x) (by trivial) hi
  have canon := PendingMigration.canonical_congr _ _ fields
  have logical := congrArg PendingMigration.Checkpoint.logical fields
  have requests := congrArg PendingMigration.Checkpoint.requests fields
  have peer := congrArg PendingMigration.Checkpoint.peer fields
  have queue := congrArg (fun p => p.queue.messages) fields
  have order := congrArg PendingMigration.Checkpoint.order fields
  have accepted := congrArg Prod.fst obs
  have business := congrArg (fun o => o.2.1) obs
  have cancellation := congrArg (fun o => o.2.2) obs
  simp only [PendingMigration.observations] at accepted business cancellation
  simp only [PendingMigration.checkpoint] at logical requests peer order queue
  dsimp only [accept,normalize,normalizeActive]
  simp only [hp,Option.isSome_none,Bool.false_eq_true,↓reduceIte]
  dsimp only [observation]
  simp only [status,order]
  cases hs : ((PendingMigration.step (PendingMigration.canonical s.active.protocol) (.accept x)).status == .accepted)
  · simp only [hs,Bool.false_eq_true,↓reduceIte]
    simp_all [observation,wire,normalizeActive,Active.residuals]
  · simp only [hs,↓reduceIte]
    cases hl : (PendingMigration.step (PendingMigration.canonical s.active.protocol) (.accept x)).session.order.getLast? <;>
      simp only [hl]
    all_goals simp_all [observation,wire,normalizeActive,updateResidual,Active.withResiduals,Active.residuals]

@[simp] theorem head_canonical (p : PendingMigration.Session) (second : Bool) :
    PendingMigration.head (PendingMigration.canonical p) second = PendingMigration.head p second := rfl


set_option maxHeartbeats 400000 in
theorem external_normalize (s : Session) (c : PendingMigration.Command)
    (hp : s.prepared = none) (hi : s.active.protocol.prepared = none) :
    observation (external s c) = observation (external (normalize s) c) := by
  by_cases hc : PendingMigration.Business c
  · obtain ⟨fields,status,obs⟩ := protocol_fields s.active.protocol c hc hi
    have logical := congrArg PendingMigration.Checkpoint.logical fields
    have requests := congrArg PendingMigration.Checkpoint.requests fields
    have peer := congrArg PendingMigration.Checkpoint.peer fields
    have order := congrArg PendingMigration.Checkpoint.order fields
    have queue := congrArg (fun p => p.queue.messages) fields
    have accepted := congrArg Prod.fst obs
    have business := congrArg (fun o => o.2.1) obs
    have cancellation := congrArg (fun o => o.2.2) obs
    simp only [PendingMigration.observations] at accepted business cancellation
    simp only [PendingMigration.checkpoint] at logical requests peer order queue
    cases c <;> dsimp only [external,normalize,normalizeActive]
    all_goals simp only [hp,Option.isSome_none,Bool.false_eq_true,↓reduceIte,head_canonical]
    all_goals dsimp only [observation]
    all_goals try simp only [status,cancellation]
    all_goals repeat' first
      | (split <;> try simp only [*])
      | dsimp only
    all_goals simp_all [observation,wire,normalize,normalizeActive,reject,updateResidual,
      Active.withResiduals,Active.residuals,PendingMigration.canonical]
  · cases c <;> simp only [PendingMigration.Business] at hc
    all_goals try contradiction
    all_goals dsimp only [external,normalize,normalizeActive]
    all_goals simp only [hp,Option.isSome_none,Bool.false_eq_true,↓reduceIte]
    all_goals simp [reject,observation,wire,PendingMigration.canonical,Active.residuals]

/-- Public business execution never installs a nested peer preparation. -/
def Ready (s : Session) : Prop := s.prepared = none ∧ s.active.protocol.prepared = none

theorem step_normalize (s : Session) (c : Command) (hc : Business c) (hs : Ready s) :
    observation (step s c) = observation (step (normalize s) c) := by
  cases c with
  | accept x => exact accept_normalize s x hs.1 hs.2
  | producer => exact producer_normalize s hs.1
  | deliverD => exact deliver_normalize s true hs.1
  | deliverN => exact deliver_normalize s false hs.1
  | join => exact join_normalize s hs.1
  | whole => exact whole_normalize s hs.1
  | external c => exact external_normalize s c hs.1 hs.2
  | prepare => cases hc
  | commit => cases hc
  | cancel => cases hc

theorem normalize_congr (s t : Session) (h : wire s.active = wire t.active) :
    normalize s = normalize t := by
  have hl := congrArg Wire.logical h
  have hr := congrArg Wire.requests h
  have hp := congrArg Wire.peer h
  have ho := congrArg Wire.order h
  have hq := congrArg Wire.external h
  have hc := congrArg Wire.residuals h
  have hd := congrArg Wire.deliveries h
  simp only [wire] at hl hr hp ho hq hc hd
  have queue : s.active.protocol.queue = t.active.protocol.queue := by
    cases hs : s.active.protocol.queue with
    | mk sm sb =>
      cases ht : t.active.protocol.queue with
      | mk tm tb =>
        simp only [hs,ht] at hq
        cases hq
        rfl
  have canon : PendingMigration.canonical s.active.protocol = PendingMigration.canonical t.active.protocol := by
    unfold PendingMigration.canonical
    rw [hl,hr,hp,ho,queue]
  have ha : normalizeActive s.active = normalizeActive t.active := by
    dsimp only [normalizeActive]
    rw [canon,hc,hd]
  exact congrArg (fun a : Active => (⟨a,none,true⟩ : Session)) ha

/-- Full joint checkpoint and selected source observations, including status. -/
theorem step_related (s t : Session) (c : Command) (hc : Business c)
    (hs : Ready s) (ht : Ready t) (h : wire s.active = wire t.active) :
    observation (step s c) = observation (step t c) := by
  rw [step_normalize s c hc hs,step_normalize t c hc ht,normalize_congr s t h]

def outerPrepared (s : Session) : Bool := s.prepared.isSome

def innerPrepared (s : Active) : Bool := PendingMigration.preparedFlag s.protocol

def readiness (s : Session) : Bool × Bool := (outerPrepared s,innerPrepared s.active)

theorem ready_iff (s : Session) : readiness s = (false,false) ↔ Ready s := by
  simp [readiness,outerPrepared,innerPrepared,Ready,PendingMigration.preparedFlag]

theorem inner_ite (p : Prop) [Decidable p] (a b : Active) :
    innerPrepared (if p then a else b) = (if p then innerPrepared a else innerPrepared b) := by
  split <;> rfl

theorem inner_option {α : Type} (o : Option α) (a : Active) (f : α → Active) :
    innerPrepared (match o with | none => a | some x => f x) =
      (match o with | none => innerPrepared a | some x => innerPrepared (f x)) := by
  cases o <;> rfl

theorem inner_update (a : Active) (slot : Bool) (r : Residual) :
    innerPrepared (updateResidual a slot r) = innerPrepared a := rfl

set_option maxHeartbeats 400000 in
theorem external_ready (s : Session) (c : PendingMigration.Command) (hs : Ready s) :
    Ready (external s c).session := by
  apply (ready_iff _).mp
  obtain ⟨hp,hi⟩ := hs
  by_cases hc : PendingMigration.Business c
  · have inner := PendingMigration.business_unprepared s.active.protocol c hc hi
    cases c <;> dsimp only [external]
    all_goals simp only [hp,Option.isSome_none,Bool.false_eq_true,↓reduceIte]
    all_goals dsimp only [readiness]
    all_goals repeat' first | (split <;> try simp only [*]) | dsimp only
    all_goals simp_all only [readiness,outerPrepared,reject,inner_ite,inner_option,inner_update]
    all_goals repeat' first | (split <;> try simp only [*]) | dsimp only
    all_goals simp_all [innerPrepared,Active.withResiduals,updateResidual,PendingMigration.preparedFlag]
  · cases c <;> simp only [PendingMigration.Business] at hc
    all_goals try contradiction
    all_goals dsimp only [external]
    all_goals simp only [hp,Option.isSome_none,Bool.false_eq_true,↓reduceIte]
    all_goals simp [readiness,outerPrepared,innerPrepared,reject,hp,hi,PendingMigration.preparedFlag]

theorem step_ready (s : Session) (c : Command) (hc : Business c) (hs : Ready s) :
    Ready (step s c).session := by
  cases c with
  | external c => exact external_ready s c hs
  | accept x =>
    have inner := PendingMigration.business_unprepared s.active.protocol (.accept x) (by trivial) hs.2
    apply (ready_iff _).mp
    dsimp only [step,accept]
    simp only [hs.1,Option.isSome_none,Bool.false_eq_true,↓reduceIte]
    dsimp only [readiness]
    repeat' first | (split <;> try simp only [*]) | dsimp only
    all_goals simp_all [readiness,outerPrepared,innerPrepared,updateResidual,Active.withResiduals,PendingMigration.preparedFlag]
    all_goals split <;> simpa [updateResidual,Active.withResiduals] using inner
  | prepare => cases hc
  | commit => cases hc
  | cancel => cases hc
  | _ =>
    apply (ready_iff _).mp
    dsimp only [step,producer,deliver,join,whole]
    simp only [hs.1,Option.isSome_none,Bool.false_eq_true,↓reduceIte]
    dsimp only [readiness]
    repeat' first | (split <;> try simp only [*]) | dsimp only
    all_goals simp_all [readiness,outerPrepared,innerPrepared,Ready,reject,updateResidual,Active.withResiduals,
      PendingMigration.update,PendingMigration.preparedFlag]

def observationTrace : Session → List Command → List (Status × Option Bool × Option Bool × Option Bool)
  | _,[] => []
  | s,c::cs => (observation (step s c)).2 :: observationTrace (step s c).session cs

/-- Arbitrary finite business suffixes preserve all selected observations and
the complete joint pending checkpoint. Readiness is preserved, not assumed for
each intermediate state. The two initial permission flags may differ. -/
theorem suffix_related (s t : Session) (cs : List Command)
    (hc : ∀ c ∈ cs, Business c) (hs : Ready s) (ht : Ready t)
    (h : wire s.active = wire t.active) :
    wire (execute s cs).1.active = wire (execute t cs).1.active ∧
      observationTrace s cs = observationTrace t cs ∧ (execute s cs).2 = (execute t cs).2 := by
  induction cs generalizing s t with
  | nil => exact ⟨h,rfl,rfl⟩
  | cons c cs ih =>
    have one := step_related s t c (hc c (by simp)) hs ht h
    have rest := ih (step s c).session (step t c).session
      (fun x hx => hc x (by simp [hx]))
      (step_ready s c (hc c (by simp)) hs) (step_ready t c (hc c (by simp)) ht)
      (congrArg Prod.fst one)
    refine ⟨rest.1,?_,?_⟩
    · simp only [observationTrace,congrArg Prod.snd one,rest.2.1]
    · have output := congrArg (fun o => o.2.2.2.1) one
      change (step s c).business = (step t c).business at output
      simp only [execute,output,rest.2.2]

theorem wire_checkpoint (s t : Session) (h : wire s.active = wire t.active) :
    checkpoint s.active = checkpoint t.active := by
  have eq := congrArg (fun s => checkpoint s.active) (normalize_congr s t h)
  simpa only [normalize,normalizeActive,checkpoint,PendingMigration.checkpoint,
    PendingMigration.canonical,Active.residuals,store_decode_split,PendingMigration.logical_delay] using eq

theorem suffix_checkpoint (s t : Session) (cs : List Command)
    (hc : ∀ c ∈ cs, Business c) (hs : Ready s) (ht : Ready t)
    (h : wire s.active = wire t.active) :
    checkpoint (execute s cs).1.active = checkpoint (execute t cs).1.active :=
  wire_checkpoint _ _ (suffix_related s t cs hc hs ht h).1

/-- Both commands are executable: every prepare attempt is followed by commit
or cancellation. Refused/failed attempts are included and remain silent in the
selected source observations. Preparation control statuses are not erased from
the public runner. -/
def reconfigure (s : Session) (e t : Cut) (k : Migration.Kind) (r : Requirements)
    (allocation validation swapped finish : Bool) : Session :=
  let attempted := (prepare s e t k r allocation validation swapped).session
  (if finish then commit attempted else cancel attempted).session

theorem reconfigure_wire (s : Session) (e t : Cut) (k : Migration.Kind) (r : Requirements)
    (a v bad finish : Bool) : wire (reconfigure s e t k r a v bad finish).active = wire s.active := by
  cases finish
  · simp only [reconfigure,Bool.false_eq_true,↓reduceIte,cancel_preserves,prepare_preserves]
  · simp only [reconfigure,↓reduceIte,commit_preserves,prepare_preserves]

set_option maxHeartbeats 400000 in
theorem reconfigure_ready (s : Session) (e t : Cut) (k : Migration.Kind) (r : Requirements)
    (a v bad finish : Bool) (hs : Ready s) : Ready (reconfigure s e t k r a v bad finish) := by
  apply (ready_iff _).mp
  obtain ⟨hp,hi⟩ := hs
  cases finish <;> dsimp only [reconfigure,prepare]
  all_goals simp only [hp,Option.isSome_none,Bool.false_eq_true,↓reduceIte]
  all_goals repeat' first
    | (split <;> try simp only [*])
    | dsimp only [commit,cancel,reject]
  all_goals simp_all [readiness,outerPrepared,innerPrepared,convert,swapConsumers,Active.withResiduals,
    PendingMigration.transfer,PendingMigration.preparedFlag]

inductive PlanAction where
  | business (command : Command) (admitted : Business command)
  | migration (expected target : Cut) (kind : Migration.Kind) (requirements : Requirements)
      (allocation validation swapped finish : Bool)

def erasePlan : List PlanAction → List Command
  | [] => []
  | .business c _ :: rest => c :: erasePlan rest
  | .migration _ _ _ _ _ _ _ _ :: rest => erasePlan rest

theorem erase_business (plan : List PlanAction) : ∀ c ∈ erasePlan plan, Business c := by
  induction plan with
  | nil => simp [erasePlan]
  | cons a plan ih => cases a <;> simp_all [erasePlan]

def runPlan : Session → List PlanAction → Session × List Bool
  | s,[] => (s,[])
  | s,.business c _ :: rest =>
      let o := step s c
      let r := runPlan o.session rest
      (r.1,o.business.toList ++ r.2)
  | s,.migration e t k r a v bad finish :: rest => runPlan (reconfigure s e t k r a v bad finish) rest

def planObservations : Session → List PlanAction → List (Status × Option Bool × Option Bool × Option Bool)
  | _,[] => []
  | s,.business c _ :: rest => (observation (step s c)).2 :: planObservations (step s c).session rest
  | s,.migration e t k r a v bad finish :: rest => planObservations (reconfigure s e t k r a v bad finish) rest

/-- Any finite sequence of actual attempts, including failures and cancellations,
can be inserted at arbitrary business cuts. Initial pending work need not be
empty, and neither producer nor completed consumer is replayed. -/
theorem repeated_migration (s : Session) (plan : List PlanAction) (hs : Ready s) :
    wire (runPlan s plan).1.active = wire (execute s (erasePlan plan)).1.active ∧
      planObservations s plan = observationTrace s (erasePlan plan) ∧
      (runPlan s plan).2 = (execute s (erasePlan plan)).2 := by
  induction plan generalizing s with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons action rest ih =>
    cases action with
    | business c hc =>
      have tail := ih (step s c).session (step_ready s c hc hs)
      refine ⟨tail.1,?_,?_⟩
      · simp only [planObservations,erasePlan,observationTrace,tail.2.1]
      · simp only [runPlan,erasePlan,execute,tail.2.2]
    | migration e t k r a v bad finish =>
      have ready := reconfigure_ready s e t k r a v bad finish hs
      have tail := ih (reconfigure s e t k r a v bad finish) ready
      have comparison := suffix_related (reconfigure s e t k r a v bad finish) s
        (erasePlan rest) (erase_business rest) ready hs (reconfigure_wire s e t k r a v bad finish)
      exact ⟨tail.1.trans comparison.1,tail.2.1.trans comparison.2.1,tail.2.2.trans comparison.2.2⟩

/-- Control commands have no accepted, published, or cancellation observation,
including validation failure after allocation. Their control status remains public. -/
theorem prepare_silent (s : Session) (e t : Cut) (k : Migration.Kind) (r : Requirements)
    (a v bad : Bool) :
    let o := prepare s e t k r a v bad
    (o.accepted,o.business,o.cancellation) = (none,none,none) := by
  dsimp only
  unfold prepare
  repeat' first | rfl | split | dsimp only

theorem commit_silent (s : Session) :
    ((commit s).accepted,(commit s).business,(commit s).cancellation) = (none,none,none) := by
  cases h : s.prepared <;> simp [commit,h,reject]

theorem cancel_silent (s : Session) :
    ((cancel s).accepted,(cancel s).business,(cancel s).cancellation) = (none,none,none) := by
  cases h : s.prepared <;> simp [cancel,h,reject]

theorem reconfigure_execute (s : Session) (e t : Cut) (k : Migration.Kind) (r : Requirements)
    (a v bad finish : Bool) :
    execute s [.prepare e t k r a v bad,if finish then .commit else .cancel] =
      (reconfigure s e t k r a v bad finish,[]) := by
  have hp := congrArg (fun x => x.2.1) (prepare_silent s e t k r a v bad)
  have hc := congrArg (fun x => x.2.1) (commit_silent (prepare s e t k r a v bad).session)
  have hx := congrArg (fun x => x.2.1) (cancel_silent (prepare s e t k r a v bad).session)
  cases finish <;> simp_all [execute,step,reconfigure]

theorem execute_append (s : Session) (xs ys : List Command) :
    execute s (xs ++ ys) =
      let first := execute s xs
      let last := execute first.1 ys
      (last.1,first.2 ++ last.2) := by
  induction xs generalizing s with
  | nil => simp [execute]
  | cons x xs ih => simp [execute,ih,List.append_assoc]

def expandPlan : List PlanAction → List Command
  | [] => []
  | .business c _ :: rest => c :: expandPlan rest
  | .migration e t k r a v bad finish :: rest =>
      [.prepare e t k r a v bad,if finish then .commit else .cancel] ++ expandPlan rest

/-- The plan interpreter is exactly the public command executor, including both
commands of each attempted ownership transfer. -/
theorem runPlan_public (s : Session) (plan : List PlanAction) :
    execute s (expandPlan plan) = runPlan s plan := by
  induction plan generalizing s with
  | nil => rfl
  | cons action rest ih =>
    cases action with
    | business c hc => simp [expandPlan,execute,runPlan,ih]
    | migration e t k r a v bad finish =>
      simp only [expandPlan,execute_append,reconfigure_execute,List.nil_append,runPlan,ih]

/-- Repeated actual migrations preserve the final complete pending checkpoint
and effective output stream for every finite business continuation. -/
theorem public_repeated_migration (s : Session) (plan : List PlanAction) (hs : Ready s) :
    checkpoint (execute s (expandPlan plan)).1.active =
      checkpoint (execute s (erasePlan plan)).1.active ∧
    (execute s (expandPlan plan)).2 = (execute s (erasePlan plan)).2 := by
  rw [runPlan_public]
  have h := repeated_migration s plan hs
  exact ⟨wire_checkpoint _ _ h.1,h.2.2⟩

theorem initial_ready (cut : Cut) (kind : Migration.Kind) : Ready (initial cut kind) := by
  constructor <;> rfl

theorem execute_ready (s : Session) (cs : List Command) (hs : Ready s)
    (hc : ∀ c ∈ cs, Business c) : Ready (execute s cs).1 := by
  induction cs generalizing s with
  | nil => exact hs
  | cons c cs ih =>
    exact ih (step s c).session (step_ready s c (hc c (by simp)) hs)
      (fun x hx => hc x (by simp [hx]))

/-- A cut after only D received the shared producer result is an admissible
starting point for arbitrary later migration attempts and business commands. -/
example (plan : List PlanAction) :
    let pending :=  (execute (initial .split .delay) [.accept true,.producer,.deliverD]).1
    checkpoint (execute pending (expandPlan plan)).1.active =
      checkpoint (execute pending (erasePlan plan)).1.active ∧
    (execute pending (expandPlan plan)).2 = (execute pending (erasePlan plan)).2 := by
  apply public_repeated_migration
  apply execute_ready _ _ (initial_ready _ _)
  simp [Business]

end FRPSpec.Regional.Pending

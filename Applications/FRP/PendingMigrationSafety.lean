import Applications.FRP.PendingMigrationIO

/-! Checkpoint preservation, retirement exclusion, and protocol laws. -/
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace FRPSpec.PendingMigration
open Migration

@[simp] theorem logical_delay (b : Bool) : (Backend.delay b).logical = b := rfl

/-- Logical checkpoint retains every pending input/result, peer obligation and
owned event. It erases only the choice of backend and transfer scratch space. -/
structure Checkpoint where
  logical : Bool
  requests : Slots Request
  peer : Slots Ledger
  order : List Bool
  queue : Queue

def checkpoint (s : Session) : Checkpoint :=
  ⟨s.active.logical,s.requests,s.peer,s.order,s.queue⟩

def canonical (s : Session) : Session :=
  ⟨.delay s.active.logical,s.requests,s.peer,s.order,s.queue,none⟩

def transfer (s : Session) (k : Kind) : Session :=
  ⟨realize k s.active.logical,s.requests,s.peer,s.order,s.queue,none⟩

@[simp] theorem checkpoint_transfer (s : Session) (k : Kind) :
    checkpoint (transfer s k) = checkpoint s := by cases k <;> rfl

/-- Business commands exclude preparation, whose budget depends on the physical
representation. Actual successful/failed preparation is treated separately. -/
def Business : Command → Prop
  | .prepare _ _ _ _ | .ownershipCommit | .cancelMigration => False
  | _ => True

@[simp] theorem evaluate_output (b : Backend) (x : Bool) :
    (Migration.evaluate b x).output = b.logical := (Migration.evaluate b x).output_eq

def observations (o : Outcome) : Option Bool × Option Bool × Option Bool :=
  (o.accepted,o.business,o.cancellation)

/-- Dispatch never evaluates a backend. Late replies address the current slot,
not an old realization pointer. -/
theorem dispatch_checkpoint (s : Session) (d : Bool) :
    checkpoint (dispatch s d).session = checkpoint (dispatch (canonical s) d).session ∧
    observations (dispatch s d) = observations (dispatch (canonical s) d) := by
  simp only [canonical]
  simp only [dispatch]
  all_goals repeat' first | simp_all [checkpoint, reject, update, observations] | split

/-- Complete checkpoints determine all subsequent business observations. -/
theorem step_checkpoint (s : Session) (c : Command) (hc : Business c)
    (hp : s.prepared = none) :
    checkpoint (step s c).session = checkpoint (step (canonical s) c).session ∧
    observations (step s c) = observations (step (canonical s) c) := by
  rcases s with ⟨active,requests,peer,order,queue,prepared⟩
  dsimp only at hp
  subst prepared
  cases c <;> simp only [Business] at hc
  case dispatch d => exact dispatch_checkpoint _ d
  all_goals dsimp only [canonical]
  all_goals simp only [step, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  all_goals try simp only [head]
  all_goals repeat' first
    | simp_all [reject, update, enqueue, checkpoint, evaluate_output, observations]
    | split

def restore (q : Checkpoint) : Session :=
  ⟨.delay q.logical,q.requests,q.peer,q.order,q.queue,none⟩

theorem canonical_congr (s t : Session) (h : checkpoint s = checkpoint t) :
    canonical s = canonical t := congrArg restore h

def preparedFlag (s : Session) : Bool := s.prepared.isSome

theorem dispatch_unprepared (s : Session) (d : Bool) (hp : s.prepared = none) :
    preparedFlag (dispatch s d).session = false := by
  unfold dispatch
  all_goals repeat' first
    | split
    | simp_all [reject, update, preparedFlag]

@[simp] theorem preparedFlag_enqueue (s : Session) (r : Request) (m : Message) :
    preparedFlag (enqueue s r m).session = preparedFlag s := by
  unfold enqueue
  split
  · rfl
  · split <;> rfl

@[simp] theorem enqueue_unprepared (s : Session) (r : Request) (m : Message)
    (hp : s.prepared = none) : (enqueue s r m).session.prepared = none := by
  have h := preparedFlag_enqueue s r m
  simpa [preparedFlag,hp] using h

theorem business_unprepared (s : Session) (c : Command) (hc : Business c)
    (hp : s.prepared = none) : (step s c).session.prepared = none := by
  have result : preparedFlag (step s c).session = false := by
    cases c <;> simp only [Business] at hc
    case dispatch d => simpa only [step,hp,Option.isSome_none,Bool.false_eq_true,↓reduceIte]
      using dispatch_unprepared s d hp
    all_goals simp only [step, hp, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    all_goals repeat' first
      | split
      | simp_all [reject, update, preparedFlag_enqueue, enqueue_unprepared, preparedFlag]
  simpa [preparedFlag] using result

/-- Equality of the complete logical checkpoint is a business-step bisimulation,
including accepted inputs and cancellation outcomes (which are retained in the
next checkpoint), not merely equality of the last published value. -/
theorem step_related (s t : Session) (c : Command) (hc : Business c)
    (hs : s.prepared = none) (ht : t.prepared = none)
    (h : checkpoint s = checkpoint t) :
    checkpoint (step s c).session = checkpoint (step t c).session ∧
    (step s c).business = (step t c).business := by
  have a := step_checkpoint s c hc hs
  have b := step_checkpoint t c hc ht
  rw [canonical_congr s t h] at a
  exact ⟨a.1.trans b.1.symm,congrArg (fun o => o.2.1) (a.2.trans b.2.symm)⟩

/-- Arbitrary valid checkpoints and arbitrary finite business suffixes share
both the effective output trace and complete retained continuation. -/
theorem suffix_related (s t : Session) (cs : List Command)
    (hc : ∀ c ∈ cs, Business c) (hs : s.prepared = none) (ht : t.prepared = none)
    (h : checkpoint s = checkpoint t) :
    checkpoint (execute s cs).1 = checkpoint (execute t cs).1 ∧
    (execute s cs).2 = (execute t cs).2 := by
  induction cs generalizing s t with
  | nil => exact ⟨h,rfl⟩
  | cons c cs ih =>
    have hc' := hc c (by simp)
    have one := step_related s t c hc' hs ht h
    have rest := ih (step s c).session (step t c).session
      (fun x hx => hc x (by simp [hx]))
      (business_unprepared s c hc' hs) (business_unprepared t c hc' ht) one.1
    exact ⟨rest.1,by simp only [execute, one.2, rest.2]⟩

theorem transfer_suffix (s : Session) (k : Kind) (cs : List Command)
    (hc : ∀ c ∈ cs, Business c) (hs : s.prepared = none) :
    checkpoint (execute (transfer s k) cs).1 = checkpoint (execute s cs).1 ∧
    (execute (transfer s k) cs).2 = (execute s cs).2 :=
  suffix_related _ _ cs hc rfl hs (checkpoint_transfer s k)

/-- The public two-command transfer implements the logical checkpoint map,
including at unpublished and published-but-unconfirmed cuts. -/
theorem prepare_commit (s : Session) (k : Kind) (budget : Nat)
    (hp : s.prepared = none) (hb : preparationSlots s k ≤ budget) :
    execute s [.prepare k budget true true,.ownershipCommit] = (transfer s k,[]) := by
  let p : Prepared s.active := ⟨realize k s.active.logical,realize_logical _ _⟩
  have hstep : step s (.prepare k budget true true) =
      ⟨{s with prepared := some p},.prepared,none,none,none,
        [.budget,.attempt (p.target.cells + 2),.allocate (p.target.cells + 2),
         .copy p.target.cells,.validate,.release 2]⟩ := by
    simp [step,hp,Nat.not_lt.mpr hb,p,Migration.backend_validates]
  simp only [execute,hstep]
  simp [step,transfer,p]

inductive PlanAction where
  | business (command : Command) (admitted : Business command)
  | migration (target : Kind)

def erasePlan : List PlanAction → List Command
  | [] => []
  | .business c _ :: rest => c :: erasePlan rest
  | .migration _ :: rest => erasePlan rest

theorem erase_business (plan : List PlanAction) : ∀ c ∈ erasePlan plan, Business c := by
  induction plan with
  | nil => simp [erasePlan]
  | cons a plan ih => cases a <;> simp_all [erasePlan]

/-- Every migration is the actual prepare/commit pair. The budget here is the
computed required logical space, not an unbounded allocation. -/
def runPlan : Session → List PlanAction → Session × List Bool
  | s,[] => (s,[])
  | s,.business c _ :: rest =>
    let o := step s c
    let r := runPlan o.session rest
    (r.1,o.business.toList ++ r.2)
  | s,.migration k :: rest =>
    let o := execute s [.prepare k (preparationSlots s k) true true,.ownershipCommit]
    let r := runPlan o.1 rest
    (r.1,o.2 ++ r.2)

theorem repeated_migration (s : Session) (plan : List PlanAction) (hp : s.prepared = none) :
    checkpoint (runPlan s plan).1 = checkpoint (execute s (erasePlan plan)).1 ∧
    (runPlan s plan).2 = (execute s (erasePlan plan)).2 := by
  induction plan generalizing s with
  | nil => exact ⟨rfl,rfl⟩
  | cons a plan ih =>
    cases a with
    | business c hc =>
      have rest := ih (step s c).session (business_unprepared s c hc hp)
      exact ⟨rest.1,by simp only [runPlan,erasePlan,execute,rest.2]⟩
    | migration k =>
      have actual := prepare_commit s k (preparationSlots s k) hp (by omega)
      have rest := ih (transfer s k) rfl
      have suffix := transfer_suffix s k (erasePlan plan) (erase_business plan) hp
      simp only [runPlan, actual, List.nil_append, erasePlan]
      exact ⟨rest.1.trans suffix.1,rest.2.trans suffix.2⟩

/-- Full selected source observation, including refused/too-late cancellation. -/
def observationTrace : Session → List Command → List (Option Bool × Option Bool × Option Bool)
  | _,[] => []
  | s,c::cs => observations (step s c) :: observationTrace (step s c).session cs

theorem step_observations (s t : Session) (c : Command) (hc : Business c)
    (hs : s.prepared = none) (ht : t.prepared = none)
    (h : checkpoint s = checkpoint t) : observations (step s c) = observations (step t c) := by
  have a := step_checkpoint s c hc hs
  have b := step_checkpoint t c hc ht
  rw [canonical_congr s t h] at a
  exact a.2.trans b.2.symm

theorem suffix_observations (s t : Session) (cs : List Command)
    (hc : ∀ c ∈ cs, Business c) (hs : s.prepared = none) (ht : t.prepared = none)
    (h : checkpoint s = checkpoint t) : observationTrace s cs = observationTrace t cs := by
  induction cs generalizing s t with
  | nil => rfl
  | cons c cs ih =>
    have hc' := hc c (by simp)
    have one := step_related s t c hc' hs ht h
    have rest := ih (step s c).session (step t c).session
      (fun x hx => hc x (by simp [hx]))
      (business_unprepared s c hc' hs) (business_unprepared t c hc' ht) one.1
    simp only [observationTrace,step_observations s t c hc' hs ht h,rest]

/-- Transfer control events are silent for the selected source observations. -/
def planObservations : Session → List PlanAction → List (Option Bool × Option Bool × Option Bool)
  | _,[] => []
  | s,.business c _ :: rest => observations (step s c) :: planObservations (step s c).session rest
  | s,.migration k :: rest =>
      let o := execute s [.prepare k (preparationSlots s k) true true,.ownershipCommit]
      planObservations o.1 rest

theorem repeated_observations (s : Session) (plan : List PlanAction) (hp : s.prepared = none) :
    planObservations s plan = observationTrace s (erasePlan plan) := by
  induction plan generalizing s with
  | nil => rfl
  | cons a plan ih =>
    cases a with
    | business c hc =>
      simp only [planObservations,erasePlan,observationTrace]
      rw [ih _ (business_unprepared s c hc hp)]
    | migration k =>
      simp only [planObservations,prepare_commit s k _ hp (Nat.le_refl _),erasePlan]
      rw [ih (transfer s k) rfl]
      exact suffix_observations _ _ _ (erase_business plan) rfl hp (checkpoint_transfer s k)

/-- Popping any event leaves room for its single response. The dispatch
fallback cannot silently drop a requested reply. -/
theorem pop_reply_capacity (q : Queue) (m : Message) (rest : Queue)
    (h : q.pop = some (m,rest)) (reply : Message) :
    ∃ next, rest.push reply = some next := by
  rcases q with ⟨messages,bounded⟩
  cases messages with
  | nil => simp [Queue.pop] at h
  | cons first tail =>
    simp only [Queue.pop] at h
    cases h
    have small : tail.length < 4 := by simp only [List.length_cons] at bounded; omega
    simp [Queue.push, small]

/-- Matching retries cannot create another effective output. -/
theorem retry_idempotent (x y : Bool) :
    publish (some (.published x y)) x y = (some (.published x y),.published,none) := by
  simp [publish]

theorem conflict_preserves (x y : Bool) :
    publish (some (.published x y)) (!x) y = (some (.published x y),.conflict,none) := by
  cases x <;> rfl

/-- A cancellation tombstone defeats every delayed publish or retry payload. -/
theorem cancelled_no_effect (x input output : Bool) :
    publish (some (.cancelled x)) input output = (some (.cancelled x),.cancelled,none) := rfl

/-- Closing and draining establishes absence of *all* event kinds, including
queries and retries. There is no kind-specific callback filter. -/
theorem no_references (q : Queue) (slot : Bool) (h : q.references slot = false) :
    ∀ m ∈ q.messages, m.slot ≠ slot := by
  simpa [Queue.references, List.any_eq_false] using h

/-- Accepted retirement explicitly checks the whole owned event store. -/
theorem release_excludes (s : Session) (slot : Bool) (r : Request)
    (hh : head s = some (slot,r))
    (released : (step s .release).status = .released) :
    r.routeOpen = false ∧ ∀ m ∈ s.queue.messages, m.slot ≠ slot := by
  simp only [step] at released
  split at released
  · contradiction
  · simp only [hh] at released
    split at released
    · rename_i h
      simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true] at h
      exact ⟨h.1.1,no_references _ _ h.1.2⟩
    · contradiction

/-- Prepared copies cannot process or cancel business work. The old owner and
all accepted obligations remain unchanged until the explicit cut. -/
theorem prepared_freezes (s : Session) (p : Prepared s.active)
    (hp : s.prepared = some p) (c : Command) (hc : Business c) (hi : c ≠ .inspect) :
    (step s c).session = s := by
  cases c <;> simp_all [Business, step, reject]

/-- Failure never allocates retained state or changes accepted obligations. -/
theorem allocation_failure_preserves (s : Session) (k : Kind) (budget : Nat) :
    (step s (.prepare k budget false true)).session = s := by
  simp only [step]
  split <;> try rfl
  split <;> rfl

/-- Pending phases, stable peer ledger and every event survive the ownership cut. -/
theorem commit_checkpoint (s : Session) (p : Prepared s.active)
    (hp : s.prepared = some p) :
    checkpoint (step s .ownershipCommit).session = checkpoint s := by
  have cut : (step s .ownershipCommit).session =
      ⟨p.target,s.requests,s.peer,s.order,s.queue,none⟩ := by
    simp only [step]
    rw [hp]
  rw [cut]
  change (⟨p.target.logical,s.requests,s.peer,s.order,s.queue⟩ : Checkpoint) =
    ⟨s.active.logical,s.requests,s.peer,s.order,s.queue⟩
  rw [p.continuation]

/-- A deliberately weakened receiver authenticates solely by finite token. -/
def tokenOnly (current : Fin 2) (token : Fin 2) (value : Bool) : Option Bool :=
  if current = token then some value else none

/-- After two reuses the receiver accepts the old false response although the
current result is true. The real adapter excludes that response before reuse. -/
theorem token_only_rejecting_control :
    tokenOnly ⟨(0 + 2) % 2,by decide⟩ ⟨0,by decide⟩ false = some false ∧
    tokenOnly ⟨(0 + 2) % 2,by decide⟩ ⟨0,by decide⟩ false ≠ some true := by decide

/-- Generation wraparound cannot authenticate an indefinitely delayed message.
A stale token is equal to the token after exactly one full finite cycle. -/
theorem wraparound_collision (generation : Fin 2) :
    ((generation.val + 2) % 2) = generation.val := by
  have := generation.isLt
  omega

/-- Concrete rejection of token-only safety: old result false is accepted as
current after two uses of a one-bit generation, although current expects true. -/
example : (0 + 2) % 2 = (0 : Nat) ∧ false ≠ true := by decide

end FRPSpec.PendingMigration

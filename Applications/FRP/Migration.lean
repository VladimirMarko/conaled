import Applications.FRP.MigrationPair

/-! Direct two-realization migration with a single accepted tick and local publication. -/
set_option autoImplicit false
set_option warningAsError true
namespace FRPSpec.Migration
open Indefinite

inductive Kind where
  | delay | redundant
  deriving DecidableEq, Repr

/-- Both physical pair cells are retained; the invariant proof is erased. -/
structure PairState where
  first : Bool
  second : Bool
  valid : second = !first

inductive Backend where
  | delay (state : Bool)
  | redundant (state : PairState)

def Backend.kind : Backend → Kind
  | .delay _ => .delay
  | .redundant _ => .redundant

def Backend.logical : Backend → Bool
  | .delay b => b
  | .redundant p => p.first

def Backend.validate : Backend → Bool
  | .delay _ => true
  | .redundant p => MigrationPair.validate (p.first,p.second)

@[simp] theorem backend_validates (b : Backend) : b.validate = true := by
  cases b with
  | delay _ => rfl
  | redundant p => exact (MigrationPair.validate_iff _).2 p.valid

def realize (k : Kind) (b : Bool) : Backend := match k with
  | .delay => .delay b
  | .redundant => .redundant ⟨b,!b,rfl⟩

@[simp] theorem realize_logical (k : Kind) (b : Bool) : (realize k b).logical = b := by cases k <;> rfl
@[simp] theorem realize_kind (k : Kind) (b : Bool) : (realize k b).kind = k := by cases k <;> rfl

/-- An actual Circuit evaluation, retaining its output and candidate continuation. -/
structure TickResult (old : Backend) (input : Bool) where
  output : Bool
  candidate : Backend
  output_eq : output = old.logical
  state_eq : candidate.logical = input
  kind_eq : candidate.kind = old.kind

def evaluate (old : Backend) (input : Bool) : TickResult old input := match old with
  | .delay b =>
    let r := delay.machine.step (input,b)
    ⟨r.1,.delay r.2,rfl,rfl,rfl⟩
  | .redundant p =>
    let r := MigrationPair.redundant.machine.step (input,(p.first,p.second))
    ⟨r.1,.redundant ⟨r.2.1,r.2.2,rfl⟩,rfl,rfl,rfl⟩

inductive Flight (old : Backend) where
  | idle
  | accepted (input : Bool)
  | pending (input : Bool) (result : TickResult old input)
  | published (input : Bool) (result : TickResult old input)

structure Prepared (old : Backend) where
  target : Backend
  continuation : target.logical = old.logical

structure Session where
  active : Backend
  flight : Flight active
  last : Option Bool
  request : Option Kind
  prepared : Option (Prepared active)

def initial (k : Kind := .delay) : Session := ⟨realize k false,.idle,none,none,none⟩

inductive Command where
  | accept (input : Bool)
  | evaluate (owner : Option Kind := none)
  | sink (ready : Bool)
  | tickCommit
  | request (target : Kind)
  | unsupported
  | prepare (budget : Nat) (allocationOK validationOK : Bool)
  | ownershipCommit
  | cancel
  | query

inductive Status where
  | accepted | evaluated | published | tickCommitted | requested | prepared | migrated
  | cancelled | query | busy | refused | wrongOwner | sameBackend | unsupported
  | resourceFailure | allocationFailure | validationFailure | idle
  deriving DecidableEq, Repr

structure Outcome where
  session : Session
  status : Status
  accepted : Option Bool := none
  business : Option Bool := none

/-- Logical slots: fixed control fields + bounded input/output frame buffers. -/
def fixedSlots : Nat := 80

def Backend.cells : Backend → Nat
  | .delay _ => 1
  | .redundant _ => 2

def conversionWork : Kind → Nat
  | .delay => 1
  | .redundant => 2

/-- Includes old/new states and a two-cell conversion temporary. -/
def preparationSlots (s : Session) (target : Kind) : Nat :=
  fixedSlots + s.active.cells + 1 + (realize target s.active.logical).cells + 2

def reject (s : Session) (status : Status) : Outcome := ⟨s,status,none,none⟩

def step (s : Session) (command : Command) : Outcome :=
  match command with
  | .query => reject s .query
  | .unsupported => reject s .unsupported
  | .cancel => ⟨{s with request := none, prepared := none},.cancelled,none,none⟩
  | .request target =>
    if s.request.isSome || s.prepared.isSome then reject s .busy
    else if target = s.active.kind then reject s .sameBackend
    else ⟨{s with request := some target},.requested,none,none⟩
  | .accept x =>
    if s.request.isSome || s.prepared.isSome then reject s .busy
    else match s.flight with
    | .idle => ⟨{s with flight := .accepted x},.accepted,some x,none⟩
    | _ => reject s .busy
  | .evaluate owner =>
    if owner.isSome && owner != some s.active.kind then reject s .wrongOwner
    else match s.flight with
    | .accepted x => ⟨{s with flight := .pending x (evaluate s.active x)},.evaluated,none,none⟩
    | _ => reject s .busy
  | .sink ready => match s.flight with
    | .pending x r => if ready then
        ⟨{s with flight := .published x r, last := some r.output},.published,none,some r.output⟩
      else reject s .refused
    | _ => reject s .busy
  | .tickCommit => match s.flight with
    | .published _ r => ⟨⟨r.candidate,.idle,s.last,s.request,none⟩,.tickCommitted,none,none⟩
    | _ => reject s .busy
  | .prepare budget allocationOK validationOK => match s.flight,s.request with
    | .idle,some target =>
      if s.prepared.isSome then reject s .busy
      else if preparationSlots s target > budget then
        ⟨{s with request := none, prepared := none},.resourceFailure,none,none⟩
      else if !allocationOK then
        ⟨{s with request := none, prepared := none},.allocationFailure,none,none⟩
      else if !validationOK || !s.active.validate then
        ⟨{s with request := none, prepared := none},.validationFailure,none,none⟩
      else ⟨{s with prepared := some ⟨realize target s.active.logical,realize_logical _ _⟩},
        .prepared,none,none⟩
    | _,_ => reject s .busy
  | .ownershipCommit => match s.flight,s.prepared with
    | .idle,some p => ⟨⟨p.target,.idle,s.last,none,none⟩,.migrated,none,none⟩
    | _,_ => reject s .busy

/-- Ghost observation only: the executable session stores no history. -/
def outstanding (s : Session) : List Bool := match s.flight with
  | .accepted _ | .pending _ _ => [s.active.logical]
  | _ => []

def future (s : Session) : Bool := match s.flight with
  | .accepted x | .pending x _ | .published x _ => x
  | .idle => s.active.logical

/-- Cumulative observation is a proof/finite-client helper, not runtime state. -/
def execute : Session → List Command → Session × List Bool × List Bool
  | s,[] => (s,[],[])
  | s,c::cs =>
    let r := step s c
    let rest := execute r.session cs
    (rest.1,r.accepted.toList ++ rest.2.1,r.business.toList ++ rest.2.2)

open Progress.Feedback

@[simp] theorem reference_nil (b : Bool) : run delay.machine.mealy b [] = ([],b) := rfl
@[simp] theorem reference_single (b x : Bool) : run delay.machine.mealy b [x] = ([b],x) := rfl

attribute [local simp] TickResult.output_eq TickResult.state_eq Prepared.continuation

set_option maxHeartbeats 800000 in
/-- Each accepted input and published output is accounted for, including the
unpublished obligation retained in accepted/pending phases. -/
theorem step_balance (s : Session) (c : Command) :
    let r := step s c
    let reference := run delay.machine.mealy (future s) r.accepted.toList
    outstanding s ++ reference.1 = r.business.toList ++ outstanding r.session ∧
      reference.2 = future r.session := by
  rcases s with ⟨active,flight,last,request,prepared⟩
  cases c <;> cases flight <;> cases request <;> cases prepared <;> simp only [step, reject]
  all_goals try split_ifs
  all_goals simp_all [outstanding, future, run,
    Progress.Feedback.Initialized.mealy, Indefinite.delay, Program.delay, Program.machine,
    Applications.Circuits.Circuit.execute]


/-- Arbitrary finite command schedules preserve the complete ordered reference
execution, with accepted-but-unpublished work explicitly retained. -/
theorem execute_balance (s : Session) (commands : List Command) :
    let r := execute s commands
    let reference := run delay.machine.mealy (future s) r.2.1
    outstanding s ++ reference.1 = r.2.2 ++ outstanding r.1 ∧
      reference.2 = future r.1 := by
  induction commands generalizing s with
  | nil => simp [execute, run]
  | cons c cs ih =>
    have h := step_balance s c
    have hr := ih (step s c).session
    simp only [execute, run_append]
    dsimp only at h hr ⊢
    rw [h.2]
    constructor
    · rw [← List.append_assoc, h.1, List.append_assoc, hr.1, List.append_assoc]
    · exact hr.2

/-- A completed schedule has exactly the ordinary delay outputs and retained
logical state, regardless of the number or placement of migrations/queries. -/
theorem completed_schedule (k : Kind) (commands : List Command)
    (done : outstanding (execute (initial k) commands).1 = []) :
    run delay.machine.mealy false (execute (initial k) commands).2.1 =
      ((execute (initial k) commands).2.2, future (execute (initial k) commands).1) := by
  have h := execute_balance (initial k) commands
  have hf : future (initial k) = false := by cases k <;> rfl
  have ho : outstanding (initial k) = [] := rfl
  dsimp only at h
  rw [hf, ho, done, List.append_nil, List.nil_append] at h
  exact Prod.ext h.1 h.2

theorem query_preserves (s : Session) : (step s .query).session = s := rfl

theorem cancellation_preserves_work (s : Session) :
    (step s .cancel).session.active = s.active ∧
    HEq (step s .cancel).session.flight s.flight := ⟨rfl,HEq.rfl⟩

theorem refusal_preserves (s : Session) : (step s (.sink false)).session = s := by
  cases s with
  | mk active flight last request prepared => cases flight <;> rfl

theorem preparation_retains_authority (s : Session) (budget : Nat) (a v : Bool) :
    (step s (.prepare budget a v)).session.active = s.active := by
  rcases s with ⟨active,flight,last,request,prepared⟩
  cases flight <;> cases request <;> simp only [step, reject]
  all_goals repeat' first | simp_all | split

def drain (s : Session) : List Command := match s.flight with
  | .idle => []
  | .accepted _ => [.evaluate none,.sink true,.tickCommit]
  | .pending _ _ => [.sink true,.tickCommit]
  | .published _ _ => [.tickCommit]

/-- Conditional finite retirement: the schedule explicitly supplies evaluation,
local sink acceptance and tick commit. No blocked-sink deadline is assumed. -/
theorem drain_idle (s : Session) : (execute s (drain s)).1.flight = .idle := by
  rcases s with ⟨active,flight,last,request,prepared⟩
  cases flight <;> rfl

end FRPSpec.Migration

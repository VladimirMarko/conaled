import Applications.FRP.RegionalSelectionCosts
import Applications.FRP.MigrationSafety

/-! Quiescent changes of actual regional cuts. Pending work is a separate stage.
The active executor is frozen while a nonauthoritative target is prepared. -/
namespace FRPSpec.Regional.Reconfiguration
open Progress Progress.Feedback Selection

/-- Reconstruct the exact nested state, preserving the delay instead of its seed. -/
def resumeCut : (c : Cut) → Bool → (compile c).State
  | .fused, b => (⟨⟩,(b,⟨⟩))
  | .split, b => (⟨⟩,(b,⟨⟩))
  | .checked, b => (((⟨⟩,⟨⟩),⟨⟩),(b,⟨⟩))

@[simp] theorem logical_resume (c : Cut) (b : Bool) : logical c (resumeCut c b) = b := by
  cases c <;> rfl

def resume (c : Sites) (b : Bool × Bool) : c.plan.State :=
  (resumeCut c.left b.1,resumeCut c.right b.2)
@[simp] theorem observe_resume (c : Sites) (b : Bool × Bool) : c.observe (resume c b) = b :=
  Prod.ext (logical_resume _ _) (logical_resume _ _)

def observation (s : Selection.Session) : Bool × Bool := s.sites.observe s.state

def transfer (s : Selection.Session) (c : Sites) : Selection.Session :=
  ⟨c,resume c (observation s)⟩
@[simp] theorem transfer_observation (s : Selection.Session) (c : Sites) :
    observation (transfer s c) = observation s := observe_resume _ _

/-- Both outputs and the entire logical continuation agree for arbitrary suffixes. -/
theorem transfer_suffix (s : Selection.Session) (c : Sites) (xs : List (Input × Input)) :
    (run c.plan.machine.mealy (transfer s c).state xs).1 =
      (run s.sites.plan.machine.mealy s.state xs).1 ∧
    c.observe (run c.plan.machine.mealy (transfer s c).state xs).2 =
      s.sites.observe (run s.sites.plan.machine.mealy s.state xs).2 := by
  have h := c.continuation (transfer s c).state xs
  have k := s.sites.continuation s.state xs
  simp only [transfer,observe_resume] at h
  exact ⟨h.1.trans k.1.symm,h.2.trans k.2.symm⟩

/-- Conversion copies two logical bits and constructs the target's retained cells. -/
def conversionWork (c : Sites) : Nat := 2 + c.plan.retained
/-- Eight reserved control/tag/plan-index cells, old state, new state and two
copied logical bits coexist. Requirements/certificates are erased proof data.
Steady-state arenas are checked separately, never overlapped by assumption. -/
def transferPeak (s : Selection.Session) (c : Sites) : Nat :=
  8 + s.sites.plan.retained + c.plan.retained + 2

def required (s : Selection.Session) (c : Sites) : Nat :=
  max (8 + c.plan.storage) (max (8 + s.sites.plan.storage) (transferPeak s c))

structure Prepared (old : Selection.Session) where
  target : Selection.Session
  continuation : observation target = observation old
  evidence : ∃ r : Requirements, Selection.Certificate r target.sites ∧
    required old target.sites ≤ r.capacity

structure Session where
  active : Selection.Session
  prepared : Option (Prepared active)
  permitted : Bool

def initial (c : Sites) : Session := ⟨Selection.Session.start c,none,true⟩

inductive Status where
  | ticked | prepared | committed | cancelled | throttled | frozen | stale
  | capacity | allocation | validation | unsupported | idle | noCandidate
  deriving DecidableEq, Repr

/-- Charged operations name the actual bounded local transitions. -/
inductive Event where
  | check | copy (cells : Nat) | allocate (cells : Nat) | release (cells : Nat)
  | execute (work : Nat) | observe | policy (work : Nat)
  deriving Repr

def Event.work : Event → Nat
  | .check | .observe => 1
  | .copy n | .allocate n | .release n | .execute n | .policy n => n

def bill (es : List Event) : Nat := (es.map Event.work).sum

structure Outcome where
  session : Session
  status : Status
  output : Option (Bool × Bool) := none
  events : List Event := []

def refuse (s : Session) (status : Status) (es : List Event := [.check]) : Outcome :=
  ⟨s,status,none,es⟩

/-- Static semantics and storage evidence are reconstructed for the exact target. -/
theorem certificate (r : Requirements) (c : Sites) (h : eligible r c) : Selection.Certificate r c :=
  ⟨h.2.2.2.1,h.2.2.2.2,c.continuation⟩

/-- Compare the converted continuation before publishing ownership. -/
def validateTransfer (old target : Selection.Session) : Bool :=
  decide (observation target = observation old)
@[simp] theorem validate_transfer (old : Selection.Session) (c : Sites) :
    validateTransfer old (transfer old c) = true := by
  simp [validateTransfer]

def prepare (s : Session) (expected target : Sites) (r : Requirements)
    (allocationOK validationOK : Bool) : Outcome :=
  if s.prepared.isSome then refuse s .frozen
  else if !s.permitted then refuse s .throttled
  else
    let attempted : Session := ⟨s.active,none,false⟩
    if expected ≠ s.active.sites then refuse attempted .stale
    else if h : eligible r target then
      if hp : required s.active target ≤ r.capacity then
        if !allocationOK then refuse attempted .allocation [.check,.check]
        else
          let converted := transfer s.active target
          if !(validateTransfer s.active converted && validationOK) then
            refuse attempted .validation [.check,.allocate 2,.copy 2,.allocate target.plan.retained,
              .copy target.plan.retained,.check,.release 2,.release target.plan.retained]
          else
            let p : Prepared s.active := ⟨converted,transfer_observation _ _,
              ⟨r,certificate r target h,hp⟩⟩
            ⟨⟨s.active,some p,false⟩,.prepared,none,
              [.check,.allocate 2,.copy 2,.allocate target.plan.retained,
                .copy target.plan.retained,.check,.release 2]⟩
      else refuse attempted .capacity [.check,.check]
    else refuse attempted .unsupported [.check,.check]

def commit (s : Session) : Outcome := match s.prepared with
  | none => refuse s .idle
  | some p => ⟨⟨p.target,none,false⟩,.committed,none,
      [.check,.release s.active.sites.plan.retained]⟩

def cancel (s : Session) : Outcome := match s.prepared with
  | none => refuse s .idle
  | some p => ⟨⟨s.active,none,false⟩,.cancelled,none,[.release p.target.sites.plan.retained]⟩

def tick (s : Session) (x : Input × Input) : Outcome :=
  if s.prepared.isSome then refuse s .frozen
  else
    let result := s.active.sites.plan.machine.step (x,s.active.state)
    ⟨⟨⟨s.active.sites,result.2⟩,none,true⟩,.ticked,some result.1,
      [.execute (s.active.sites.plan.stepWork x s.active.state),.observe,.observe]⟩

/-- Policy is a proposal only. Its steady-state admission cannot authorize transfer. -/
def propose (s : Session) (r : Requirements) (w : String)
    (e : Option Optimization.Choice.Epoch) (cs : List Sites := Selection.catalog) : Outcome :=
  let assessed := Selection.inspect r cs
  let ctx := {Selection.context r w with catalog := assessed.1.map Sites.name}
  let scores := Selection.preparedScores e ctx
  let ranked := Selection.rank scores.1 assessed.1
  let policyEvents := [Selection.Event.feature (Selection.contextSize (Selection.context r w))] ++
    assessed.2 ++ scores.2 ++ ranked.2
  match ranked.1 with
  | none => refuse s .noCandidate [.policy (Selection.bill policyEvents)]
  | some c =>
      let result := prepare s s.active.sites c r true true
      { result with events := .policy (Selection.bill policyEvents) :: result.events }

inductive Command where
  | input (x : Input × Input)
  | prepare (expected target : Sites) (requirements : Requirements) (allocationOK validationOK : Bool)
  | commit | cancel | unsupported
  | policy (requirements : Requirements) (workload : String)
      (evidence : Option Optimization.Choice.Epoch) (catalog : List Sites)

def step (s : Session) : Command → Outcome
  | .input x => tick s x
  | .prepare e c r a v => prepare s e c r a v
  | .commit => commit s
  | .cancel => cancel s
  | .unsupported => refuse s .unsupported
  | .policy r w e cs => propose s r w e cs

def execute : Session → List Command → Session × List (Bool × Bool)
  | s, [] => (s,[])
  | s, c::cs =>
      let next := step s c
      let rest := execute next.session cs
      (rest.1,next.output.toList ++ rest.2)

end FRPSpec.Regional.Reconfiguration

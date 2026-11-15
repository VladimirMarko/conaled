import Applications.FRP.RegionalAdmission
import Applications.Optimization.Choice.Evidence

/-! Session-boundary selection of two interacting regional choice sites. -/
namespace FRPSpec.Regional.Selection
open Progress Progress.Feedback

structure Sites where
  left : Cut
  right : Cut
  deriving DecidableEq, Repr

def cuts : List Cut := [.fused,.split,.checked]
def catalog : List Sites := cuts.flatMap fun l => cuts.map fun r => ⟨l,r⟩
def Sites.plan (c : Sites) : Plan (Input × Input) (Bool × Bool) :=
  .par (compile c.left) (compile c.right)
def Sites.observe (c : Sites) (s : c.plan.State) : Bool × Bool :=
  (logical c.left s.1,logical c.right s.2)

def oracle : Initialized (Input × Input) (Bool × Bool) (Bool × Bool) :=
  ⟨fun (x,s) => ((!s.1,!s.2),(Rich.oracle x.1,Rich.oracle x.2)),(false,false)⟩

theorem Sites.step_correct (c : Sites) (s : c.plan.State) (x : Input × Input) :
    (c.plan.machine.step (x,s)).1 = (!(c.observe s).1, !(c.observe s).2) ∧
    c.observe (c.plan.machine.step (x,s)).2 = (Rich.oracle x.1,Rich.oracle x.2) := by
  have hl := Regional.step_correct c.left s.1 x.1
  have hr := Regional.step_correct c.right s.2 x.2
  exact ⟨Prod.ext hl.1 hr.1,Prod.ext hl.2 hr.2⟩

theorem Sites.continuation (c : Sites) (s : c.plan.State) (xs : List (Input × Input)) :
    (run c.plan.machine.mealy s xs).1 = (run oracle.mealy (c.observe s) xs).1 ∧
    c.observe (run c.plan.machine.mealy s xs).2 = (run oracle.mealy (c.observe s) xs).2 := by
  have h := run_related c.plan.machine.mealy oracle.mealy Eq
    (fun t b => c.observe t = b) Eq
    (by intro x y t b hxy htb; subst y; subst b; exact c.step_correct t x)
    (List.forall₂_same.mpr (fun _ _ => rfl) : List.Forall₂ Eq xs xs) (s := s) rfl
  exact ⟨by simpa only [List.forall₂_eq_eq_eq] using h.1,h.2⟩

theorem Sites.initial_correct (c : Sites) : c.observe c.plan.machine.initial = (false,false) :=
  Prod.ext (Regional.initial_correct c.left) (Regional.initial_correct c.right)

/-- Requirements name the supported port and scheduling contract. The supplied
finite waits are the progress premise, not a promise about a blocked sink. -/
structure Requirements where
  capacity : Nat
  protocol : Nat := 1
  ordered : Bool := true
  finiteWaits : Bool := true
  deriving DecidableEq, Repr

def eligible (r : Requirements) (c : Sites) : Prop :=
  r.protocol = 1 ∧ r.ordered = true ∧ r.finiteWaits = true ∧
  c.plan.analyzed = true ∧ c.plan.storage ≤ r.capacity
instance (r : Requirements) : DecidablePred (eligible r) := fun _ => inferInstanceAs (Decidable (_ ∧ _))

def cutName : Cut → String
  | .fused => "fused"
  | .split => "split"
  | .checked => "checked"
def Sites.name (c : Sites) : String := cutName c.left ++ "/" ++ cutName c.right

def context (r : Requirements) (workload : String) : Optimization.Choice.Context :=
  ⟨"regional-v1", "Lean-modeled-cells", workload, "left/right:F-D-N", "typed-copy-left-then-right-v1",
    [r.capacity,r.protocol,if r.ordered then 1 else 0,if r.finiteWaits then 1 else 0],[]⟩

def select (r : Requirements) (workload : String) (e : Option Optimization.Choice.Epoch)
    (cs : List Sites := catalog) : Option Sites :=
  Optimization.Choice.choose cs (eligible r) Sites.name (context r workload) 1
    (fun c => c.plan.work) e

/-- State remains indexed by the chosen whole executor. Updating evidence cannot
cast or replace this state; a new session requires explicit initialization. -/
structure Session where
  sites : Sites
  state : sites.plan.State

def Session.start (c : Sites) : Session := ⟨c,c.plan.machine.initial⟩
def Session.advance (s : Session) (xs : List (Input × Input)) : List (Bool × Bool) × Session :=
  let result := run s.sites.plan.machine.mealy s.state xs
  (result.1,⟨s.sites,result.2⟩)

theorem selected_execution {r : Requirements} {w : String} {e} {cs} {c : Sites}
    (h : select r w e cs = some c) (x : Input × Input) (s : c.plan.State) :
    ∃ trace, Plan.SpaceRuns c.plan x s (c.plan.machine.step (x,s)) trace ∧
      ∀ live ∈ trace, c.plan.retained + live ≤ r.capacity := by
  have hc : eligible r c := Optimization.Choice.choose_contract (eligible r)
    (fun _ _ hc => hc) h
  exact c.plan.sufficient_storage hc.2.2.2.1 r.capacity hc.2.2.2.2 x s

theorem selected_continuation {r : Requirements} {w : String} {e} {cs} {c : Sites}
    (h : select r w e cs = some c) (s : c.plan.State) (xs : List (Input × Input)) :
    (run c.plan.machine.mealy s xs).1 = (run oracle.mealy (c.observe s) xs).1 ∧
    c.observe (run c.plan.machine.mealy s xs).2 = (run oracle.mealy (c.observe s) xs).2 :=
  Optimization.Choice.choose_contract
    (fun d => ∀ (t : d.plan.State) (ys : List (Input × Input)), (run d.plan.machine.mealy t ys).1 = (run oracle.mealy (d.observe t) ys).1 ∧
      d.observe (run d.plan.machine.mealy t ys).2 = (run oracle.mealy (d.observe t) ys).2)
    (fun d _ _ => d.continuation) h s xs

/-- The selected plan retains the service theorem's explicit finite waits. -/
theorem selected_service {r : Requirements} {w} {e} {cs} {c : Sites}
    (h : select r w e cs = some c) (env : Indefinite.Program.Environment)
    (input : Stream (Input × Input)) (deadline : Nat) :
    ∃ k, deadline < c.plan.starts env (k+1) ∧
      Plan.Round c.plan env k (input k) (state c.plan.machine input k)
        (c.plan.starts env k) (output c.plan.machine input k,state c.plan.machine input (k+1))
        (c.plan.starts env (k+1)) := by
  have hc : eligible r c := Optimization.Choice.choose_contract (eligible r)
    (fun _ _ hc => hc) h
  exact ⟨deadline,lt_of_lt_of_le (Nat.lt_succ_self deadline) (c.plan.starts_grow env _),
    c.plan.scheduled hc.2.2.2.1 env input deadline⟩

/-- Whole-plan construction commutes with finite selection when requirements
and scores are evaluated in the enclosing context. -/
theorem select_constructed (capacity : Nat) :
    Optimization.Choice.select (catalog.map Sites.plan)
      (fun p => p.storage ≤ capacity) (fun p => p.work) =
    (Optimization.Choice.select catalog (fun c => c.plan.storage ≤ capacity)
      (fun c => c.plan.work)).map Sites.plan :=
  Optimization.Choice.select_map Sites.plan catalog (fun p => p.storage ≤ capacity) (fun p => p.work)

end FRPSpec.Regional.Selection

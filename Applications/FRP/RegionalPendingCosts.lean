import Applications.FRP.RegionalPendingService
import Applications.FRP.RegionalPendingPolicy

/-! Workload projections retain every actual command, including failed migration
and refused business work. They reuse the public pending executor and tariffs. -/
namespace FRPSpec.Regional.Pending

/-- The wrapper adapter is charged once per command, before its ordered work. -/
inductive BilledEvent where
  | adapter
  | operation (event : WorkEvent)

def BilledEvent.work : BilledEvent → Nat
  | .adapter => 1
  | .operation e => e.work

def Outcome.billedEvents (o : Outcome) : List BilledEvent :=
  .adapter :: o.events.map .operation

def events (s : Session) (cs : List Command) : List BilledEvent :=
  (outcomes s cs).flatMap Outcome.billedEvents

def totalWork (s : Session) (cs : List Command) : Nat :=
  ((events s cs).map BilledEvent.work).sum

theorem outcome_bill (o : Outcome) :
    (o.billedEvents.map BilledEvent.work).sum = work o := by
  simp [Outcome.billedEvents,Function.comp_def,BilledEvent.work,work]

theorem totalWork_projection (s : Session) (cs : List Command) :
    totalWork s cs = ((outcomes s cs).map work).sum := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    simp only [totalWork,events,outcomes,List.flatMap_cons,List.map_append,List.sum_append,
      outcome_bill,List.map_cons,List.sum_cons] at *
    rw [ih]

theorem outcomes_append (s : Session) (xs ys : List Command) :
    outcomes s (xs ++ ys) = outcomes s xs ++ outcomes (execute s xs).1 ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons c cs ih => simp [outcomes,execute,ih]

theorem events_append (s : Session) (xs ys : List Command) :
    events s (xs ++ ys) = events s xs ++ events (execute s xs).1 ys := by
  simp [events,outcomes_append]

theorem totalWork_append (s : Session) (xs ys : List Command) :
    totalWork s (xs ++ ys) = totalWork s xs + totalWork (execute s xs).1 ys := by
  simp [totalWork,events_append]

/-- Costs erase to the original public observations and source refinement. -/
theorem workload_refines (cut : Cut) (kind : Migration.Kind) (cs : List Command) :
    (outcomes (initial cut kind) cs).flatMap (fun o => o.business.toList) =
      (execute (initial cut kind) cs).2 ∧
    SourceRun (source (initial cut kind).active) (outcomes (initial cut kind) cs)
      (source (execute (initial cut kind) cs).1.active) :=
  ⟨(execute_outputs _ _).symm,(reachable_refinement cut kind cs).2.2⟩

/-- Finite plan comparisons retain complete ownership checkpoints and the source
stream, while billing both commands of every attempted transfer. -/
theorem migration_projection (s : Session) (plan : List PlanAction) (ready : Ready s) :
    checkpoint (execute s (expandPlan plan)).1.active =
      checkpoint (execute s (erasePlan plan)).1.active ∧
    (outcomes s (expandPlan plan)).flatMap (fun o => o.business.toList) =
      (execute s (erasePlan plan)).2 ∧
    totalWork s (expandPlan plan) = ((outcomes s (expandPlan plan)).map work).sum := by
  have h := public_repeated_migration s plan ready
  exact ⟨h.1,(execute_outputs _ _).symm.trans h.2,totalWork_projection _ _⟩

/-- Proposal is an existing public operation, not a new command interpreter. -/
def proposedWork (s : Session) (r : Requirements) (w : String)
    (e : Option Optimization.Choice.Epoch) (catalog : List Candidate)
    (cs : List Command) : Nat :=
  let proposed := propose s r w e catalog
  work proposed + totalWork proposed.session cs

def retainedObservations (s : Session) (cs : List Command) : List Nat :=
  wrapperRetained s :: (outcomes s cs).map (fun o => wrapperRetained o.session)

end FRPSpec.Regional.Pending

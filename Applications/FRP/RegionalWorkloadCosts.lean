import Applications.FRP.RegionalMigrationResources

/-! Ordered workload accounting for the existing regional command executor.
Tariffs count modeled operations; retained storage is observed separately. -/
namespace FRPSpec.Regional.Reconfiguration

/-- Observe the actual transitions without introducing another evaluator. -/
def outcomes : Session → List Command → List Outcome
  | _, [] => []
  | s, c :: cs => let o := step s c; o :: outcomes o.session cs

def events (s : Session) (cs : List Command) : List Event :=
  (outcomes s cs).flatMap Outcome.events

def totalWork (s : Session) (cs : List Command) : Nat := bill (events s cs)

theorem outcomes_append (s : Session) (xs ys : List Command) :
    outcomes s (xs ++ ys) = outcomes s xs ++ outcomes (execute s xs).1 ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons c cs ih => simp [outcomes,execute,ih]

theorem events_append (s : Session) (xs ys : List Command) :
    events s (xs ++ ys) = events s xs ++ events (execute s xs).1 ys := by
  simp [events,outcomes_append]

theorem bill_append (xs ys : List Event) : bill (xs ++ ys) = bill xs + bill ys := by
  simp [bill]

/-- The suffix is charged at its live continuation, including failed attempts. -/
theorem totalWork_append (s : Session) (xs ys : List Command) :
    totalWork s (xs ++ ys) = totalWork s xs + totalWork (execute s xs).1 ys := by
  simp [totalWork,events_append,bill_append]

theorem outputs_projection (s : Session) (cs : List Command) :
    (outcomes s cs).flatMap (fun o => o.output.toList) = (execute s cs).2 := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih => simp [outcomes,execute,ih]

/-- Erasing cost observations recovers the independent source, including state. -/
theorem workload_refines (s : Session) (cs : List Command) :
    (outcomes s cs).flatMap (fun o => o.output.toList) =
      (Progress.Feedback.run Selection.oracle.mealy (observation s.active)
        (acceptedInputs s cs)).1 ∧
    observation (execute s cs).1.active =
      (Progress.Feedback.run Selection.oracle.mealy (observation s.active)
        (acceptedInputs s cs)).2 := by
  rw [outputs_projection]
  exact execute_refines s cs

/-- Keep admission/selection/construction events distinct from execution events. -/
inductive WorkloadEvent where
  | installation (event : Selection.Event)
  | execution (event : Event)

def WorkloadEvent.work : WorkloadEvent → Nat
  | .installation e => e.charge
  | .execution e => e.work

/-- A rejected installation retains its bill and cannot execute the schedule. -/
def installedEvents (r : Selection.Requirements) (w : String)
    (e : Option Optimization.Choice.Epoch) (catalog : List Selection.Sites)
    (cs : List Command) : List WorkloadEvent :=
  let installed := Selection.installation r w e catalog
  installed.2.map .installation ++ match installed.1 with
    | none => []
    | some s => (events ⟨s,none,true⟩ cs).map .execution

theorem installed_bill (r : Selection.Requirements) (w : String)
    (e : Option Optimization.Choice.Epoch) (catalog : List Selection.Sites)
    (cs : List Command) :
    ((installedEvents r w e catalog cs).map WorkloadEvent.work).sum =
      Selection.bill (Selection.installation r w e catalog).2 +
      ((Selection.installation r w e catalog).1.map
        (fun s => totalWork ⟨s,none,true⟩ cs)).getD 0 := by
  unfold installedEvents
  cases h : (Selection.installation r w e catalog).1 <;>
    simp [h,Function.comp_def,WorkloadEvent.work,totalWork,bill,Selection.bill]

/-- Retained old and prepared states coexist; this is not an additive work bill. -/
def retained (s : Session) : Nat :=
  8 + s.active.sites.plan.retained +
    (s.prepared.map (fun p => p.target.sites.plan.retained)).getD 0

def retainedObservations (s : Session) (cs : List Command) : List Nat :=
  retained s :: (outcomes s cs).map (fun o => retained o.session)

end FRPSpec.Regional.Reconfiguration

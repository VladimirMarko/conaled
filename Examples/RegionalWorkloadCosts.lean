import Applications.FRP.RegionalWorkloadCosts
import Examples.RegionalSelection
import Examples.RegionalMigration

/-! Fixed finite workloads compare modeled operation totals, including selection
and installation. Synthetic evidence chooses the initial checked executor. -/
set_option maxRecDepth 8192
namespace Examples.RegionalWorkloadCosts
open FRPSpec.Regional hiding Command
open FRPSpec.Regional.Reconfiguration

abbrev checked : Selection.Sites := both .checked
abbrev split : Selection.Sites := both .split

def block : List Command := Selection.inputs.map Command.input
def workload (n : Nat) : List Command := (List.replicate n block).flatten

def switch : List Command := [.policy roomy "cost-comparison" none Selection.catalog,.commit]
def startup := Selection.installation roomy "cost-comparison"
  (some (Selection.synthetic roomy "cost-comparison" checked)) Selection.catalog

def invoice (cs : List Command) : Nat :=
  ((installedEvents roomy "cost-comparison"
    (some (Selection.synthetic roomy "cost-comparison" checked)) Selection.catalog cs).map
      WorkloadEvent.work).sum

theorem startup_checked : startup.1 = some (Selection.Session.start checked) := by rfl

theorem invoice_execution (cs : List Command) :
    invoice cs = Selection.bill startup.2 + totalWork (initial checked) cs := by
  rw [invoice,installed_bill]
  change Selection.bill startup.2 + (startup.1.map _).getD 0 = _
  rw [startup_checked]
  rfl

/-- Independent expected outputs and final delay state, for every supplied cut. -/
theorem block_observations (c : Cut) :
    (outcomes (initial (both c)) block).flatMap (fun o => o.output.toList) =
      [(true,true),(false,true),(true,false)] ∧
    observation (execute (initial (both c)) block).1.active = (false,true) := by
  have h := workload_refines (initial (both c)) block
  cases c <;> exact h

/-- An unequal live continuation distinguishes copying both states from reset
or interchange. The empty suffix already observes the transferred state. -/
def unequal : Session := ⟨⟨split,resume split (true,false)⟩,none,true⟩
def moveUnequal : List Command := [.prepare split checked roomy true true,.commit]

example : observation (execute unequal moveUnequal).1.active = (true,false) ∧
    (execute unequal (moveUnequal ++ block)).2 =
      [(false,true),(false,true),(true,false)] := by decide

/-- The bill composes at the state actually left by the policy and commit. -/
example (n : Nat) : totalWork (initial checked) (switch ++ workload n) =
    totalWork (initial checked) switch +
      totalWork (execute (initial checked) switch).1 (workload n) :=
  totalWork_append _ _ _

/-- The independent two-delay continuation survives the chosen plan change. -/
example : (outcomes (initial checked) (switch ++ block)).flatMap
    (fun o => o.output.toList) = [(true,true),(false,true),(true,false)] ∧
    observation (execute (initial checked) (switch ++ block)).1.active = (false,true) :=
  workload_refines _ _

/-- One block cannot repay the full-catalog policy and migration overhead. -/
theorem short_switch_loses : invoice (workload 1) = 12952 ∧
    invoice (switch ++ workload 1) = 13631 := by decide

set_option maxRecDepth 32768 in
/-- Sixty-four blocks repay the same overhead using the actual selected plan. -/
theorem long_switch_saves : invoice (workload 64) = 27064 ∧
    invoice (switch ++ workload 64) = 23207 := by decide

set_option maxRecDepth 32768 in
theorem long_observations :
    (execute (initial checked) (switch ++ workload 64)).2 =
      (execute (initial checked) (workload 64)).2 ∧
    (execute (initial checked) (switch ++ workload 64)).2.length = 192 ∧
    observation (execute (initial checked) (switch ++ workload 64)).1.active = (false,true) := by
  decide

/-- Charge validation, including rejected evidence and an empty admitted catalog. -/
example : 0 < Selection.bill (Selection.installation {capacity := 0}
    "cost-comparison" none Selection.catalog).2 ∧
    (Selection.installation {capacity := 0} "cost-comparison" none Selection.catalog).1 = none := by
  decide

example : (Selection.preparedScores
    (some (Selection.synthetic roomy "other-workload" checked))
    (Optimization.Choice.admittedContext Selection.catalog (Selection.eligible roomy) Selection.Sites.name
      (Selection.context roomy "cost-comparison"))).1 split =
    (split.plan.work,[Selection.Event.rank (Selection.planNodes split.plan)]) := by rfl

/-- Every tick completes before another migration attempt is made. -/
def frequent : List Command :=
  [.prepare split checked roomy true true,.commit,.input fixtureA,
   .prepare checked split roomy true true,.commit,.input fixtureB,
   .prepare split checked roomy true true,.commit,.input fixtureC]

example : (execute (initial split) frequent).2 = (execute (initial split) block).2 ∧
    totalWork (initial split) block < totalWork (initial split) frequent := by decide

/-- Allocation/copy/validation/release work survives a failed preparation. -/
def failed : List Command := [.prepare checked split roomy true false,.commit]
example : totalWork (initial checked) failed = 15 ∧
    observation (execute (initial checked) failed).1.active = (false,false) := by decide

/-- A tick attempted during preparation is refused; it is not a source input. -/
def frozen : List Command :=
  [.prepare checked split roomy true true,.input fixtureA,.cancel,.input fixtureB]
example : acceptedInputs (initial checked) frozen = [fixtureB] ∧
    (outcomes (initial checked) frozen).map Outcome.status =
      [.prepared,.frozen,.cancelled,.ticked] := by decide

/-- Peak transfer storage and retained prepared storage are distinct observations. -/
example : retainedObservations (initial checked)
    [.prepare checked split roomy true true,.cancel] = [10,12,10] ∧
    transferPeak (initial checked).active split = 14 := by decide

end Examples.RegionalWorkloadCosts

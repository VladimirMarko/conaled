import Applications.FRP.RegionalPendingCosts
import Examples.RegionalPending
import Examples.RegionalPendingPolicy

/-! Transaction bills include producer, consumers, publication, confirmation and
retirement. A migration between consumer deliveries keeps completed work. -/
set_option maxRecDepth 8192
namespace Examples.RegionalPendingCosts
open FRPSpec
open FRPSpec.Regional
open FRPSpec.Regional.Pending

def transaction (input : Bool) : List Command :=
  [.accept input,.producer,.whole] ++ RegionalPending.retire

def workload (pairs : Nat) : List Command :=
  (List.replicate pairs (transaction true ++ transaction false)).flatten

def switch : List Command := RegionalPending.change .checked .split

/-- The switch costs 52 operations; one transaction saves only 12. -/
theorem short_switch_loses : totalWork (initial .checked) switch = 52 ∧
    totalWork (initial .checked) (transaction true) = 156 ∧
    totalWork (initial .checked) (switch ++ transaction true) = 196 := by decide

set_option maxRecDepth 32768 in
/-- Sixty-four complete transactions repay the actual conversion and release. -/
theorem long_switch_saves : totalWork (initial .checked) (workload 32) = 9984 ∧
    totalWork (initial .checked) (switch ++ workload 32) = 9268 := by decide

set_option maxRecDepth 32768 in
theorem long_observations :
    (execute (initial .checked) (workload 32)).2 = List.replicate 64 false ∧
    (execute (initial .checked) (switch ++ workload 32)).2 = List.replicate 64 false ∧
    (execute (initial .checked) (switch ++ workload 32)).1.active.protocol.active.logical = false := by
  decide

inductive NativeCall where
  | producer | delay | negate | join | whole
  deriving DecidableEq

/-- Count actual native calls, retaining the distinction between whole-consumer
execution and individual deliveries. Refused calls contribute no evaluator work. -/
def calls (s : Session) (cs : List Command) : List NativeCall :=
  ((outcomes s cs).flatMap Outcome.events).filterMap fun e => match e with
    | .producer => some .producer | .deliverD => some .delay
    | .deliverN => some .negate | .join => some .join
    | .consumers _ _ => some .whole | _ => none

/-- Lost confirmation and migration preserve the independent three-output fixture. -/
theorem lost_confirmation :
    (execute (initial .split) RegionalPending.repartitioned).2 = [false,true,false] ∧
    (execute (initial .split) RegionalPending.repartitioned).1.active.protocol.active.logical = false := by
  decide

/-- The costed trace is the same trace already related to the independent source. -/
example : SourceRun (source (initial .split).active)
    (outcomes (initial .split) RegionalPending.repartitioned)
    (source (execute (initial .split) RegionalPending.repartitioned).1.active) :=
  (workload_refines .split .delay _).2

example (plan : List PlanAction) :
    checkpoint (execute (initial .checked) (expandPlan plan)).1.active =
      checkpoint (execute (initial .checked) (erasePlan plan)).1.active ∧
    (outcomes (initial .checked) (expandPlan plan)).flatMap (fun o => o.business.toList) =
      (execute (initial .checked) (erasePlan plan)).2 ∧
    totalWork (initial .checked) (expandPlan plan) =
      ((outcomes (initial .checked) (expandPlan plan)).map work).sum :=
  migration_projection _ _ (initial_ready _ _)

def producedDelay : List Command := [.accept true,.producer,.deliverD]
def suffix : List Command := [.deliverN,.join] ++ RegionalPending.retire

def migrated : List Command := producedDelay ++ RegionalPending.change .checked .fused ++ suffix

def failed : List Command := producedDelay ++
  [.prepare .checked .fused .delay {} true true true,.commit] ++ suffix

/-- The completed delay consumer and cached producer each execute once. -/
example : calls (initial .checked) migrated = [.producer,.delay,.negate,.join] ∧
    calls (initial .checked) failed = [.producer,.delay,.negate,.join] := by decide

example : (execute (initial .checked) migrated).2 = [false] ∧
    (execute (initial .checked) failed).2 = [false] ∧
    checkpoint (execute (initial .checked) migrated).1.active =
      checkpoint (execute (initial .checked) (producedDelay ++ suffix)).1.active ∧
    checkpoint (execute (initial .checked) failed).1.active =
      checkpoint (execute (initial .checked) (producedDelay ++ suffix)).1.active := by
  refine ⟨by decide,by decide,?_,?_⟩ <;> rfl

/-- The failed candidate is released; the original pending owner stays active. -/
def afterDelay : Session := (execute (initial .checked) producedDelay).1
example : (prepare afterDelay .checked .fused .delay {} true true true).status = .validation ∧
    wire (prepare afterDelay .checked .fused .delay {} true true true).session.active = wire afterDelay.active ∧
    work (prepare afterDelay .checked .fused .delay {} true true true) = 50 := by decide

/-- Frozen service cannot discard the prepared executor's retained storage. -/
def prepared : Session := (execute (initial .checked)
  (producedDelay ++ [.prepare .checked .fused .delay {} true true false])).1
example : wrapperRetained prepared > wrapperRetained afterDelay ∧
    (producer prepared).status = .frozen ∧
    wrapperRetained (producer prepared).session = wrapperRetained prepared ∧
    work (producer prepared) = 2 := by decide

/-- Work accounting and native service bounds refer to the same reached session,
including schedules paused with a prepared target. -/
example (cs : List Command) :
    let s := (execute (initial .checked) cs).1
    totalWork (initial .checked) cs = ((outcomes (initial .checked) cs).map work).sum ∧
    ∃ trace, ServiceExecution s .producer (step s .producer) trace ∧
      ∀ live ∈ trace, live ≤ serviceCapacity s.active.cut :=
  ⟨totalWork_projection _ _,reachable_service_bound .checked .delay cs .producer trivial⟩

/-- Policy validation/filtering/ranking work precedes the actual migration bill. -/
example : proposedWork (initial .checked) {} "pending-costs" none candidates
    [.commit] = work (propose (initial .checked) {} "pending-costs" none candidates) +
      totalWork (propose (initial .checked) {} "pending-costs" none candidates).session [.commit] := rfl

end Examples.RegionalPendingCosts

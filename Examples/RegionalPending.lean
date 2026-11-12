import Applications.FRP.RegionalPendingIO
import Applications.FRP.RegionalPendingRefinement
import Applications.FRP.RegionalPendingProgress
import Applications.FRP.RegionalPendingResources
import Applications.FRP.RegionalPendingService

/-! Independent source fixtures for a shared dependency and pending cut changes. -/
namespace Examples.RegionalPending
open FRPSpec FRPSpec.Regional FRPSpec.Regional.Pending

/-- First effect is visible but its confirmation is lost; second input is owned. -/
def lostPrefix : List Command :=
  [.accept true,.producer,.whole,.external .publish,.external (.dispatch false),.accept true]

def reconcile : List Command :=
  [.external .queryPeer,.external (.dispatch true),.external (.dispatch true),
   .external .tickCommit,.external .close,.external .release]

def retire : List Command :=
  [.external .publish,.external (.dispatch true),.external (.dispatch true),
   .external .tickCommit,.external .close,.external .release]

def change (old target : Cut) (kind : FRPSpec.Migration.Kind := .delay) : List Command :=
  [.prepare old target kind {} true true false,.commit]

def matched : List Command :=
  lostPrefix ++ reconcile ++ [.producer,.deliverD,.deliverN,.join] ++ retire ++
  [.accept false,.producer,.whole] ++ retire

def moved : List Command :=
  lostPrefix ++ change .split .split .redundant ++ reconcile ++
  [.producer,.deliverD,.deliverN,.join] ++ retire ++ [.accept false,.producer,.whole] ++ retire

def repartitioned : List Command :=
  lostPrefix ++ change .split .checked .redundant ++ reconcile ++ [.producer,.deliverD] ++
  change .checked .fused ++ [.deliverN,.join] ++ retire ++ [.accept false,.producer,.whole] ++ retire

example : (execute (initial .split) matched).2 = [false,true,false] := by decide
example : (execute (initial .split) moved).2 = [false,true,false] := by decide
example : (execute (initial .split) repartitioned).2 = [false,true,false] := by decide
set_option maxRecDepth 4096 in
example : (execute (initial .split) repartitioned).1.active.protocol.active.logical = false := by decide

/-- The actual peer records the joined payload, which differs from old delay
state for the final false input. This cannot pass by relabeling an output log. -/
def thirdPublished : FRPSpec.Regional.Pending.Session :=
  (execute (initial .split)
    (lostPrefix ++ reconcile ++ [.producer,.deliverD,.deliverN,.join] ++ retire ++
      [.accept false,.producer,.whole,.external .publish,.external (.dispatch false)])).1

set_option maxRecDepth 4096 in
example : thirdPublished.active.protocol.peer.left = some (.published false false) ∧
    thirdPublished.active.protocol.active.logical = true := by decide

example (input state : Bool) : wholeResult .fused input state = oracle input state :=
  whole_correct _ _ _
example (input state : Bool) : wholeResult .checked input state = oracle input state :=
  whole_correct _ _ _

def partialD : Session := (execute (initial .split) [.accept true,.producer,.deliverD]).1

/-- Swapping D/N state is locally representable but violates the joint continuation. -/
example : (prepare partialD .split .fused .delay {} true true true).status = .validation := by decide

example : (prepare partialD .split .fused .delay {protocol := 1} true true false).status = .unsupported := by decide

/-- The independent source theorem applies to the concrete lost-ack/shared-cut
fixture; runtime equality alone is not the proof of refinement. -/
example : SourceRun (source (initial .split).active)
    (outcomes (initial .split) repartitioned)
    (source (execute (initial .split) repartitioned).1.active) :=
  (reachable_refinement .split .delay repartitioned).2.2

example (cs : List Command) :
    (source (initial .checked .redundant).active).waiting.length +
      acceptedCount (outcomes (initial .checked .redundant) cs) =
    (source (execute (initial .checked .redundant) cs).1.active).waiting.length +
      publishedCount (outcomes (initial .checked .redundant) cs) +
      preventedCount (outcomes (initial .checked .redundant) cs) :=
  execute_no_loss _ cs (initial_invariant .checked .redundant) (initial_innerReady .checked .redundant)

example (s : Session) (hs : Invariant s.active) (ready : Ready s) (slot : Bool) :
    let afterInternal := (execute s [.deliverD,.deliverN]).1
    let final := (execute afterInternal (List.replicate 8 (.external (.dispatch true)))).1
    final.active.deliveries.references slot = false ∧
      final.active.protocol.queue.references slot = false :=
  ten_opportunities_retire_references s hs ready slot

/-- Every reachable command has an execution-linked complete service bound. -/
example (cs : List Command) (c : Command) (hc : Business c) :
    let s := (execute (initial .split .delay) cs).1
    ∃ trace, ServiceExecution s c (step s c) trace ∧
      ∀ live ∈ trace, live ≤ serviceCapacity s.active.cut :=
  reachable_service_bound .split .delay cs c hc

example : serviceCapacity .split = 441 ∧ serviceCapacity .checked = 445 := by decide

/-- A paused prepared target remains live even when business work is refused. -/
example : wrapperRetained (prepare partialD .split .fused .delay {}).session >
    wrapperRetained partialD := by decide

/-- Whole split execution retains all three native consumer arenas. -/
example : (serviceAllocations partialD.active (.whole true false)).sum >
    max Indefinite.delay.body.arena (max Applications.Circuits.Circuit.not.arena
      Applications.Circuits.Circuit.xor.arena) := by decide

/-- Old/new encoded stores coexist with both decoded store generations. -/
example : (serviceTrace partialD.active []).getLast? = some
    (PendingMigration.stateSlots partialD.active.protocol + 16 + 4 +
      2 * retainedCells partialD.active.cut + 44 + 8) := by decide

/-- The inherited command accounts for the actual queued payloads, even when
confirmation is lost; an empty queue has a strictly smaller dispatch scratch. -/
example : (serviceAllocations (execute (initial .split)
      [.accept true,.producer,.whole,.external .publish,.external .queryPeer,
        .external .queryPeer,.external .queryPeer]).1.active
      (.protocol (.dispatch true))).sum >
    (serviceAllocations (initial .split).active (.protocol (.dispatch true))).sum := by decide

end Examples.RegionalPending

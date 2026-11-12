import Applications.FRP.RegionalPendingIO
import Applications.FRP.RegionalPendingRefinement
import Applications.FRP.RegionalPendingProgress
import Applications.FRP.RegionalPendingResources

/-! Independent source fixtures for a shared dependency and pending cut changes. -/
namespace Examples.RegionalPending
open FRPSpec.Regional FRPSpec.Regional.Pending

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

end Examples.RegionalPending

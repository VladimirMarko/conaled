import Applications.FRP.PendingMigrationResources
import Applications.FRP.PendingMigrationProgress
import Applications.FRP.PendingMigrationSource

/-! Checked cuts of the public bounded peer protocol. -/
set_option autoImplicit false
namespace FRPSpec.PendingMigration.Examples
open Migration

/-- The first peer effect occurs before migration, but its acknowledgement is
lost. The second input is already accepted when ownership changes. -/
def lostAcknowledgement : List Command :=
  [.accept true,.evaluate,.publish,.dispatch false,.accept false,
   .prepare .redundant,.ownershipCommit,.queryPeer,.dispatch true,.dispatch true,
   .tickCommit,.close,.release,.evaluate,.publish,.dispatch true,.dispatch true,
   .tickCommit,.close,.release]

example : (execute (initial .delay) lostAcknowledgement).2 = [false,true] := by decide
example : (execute (initial .delay) lostAcknowledgement).1.active.logical = false := by decide
example : (execute (initial .delay) lostAcknowledgement).1.order = [] := by decide

/-- Publication alone is insufficient knowledge for local commit. -/
def ambiguous : Session :=
  (execute (initial .delay) [.accept true,.evaluate,.publish,.dispatch false]).1

example : ambiguous.active.logical = false := by decide
example : (step ambiguous .tickCommit).status = .busy := by decide
example : (step ambiguous (.cancelWork false)).status = .tooLate := by decide
example : (step ambiguous (.cancelWork false)).session.active.logical = false := by decide

/-- Cancellation before the peer effect defeats already queued work. -/
example : (execute (initial .delay)
    [.accept true,.evaluate,.publish,.cancelWork false,.dispatch true,.dispatch true]).2 = [] := by decide

example : (step ambiguous (.prepare .redundant 0)).transfer = [.budget] := by decide
example : (step ambiguous (.prepare .redundant 256 false true)).transfer =
    [.budget,.attempt 4] := by decide
example : (step ambiguous (.prepare .redundant 256 true false)).session = ambiguous := by rfl

/-- A retry remains quarantined after close until dispatch consumes it. -/
def quarantined : Session :=
  (execute (initial .delay)
    [.accept true,.evaluate,.publish,.dispatch true,.dispatch true,.tickCommit,
     .retry false,.close]).1
example : (step quarantined .release).status = .refused := by decide
example : (execute quarantined [.dispatch true,.release]).1.order = [] := by decide

/-- Every checkpoint, finite suffix, and number/direction of transfers uses the
same theorem; no initial-state or fixed-fixture assumption occurs here. -/
example (s : Session) (plan : List PlanAction) (hp : s.prepared = none) :
    checkpoint (runPlan s plan).1 = checkpoint (execute s (erasePlan plan)).1 ∧
    (runPlan s plan).2 = (execute s (erasePlan plan)).2 := repeated_migration s plan hp

example (s : Session) (plan : List PlanAction) (hp : s.prepared = none) :
    planObservations s plan = observationTrace s (erasePlan plan) :=
  repeated_observations s plan hp

def continuationPlan : List PlanAction :=
  [.migration .redundant,.migration .delay,
   .business .queryPeer (by trivial),.business (.dispatch true) (by trivial),
   .business (.dispatch true) (by trivial),.business .tickCommit (by trivial),
   .business .close (by trivial),.business .release (by trivial),
   .business .evaluate (by trivial),.business .publish (by trivial),
   .business (.dispatch true) (by trivial),.business (.dispatch true) (by trivial),
   .business .tickCommit (by trivial),.business .close (by trivial),
   .business .release (by trivial)]

def twoPending : Session := (step ambiguous (.accept false)).session

/-- The false output already happened before this suffix; transfers and
reconciliation emit only the second output true. This uses the general law. -/
example : (runPlan twoPending continuationPlan).2 = [true] := by
  rw [(repeated_migration twoPending continuationPlan rfl).2]
  decide

example : (runPlan twoPending continuationPlan).1.active.logical = false := by
  have h := congrArg Checkpoint.logical (repeated_migration twoPending continuationPlan rfl).1
  exact h.trans (by decide)

example : planObservations ambiguous
    [.migration .redundant,.business (.cancelWork false) (by trivial)] =
      [(none,none,some false)] := by
  rw [repeated_observations ambiguous _ rfl]
  decide

/-- Concrete budget and phase premises exercise the executed allocation trace
at the published-but-unconfirmed cut. -/
example :
    let o := step ambiguous (.prepare .redundant 256 true true)
    liveAfter (stateSlots ambiguous) o.transfer = stateSlots o.session :=
  preparation_retained ambiguous .redundant 256 rfl (by decide)

example :
    let trace := (step ambiguous (.prepare .redundant 256 true false)).transfer
    ReleasesSafe (stateSlots ambiguous) trace ∧
      liveAfter (stateSlots ambiguous) trace = stateSlots ambiguous ∧
      transferPeak (stateSlots ambiguous) trace = preparationSlots ambiguous .redundant :=
  failed_preparation_lifetime ambiguous .redundant 256 rfl (by decide)

example (s : Session) (h : Bounded s) (c : Command) : commandPeak s c ≤ 192 :=
  command_peak_bound s c h

example (s : Session) (hp : s.prepared = none) (slot : Bool) :
    (execute s (List.replicate 8 (.dispatch true))).1.queue.references slot = false :=
  public_drain_excludes s hp slot

example : tokenOnly ⟨(0+2)%2,by decide⟩ ⟨0,by decide⟩ false ≠ some true :=
  token_only_rejecting_control.2

/-- Independent source refinement connects the actual fixture to the delay
source, rather than comparing two executions of the same protocol. -/
example : SourceRun ⟨false,[]⟩ (executionTrace (initial .delay) lostAcknowledgement)
    ⟨false,[]⟩ := initial_execution_refines .delay lostAcknowledgement

example : Valid ambiguous :=
  execute_valid (initial .delay) _ (initial_valid .delay)

/-- This projection is proof-only: source publication advanced, although the
session's executable local state remains false until a delivered reply. -/
example : source ambiguous = ⟨true,[]⟩ := by decide

example : SourceRun ⟨false,[]⟩
    (executionTrace (initial .delay)
      [.accept true,.accept false,.cancelWork true,.evaluate,.publish,.dispatch true,
       .dispatch true,.tickCommit,.close,.release,.close,.release]) ⟨true,[]⟩ :=
  initial_execution_refines .delay _

example (cs : List Command) :
    (waiting (execute (initial .redundant) cs).1).length +
      (execute (initial .redundant) cs).2.length +
      sourceCancellations (executionTrace (initial .redundant) cs) =
    (sourceAcceptances (executionTrace (initial .redundant) cs)).length :=
  initial_no_loss .redundant cs

example (cs : List Command) : (execute (initial .delay) cs).1.order.Nodup :=
  (reachable_owners .delay cs).1

end FRPSpec.PendingMigration.Examples

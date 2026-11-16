import Applications.FRP.PendingRetention.Refinement
import Applications.FRP.PendingRetention.Runtime
import Applications.FRP.PendingRetention.Effects
import Applications.FRP.PendingRetention.Costs
import Applications.FRP.PendingRetention.ObservationsReachable
import Applications.FRP.PendingRetention.Realization
import Applications.FRP.PendingRetention.Workspace
import Applications.FRP.PendingRetention.Deletion
import Applications.FRP.PendingRetention.ValidatorWorkspace

/-! Source observations that distinguish retained state from arbitrary valid frames. -/
namespace Examples.PendingRetention
open FRPSpec.PendingCrash (Frame Peer sourceView initialFrame DelaySource)
open FRPSpec.PendingRetention

def retainedFrame : Frame :=
  {kind := .delay, logical := true,
   requests := {left := some {identity := 1, input := false}},
   order := [false], nextIdentity := 2}

def lifetimePeer : Peer := [(0, .published true false), (1, .reserved false)]

/-- The completed first request changed the delay state; the second is still live. -/
theorem retained_source_observation :
    sourceView retainedFrame (lifetimePeer.filter (fun entry => 1 ≤ entry.1)) =
      {state := true, waiting := [(1,false)]} := by
  rw [sourceView_filter_ge retainedFrame lifetimePeer 1 (by
    intro slot request present
    cases slot <;> simp [retainedFrame, FRPSpec.PendingMigration.Slots.get] at present
    subst request
    decide)]
  rfl

/-- Local frame validity cannot replace a reachable source relation. -/
theorem valid_frame_can_have_wrong_initial_state :
    ({initialFrame with logical := true} : Frame).Valid ∧
    sourceView {initialFrame with logical := true} [] ≠ ({} : DelaySource) := by
  constructor
  · decide
  · decide


set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-- Small capacities leave room for two live occurrences and one retained result. -/
def exampleConfig : Config := ⟨4,3,4⟩
def settle : List Command := List.replicate 16 .progress

/-- Neither endpoint has a receipt when it restarts. The durable peer result
lets a later query recover the outcome without publishing a second effect. -/
def lostReply : List Command :=
  [.local (.accept true)] ++ settle ++ [.local .evaluate] ++ settle ++
  [.send 0 .reserve, .transferRequest, .deliverRequest] ++ settle ++
  [.drop .peerOut, .send 0 .publish, .transferRequest, .deliverRequest] ++ settle ++
  [.drop .peerOut, .crashLocal, .recoverLocal, .crashPeer, .recoverPeer,
   .send 0 .query, .transferRequest, .deliverRequest, .transferReply, .deliverReply] ++ settle ++
  [.local .tickCommit] ++ settle ++ [.local .close] ++ settle ++
  [.local .release] ++ settle

def afterLostReply := (execute exampleConfig initial lostReply).system

theorem lost_reply_observations :
    (execute exampleConfig initial lostReply).labels.filter (· != .internal) =
      [.accept 0 true, .output 0 false] ∧
    query afterLostReply.localBank.selected 0 = .terminal (.published true false) ∧
    afterLostReply.localBank.selected.frame.logical = true := by decide

/-- Closing and releasing the occurrence leaves its outcome queryable. -/
theorem release_keeps_query_rights :
    afterLostReply.localBank.selected.floor = 0 ∧
    query afterLostReply.localBank.selected 0 = .terminal (.published true false) := by decide

def retire : List Command :=
  [.relinquishBefore 1] ++ settle ++ [.retryRetirement,.transferRequest,.deliverRequest] ++
  settle ++ [.resumeDeletion] ++ settle ++ [.transferReply,.deliverReply] ++ settle

def afterRetirement := (execute exampleConfig afterLostReply retire).system

theorem retirement_observations :
    afterRetirement.localBank.selected.pending = none ∧
    afterRetirement.localBank.selected.outcomes = [] ∧
    afterRetirement.peer.selected.entries = [] ∧
    query afterRetirement.localBank.selected 0 = .expired 1 ∧
    .retirementComplete 1 ∈ (execute exampleConfig afterLostReply retire).observations := by decide

/-- Expiry is already durable while the peer still retains its old entry.
The controller cannot reserve another identity until deletion is acknowledged. -/
def awaitingDeletion := (execute exampleConfig afterLostReply
  ([.relinquishBefore 1] ++ settle)).system

theorem local_expiry_precedes_deletion :
    awaitingDeletion.localBank.selected.floor = 1 ∧
    awaitingDeletion.peer.selected.floor = 0 ∧
    awaitingDeletion.peer.selected.entries ≠ [] ∧
    (step exampleConfig awaitingDeletion (.local (.accept false))).observation = .refused .busy ∧
    query awaitingDeletion.localBank.selected 0 = .expired 1 := by decide

/-- Admission reserves capacity before processing. Neither a full pool nor an
exhausted lifetime is repaired by wrapping an identity. -/
theorem admission_rejections :
    (step ⟨0,3,4⟩ initial (.local (.accept true))).observation = .refused .exhausted ∧
    (step ⟨4,0,4⟩ initial (.local (.accept true))).observation = .refused .full := by decide

/-- Relinquishment cannot discard a live unresolved occurrence. -/
theorem unresolved_prefix_rejected :
    let accepted := (execute exampleConfig initial ([.local (.accept true)] ++ settle)).system
    let result := execute exampleConfig accepted ([.relinquishBefore 1] ++ settle)
    result.system.localBank.selected.floor = 0 ∧ .refused .unresolved ∈ result.observations := by decide


/-- Acknowledgement loss and a local restart reuse the same retirement target. -/
def lostRetirementReply : List Command :=
  [.relinquishBefore 1] ++ settle ++ [.retryRetirement,.transferRequest,.deliverRequest] ++
  settle ++ [.resumeDeletion] ++ settle ++ [.drop .peerOut,.crashLocal,.recoverLocal,
    .crashPeer,.recoverPeer,.retryRetirement,.transferRequest,.deliverRequest,
    .transferReply,.deliverReply] ++ settle

theorem lost_retirement_reply_recovers :
    let result := execute exampleConfig afterLostReply lostRetirementReply
    result.system.localBank.selected.pending = none ∧
    result.system.localBank.selected.floor = 1 ∧
    result.system.peer.selected.entries = [] ∧
    result.labels.all (· == .internal) = true := by decide

/-- Receipt deletion without a rejection floor permits the same effect again.
This separating case explains why local compaction alone is insufficient. -/
theorem deletion_without_floor_reexecutes :
    let requests : List (Nat × FRPSpec.PendingCrash.PeerCommand) :=
      [(0,.reserve true),(0,.publish true false)]
    let first := FRPSpec.PendingCrash.peerExecute [] requests
    let second := FRPSpec.PendingCrash.peerExecute
      (first.peer.filter (fun entry => 1 ≤ entry.1)) requests
    first.effects ++ second.effects = [(0,false),(0,false)] := by decide

/-- The retained-history theorem covers arbitrary later commands, including
reserve followed by publication, even after the actual entry has been deleted. -/
theorem retired_publication_cannot_reexecute (command : FRPSpec.PendingCrash.PeerCommand)
    (target : PeerSnapshot) (reply : ReplyPacket) (effect prevented : Option Bool)
    (changed : peerDecision exampleConfig
      {floor := 1, entries := ([(0,.published true false)] : Peer).filter (fun e => 1 ≤ e.1)}
      0 command = .ok (target,reply,effect,prevented)) : effect = none := by
  apply peerDecision_no_reexecution true false
    (PeerExtension.refl 1 [(0,.published true false)]).filter (by decide) changed

/-- Failure before migration publication preserves the current owner and frame. -/
theorem failed_migration_keeps_current :
    let result := step exampleConfig afterLostReply (.local (.migrate .redundant true false))
    result.observation = .refused .invalid ∧
    result.system.localBank.selected = afterLostReply.localBank.selected ∧
    result.system.active = afterLostReply.active := by exact ⟨rfl,rfl,rfl⟩


/-- A genuine old request survives in transport until after peer deletion.
Its replay is rejected by the durable floor, without a new business effect. -/
def delayedRequestRetirement : List Command :=
  [.send 0 .reserve,.transferRequest,.relinquishBefore 1] ++ settle ++
  [.retryRetirement,.transferRequest,.duplicate .peerIn 0,.drop .peerIn,.deliverRequest] ++ settle ++
  [.resumeDeletion] ++ settle ++ [.deliverRequest,.transferReply,.deliverReply] ++ settle ++
  [.transferReply,.deliverReply]

theorem delayed_request_is_expired :
    let result := execute exampleConfig afterLostReply delayedRequestRetirement
    result.labels.all (· == .internal) = true ∧
    result.system.peer.selected.entries = [] ∧
    result.system.localBank.selected.pending = none ∧
    .expired 1 none ∈ result.observations := by decide

/-- An old deletion acknowledgement cannot finish a newer retirement. -/
theorem stale_acknowledgement_rejected :
    finishRetirement {floor := 2,pending := some 2} 1 = none := by decide



/-- A completed higher identity cannot authorize expiry across a lower live
request, even when cancellation survives independent endpoint restarts. -/
def cancelledHigher : List Command :=
  [.local (.accept true)] ++ settle ++ [.local .evaluate] ++ settle ++
  [.local (.accept false)] ++ settle ++
  [.send 1 .reserve,.transferRequest,.deliverRequest] ++ settle ++
  [.drop .peerOut,.send 1 .cancel,.transferRequest,.deliverRequest] ++ settle ++
  [.transferReply,.deliverReply] ++ settle ++
  [.crashLocal,.recoverLocal,.crashPeer,.recoverPeer,.relinquishBefore 2] ++ settle

theorem cancelled_higher_preserves_live_prefix :
    let result := execute exampleConfig initial cancelledHigher
    result.system.localBank.selected.floor = 0 ∧
    query result.system.localBank.selected 1 = .terminal (.prevented false) ∧
    (result.system.localBank.selected.frame.requests.get false).map (·.output) = some (some false) ∧
    .refused .unresolved ∈ result.observations := by decide

/-- The lost-reply and retirement trace remains a source execution for every
later command sequence, including further crashes and delayed transport. -/
theorem retirement_source_for_every_suffix (suffix : List Command) :
    SourceRun (sourceView initialFrame [])
      (execute exampleConfig initial (lostReply ++ lostRetirementReply ++ suffix)).labels
      (sourceView
        (execute exampleConfig initial (lostReply ++ lostRetirementReply ++ suffix)).system.localBank.selected.frame
        (FRPSpec.PendingCrash.peerExecute []
          (peerActions exampleConfig initial (lostReply ++ lostRetirementReply ++ suffix))).peer) :=
  initial_execution_source _ _

/-- Once the worked request has executed, no continuation can execute that
identity again, even after the retained peer entry has been deleted. -/
theorem retirement_effects_unique_for_every_suffix (suffix : List Command) :
    ((emittedEffects (execute exampleConfig initial
      (lostReply ++ lostRetirementReply ++ suffix)).labels).map Prod.fst).Nodup :=
  initial_effects_unique _ _

/-- Every cut in the same trace, including failed operations in its arbitrary
suffix, admits the complete finite-state encoding with an exact inverse. -/
theorem retirement_encoding_at_every_cut (suffix : List Command) (cut : Nat) :
    let commands := (lostReply ++ lostRetirementReply ++ suffix).take cut
    (Encoding.system exampleConfig).decode
      (encodeBounded exampleConfig (execute exampleConfig initial commands).system
        (execution_resourceBound exampleConfig commands)) =
      (execute exampleConfig initial commands).system :=
  execution_encoding_roundtrip _ _

/-- The concrete released request exercises the general retained-result theorem,
including the receipt's connection to the lifetime peer history. -/
theorem released_query_is_authenticated :
    ∃ answer, query afterLostReply.localBank.selected 0 = .terminal answer ∧
      terminalAnswer answer = true ∧
      FRPSpec.PendingCrash.ReceiptAuthentic
        (FRPSpec.PendingCrash.peerExecute [] (peerActions exampleConfig initial lostReply)).peer
        ⟨0,answer⟩ := by
  apply initial_execution_query_completed exampleConfig lostReply 0 (by decide) (by decide)
  have empty : afterLostReply.localBank.selected.frame.requests = {left := none, right := none} := by decide
  intro slot request present
  change request ∈ afterLostReply.localBank.selected.frame.requests.get slot at present
  rw [empty] at present
  cases slot <;> simp [FRPSpec.PendingMigration.Slots.get] at present

/-- The next progress step publishes the exact retirement acknowledgement.
The general barrier theorem certifies deletion when pending becomes clear. -/
def completionPrefix : List Command :=
  lostReply ++ retire.take (retire.length - 14)

theorem completed_retirement_certifies_deletion :
    (step exampleConfig (execute exampleConfig initial completionPrefix).system .progress).observation =
      .retirementComplete 1 ∧
    DeletedPrefix
      (step exampleConfig (execute exampleConfig initial completionPrefix).system .progress).system.peer.selected 1 :=
  initial_pending_cleared exampleConfig completionPrefix .progress 1 (by decide) (by decide)

/-- Failed reconciliation still pays for the outcome search it performed. -/
theorem unknown_send_charges_lookup :
    let result := step exampleConfig afterLostReply (.send 1 .query)
    result.observation = .refused .invalid ∧
    result.system = afterLostReply ∧
    outcomeProbes 1 afterLostReply.localBank.selected.outcomes = 1 ∧
    executionWork exampleConfig afterLostReply [.send 1 .query] .scans =
      bill (dimensionPrice .scans) (controllerWork afterLostReply) +
        outcomeProbes 1 afterLostReply.localBank.selected.outcomes := by
  refine ⟨by decide, rfl, ?_⟩
  decide

/-- Finding a retained record does not authorize publication after release;
its lookup is charged even though the operation is refused. -/
theorem released_publication_charges_lookup :
    let result := step exampleConfig afterLostReply (.send 0 .publish)
    result.observation = .refused .invalid ∧
    result.system = afterLostReply ∧
    outcomeProbes 0 afterLostReply.localBank.selected.outcomes = 1 ∧
    executionWork exampleConfig afterLostReply [.send 0 .publish] .scans =
      bill (dimensionPrice .scans) (controllerWork afterLostReply) +
        outcomeProbes 0 afterLostReply.localBank.selected.outcomes := by
  refine ⟨by decide, rfl, ?_⟩
  decide

/-- Relinquishment reports expiry on reconciliation without searching the pool,
enqueuing a packet, or emitting a business effect. -/
theorem expired_send_skips_lookup :
    let result := step exampleConfig afterRetirement (.send 0 .query)
    result.observation = .expired 1 none ∧
    result.system = afterRetirement ∧
    result.label = .internal ∧
    result.events = controllerWork afterRetirement ++ [.check] ∧
    executionWork exampleConfig afterRetirement [.send 0 .query] .scans =
      bill (dimensionPrice .scans) (controllerWork afterRetirement) := by
  refine ⟨by decide, rfl, ?_⟩
  decide

/-- A real unfinished acceptance owns the controller before a send can search. -/
def duringNextAcceptance :=
  (execute exampleConfig afterLostReply [.local (.accept false)]).system

theorem busy_send_skips_lookup :
    let result := step exampleConfig duringNextAcceptance (.send 0 .query)
    result.observation = .refused .busy ∧
    result.system = duringNextAcceptance ∧
    outcomeProbes 0 duringNextAcceptance.localBank.selected.outcomes = 1 ∧
    result.events = controllerWork duringNextAcceptance ++ [.check] ∧
    executionWork exampleConfig duringNextAcceptance [.send 0 .query] .scans =
      bill (dimensionPrice .scans) (controllerWork duringNextAcceptance) := by
  refine ⟨by decide, rfl, ?_⟩
  decide

/-- A failed search remains charged through every continuation. -/
theorem unknown_send_work_append (suffix : List Command) :
    executionWork exampleConfig afterLostReply ([.send 1 .query] ++ suffix) .scans =
      executionWork exampleConfig afterLostReply [.send 1 .query] .scans +
      executionWork exampleConfig
        (execute exampleConfig afterLostReply [.send 1 .query]).system suffix .scans :=
  executionWork_append _ _ _ _ _

theorem unknown_send_probe_survives_suffix (suffix : List Command) :
    outcomeProbes 1 afterLostReply.localBank.selected.outcomes ≤
      executionWork exampleConfig afterLostReply ([.send 1 .query] ++ suffix) .scans := by
  rw [unknown_send_work_append]
  have charged := unknown_send_charges_lookup.2.2.2
  omega

theorem unknown_send_work_survives_restart :
    executionBill cellWork exampleConfig afterLostReply [.send 1 .query] ≤
      executionBill cellWork exampleConfig afterLostReply
        [.send 1 .query,.crashLocal,.recoverLocal,.crashPeer,.recoverPeer] :=
  failed_work_survives_suffix _ _ _ _

end Examples.PendingRetention

import Applications.Interaction.CapturedAttempt
import Applications.Interaction.RetainedMeasurement

/-! # Captured-attempt statement cases
The mixed pair is read from two different stable windows; a zero process result
cannot repair execution against the wrong live pair.
-/
namespace CapturedAttemptExamples
open Interaction Interaction.CapturedAttempt Interaction.Measurement

def readsA (h : Bool × Bool) (a : Bool) : Prop := a = h.1
def readsB (h : Bool × Bool) (b : Bool) : Prop := b = h.2

theorem mixedChain : CaptureChain readsA readsB (false, false) (true, true)
    (false, true) (false, true) (false, true) := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem mixed_execution : CapturedExecution readsA readsB (false, false) (true, true)
    (false, true) (false, true) := capture_chain mixedChain

theorem mixed_not_revision : (false, true) ∉ Snapshot.history := Snapshot.never_coexisted

theorem wrong_live_input : ¬ CapturedExecution readsA readsB (false, false) (true, true)
    (false, true) (true, true) := by
  intro h
  have bad := congrArg Prod.fst h.2.2
  cases bad

theorem mixed_snapshot : Snapshot.CompileCaptured
    ⟨(true, true), (false, true), none⟩
    ⟨(true, true), (false, true), some (false, true)⟩ := captured_step mixedChain

theorem partial_capture_cannot_launch : sealedValue (CaptureState.readB false true) = none := rfl

theorem capture_order_rejected : captureAdvance (CaptureState.empty : CaptureState Bool Bool)
    .sealB = none := rfl

theorem sealed_input_cannot_change : captureAdvance (CaptureState.sealed false true)
    (.readA true) = none := sealed_rejects false true _

def absent : World := ⟨none, false, false, false⟩
def published : World := ⟨none, false, false, true⟩

theorem unknown_both_worlds : Evidence absent unknown ∧ Evidence published unknown :=
  ⟨.initial _, .initial _⟩

theorem unknown_does_not_decide_publication : absent.published ≠ published.published := by decide

theorem impossible_zero : ¬ Evidence absent (observe unknown (.raw 0)) := by
  intro h
  have bad := (evidence_corresponds h).1 0 rfl
  cases bad

def issued : Observer := ⟨⟨true, none⟩, unknown⟩

theorem lost_ack_no_retry : advance
    ⟨record issued.controller (observe unknown (.publication .unknown)),
      observe unknown (.publication .unknown)⟩ .authorize = none :=
  no_reexecution (Relation.ReflTransGen.single (.response issued rfl (.publication .unknown))) rfl

theorem pending_safe : Interaction.Run ControlStep (fun _ => issued) := pending_run issued

theorem zero_is_not_enough : successful (record issued.controller (observe unknown (.raw 0))) = false := rfl

theorem signal_not_zero : (observe unknown (.raw 143)).completion = .unknown := rfl

def good : Observation := ⟨.exited 0, true, .confirmed, .confirmed⟩
def finished : World := ⟨some 0, true, true, true⟩

theorem good_evidence : Evidence finished good := by
  have e0 : Evidence (⟨none, false, false, false⟩ : World) unknown := .initial _
  have e1 : Evidence (⟨some 0, false, false, false⟩ : World) (observe unknown (.raw 0)) :=
    .response e0 (by simp [Extends]) (.raw 0) (by simp [Supports])
  have e2 : Evidence (⟨some 0, true, false, false⟩ : World)
      (observe (observe unknown (.raw 0)) (.channels true)) :=
    .response e1 (by simp [Extends]) (.channels true) (by simp [Supports])
  have e3 : Evidence (⟨some 0, true, true, false⟩ : World)
      (observe (observe (observe unknown (.raw 0)) (.channels true)) (.cleanup .confirmed)) :=
    .response e2 (by simp [Extends]) (.cleanup .confirmed) (by simp [Supports])
  exact .response e3 (by simp [Extends, finished]) (.publication .confirmed)
    (by simp [Supports, finished])

theorem both_consumers : CapturedExecution readsA readsB (false, false) (true, true)
    (false, true) (false, true) ∧ Completed finished :=
  accepted_capture mixedChain good_evidence (record issued.controller good) rfl rfl

theorem duplicate_authorization_rejected : runEvents {} [.authorize, .authorize] = none := rfl

theorem one_issuance (s t : Observer) (es : List Interaction.CapturedAttempt.Event)
    (h : runEvents s es = some t) : launches es ≤ 1 := launches_bound h

theorem infinite_pending_preserves_issue : ∀ n : Nat, ((fun _ : Nat => issued) n).controller.started = true :=
  run_started (pending_run issued) rfl

def lostAcknowledgment : Observation := ⟨.exited 0, true, .confirmed, .unknown⟩

theorem lost_ack_effect_ambiguous :
    Corresponds ⟨some 0, true, true, false⟩ lostAcknowledgment ∧
    Corresponds ⟨some 0, true, true, true⟩ lostAcknowledgment := by
  simp [Corresponds, lostAcknowledgment]

theorem response_before_issue_rejected : runEvents {} [.response (.raw 0)] = none := rfl

/-- Reuse the existing rollback interpretation for this adapter's selected response. -/
theorem rollback_keeps_lost_ack :
    RetainedException.scopedFold Interaction.Measurement.Retained.attempt .undo
      (Interaction.Measurement.Retained.protectedAttempt lostAcknowledgment) false
      (Interaction.Measurement.Retained.fresh []) =
      ((.ok (Interaction.Measurement.Retained.selected lostAcknowledgment), false),
        ⟨Interaction.Measurement.Retained.selected lostAcknowledgment,
          [.issued, .observed lostAcknowledgment]⟩) :=
  Interaction.Measurement.Retained.exact_new_evidence _ _ _ _


namespace JointCases
open Interaction.CapturedAttempt.Joint

abbrev Phase := Interaction.CapturedAttempt.Joint.Phase Bool Bool (Bool × Bool) String
abbrev Event := Interaction.CapturedAttempt.Joint.Event Bool Bool (Bool × Bool) String
abbrev State := Interaction.CapturedAttempt.Joint.State Bool Bool (Bool × Bool) String

def capture : Capture Bool Bool (Bool × Bool) :=
  ⟨(false,false), (true,true), (false,true), (false,true)⟩
def execution : Execution Bool Bool (Bool × Bool) := ⟨capture, 7, 7, (false,true)⟩
def encode (phase : Phase) : String := reprStr phase

def ready : Phase := .channels execution (.exited 0) (some 0) .confirmed true true true
def payload : String := encode ready

def events (status : Status) (effect : Option String) : List Event :=
  [.readA (false,false) false, .sealA false, .interfere (true,false),
   .interfere (true,true), .readB (true,true) true, .sealB true,
   .authorize 7, .spawn 7 (false,true), .pending,
   .wait (.exited 0) (some 0), .cleanup .confirmed (some 0) true,
   .channels true true, .request payload, .publish status effect, .select]

def finalState (status : Status) (effect : Option String) : State :=
  ⟨(true,true), .selected ready payload status effect⟩

/-- Concrete independent read windows and all primitive premises inhabit the joint
prefix, including two live changes between the reads. -/
theorem admitted (status : Status) (effect : Option String)
    (ack : status = .confirmed → effect = some payload) :
    Admissible readsA readsB encode ⟨(false,false), .empty⟩
      (events status effect) (finalState status effect) := by
  unfold events finalState
  repeat' first
    | apply Admissible.cons rfl (by simp_all [Primitive, readsA, readsB, exitSupported,
        payload, ready, execution, capture])
    | exact Admissible.nil _

/-- The positive/interference case consumes the joint theorem, not two unrelated
capture and process witnesses. -/
theorem mixed_joint_success :
    ∃ source, AllowedPrefix readsA readsB encode ⟨⟨(false,false), .empty⟩⟩
      (events .confirmed (some payload)) source ∧
      Related source (finalState .confirmed (some payload)) ∧
      JointSuccess readsA readsB encode source.state.phase :=
  joint_success (admitted .confirmed (some payload) (fun _ => rfl)) rfl

theorem mixed_joint_measurement :
    Corresponds (world (finalState .confirmed (some payload)).phase)
      (observation (finalState .confirmed (some payload)).phase) ∧
    Completed (world (finalState .confirmed (some payload)).phase) := by
  obtain ⟨source, _, related, success⟩ := mixed_joint_success
  have h := joint_measurement success
  simpa [Related] using related ▸ h

theorem mixed_joint_capture :
    CapturedExecution readsA readsB (false,false) (true,true) (false,true) (false,true) ∧
    (false,true) ∉ Snapshot.history := by
  obtain ⟨source, allowed, related, _⟩ := mixed_joint_success
  have valid := prefix_valid allowed trivial
  have finalValid : Valid readsA readsB encode (finalState .confirmed (some payload)).phase :=
    related ▸ valid
  have ev : executionValid readsA readsB execution := finalValid.1.1
  exact ⟨capture_chain ⟨ev.1.1, ev.1.2.1, ev.1.2.2.1, ev.1.2.2.2,
    ev.2.2.1, ev.2.2.2⟩, mixed_not_revision⟩

/-- The exact publication payload is not replaced by a success flag. -/
theorem wrong_publication_payload :
    ¬ Primitive readsA readsB encode (.requested ready payload)
      (.publish .confirmed (some (payload ++ "wrong"))) := by
  intro h
  have eq : payload ++ "wrong" = payload := Option.some.inj (h ready payload rfl rfl)
  have len := congrArg String.length eq
  simp at len

theorem wrong_publication_prefix (tail : List Event) (target : State) :
    ¬ Admissible readsA readsB encode ⟨(true,true), .requested ready payload⟩
      (.publish .confirmed (some (payload ++ "wrong")) :: tail) target := by
  intro h
  cases h with
  | cons _ primitive _ => exact wrong_publication_payload primitive

theorem wrong_request_payload :
    ¬ Primitive readsA readsB encode ready (.request (payload ++ "wrong")) := by
  intro h
  have len := congrArg String.length h
  simp [payload] at len

theorem premature_publication :
    nextPhase (.running execution : Phase) (.publish .confirmed (some payload)) = none := rfl

theorem premature_request :
    nextPhase (.decided execution (.exited 0) (some 0) : Phase) (.request payload) = none := rfl

theorem no_seal_no_authorization :
    nextPhase (.empty : Phase) (.authorize 7) = none := rfl

theorem no_seal_prefix_rejected (tail : List Event) (target : State) :
    ¬ Admissible readsA readsB encode ⟨(false,false), .empty⟩ (.authorize 7 :: tail) target := by
  intro h
  cases h with
  | cons step _ _ => cases step

theorem timeout_overwrite_rejected :
    nextPhase (.decided execution .timedOut none : Phase) (.wait (.exited 0) (some 0)) = none :=
  timeout_cannot_be_overwritten _ _ _ _

theorem timeout_reap_remains_timeout :
    nextPhase (.decided execution .timedOut none : Phase) (.cleanup .confirmed (some 0) true) =
      some (.cleaned execution .timedOut (some 0) .confirmed true) :=
  cleanup_keeps_choice _ _ _ _ _ _

theorem wrong_child_identity :
    ¬ Primitive readsA readsB encode (.authorized capture 7) (.spawn 8 (false,true)) := by
  intro h
  have bad := (h capture 7 rfl).1
  cases bad

theorem wrong_live_consumption :
    ¬ Primitive readsA readsB encode (.authorized capture 7) (.spawn 7 (true,true)) := by
  intro h
  have bad := (h capture 7 rfl).2.1
  cases bad

/-- Identical unknown publication observations admit either external effect. -/
theorem unknown_effect_worlds :
    Admissible readsA readsB encode ⟨(false,false), .empty⟩
      (events .unknown none) (finalState .unknown none) ∧
    Admissible readsA readsB encode ⟨(false,false), .empty⟩
      (events .unknown (some payload)) (finalState .unknown (some payload)) :=
  ⟨admitted _ _ (by simp), admitted _ _ (by simp)⟩

theorem unknown_same_observation :
    observation (finalState .unknown none).phase =
      observation (finalState .unknown (some payload)).phase := rfl

theorem unknown_different_effects :
    (world (finalState .unknown none).phase).published = false ∧
    (world (finalState .unknown (some payload)).phase).published = true := ⟨rfl,rfl⟩

theorem lost_ack_refuses_second_spawn (effect : Option String) :
    nextPhase (finalState .unknown effect).phase (.authorize 7) = none :=
  no_authorize_after_spawn rfl _

theorem final_one_spawn : spawnCount (events .confirmed (some payload)) ≤ 1 := by
  obtain ⟨source, allowed, _⟩ := prefix_refines (admitted .confirmed (some payload) (fun _ => rfl))
  exact prefix_one_spawn allowed

theorem lost_ack_payload_retained :
    Valid readsA readsB encode (finalState .unknown (some payload)).phase ∧
    payload = encode ready := by
  obtain ⟨source, allowed, related⟩ := prefix_refines unknown_effect_worlds.2
  have valid : Valid readsA readsB encode (finalState .unknown (some payload)).phase :=
    related ▸ prefix_valid allowed trivial
  exact ⟨valid, (selected_payload valid).1⟩

theorem joint_infinite_pending :
    Interaction.Run (fun a b => SourceStep readsA readsB encode a .pending b)
      (fun _ => (⟨finalState .unknown (some payload)⟩ : Source Bool Bool (Bool × Bool) String)) :=
  pending_source _

end JointCases

end CapturedAttemptExamples

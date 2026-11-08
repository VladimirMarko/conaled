import Applications.Interaction.RetainedMeasurement
import Examples.StateException

/-! # Newly recorded evidence survives nested rollback

The older #373 cases remain imported and checked. These cases place the
measurement operation inside the protected body and inspect its event history.
-/
namespace RetainedException.Examples
open Interaction.Measurement Interaction.Measurement.Retained

/-- Missing reply is positive knowledge of a modeled attempt, not knowledge
that nothing happened. -/
def unknownReply : Observation := ⟨.unknown, false, .confirmed, .unknown⟩

theorem unknown_retained (s : Bool) :
    scopedFold attempt .undo (protectedAttempt unknownReply) s (fresh []) =
      ((.ok (selected unknownReply), s),
        ⟨selected unknownReply, [.issued, .observed unknownReply]⟩) ∧
    successful (selected unknownReply) = false ∧ begin (selected unknownReply) = none :=
  ⟨exact_new_evidence _ _ _ _, rfl, no_retry _⟩

/-- Unknown completion is compatible with either physical exit possibility.
The model cannot infer nonoccurrence from this observation. -/
theorem unknown_correspondences :
    Corresponds ⟨none, false, true, false⟩ unknownReply ∧
    Corresponds ⟨some 0, true, true, true⟩ unknownReply := by
  simp [Corresponds, unknownReply]

/-- Erasing even just the newly produced history violates the independently
specified operation contract, despite retaining the correct controller. -/
theorem erased_rejected :
    ¬ AttemptContract unknownReply (fresh [])
      ⟨selected unknownReply, []⟩ (selected unknownReply) := by
  simp [AttemptContract, fresh, initial]

/-- A purported retry adds events where the existing controller forbids issue. -/
theorem retry_rejected :
    ¬ AttemptContract unknownReply ⟨selected unknownReply, [.issued]⟩
      ⟨selected unknownReply, [.issued, .issued, .observed unknownReply]⟩
      (selected unknownReply) := by
  simp [AttemptContract, selected, record]

/-- The retry operation itself leaves both selected evidence and history intact. -/
example : attempt unknownReply ⟨selected unknownReply, [.issued, .observed unknownReply]⟩ =
    (selected unknownReply, ⟨selected unknownReply, [.issued, .observed unknownReply]⟩) :=
  retry_refused _ _ _

/-- Inner handler rethrows the selected controller; the outer handler retains it. -/
def nested (o : Observation) : Scoped Bool Observation Controller Controller Controller :=
  .handle
    (.handle (.body (.write true (.act o (fun c => .raise c))))
      (fun c => .body (.raise c)))
    (fun c => .body (.ret c))

theorem nested_exact (p : Policy) (o : Observation) (s : Bool) (hist : List Event) :
    scopedFold attempt p (nested o) s (fresh hist) =
      ((.ok (selected o), match p with | .keep => true | .undo => s),
        ⟨selected o, hist ++ [.issued, .observed o]⟩) := by
  cases p <;> rfl

example (m : Scoped Bool Observation Controller Controller Controller) (p : Policy)
    (s : Bool) (r : Evidence) : Extends r (scopedFold attempt p m s r).2 :=
  history_preserved m p s r

example (m : Tree Bool Observation Controller Controller Nat)
    (k : Nat → Tree Bool Observation Controller Controller Controller) :
    fold (algebra attempt) (m.bind k) =
      Run.bind (fold (algebra attempt) m) (fun n => fold (algebra attempt) (k n)) :=
  fold_bind _ (local_laws _) _ _

/-- Recomputing from local state can change the exact evidence while preserving
its Boolean success decision. This is not an admissible evidence replacement. -/
def alternateReply : Observation := ⟨.timedOut, false, .confirmed, .unknown⟩
def recompute (b : Bool) : Controller := selected (if b then alternateReply else unknownReply)

theorem recomputation_fails :
    successful (recompute true) = successful (recompute false) ∧
      recompute true ≠ recompute false := by decide

example (f : Bool → Controller) (s : Bool)
    (kept : f true = selected unknownReply) (undone : f s = selected unknownReply) :
    f true = f s := recompute_contract _ _ _ ⟨kept, undone⟩

/-- A genuine successful response uses all four primitive world premises. -/
def goodReply : Observation := ⟨.exited 0, true, .confirmed, .confirmed⟩
example (w : World) (truth : Corresponds w goodReply) : Completed w :=
  physical_success goodReply w truth rfl
end RetainedException.Examples

import SquareKit.RetainedException
import Applications.Interaction.Measurement

/-! # Measurement evidence produced inside a rollback scope

The supplied observation models an adapter response at the operation site.
An issued event records model authorization; physical occurrence still requires
an adapter adequacy argument. Neither crash persistence nor IO is implemented.
-/
namespace Interaction.Measurement.Retained
open RetainedException

inductive Event where
  | issued
  | observed (o : Observation)
  deriving DecidableEq, Repr

structure Evidence where
  controller : Controller
  history : List Event
  deriving DecidableEq, Repr

/-- Independently stated operation postcondition. A previously started attempt
must produce no new issue event; an authorized attempt retains its exact reply. -/
def AttemptContract (o : Observation) (before after : Evidence) (selected : Controller) : Prop :=
  selected = after.controller ∧
  if before.controller.started = true then after = before else
    after.controller.started = true ∧ after.controller.observation = some o ∧
    after.history = before.history ++ [.issued, .observed o] ∧ ResultValid after.controller

/-- `begin` authorizes issuance; `record` records this attempt's response. -/
def attempt (o : Observation) (r : Evidence) : Controller × Evidence :=
  match begin r.controller with
  | none => (r.controller, r)
  | some started =>
    let selected := record started o
    (selected, ⟨selected, r.history ++ [.issued, .observed o]⟩)

theorem attempt_contract (o : Observation) (r : Evidence) :
    AttemptContract o r (attempt o r).2 (attempt o r).1 := by
  rcases r with ⟨⟨started, obs⟩, hist⟩
  cases started <;> simp [AttemptContract, attempt, begin, record, result_valid]

/-- Prefix includes event payloads and ordering. -/
def Extends (r u : Evidence) : Prop := ∃ tail, u.history = r.history ++ tail

theorem extends_refl (r : Evidence) : Extends r r := ⟨[], by simp⟩
theorem extends_trans {r u v : Evidence} (h : Extends r u) (k : Extends u v) : Extends r v := by
  obtain ⟨xs, hx⟩ := h
  obtain ⟨ys, hy⟩ := k
  exact ⟨xs ++ ys, by simp [hy, hx, List.append_assoc]⟩
theorem attempt_extends (o : Observation) (r : Evidence) : Extends r (attempt o r).2 := by
  unfold attempt
  split
  · exact extends_refl r
  · exact ⟨[.issued, .observed o], rfl⟩

/-- The response is created by the operation under the scope, then passed as
selected evidence in the exception. It is not captured before protected work. -/
def protectedAttempt (o : Observation) : Scoped Bool Observation Controller Controller Controller :=
  .handle (.body (.write true (.act o (fun selected => .raise selected))))
    (fun selected => .body (.ret selected))

def native (p : Policy) (o : Observation) : RetainedException.Run Bool Evidence Controller Controller :=
  fun s r => let (selected, after) := attempt o r
             ((.ok selected, match p with | .keep => true | .undo => s), after)

theorem shared_native (p : Policy) (o : Observation) :
    scopedFold attempt p (protectedAttempt o) = native p o := by
  funext s r
  cases p <;> rfl

/-- Matched contract observes exact selection and history, with policy-specific
local state. It is independent of either syntax or handler implementation. -/
def ProtectedContract (p : Policy) (o : Observation) (s : Bool) (r : Evidence)
    (out : (Except Controller Controller × Bool) × Evidence) : Prop :=
  ∃ selected, out.1.1 = .ok selected ∧
    out.1.2 = (match p with | .keep => true | .undo => s) ∧
    AttemptContract o r out.2 selected

theorem native_contract (p : Policy) (o : Observation) (s : Bool) (r : Evidence) :
    ProtectedContract p o s r (native p o s r) :=
  ⟨_, rfl, rfl, attempt_contract o r⟩
theorem shared_contract (p : Policy) (o : Observation) (s : Bool) (r : Evidence) :
    ProtectedContract p o s r (scopedFold attempt p (protectedAttempt o) s r) := by
  rw [shared_native]; exact native_contract p o s r

/-- Every scope, including handler failures, preserves the complete old prefix. -/
theorem history_preserved (m : Scoped Bool Observation Controller Controller Controller)
    (p : Policy) (s : Bool) (r : Evidence) : Extends r (scopedFold attempt p m s r).2 :=
  scoped_retained attempt Extends extends_refl (fun h k => extends_trans h k)
    attempt_extends m p s r

def fresh (history : List Event) : Evidence := ⟨initial, history⟩
def selected (o : Observation) : Controller := record ⟨true, none⟩ o

theorem exact_new_evidence (p : Policy) (o : Observation) (s : Bool) (hist : List Event) :
    scopedFold attempt p (protectedAttempt o) s (fresh hist) =
      ((.ok (selected o), match p with | .keep => true | .undo => s),
        ⟨selected o, hist ++ [.issued, .observed o]⟩) := by
  rw [shared_native]; rfl

theorem no_retry (o : Observation) : begin (selected o) = none :=
  no_reexecution (s := ⟨true, none⟩) rfl (Relation.ReflTransGen.single ⟨o, rfl⟩)

theorem retry_refused (o reply : Observation) (hist : List Event) :
    attempt reply ⟨selected o, hist⟩ = (selected o, ⟨selected o, hist⟩) := by
  simp [attempt, no_retry]

theorem selected_valid (o : Observation) : ResultValid (selected o) := recording_safe _ _

theorem physical_success (o : Observation) (w : World) (truth : Corresponds w o)
    (success : successful (selected o) = true) : Completed w :=
  successful_world (selected o) o w rfl truth success

/-- Recomputing selection needs equality of the entire selected controller,
not just agreement of its success flag. -/
theorem recompute_contract (o : Observation) (f : Bool → Controller) (s : Bool)
    (same : f true = selected o ∧ f s = selected o) :
    f true = f s := same.1.trans same.2.symm
end Interaction.Measurement.Retained

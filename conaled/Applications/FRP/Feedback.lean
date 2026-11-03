import Applications.Progress.CoupledFeedback
import Applications.FRP.TemporalCausality

/-! Finite completed-batch feedback. An emitted batch advances one logical tick,
including an empty batch. No-emission observations leave feedback state alone. -/
namespace FRPSpec.Feedback
open Progress
universe u
variable {α B S : Type u}

/-- A finite selection of explicitly supplied batches; no infinite filtering. -/
def completed : List (Option (List α)) → List (List α)
  | [] => []
  | none :: xs => completed xs
  | some batch :: xs => batch :: completed xs

def consume (f : Progress.Feedback.Initialized (List α) B S) (s : S) :
    List (Option (List α)) → List B × S
  | [] => ([],s)
  | none :: xs => consume f s xs
  | some batch :: xs =>
    let next := f.step (batch,s)
    let rest := consume f next.2 xs
    (next.1 :: rest.1,rest.2)

theorem agreement (f : Progress.Feedback.Initialized (List α) B S)
    (s : S) (xs : List (Option (List α))) :
    consume f s xs = Progress.Feedback.run f.mealy s (completed xs) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [consume,completed,Progress.Feedback.run,
      Progress.Feedback.Initialized.mealy,ih]

theorem completed_append (xs ys : List (Option (List α))) :
    completed (xs ++ ys) = completed xs ++ completed ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [completed,ih]

theorem chunk (f : Progress.Feedback.Initialized (List α) B S)
    (s : S) (xs ys : List (Option (List α))) :
    consume f s (xs ++ ys) =
      let first := consume f s xs; let second := consume f first.2 ys;
      (first.1 ++ second.1,second.2) := by
  simp only [agreement,completed_append,Progress.Feedback.run_append]

theorem tick_count (f : Progress.Feedback.Initialized (List α) B S)
    (s : S) (xs : List (Option (List α))) :
    (consume f s xs).1.length = (completed xs).length := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [consume,completed,ih]

theorem stream_agreement (f : Progress.Feedback.Initialized (List α) B S)
    (xs : List (Option (List α))) (a : Stream (List α)) (n : Nat)
    (h : completed xs = prefixOf a n) :
    (consume f f.initial xs).1 = prefixOf (Progress.Feedback.output f a) n := by
  rw [agreement,Progress.Feedback.run_outputs,h,Progress.Feedback.output_prefix]

theorem synchronous (f : Progress.Feedback.Initialized (List α) B S) :
    Temporal.Synchronous (Progress.Feedback.output f) :=
  Progress.Feedback.causal f

end FRPSpec.Feedback

namespace FRPSpec.Frontier.Demand.Temporal
open FRPSpec.Frontier.Trace
variable {T α B S : Type} [LinearOrder T]

/-- Use the one-shot emission, not persistent `observed` knowledge. The query
parameter affects the observed field, but does not filter or duplicate emission. -/
def frameBatch (fr : Frame (T := T) (α := α)) : Option (List α) :=
  fr.emitted.map Prod.snd

/-- Each processing position is visited once in order. Event timestamps remain
inside the source frame; feedback ticks count only its actual emissions. -/
def feedbackInputs (s : Inputs T α) (ms : Streams T α) (a : Nat → Action T) (t : T)
    (n : Nat) : List (Option (List α)) :=
  (List.range n).map (fun j => frameBatch (frame s ms a t j))

/-- A real honest response supplies exactly one completed input, preserving its
ordered list including repetitions. Honesty is not inferred from packet validity. -/
theorem feedback_response (s : Inputs T α) (ms : Streams T α) (a : Nat → Action T) (t : T)
    (truth : Source → T → List α) (honest : (traceRep ms).Rel s truth)
    (f : Progress.Feedback.Initialized (List α) B S) (state : S) (n : Nat) (out : List α)
    (emitted : (frame s ms a t n).emitted = some (t,out)) :
    FRPSpec.Feedback.consume f state [frameBatch (frame s ms a t n)] =
      ([(f.step (truth .left t ++ truth .right t,state)).1],
        (f.step (truth .left t ++ truth .right t,state)).2) := by
  have eq : out = truth .left t ++ truth .right t :=
    (responseSquare ms a n t).preserves honest out
      ((responseFor_iff s ms a n t out).mpr emitted)
  simp [FRPSpec.Feedback.consume,frameBatch,emitted,eq]

end FRPSpec.Frontier.Demand.Temporal

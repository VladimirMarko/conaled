import Applications.FRP.Trace
import Applications.Resources.AttemptCounts

/-! Finite source-window attempts continue after rejection, retaining branch observations. -/
namespace FRPSpec.Frontier.Trace.Measured
open Resources
variable {T α : Type} [LinearOrder T]

/-- Branch on the same actual advance used by `Trace.process`, not state equality. -/
def step (m : Message T α) (s : State T α) : Resources.Measured (State T α) AttemptCounts :=
  match advance s m.frontier m.packet with
  | none => (s,rejectedAttempt)
  | some q => (q,acceptedAttempt)

theorem step_erases (m : Message T α) (s : State T α) : (step m s).1 = process s m := by
  unfold step process
  cases advance s m.frontier m.packet <;> rfl

def run (ms : List (Message T α)) (s : State T α) := Resources.run step ms s

theorem run_erases (ms : List (Message T α)) (s : State T α) :
    (run ms s).1 = ms.foldl process s := by
  rw [run, Resources.run_state]
  simp only [step_erases]

def erasureSquare (ms : List (Message T α)) :=
  Resources.erasureSquare (run ms) (ms.foldl process) (run_erases ms)

theorem run_append (ms ns : List (Message T α)) (s : State T α) :
    run (ms++ns) s = Resources.bind (run ms s) (run ns) := Resources.run_append step ms ns s

theorem reweight_run {C : Type} [AddMonoid C] (h : AttemptCounts →+ C)
    (ms : List (Message T α)) (s : State T α) :
    reweight h (run ms s) = Resources.run (fun m s => reweight h (step m s)) ms s :=
  Resources.reweight_run h step ms s

theorem run_valid (ms : List (Message T α)) (s : State T α) (hs : s.Valid) :
    (run ms s).1.Valid :=
  Resources.run_invariant step State.Valid
    (fun m s h => (step_erases m s).symm ▸ process_valid h m) ms s hs

theorem run_refines (ms : List (Message T α)) (s : State T α) : Refines s (run ms s).1 := by
  induction ms generalizing s with
  | nil => exact Refines.refl s
  | cons m ms ih =>
    exact ((step_erases m s).symm ▸ process_refines s m).trans (ih (step m s).1)

theorem step_counts (m : Message T α) (s : State T α) :
    (step m s).2.1 = 1 ∧ (step m s).2.2.1 + (step m s).2.2.2 = 1 := by
  unfold step
  cases advance s m.frontier m.packet <;> exact ⟨rfl,rfl⟩

theorem run_counts (ms : List (Message T α)) (s : State T α) :
    (run ms s).2.1 = ms.length ∧
      (run ms s).2.2.1 + (run ms s).2.2.2 = ms.length := by
  induction ms generalizing s with
  | nil => exact ⟨rfl,rfl⟩
  | cons m ms ih =>
    have h := ih (step m s).1
    have hc := step_counts m s
    change (step m s).2.1 + (run ms (step m s).1).2.1 = (m::ms).length ∧
      ((step m s).2.2.1 + (run ms (step m s).1).2.2.1) +
        ((step m s).2.2.2 + (run ms (step m s).1).2.2.2) = (m::ms).length
    simp only [List.length_cons]
    omega

theorem run_prefix (s : State T α) (messages : Nat → Message T α) (n : Nat) :
    (run ((List.range n).map messages) s).1 = sourcePrefix s messages n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, run_append]
    change (step (messages n) (run ((List.range n).map messages) s).1).1 = _
    rw [step_erases, ih]
    rfl

theorem run_prefix_sound {s : State T α} {truth : T → List α}
    (messages : Nat → Message T α) (hs : s.Valid) (old : s.Completes truth)
    (honest : ∀ n, Honest (sourcePrefix s messages n) (messages n) truth) (n : Nat) :
    (run ((List.range n).map messages) s).1.Completes truth :=
  (run_prefix s messages n).symm ▸ prefix_sound messages hs old honest n

end FRPSpec.Frontier.Trace.Measured

import Applications.FRP.Pipeline
import SquareKit.TraceFold

/-! Recover the native engine/consumer factorization through finite-fold
fusion. Exact tagged and silent event positions are retained. -/
namespace FRPSpec.Frontier.Pipeline
open Trace Progress
variable {T α B S : Type} [LinearOrder T]

def factorDecode (f : Feedback.Initialized (List α) B S) (initial : S)
    (a : Engine.MachineState T α × List (Option (T × List α))) : State T α S × List (Event T α B) :=
  let d := Feedback.run (responseMealy f) initial a.2
  (⟨a.1,d.2⟩,a.2.zip d.1)

omit [LinearOrder T] in
private theorem response_length (f : Feedback.Initialized (List α) B S) (s : S)
    (events : List (Option (T × List α))) :
    (Feedback.run (responseMealy f) s events).1.length = events.length := by
  induction events generalizing s with
  | nil => rfl
  | cons e es ih => simp only [Feedback.run, List.length_cons, ih]

theorem factor_step (f : Feedback.Initialized (List α) B S) (initial : S)
    (a : Engine.MachineState T α × List (Option (T × List α))) (c : Engine.Command T α) :
    factorDecode f initial (SquareKit.TraceFold.accumulate Engine.step a c) =
      SquareKit.TraceFold.accumulate (step f) (factorDecode f initial a) c := by
  simp only [factorDecode, SquareKit.TraceFold.accumulate, Feedback.run_append,
    Feedback.run, step]
  rw [List.zip_append (response_length f initial a.2).symm]
  rfl

/-- Same native statement as run_factor, now discharged by generic fold fusion. -/
theorem run_factor_via_fusion (f : Feedback.Initialized (List α) B S) (s : State T α S)
    (cs : List (Engine.Command T α)) :
    run f s cs =
      let e := Engine.run s.engine cs
      let d := Feedback.run (responseMealy f) s.consumer e.2
      (⟨e.1,d.2⟩,e.2.zip d.1) := by
  have fusion := SquareKit.ListFusion.foldl_reachable
    (SquareKit.TraceFold.accumulate Engine.step)
    (SquareKit.TraceFold.accumulate (step f)) (factorDecode f s.consumer)
    (fun _ => True) (s.engine,[]) trivial (fun _ _ _ => trivial)
    (fun a c _ => factor_step f s.consumer a c) cs
  rw [SquareKit.TraceFold.identifies_empty Engine.step Engine.run
    (fun _ => rfl) (fun _ _ _ => rfl)] at fusion
  change factorDecode f s.consumer (Engine.run s.engine cs) =
    cs.foldl (SquareKit.TraceFold.accumulate (step f)) (s,[]) at fusion
  rw [SquareKit.TraceFold.identifies_empty (step f) (run f)
    (fun _ => rfl) (fun _ _ _ => rfl)] at fusion
  exact fusion.symm

end FRPSpec.Frontier.Pipeline

import Applications.FRP.ReactiveConsumers
import Examples.FRPEngine

/-! Compiled finite consumers, independent wired/direct comparison, and an actual
one-shot engine emission. Synthetic multiple batches do not extend its lifecycle. -/
namespace Examples.ReactiveTarget
open FRPSpec FRPSpec.Reactive Progress Progress.Feedback

abbrev samples : List (Option (List Nat)) := [none,some [3,4],some [],some [3]]

theorem aggregate_expected : Feedback.consume (batches jointMachine) jointMachine.initial samples =
    ([(1,7),(2,7),(3,10)],(3,10)) := by
  rw [consume_joint]
  decide

#eval Feedback.consume (batches jointMachine) jointMachine.initial samples

theorem wired_expected :
    (Feedback.consume (batches wired) wired.initial samples).1 = [(1,8),(2,9),(3,13)] ∧
    StateRel (Feedback.consume (batches wired) wired.initial samples).2 (3,10) := by
  have h := consume_wired samples
  exact h

#eval Feedback.consume (batches wired) wired.initial samples

/-- Resetting between chunks is unnecessary; the retained state is passed on. -/
example (xs ys : List (Option (List Nat))) :
    Feedback.consume (batches wired) wired.initial (xs ++ ys) =
      let first := Feedback.consume (batches wired) wired.initial xs
      let second := Feedback.consume (batches wired) first.2 ys
      (first.1 ++ second.1,second.2) := Feedback.chunk _ _ _ _

example (xs ys : List Nat) :
    run jointMachine.mealy jointMachine.initial (xs ++ ys) =
      let first := run jointMachine.mealy jointMachine.initial xs
      let second := run jointMachine.mealy first.2 ys
      (first.1 ++ second.1,second.2) := run_append _ _ _ _

/-- Every finite input, not just the displayed sample, uses compiler correctness. -/
example (xs : List Nat) : run jointMachine.mealy jointMachine.initial xs =
    run jointSpec.mealy jointSpec.initial xs :=
  ReactiveCompiler.run_sound K sound jointSeed jointBody xs

example (xs : List Nat) :
    (run wired.mealy wired.initial xs).1 = (run wiredSpec.mealy wiredSpec.initial xs).1 ∧
      StateRel (run wired.mealy wired.initial xs).2 (run wiredSpec.mealy wiredSpec.initial xs).2 :=
  wired_run xs _ _ wired_initial

example (a : Stream Nat) (n : Nat) : output wired a n = output wiredSpec a n :=
  (wired_stream a).2 n

/-- This decomposition invokes the public sequential and parallel finite laws. -/
example (xs : List Nat) :
    run wired.mealy wired.initial xs =
      let count := run countMachine.mealy countMachine.initial xs
      let total := run totalMachine.mealy totalMachine.initial xs
      ((count.1.zip total.1).map finishFn,((PUnit.unit,(count.2,total.2)),PUnit.unit)) := by
  change run (seq (seq (Progress.Feedback.pure duplicateFn) (par countMachine totalMachine))
    (Progress.Feedback.pure finishFn)).mealy
    ((PUnit.unit,(countMachine.initial,totalMachine.initial)),PUnit.unit) xs = _
  simp only [run_seq,run_pure,run_par]
  simp only [List.map_map,Function.comp_def,duplicate_correct]
  simp

example (xs : List Nat) : run (pure (fun x : Nat => x+1)).mealy PUnit.unit xs =
    (xs.map (fun x => x+1),PUnit.unit) := run_pure _ _

example : run delayed.mealy delayed.initial [7,0,3] = ([42,7,0],3) := by decide
example : (run delayed.mealy delayed.initial [7,0,3]).1 ≠ [7,0,3] := by decide
example : delayed.step (7,delayed.initial) = (42,7) := by rw [delayed_step,delayed_initial]

/-- Dropping empty batches loses a completed tick, even though its sum is zero. -/
def dropEmpty (xs : List (Option (List Nat))) := xs.filter (fun x =>
  match x with | none => true | some batch => !batch.isEmpty)

example : Feedback.consume (batches jointMachine) jointMachine.initial (dropEmpty samples) =
    ([(1,7),(2,10)],(2,10)) := by decide
example : (Feedback.consume (batches jointMachine) jointMachine.initial (dropEmpty samples)).2 ≠
    (Feedback.consume (batches jointMachine) jointMachine.initial samples).2 := by decide

example : Feedback.consume (batches jointMachine) (4,20) [none] = ([],(4,20)) := rfl
example : Feedback.consume (batches jointMachine) (4,20) [some []] = ([(5,20)],(5,20)) := by decide

/-- Keep the engine's timestamped events as a distinct value. -/
def actualResponses := (Frontier.Engine.run (Frontier.Engine.init FRPTrace.start) FRPEngine.script).2
def actualBatches := actualResponses.map (Option.map Prod.snd)

theorem actual_events : actualResponses = [none,none,none,none,some (2,[3,4,3])] :=
  FRPEngine.script_events

example : Feedback.consume (batches jointMachine) jointMachine.initial actualBatches =
    ([(1,10)],(1,10)) := by
  rw [consume_joint]
  decide

example : (Feedback.consume (batches wired) wired.initial actualBatches).1 = [(1,11)] := by
  exact (consume_wired actualBatches).1

#eval (actualResponses,Feedback.consume (batches jointMachine) jointMachine.initial actualBatches)

example : Feedback.consume (batches jointMachine) jointMachine.initial
    ((Frontier.Engine.run (Frontier.Engine.init FRPTrace.start)
      [.register 2,.process,.process]).2.map (Option.map Prod.snd)) = ([],(0,0)) := by decide

/-- Repeated processing cannot turn the real one-shot engine into multiple ticks. -/
example : Feedback.consume (batches jointMachine) jointMachine.initial
    ((Frontier.Engine.run (Frontier.Engine.init FRPTrace.start)
      (FRPEngine.script ++ [.process,.process])).2.map (Option.map Prod.snd)) =
    ([(1,10)],(1,10)) := by decide

end Examples.ReactiveTarget

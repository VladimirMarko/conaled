import Applications.FRP.ReactiveContracts
import Examples.TemporalFRP

namespace Examples.ReactiveContracts
open FRPSpec.Frontier FRPSpec.Frontier.Trace FRPSpec.Frontier.Demand
open FRPSpec.Frontier.Demand.Temporal FRPSpec.Feedback FRPSpec.ReactiveContracts
open Examples.FRPTrace Examples.FRPDemand Examples.TemporalFRP
open SquareKit.RelationTransport

def initialHistory : History Nat := (2,[8])

/-- An ordinary executable consumer; explicit finite prefixes supply observations. -/
def actual (n : Nat) : Result Nat :=
  consume (history initialHistory) initialHistory (feedbackInputs start packets early 2 n)

example (s : Inputs ℚ Nat) (ms : Streams ℚ Nat) :
    request s ms (register 2 (fun n => early (n+1))) 1 = .pending 2 := bootstrap _ _ _ _
example : register 2 (fun n => early (n+1)) = early := by
  funext n; cases n <;> rfl

example : actual 5 = ([],(2,[8])) :=
  consume_zero initialHistory _ (by decide)
example : actual 6 = ([(3,[8,3,4,3])],(3,[8,3,4,3])) := by
  exact delivered_result start packets early 2 rfl truth honest initialHistory 5 [3,4,3] (by decide)
example : consume (history initialHistory) initialHistory (feedbackInputs start packets emptyQuery 1 2) =
    ([(3,[8])],(3,[8])) := by
  exact delivered_result start packets emptyQuery 1 rfl truth honest initialHistory 1 [] (by decide)
example : actual 7 = actual 6 := by decide
example : (frame start packets early 2 6).observed = some [3,4,3] ∧
    frameBatch (frame start packets early 2 6) = none := by decide
example : process (sourcePrefix (start .left) (packets .left) 1) (packets .left 1) =
    sourcePrefix (start .left) (packets .left) 1 ∧ early 6 = .source .left := by decide
example : consume (history initialHistory) initialHistory [none,some []] ≠
    consume (history initialHistory) initialHistory [none,none] := by decide

/-- Both concrete compatibility inclusions are used in a connected execution. -/
theorem actual_allowed (n : Nat) : AllowedResult initialHistory [3,4,3] (actual n) := by
  apply connected_image packets early 2 rfl truth n initialHistory
  exact ⟨start,honest,feedbackInputs start packets early 2 n,rfl,rfl⟩
example (n : Nat) : (actual n).2 = initialHistory ∨
    (actual n).2 = updated initialHistory [3,4,3] := by
  apply connected_history packets early 2 rfl truth n initialHistory
  exact ⟨start,honest,feedbackInputs start packets early 2 n,rfl,rfl⟩
example (n : Nat) : admissible packets truth ⊆
    requirement (Relation.Comp (broker packets early 2 n) (consumer initialHistory))
      (AllowedResult initialHistory [3,4,3]) :=
  connected_requirement packets early 2 rfl truth n initialHistory
example (xs ys : List (Option (List Nat))) :
    consume (history initialHistory) initialHistory (xs++ys) =
      let first := consume (history initialHistory) initialHistory xs
      let second := consume (history initialHistory) first.2 ys
      (first.1++second.1,second.2) := chunk _ _ _ _
example (xs : List (Option (List Nat))) :
    (consume (history initialHistory) initialHistory xs).1.length = (completed xs).length :=
  tick_count _ _ _
example : _root_.Temporal.Synchronous (Progress.Feedback.output (history initialHistory)) :=
  synchronous _

/-- A concrete environment makes each scheduled prefix available in time. -/
def earlyDelivery : Delivery (sourceSchedule early) where
  available source n := count (sourceSchedule early) source (n+1)
  monotone source _ _ h := count_mono _ source (Nat.succ_le_succ h)
  legal n source h := by simp [count,h]

theorem early_fair : earlyDelivery.Fair := by
  intro source n k hk
  exact ⟨n+1,Nat.le_succ n,hk⟩

theorem early_processing (ms : Streams ℚ Nat) : ProcessingFair start ms early := by
  intro n t _ _
  exact ⟨n+7,by omega,rfl⟩

theorem early_progress : ∀ source, ∃ k n, k ≤ earlyDelivery.available source n ∧
    (2 : ℚ) < (sourcePrefix (start source) (packets source) k).frontier := by
  intro source
  refine ⟨1,4,?_,?_⟩ <;> cases source <;> decide

/-- Conditional progress is applied with its actual source and scheduling witnesses. -/
example : ∃ n, actual n = ([(3,[8,3,4,3])],(3,[8,3,4,3])) :=
  eventual_update start packets early 2 rfl truth honest initialHistory
    earlyDelivery early_fair (early_processing packets) early_progress

/-- No advance: available and fairly scheduled messages still cannot close time 2. -/
example : ¬ (∀ source, ∃ k n, k ≤ earlyDelivery.available source n ∧
    (2 : ℚ) < (sourcePrefix (start source) (stalled source) k).frontier) := by
  intro h
  obtain ⟨k,_,_,hk⟩ := h .left
  simp [stalled_prefix,initial] at hk
example : ProcessingFair start stalled early := early_processing stalled

theorem stalled_early_silent (n : Nat) : response start stalled early n = none := by
  cases he : response start stalled early n with
  | none => rfl
  | some pair =>
    obtain ⟨t,b⟩ := pair
    have ht := emitted_time start stalled early 2 rfl n t b he
    subst t
    have ho := (emit_iff.mp he).2.2
    simp [observe,run,stalled_prefix,observeMerge,initial] at ho

example (n : Nat) : consume (history initialHistory) initialHistory
    (feedbackInputs start stalled early 2 n) = ([],initialHistory) :=
  silent_consume start stalled early 2 stalled_early_silent initialHistory n

/-- The separately supplied starved environment closes sources but never processes. -/
example : ¬ ProcessingFair start packets starved := by
  intro h
  obtain ⟨m,_,hm⟩ := h 3 2 (by decide) ⟨[3,4,3],by decide⟩
  exact starved_no_process m hm
example (n : Nat) : response start packets starved n = none := Examples.TemporalFRP.starved_silent n
example (n : Nat) : consume (history initialHistory) initialHistory
    (feedbackInputs start packets starved 2 n) = ([],initialHistory) :=
  silent_consume start packets starved 2 Examples.TemporalFRP.starved_silent initialHistory n

/-- Universal per-delivery safety says nothing about occurrence of a delivery. -/
example : AllowedInput [3,4,3] [none,none,none] ∧
    consume (history initialHistory) initialHistory [none,none,none] = ([],initialHistory) :=
  ⟨Or.inl rfl,rfl⟩
example : response start packets (fun _ => .idle) 0 = none ∧
    request start packets (fun _ => .idle) 1 ≠ .pending 2 := by decide

/-- A legitimate empty response blocks a consumer requiring nonempty deliveries. -/
def nonemptyInputs : Set (List (Option (List Nat))) :=
  {xs | ∀ batch ∈ completed xs, batch ≠ []}
example : ¬ image (broker packets emptyQuery 1 2) (admissible packets truth) ⊆ nonemptyInputs := by
  intro h
  have bad := h ⟨start,honest,rfl⟩
  exact bad [] (by decide) rfl
example : ¬ AllowedInput [3,4,3] [some [9]] := by
  change ¬ (([[9]] : List (List Nat)) = [] ∨ [[9]] = [[3,4,3]])
  decide
example : consume (history initialHistory) initialHistory [some [9]] =
    ([(3,[8,9])],(3,[8,9])) := rfl

#eval actual 7
end Examples.ReactiveContracts

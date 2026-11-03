import SquareKit.Temporal.Syntax
import Applications.FRP.TemporalCausality
import Examples.FRPDemand

/-! Checked #206 boundaries: processing horizons are independent of rational
query timestamps. Empty batches, source progress and scheduling remain distinct. -/
namespace Examples.TemporalFRP
open FRPSpec.Frontier FRPSpec.Frontier.Trace FRPSpec.Frontier.Demand
open FRPSpec.Frontier.Demand.Temporal
open Examples.FRPTrace Examples.FRPDemand
open _root_.Temporal

example : (searchArrival start packets late 2 1 3 (by decide)).map Until.horizon = some 0 := by
  decide
example : (searchArrival start packets early 2 5 1 (by decide)).map Until.horizon = some 4 := by
  decide
example : (searchArrival start packets early 2 4 1 (by decide)).isNone = true := by decide
example : (searchArrival start packets late 2 0 3 (by decide)).isNone = true := by decide
example : Progress.search (machine start packets early 2) 5 1 = some ((5,[3,4,3]),5) := by decide
example : Progress.search (machine start packets late 2) 1 3 = some ((3,[3,4,3]),1) := by decide
example : (searchArrival start packets emptyQuery 1 1 1 (by decide)).map
    (output start packets emptyQuery 1) = some [] := by decide
example : response start packets emptyQuery 2 = none := by decide
example : observe (run start packets (sourceSchedule late) 3) 3 = none := by decide

example : (frame start packets emptyQuery 1 1).observed = some [] :=
  (frame_comparison start packets emptyQuery 1 (n := 1) (out := []) (by decide)).2

/-- The same first arrival is a direct ordinary Lean value. -/
def earlyWitness : Arrival start packets early 2 1 :=
  .wait ⟨by decide⟩ (.wait ⟨by decide⟩ (.wait ⟨by decide⟩ (.wait ⟨by decide⟩
    (.now ⟨[3,4,3], ⟨by decide⟩⟩))))
example : earlyWitness.horizon = 4 := rfl
example : earlyWitness.window.1 = 4 := rfl

example : ∃ fuel result, searchArrival start packets early 2 fuel 1 (by decide) = some result :=
  arrival_has_fuel start packets early 2 earlyWitness (by decide)
example : Until.windowEquiv (Pending start packets early 2) (Delivered start packets early 2) 1
    earlyWitness = earlyWitness.window := rfl
example : Until.ofWindow 1 earlyWitness.window.1 earlyWitness.window.2.1 earlyWitness.window.2.2 =
    earlyWitness := Until.ofWindow_window _

/-- Optional syntax records exactly the same waiting assumptions. -/
def Γ : Context Bool := [(1,.atom false),(2,.atom false),(3,.atom false),
  (4,.atom false),(5,.atom true)]
def earlyTerm : Term Γ 1 (.until (.atom false) (.atom true)) :=
  .untilWait (.var .here) (.untilWait (.var (.there .here))
    (.untilWait (.var (.there (.there .here)))
      (.untilWait (.var (.there (.there (.there .here))))
        (.untilNow (.var (.there (.there (.there (.there .here)))))))))
def valuation : Bool → Nat → Type
  | false => Pending start packets early 2
  | true => Delivered start packets early 2

def environment : Env valuation Γ := by
  intro n a v
  cases v with
  | here => exact ⟨by decide⟩
  | there v => cases v with
    | here => exact ⟨by decide⟩
    | there v => cases v with
      | here => exact ⟨by decide⟩
      | there v => cases v with
        | here => exact ⟨by decide⟩
        | there v => cases v with
          | here => exact ⟨[3,4,3], ⟨by decide⟩⟩
          | there v => cases v
example : Term.eval environment earlyTerm = earlyWitness := rfl
example : Term.eval environment (Term.nextE (Term.nextI earlyTerm)) = earlyWitness := rfl
example : Term.eval environment (Term.subst (fun x => .var x) earlyTerm) = earlyWitness := by
  rw [Term.subst_id]; rfl

/-- Scheduling premises are discharged from available packets and concrete actions. -/
theorem closing : ∀ source, ∃ k n, k ≤ available.available source n ∧
    (2 : ℚ) < (sourcePrefix (start source) (packets source) k).frontier := by
  intro source
  refine ⟨1,0,le_rfl,?_⟩
  cases source <;> decide

theorem honest : (traceRep packets).Rel start truth := by
  refine ⟨?_,?_,packets_honest⟩
  · intro source; simp [start, initial, State.Valid]
  · intro source t ht
    cases source with
    | left =>
      change t < (2 : ℚ) at ht
      simp [start, initial, batch, truth, ne_of_lt ht]
    | right => rfl

example : Nonempty (Arrival start packets late 2 3) :=
  eventual_arrival start packets late 2 available available_fair (processing_fair packets)
    3 (by decide) closing
example : Nonempty (Until (Pending start packets late 2) (Correct start packets late 2 truth) 3) :=
  eventual_correct start packets late 2 available available_fair (processing_fair packets)
    3 (by decide) closing truth honest
example : (correct start packets early 2 truth honest earlyWitness).horizon = 4 :=
  Until.horizon_map _ _ earlyWitness

theorem stalled_silent (n : Nat) : response start stalled late n = none := by
  unfold response emit
  split <;> try rfl
  rename_i t ha hq
  have ht : t = 2 := by
    obtain ⟨k, _, hk⟩ := pending_registered start stalled late hq
    cases k with
    | zero => simp [late] at hk
    | succ k => cases k with
      | zero => simp [late] at hk
      | succ k => cases k <;> simp_all [late]
  subst t
  simp [observe, run, stalled_prefix, observeMerge, initial]
example : ¬ Nonempty (Arrival start stalled late 2 3) :=
  no_arrival start stalled late 2 stalled_silent 3
example : ProcessingFair start stalled late := processing_fair stalled
example : available.Fair := available_fair
example : ¬ (∀ source, ∃ k n, k ≤ available.available source n ∧
    (2 : ℚ) < (sourcePrefix (start source) (stalled source) k).frontier) := by
  intro h
  obtain ⟨k,_,_,hk⟩ := h .left
  simp [stalled_prefix,initial] at hk

theorem starved_silent (n : Nat) : response start packets starved n = none := by
  unfold response emit
  split <;> try rfl
  exact (starved_no_process n (by assumption)).elim
example : ¬ Nonempty (Arrival start packets starved 2 3) :=
  no_arrival start packets starved 2 starved_silent 3
example : ¬ ProcessingFair start packets starved := by
  intro h
  obtain ⟨m,_,hm⟩ := h 3 2 (by decide) ⟨[3,4,3],by decide⟩
  exact starved_no_process m hm
example : starvedAvailable.Fair := by
  intro source n k hk
  obtain ⟨m,hm,hc⟩ := available_fair source n k hk
  exact ⟨m,hm,by simpa [starved_schedule] using hc⟩
example : ¬ idleDelivery.Fair := by
  intro h
  obtain ⟨m,_,hm⟩ := h .left 0 1 (by decide)
  simp [idle_count] at hm

example : ∀ source, ∃ k n, k ≤ starvedAvailable.available source n ∧
    (2 : ℚ) < (sourcePrefix (start source) (packets source) k).frontier := by
  intro source
  refine ⟨1,0,le_rfl,?_⟩
  cases source <;> decide

/-- Denotational never remains valid but has no finite occurrence certificate. -/
example (clock : Nat → ℝ) (n : Nat) : ¬ Nonempty (Eventually
    (fun j => PLift ((FRPSpec.Event.never (α := Nat)).at (clock j) ≠ [])) n) := by
  rintro ⟨w⟩
  exact Until.no_terminal (fun _ h => h.down rfl) w

/-- Protocol acceptance alone cannot identify a batch with an arbitrary external truth. -/
example : response start packets late 3 = some (2,[3,4,3]) ∧
    ¬ (traceRep packets).Rel start (fun _ _ => []) := by
  refine ⟨by decide, ?_⟩
  intro bad
  have e := (responseSquare packets late 3 (2 : ℚ)).preserves bad [3,4,3]
    ((responseFor_iff start packets late 3 2 [3,4,3]).mpr (by decide))
  change [3,4,3] = [] at e
  cases e

/-- Productive processing-index frames do not make a filtered value stream productive. -/
example : ¬ Progress.Productive
    (Progress.filterProducer (Option.isSome : Option Nat → Bool)
      (fun s : Unit => (none,s))) () :=
  Progress.filter_no_match _ _ (fun _ => rfl) ()

/-- Mapping preserves the actual output's order and duplicates. -/
example : (responseFor start packets early 5 2).map (List.map (·+1)) = some [4,5,4] := by decide
example (n : Nat) (out : List Nat)
    (h : (responseFor start packets early n 2).map (List.map (·+1)) = some out) :
    out = (truth .left 2 ++ truth .right 2).map (·+1) :=
  (Relational.compose (mapObservation (fun x : Nat => x+1))
    (responseSquare packets early n 2)).preserves honest out h

def countEmissions : Progress.Mealy Nat (Option (ℚ × List Nat)) Nat :=
  fun count response => let next := count + if response.isSome then 1 else 0; (next,next)
example : Synchronous (Progress.runStream countEmissions 0) := mealy_synchronous _ _
example : Progress.DeliversWithin (Progress.mealyProcessor countEmissions 0) (fun n => n+1) :=
  Progress.mealy_delivery _ _
example : Progress.prefixOf (Progress.runStream countEmissions 0 (response start packets early)) 7 =
    [0,0,0,0,0,1,1] := by decide
def mapResponse : Option (ℚ × List Nat) → Option (ℚ × List Nat) :=
  Option.map (fun (t,xs) => (t,xs.map (·+1)))
example : mapResponse none = none := rfl
example : mapResponse (some (1,[])) = some (1,[]) := rfl
example : Synchronous (Progress.mapProcessor mapResponse).meaning :=
  synchronous_of_delivery _ _ (Progress.map_delivery _) (fun _ => le_rfl)
example : Progress.DeliversWithin
    (Progress.composeProcessor (Progress.mealyProcessor countEmissions 0)
      (Progress.mapProcessor mapResponse)) (fun n => (n+1)+(n+1)) :=
  Progress.compose_delivery (Progress.map_delivery _) (Progress.mealy_delivery _ _)
example : Synchronous
    (Progress.composeProcessor (Progress.mealyProcessor countEmissions 0)
      (Progress.mapProcessor mapResponse)).meaning :=
  synchronous_of_delivery _ _
    (Progress.compose_delivery (Progress.map_delivery _) (Progress.mealy_delivery _ _))
    (fun _ => le_rfl)
example : ¬ Synchronous (Progress.shift (A := Nat)) := shift_not_synchronous

end Examples.TemporalFRP

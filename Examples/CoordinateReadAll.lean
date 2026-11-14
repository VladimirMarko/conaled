import Applications.Selection.CoordinateReadAll
import Mathlib.Data.Fin.VecNotation

/-! Actual full-coordinate executions and repeated-plan query charges. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.CoordinateReadAll
open Applications.Selection.CoordinateQueries
universe u v

variable {n : Nat} {α : Type u} {β : Type v}

/-- Even an empty payload type needs no fabricated answer when n=0. -/
theorem empty_run (compute : List α → β) (input : Fin 0 → α) :
    Runs (readAll compute) input [] [] (compute []) := by
  simpa only [List.ofFn_zero] using readAll_run compute input

theorem empty_every_run (compute : List α → β) (input : Fin 0 → α)
    (trace : Transcript 0 α) (value : β)
    (run : Runs (readAll compute) input [] trace value) (c : Nat) :
    trace = [] ∧ value = compute [] ∧ queryWork (fun _ _ => c) trace = 0 := by
  obtain ⟨ht, hv⟩ := run.deterministic (empty_run compute input)
  exact ⟨ht, hv, by rw [ht]; rfl⟩

/-- Totality supplies the run before the exact observation laws are applied. -/
theorem full_read_exists (compute : List α → β) (input : Fin n → α) (c : Nat) :
    ∃ (trace : Transcript n α) (value : β),
      Runs (readAll compute) input [] trace value ∧
      trace.map Prod.fst = List.finRange n ∧
      value = compute (List.ofFn input) ∧ trace.length = n ∧
      queryWork (fun _ _ => c) trace = c * n := by
  obtain ⟨trace, value, run⟩ := readAll_total compute input
  exact ⟨trace, value, run, readAll_coordinates compute input trace value run,
    ((readAll_run_iff compute input trace value).mp run).2,
    readAll_length compute input trace value run, readAll_work compute input trace value run c⟩

/-- The same complete observation is forced for every terminating run. -/
theorem full_read_every_run (compute : List α → β) (input : Fin n → α)
    (trace : Transcript n α) (value : β)
    (run : Runs (readAll compute) input [] trace value) (c : Nat) :
    trace = List.ofFn (fun i => (i, input i)) ∧
      value = compute (List.ofFn input) ∧ trace.length = n ∧
      queryWork (fun _ _ => c) trace = c * n := by
  obtain ⟨ht, hv⟩ := (readAll_run_iff compute input trace value).mp run
  exact ⟨ht, hv, readAll_length compute input trace value run,
    readAll_work compute input trace value run c⟩

/-- A pure specification transfers through the observations actually obtained. -/
theorem observed_sum (input : Fin n → Nat) (trace : Transcript n Nat) (value : Nat)
    (run : Runs (readAll (fun xs : List Nat => xs.sum)) input [] trace value) :
    value = (List.ofFn input).sum :=
  readAll_correct (fun xs : List Nat => xs.sum) (fun xs a => a = xs.sum)
    (by intro xs _; rfl) input trace value run

/-- Coordinate order is 0,1,2; the observed values sum to 16. -/
theorem concrete_full_read :
    Runs (readAll (fun xs : List Nat => xs.sum)) (![8, 3, 5] : Fin 3 → Nat) []
      [(0, 8), (1, 3), (2, 5)] 16 := by
  have observations : List.ofFn (fun i : Fin 3 => (i, (![8, 3, 5] : Fin 3 → Nat) i)) =
      [(0, 8), (1, 3), (2, 5)] := by decide +kernel
  have result : (List.ofFn (![8, 3, 5] : Fin 3 → Nat)).sum = 16 := by decide +kernel
  simpa only [observations, result] using
    readAll_run (fun xs : List Nat => xs.sum) (![8, 3, 5] : Fin 3 → Nat)

/-- Equal payload values still arise from three different charged coordinates. -/
theorem duplicate_full_read :
    Runs (readAll (fun xs : List Nat => xs.sum)) (![4, 4, 4] : Fin 3 → Nat) []
      [(0, 4), (1, 4), (2, 4)] 12 := by
  have observations : List.ofFn (fun i : Fin 3 => (i, (![4, 4, 4] : Fin 3 → Nat) i)) =
      [(0, 4), (1, 4), (2, 4)] := by decide +kernel
  have result : (List.ofFn (![4, 4, 4] : Fin 3 → Nat)).sum = 12 := by decide +kernel
  simpa only [observations, result] using
    readAll_run (fun xs : List Nat => xs.sum) (![4, 4, 4] : Fin 3 → Nat)

theorem duplicate_every_charge (trace : Transcript 3 Nat) (value : Nat)
    (run : Runs (readAll (fun xs : List Nat => xs.sum))
      (![4, 4, 4] : Fin 3 → Nat) [] trace value) :
    value = 12 ∧ trace.length = 3 ∧ queryWork (fun _ _ => 2) trace = 6 := by
  exact ⟨(run.deterministic duplicate_full_read).2,
    readAll_length _ _ trace value run, readAll_work _ _ trace value run 2⟩

/-- The third read really repeats coordinate zero; no deduplication occurs. -/
theorem repeated_plan_run (compute : List α → β) (input : Fin 2 → α) :
    Runs (readPlan [0, 1, 0] compute) input []
      [(0, input 0), (1, input 1), (0, input 0)]
      (compute [input 0, input 1, input 0]) := by
  simpa only [List.map_cons, List.map_nil] using
    readPlan_run [0, 1, 0] compute input

theorem repeated_plan_every_charge (compute : List α → β) (input : Fin 2 → α)
    (trace : Transcript 2 α) (value : β)
    (run : Runs (readPlan [0, 1, 0] compute) input [] trace value) (c : Nat) :
    value = compute [input 0, input 1, input 0] ∧ trace.length = 3 ∧
      queryWork (fun _ _ => c) trace = c * 3 := by
  exact ⟨(run.deterministic (repeated_plan_run compute input)).2,
    readPlan_length [0, 1, 0] compute input trace value run,
    readPlan_work [0, 1, 0] compute input trace value run c⟩

/-- This supplied history is not asserted to be reachable. The equation only
shows that an exhausted plan computes from its recorded chronological answers. -/
theorem supplied_history_values :
    readPlan ([0, 1] : List (Fin 2)) (fun xs : List Nat => xs)
      [(0, 99), (1, 7)] = Sum.inl [7, 99] :=
  readPlan_done [0, 1] (fun xs : List Nat => xs) [(0, 99), (1, 7)] rfl

end Examples.CoordinateReadAll

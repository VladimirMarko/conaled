import Applications.Selection.CoordinateSelection
import Examples.CoordinateQueries

/-! Actual acquisition, selector calls, and coordinate-model comparison. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.CoordinateSelection
open Applications.Selection
open Applications.Selection.CoordinateQueries
open Applications.Selection.CoordinateSelection
universe u

variable {n : Nat} {α : Type u}

/-- Existence precedes the observation contract; the worker consumes exactly
the chronological answers of this actual run. -/
theorem acquired_worker_execution [LinearOrder α] (k : Nat) (input : Fin n → α)
    (c : Nat) :
    ∃ (trace : Transcript n α) (observation : Resources.Measured (Option α) Nat),
      Runs (observedSelect k) input [] trace observation ∧
      trace.map Prod.snd = List.ofFn input ∧
      observation = Resources.Selection.selectRun k (trace.map Prod.snd) ∧
      work c trace observation = c * n + observation.2 := by
  obtain ⟨trace, observation, run⟩ := observedSelect_total k input
  exact ⟨trace, observation, run, observedSelect_acquired k input trace observation run,
    observedSelect_on_acquired k input trace observation run,
    work_acquisition k input trace observation run c⟩

/-- The optional empty extension still pays its selector entry and length. -/
theorem empty_run [LinearOrder α] (k : Nat) (input : Fin 0 → α) :
    Runs (observedSelect k) input [] [] (none, 2) := by
  simpa only [List.ofFn_zero, Resources.Selection.selectRun_nil] using
    observedSelect_run k input

theorem empty_every_work [LinearOrder α] (k : Nat) (input : Fin 0 → α)
    (trace : Transcript 0 α) (observation : Resources.Measured (Option α) Nat)
    (run : Runs (observedSelect k) input [] trace observation) (c : Nat) :
    trace = [] ∧ observation = (none, 2) ∧ work c trace observation = 2 := by
  obtain ⟨ht, ho⟩ := run.deterministic (empty_run k input)
  exact ⟨ht, ho, by rw [ht, ho]; rfl⟩

/-- One sort entry, insertion, empty sort and lookup cost4; selector entry and
length cost3. The one acquired coordinate is charged separately. -/
theorem singleton_run (a : Int) :
    Runs (observedSelect 0) (fun _ : Fin 1 => a) [] [(0, a)] (some a, 7) := by
  have selector : Resources.Selection.selectRun 0 [a] = (some a, 7) := by
    rw [Resources.Selection.selectRun_small 0 [a] (by simp) (by simp)]
    rfl
  simpa only [List.ofFn_succ, List.ofFn_zero, selector] using
    observedSelect_run 0 (fun _ : Fin 1 => a)

theorem singleton_every_work (a : Int) (trace : Transcript 1 Int)
    (observation : Resources.Measured (Option Int) Nat)
    (run : Runs (observedSelect 0) (fun _ : Fin 1 => a) [] trace observation)
    (c : Nat) : observation = (some a, 7) ∧ work c trace observation = c + 7 := by
  obtain ⟨ht, ho⟩ := run.deterministic (singleton_run a)
  exact ⟨ho, by rw [ht, ho]; rfl⟩

/-- Sort9 + lookup2 + length4 + entry1 gives actual source count16. -/
theorem concrete_run :
    Runs (observedSelect 1) (![8, 3, 5] : Fin 3 → Int) []
      [(0, 8), (1, 3), (2, 5)] (some 5, 16) := by
  have values : List.ofFn (![8, 3, 5] : Fin 3 → Int) = [8, 3, 5] := by decide +kernel
  have trace : List.ofFn (fun i : Fin 3 => (i, (![8, 3, 5] : Fin 3 → Int) i)) =
      [(0, 8), (1, 3), (2, 5)] := by decide +kernel
  have selector : Resources.Selection.selectRun 1 ([8, 3, 5] : List Int) =
      (some 5, 16) := by
    rw [Resources.Selection.selectRun_small 1 [8, 3, 5] (by decide) (by decide)]
    decide +kernel
  simpa only [values, trace, selector] using
    observedSelect_run 1 (![8, 3, 5] : Fin 3 → Int)

/-- The value view is the same measured execution, with the valid some result. -/
theorem concrete_value_run :
    Runs (selectedValue 1) (![8, 3, 5] : Fin 3 → Int) []
      [(0, 8), (1, 3), (2, 5)] 5 :=
  (selectedValue_run_iff 1 (![8, 3, 5] : Fin 3 → Int)
    [(0, 8), (1, 3), (2, 5)] 5).mpr ⟨(some 5, 16), concrete_run, rfl⟩

/-- Zero acquisition tariff does not make the deterministic selector free. -/
theorem concrete_every_work (trace : Transcript 3 Int)
    (observation : Resources.Measured (Option Int) Nat)
    (run : Runs (observedSelect 1) (![8, 3, 5] : Fin 3 → Int) [] trace observation) :
    observation = (some 5, 16) ∧ work 2 trace observation = 22 ∧
      work 0 trace observation = 16 := by
  obtain ⟨ht, ho⟩ := run.deterministic concrete_run
  exact ⟨ho, by rw [ht, ho]; rfl, by rw [ht, ho]; rfl⟩

/-- Sort7 + lookup2 + length4 + entry1 gives count14, despite repeated values. -/
theorem duplicate_run :
    Runs (observedSelect 1) (![4, 4, 4] : Fin 3 → Int) []
      [(0, 4), (1, 4), (2, 4)] (some 4, 14) := by
  have values : List.ofFn (![4, 4, 4] : Fin 3 → Int) = [4, 4, 4] := by decide +kernel
  have trace : List.ofFn (fun i : Fin 3 => (i, (![4, 4, 4] : Fin 3 → Int) i)) =
      [(0, 4), (1, 4), (2, 4)] := by decide +kernel
  have selector : Resources.Selection.selectRun 1 ([4, 4, 4] : List Int) =
      (some 4, 14) := by
    rw [Resources.Selection.selectRun_small 1 [4, 4, 4] (by decide) (by decide)]
    decide +kernel
  simpa only [values, trace, selector] using
    observedSelect_run 1 (![4, 4, 4] : Fin 3 → Int)

theorem duplicate_every_work (trace : Transcript 3 Int)
    (observation : Resources.Measured (Option Int) Nat)
    (run : Runs (observedSelect 1) (![4, 4, 4] : Fin 3 → Int) [] trace observation) :
    observation.1 = some 4 ∧ trace.length = 3 ∧ work 2 trace observation = 20 := by
  obtain ⟨ht, ho⟩ := run.deterministic duplicate_run
  exact ⟨by rw [ho], observedSelect_length 1 _ trace observation run,
    by rw [ht, ho]; rfl⟩

/-- Invalid rank is an optional extension, not a valid-rank selection claim. -/
theorem invalid_every_work (input : Fin 3 → Int) (trace : Transcript 3 Int)
    (observation : Resources.Measured (Option Int) Nat)
    (run : Runs (observedSelect 3) input [] trace observation) :
    observation = (none, 5) ∧ work 2 trace observation = 11 := by
  have ho := observedSelect_of_invalid 3 input trace observation run (by decide)
  refine ⟨ho, ?_⟩
  rw [work_acquisition 3 input trace observation run 2, ho]
  rfl

/-- The size20 base uses the actual insertion helper: source count73 and
twenty unit-price coordinate reads give combined work93. -/
theorem cutoff_twenty_run :
    ∃ trace : Transcript 20 Int,
      Runs (observedSelect 9) (fun i : Fin 20 => (i.val : Int)) [] trace (some 9, 73) ∧
      trace.length = 20 ∧ work 1 trace (some 9, 73) = 93 := by
  have selector : Resources.Selection.selectRun 9
      (List.ofFn (fun i : Fin 20 => (i.val : Int))) = (some 9, 73) := by
    rw [Resources.Selection.selectRun_small 9 _
      (by simpa only [List.length_ofFn] using (show 9 < 20 by decide))
      (by simpa only [List.length_ofFn] using (Nat.le_refl 20))]
    decide +kernel
  have run : Runs (observedSelect 9) (fun i : Fin 20 => (i.val : Int)) []
      (List.ofFn (fun i : Fin 20 => (i, (i.val : Int)))) (some 9, 73) := by
    simpa only [selector] using
      observedSelect_run 9 (fun i : Fin 20 => (i.val : Int))
  refine ⟨_, run, observedSelect_length 9 _ _ _ run, ?_⟩
  exact work_acquisition 9 _ _ _ run 1

/-- At size21 the actual worker takes its nested branch. The scalar children
have sizes5 and18, so F21=1419 and unit acquisition gives the budget1440. -/
theorem first_recursive_run :
    ∃ (trace : Transcript 21 Int) (observation : Resources.Measured (Option Int) Nat),
      Runs (observedSelect 10) (fun i : Fin 21 => (i.val : Int)) [] trace observation ∧
      observation.1 = some 10 ∧ trace.length = 21 ∧ work 1 trace observation ≤ 1440 := by
  obtain ⟨trace, observation, run⟩ :=
    observedSelect_total 10 (fun i : Fin 21 => (i.val : Int))
  have ranked : RankedAt (List.ofFn (fun i : Fin 21 => (i.val : Int))) 10 10 := by
    apply ranked_iff_count_bounds.mpr
    decide +kernel
  have scalar : Resources.SelectionRecurrence.F 21 = 1419 := by
    calc
      Resources.SelectionRecurrence.F 21 = Resources.SelectionRecurrence.F 5 +
          Resources.SelectionRecurrence.F 18 + 19 * 21 + 54 :=
        Resources.SelectionRecurrence.F_of_twenty_lt 21 (by decide)
      _ = 1419 := by
        rw [Resources.SelectionRecurrence.F_of_le_twenty 5 (by decide),
          Resources.SelectionRecurrence.F_of_le_twenty 18 (by decide)]
  refine ⟨trace, observation, run,
    (observedSelect_some_iff 10 _ trace observation run 10).mpr ranked,
    observedSelect_length 10 _ trace observation run, ?_⟩
  simpa only [scalar] using work_le_F 10 _ trace observation run 1

/-- All valid ranks provide an actual total correct member of the competitor
class. Correctness has no distinctness premise. -/
theorem total_correct_value_view (k : Fin n) :
    Total (selectedValue (n := n) k.val) ∧ Selects (selectedValue k.val) k :=
  ⟨selectedValue_total k.val, selectedValue_correct k⟩

theorem any_valid_input_contract (k : Fin n) (input : Fin n → Int)
    (trace : Transcript n Int) (observation : Resources.Measured (Option Int) Nat)
    (run : Runs (observedSelect k.val) input [] trace observation)
    (c : Nat) (positive : 1 ≤ c) :
    RankedAt (List.ofFn input) k.val (observation.1.getD 0) ∧
      n ≤ work c trace observation ∧
      work c trace observation ≤ c * n + Resources.SelectionRecurrence.F n :=
  ⟨(observedSelect_valid k input trace observation run).2,
    work_lower_input k.val input trace observation run c positive,
    work_le_F k.val input trace observation run c⟩

/-- Compare with the previously proved two-coordinate minimum protocol.
Both executions and their equal answers are supplied, with a uniform factor. -/
theorem pair_minimum_comparison :
    ∃ K : Nat, ∀ input : Fin 2 → Int, (List.ofFn input).Nodup →
      ∃ (trace : Transcript 2 Int) (observation : Resources.Measured (Option Int) Nat)
        (otherTrace : Transcript 2 Int) (value : Int),
        Runs (observedSelect 0) input [] trace observation ∧
        Runs Examples.CoordinateQueries.pairMinimum input [] otherTrace value ∧
        observation.1 = some value ∧ 2 ≤ otherTrace.length ∧
        work 1 trace observation ≤ K * otherTrace.length := by
  obtain ⟨K, bound⟩ := exists_uniform_optimality
  refine ⟨K, ?_⟩
  intro input distinct
  simpa only [queryWork_unit, show (0 : Fin 2).val = 0 by decide] using
    bound 1 2 (0 : Fin 2) input distinct
      Examples.CoordinateQueries.pairMinimum Examples.CoordinateQueries.pairMinimum_total
      Examples.CoordinateQueries.pairMinimum_correct (by decide)

end Examples.CoordinateSelection

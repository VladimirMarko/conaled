import Applications.Selection.CoordinateQueries
import Mathlib.Data.Fin.VecNotation

/-! Total correct query protocols, adaptive repetition, and their actual charges. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.CoordinateQueries
open Applications.Selection
open Applications.Selection.CoordinateQueries

/-- A nonvacuous one-coordinate protocol: ask, then return the recorded answer. -/
def oneQuery : Protocol 1 Int Int
  | [] => Sum.inr 0
  | (_, a) :: _ => Sum.inl a

theorem oneQuery_run (input : Fin 1 → Int) :
    Runs oneQuery input [] [(0, input 0)] (input 0) :=
  Runs.query rfl (Runs.done rfl)

theorem oneQuery_total : Total oneQuery :=
  fun input => ⟨[(0, input 0)], input 0, oneQuery_run input⟩

theorem oneQuery_correct : Selects oneQuery 0 := by
  intro input trace value run
  have hv := (run.deterministic (oneQuery_run input)).2
  rw [hv]
  have he : List.ofFn input = [input 0] := by
    simp only [List.ofFn_succ, List.ofFn_zero]
  rw [he]
  exact ⟨[], [], List.Perm.refl _, rfl, by simp, by simp⟩

theorem oneQuery_every_run (input : Fin 1 → Int) (trace : Transcript 1 Int)
    (value : Int) (run : Runs oneQuery input [] trace value) :
    trace = [(0, input 0)] ∧ value = input 0 ∧ 1 ≤ trace.length := by
  have h := run.deterministic (oneQuery_run input)
  exact ⟨h.1, h.2, run.length_lower_bound 0 oneQuery_correct
    (fun i j _ => Subsingleton.elim i j)⟩

/-- The number of queries really depends on an observed value. A repeated
coordinate remains a second query and incurs a second charge. -/
def repeatNegative : Protocol 1 Int Int
  | [] => Sum.inr 0
  | [(_, a)] => if a < 0 then Sum.inr 0 else Sum.inl a
  | (_, a) :: _ :: _ => Sum.inl a

theorem repeatNegative_negative_run (input : Fin 1 → Int) (negative : input 0 < 0) :
    Runs repeatNegative input [] [(0, input 0), (0, input 0)] (input 0) :=
  Runs.query rfl (Runs.query (by simp only [repeatNegative, negative, ↓reduceIte])
    (Runs.done rfl))

theorem repeatNegative_nonnegative_run (input : Fin 1 → Int) (nonnegative : 0 ≤ input 0) :
    Runs repeatNegative input [] [(0, input 0)] (input 0) :=
  Runs.query rfl (Runs.done (by
    simp only [repeatNegative, not_lt_of_ge nonnegative, ↓reduceIte]))

theorem repeatNegative_total : Total repeatNegative := by
  intro input
  by_cases negative : input 0 < 0
  · exact ⟨_, _, repeatNegative_negative_run input negative⟩
  · exact ⟨_, _, repeatNegative_nonnegative_run input (le_of_not_gt negative)⟩

theorem repeatNegative_correct : Selects repeatNegative 0 := by
  intro input trace value run
  have hv : value = input 0 := by
    by_cases negative : input 0 < 0
    · exact (run.deterministic (repeatNegative_negative_run input negative)).2
    · exact (run.deterministic
        (repeatNegative_nonnegative_run input (le_of_not_gt negative))).2
  rw [hv]
  exact oneQuery_correct input [(0, input 0)] (input 0) (oneQuery_run input)

theorem repeated_negative_charges (a : Int) (negative : a < 0) :
    Runs repeatNegative (fun _ => a) [] [(0, a), (0, a)] a ∧
      ([(0, a), (0, a)] : Transcript 1 Int).length = 2 ∧
      queryWork (fun _ _ => 3) ([(0, a), (0, a)] : Transcript 1 Int) = 6 := by
  refine ⟨repeatNegative_negative_run _ negative, rfl, ?_⟩
  norm_num [queryWork_constant]

theorem nonnegative_single_charge (a : Int) (nonnegative : 0 ≤ a) :
    Runs repeatNegative (fun _ => a) [] [(0, a)] a ∧
      queryWork (fun _ _ => 3) ([(0, a)] : Transcript 1 Int) = 3 := by
  refine ⟨repeatNegative_nonnegative_run _ nonnegative, ?_⟩
  norm_num [queryWork_constant]

theorem adaptive_run_lower_bound (input : Fin 1 → Int) (trace : Transcript 1 Int)
    (value : Int) (run : Runs repeatNegative input [] trace value) :
    1 ≤ queryWork (fun _ _ => 1) trace :=
  run.work_lower_bound 0 repeatNegative_correct (fun i j _ => Subsingleton.elim i j)
    (fun _ _ => 1) (by intro _ _; exact Nat.le_refl 1)

/-- Reading both coordinates before returning their minimum is correct even
when they are equal. The operation sees only its two recorded answers. -/
def pairMinimum : Protocol 2 Int Int
  | [] => Sum.inr 0
  | [_] => Sum.inr 1
  | (_, b) :: (_, a) :: _ => Sum.inl (min a b)

theorem pairMinimum_run (input : Fin 2 → Int) :
    Runs pairMinimum input [] [(0, input 0), (1, input 1)]
      (min (input 0) (input 1)) :=
  Runs.query rfl (Runs.query rfl (Runs.done rfl))

theorem pairMinimum_total : Total pairMinimum :=
  fun input => ⟨_, _, pairMinimum_run input⟩

theorem pair_minimum_ranked (a b : Int) : RankedAt [a, b] 0 (min a b) := by
  by_cases hab : a ≤ b
  · rw [min_eq_left hab]
    refine ⟨[], [b], List.Perm.refl _, rfl, by simp, ?_⟩
    intro y hy
    have he : y = b := List.mem_singleton.mp hy
    subst y
    exact hab
  · have hba : b ≤ a := le_of_lt (lt_of_not_ge hab)
    rw [min_eq_right hba]
    refine ⟨[], [a], List.Perm.swap a b [], rfl, by simp, ?_⟩
    intro y hy
    have he : y = a := List.mem_singleton.mp hy
    subst y
    exact hba

theorem pairMinimum_correct : Selects pairMinimum 0 := by
  intro input trace value run
  have hv := (run.deterministic (pairMinimum_run input)).2
  rw [hv]
  simpa only [List.ofFn_succ, List.ofFn_zero,
    show ((0 : Fin 1).succ : Fin 2) = 1 by decide,
    show (0 : Fin 2).val = 0 by decide] using
    pair_minimum_ranked (input 0) (input 1)

theorem pairMinimum_distinct_coverage :
    ∀ i : Fin 2, i ∈ ([(0, (8 : Int)), (1, 1)] : Transcript 2 Int).map Prod.fst := by
  have run : Runs pairMinimum (![8, 1] : Fin 2 → Int) [] [(0, 8), (1, 1)] 1 := by
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one,
      show min (8 : Int) 1 = 1 by decide] using
      pairMinimum_run (![8, 1] : Fin 2 → Int)
  exact run.queries_all 0 pairMinimum_correct (by decide +kernel)

theorem pairMinimum_distinct_lower_bound :
    2 ≤ ([(0, (8 : Int)), (1, 1)] : Transcript 2 Int).length := by
  have run : Runs pairMinimum (![8, 1] : Fin 2 → Int) [] [(0, 8), (1, 1)] 1 := by
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one,
      show min (8 : Int) 1 = 1 by decide] using
      pairMinimum_run (![8, 1] : Fin 2 → Int)
  exact run.length_lower_bound 0 pairMinimum_correct (by decide +kernel)

theorem pairMinimum_measured_contract (input : Fin 2 → Int)
    (distinct : Function.Injective input) (trace : Transcript 2 Int) (value : Int)
    (run : Runs pairMinimum input [] trace value) (resource : Nat)
    (contract : 2 * trace.length ≤ resource) : 2 ≤ resource := by
  apply run.resource_lower_bound 0 pairMinimum_correct distinct
    (fun _ _ => 2) (by intro _ _; decide) resource
  simpa only [queryWork_constant] using contract

/-- Replay is useful before correctness is assumed: any unqueried coordinate
can change while the completed observations stay the same. -/
theorem unqueried_update_replays {n : Nat} (next : Protocol n Int Int)
    (input : Fin n → Int) (trace : Transcript n Int) (value : Int)
    (run : Runs next input [] trace value) (i : Fin n)
    (missing : i ∉ trace.map Prod.fst) (z : Int) :
    Runs next (Function.update input i z) [] trace value :=
  run.replay_update_of_not_mem i z missing

theorem total_correct_protocol_has_witness {n : Nat} (next : Protocol n Int Int)
    (k : Fin n) (total : Total next) (correct : Selects next k) :
    ∃ (input : Fin n → Int) (trace : Transcript n Int) (value : Int),
      Function.Injective input ∧ Runs next input [] trace value ∧ n ≤ trace.length :=
  exists_linear_run next k total correct

theorem any_uniform_query_bound_is_linear
    (next : (m : Nat) → Protocol (m + 1) Int Int) (k : (m : Nat) → Fin (m + 1))
    (total : ∀ m, Total (next m)) (correct : ∀ m, Selects (next m) (k m))
    (bound : Nat → Nat)
    (upper : ∀ m input trace value,
      Runs (next m) input [] trace value → trace.length ≤ bound (m + 1)) :
    Asymptotics.IsBigO Filter.atTop (fun m : Nat => (m : ℝ))
      (fun m => (bound m : ℝ)) :=
  linear_isBigO_of_query_bound next k total correct bound upper

end Examples.CoordinateQueries

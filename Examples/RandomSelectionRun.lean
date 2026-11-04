import Applications.Resources.RandomSelectionRun
import Mathlib.Tactic.FinCases

/-! Connected actual-run cases for fresh-occurrence selection. Empty and
invalid inputs retain the explicit Option extension; valid source calls use
zero-based worker ranks and positive one-based public ranks. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.RandomSelectionRun
open Resources.RandomSelection
open Applications.Selection
universe u
variable {α : Type u} [LinearOrder α]

noncomputable section

theorem empty_failure (k : Nat) :
    run k ([] : List α) = PMF.pure (none, ([], 2)) := run_nil k

theorem singleton_execution (x : α) :
    run 0 [x] = PMF.pure (some x, ([(1, 0)], 9)) := by
  simp [run_cons, Resources.RandomQuickSort.uniformIndex_zero, stepRun_eq, partition3_eq_filters]

theorem invalid_singleton :
    run 1 ([7] : List Nat) = PMF.pure (none, ([(1, 0)], 11)) := by
  simp [run_cons, Resources.RandomQuickSort.uniformIndex_zero, stepRun_eq,
    partition3_eq_filters, prepend]

theorem rank_zero_public_failure (xs : List α) :
    select 0 xs = PMF.pure (none, ([], 0)) := by simp [select]

/-- Every supported run has the same value; its two possible traces differ.
The initial pivot at value zero returns immediately. Value one causes one
recursive singleton call and pays both invocations' actual operations. -/
theorem two_key_execution :
    run 0 ([0, 1] : List Nat) =
      PMF.map (fun i : Fin 2 =>
        if i = 0 then (some 0, ([(2, 0)], 11))
        else (some 0, ([(2, 1), (1, 0)], 20)))
        (Resources.RandomQuickSort.uniformIndex 1) := by
  rw [run_cons, PMF.map]
  apply congrArg (PMF.bind _)
  funext i
  fin_cases i <;> simp [stepRun_eq, partition3_eq_filters, singleton_execution, prepend]

/-- Duplicate values still leave two occurrence choices. Both terminate in
one active call, while the measured lookup distinguishes their source costs. -/
theorem duplicate_execution (x : α) :
    run 1 [x, x] =
      PMF.map (fun i : Fin 2 => (some x, ([(2, i.val)], 12 + i.val)))
        (Resources.RandomQuickSort.uniformIndex 1) := by
  rw [run_cons, PMF.map]
  apply congrArg (PMF.bind _)
  funext i
  simp [stepRun_eq, partition3_eq_filters, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem two_key_first_path :
    ((some 0, ([(2, 0)], 11)) : Outcome Nat) ∈ (run 0 [0, 1]).support := by
  rw [two_key_execution]
  apply (PMF.mem_support_map_iff _ _ _).mpr
  exact ⟨0, Resources.RandomQuickSort.mem_support_uniformIndex 1 0, by simp⟩

theorem two_key_long_path :
    ((some 0, ([(2, 1), (1, 0)], 20)) : Outcome Nat) ∈ (run 0 [0, 1]).support := by
  rw [two_key_execution]
  apply (PMF.mem_support_map_iff _ _ _).mpr
  exact ⟨1, Resources.RandomQuickSort.mem_support_uniformIndex 1 1, by simp⟩

theorem same_value_different_scan :
    ((some 0, ([(2, 0)], 11)) : Outcome Nat).1 =
      ((some 0, ([(2, 1), (1, 0)], 20)) : Outcome Nat).1 ∧
    scanVolume [(2, 0)] ≠ scanVolume [(2, 1), (1, 0)] := by
  constructor
  · exact (run_value 0 [0, 1] _ two_key_first_path).trans
      (run_value 0 [0, 1] _ two_key_long_path).symm
  · decide

theorem maximum_scan_on_pair :
    scanVolume [(2, 1), (1, 0)] = 3 ∧
      scanVolume [(2, 1), (1, 0)] ≤ (2 * (2 + 1)) / 2 :=
  ⟨rfl, run_scanVolume_le 0 [0, 1] _ two_key_long_path⟩

theorem bounded_actual_pair_calls :
    scanVolume [(2, 1), (1, 0)] ≤ 20 ∧
      20 ≤ 9 * scanVolume [(2, 1), (1, 0)] + 2 :=
  run_source_bridge 0 [0, 1] _ two_key_long_path

theorem arbitrary_supported_rank (xs : List α) (k : Nat) (result : Outcome α)
    (h : result ∈ (select k xs).support) (a : α) :
    result.1 = some a ↔ 0 < k ∧ RankedAt xs (k - 1) a :=
  select_some_iff k xs result h a

end
end Examples.RandomSelectionRun

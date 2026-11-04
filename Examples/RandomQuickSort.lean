import Applications.Resources.RandomQuickSort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Independent clients of the actual fresh occurrence-pivot execution.
The exercise counts 5, 13, 21 and 25, the three-key masses 1/3 and 2/3,
the two-key append counts 6 and 7, and the duplicate quadratic family were
fixed before implementation. The finite laws below refer to the actual run
and its projections. They do not replace the pending general mean proof.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.RandomQuickSort
open Resources Resources.RandomQuickSort Applications.Sorting
open scoped BigOperators ENNReal
universe u

noncomputable section

local notation "natLt" => (fun a b : Nat => decide (a < b))

/-- There is no inhabited payload instance hidden in empty-input execution. -/
theorem empty_uninhabited :
    run (fun _ _ : Empty => false) [] = PMF.pure ([], (1, 0)) := run_nil _

theorem singleton_source {α : Type u} (lt : α → α → Bool) (x : α) :
    run lt [x] = PMF.pure ([x], (5, 3)) := run_singleton lt x

/-- The selected root factor in run_cons is uniform on occurrences. Two equal
tags occupy two of its three indices. -/
theorem repeated_occurrence_pivot :
    PMF.map (fun i : Fin 3 => ([true, true, false] : List Bool)[i.val])
      (uniformIndex 2) true = (2 : ℝ≥0∞) / 3 := by
  have hc : (Finset.univ.filter (fun i : Fin 3 =>
      ([true, true, false] : List Bool)[i.val] = true)).card = 2 := by decide
  rw [uniformIndex_event, hc]
  norm_num

private theorem pair_exercise (a b : Nat) :
    exerciseLaw natLt [a, b] = PMF.pure 13 := by
  calc
    _ = PMF.bind (uniformIndex 1) (fun _ => PMF.pure 13) := by
      rw [exerciseLaw_cons]
      apply congrArg (PMF.bind _)
      funext i
      fin_cases i
      · by_cases h : b < a <;> simp [h]
      · by_cases h : a < b <;> simp [h]
    _ = _ := PMF.bind_const _ _

theorem two_key_exercise : exerciseLaw natLt [0, 1] = PMF.pure 13 :=
  pair_exercise 0 1

/-- This equality exposes the two actual measured execution outcomes. -/
theorem two_key_execution :
    run natLt [0, 1] =
      PMF.map (fun i : Fin 2 => (([0, 1] : List Nat), (13, if i = 0 then 6 else 7)))
        (uniformIndex 1) := by
  rw [run_cons, PMF.map]
  apply congrArg (PMF.bind _)
  funext i
  fin_cases i <;> simp [Function.comp_def]

theorem two_key_append_mass (cost : Nat) :
    PMF.map (fun result => result.2.2) (run natLt [0, 1]) cost =
      if cost = 6 then (1 : ℝ≥0∞) / 2 else if cost = 7 then 1 / 2 else 0 := by
  rw [two_key_execution, PMF.map_comp, PMF.map_apply, tsum_fintype, Fin.sum_univ_two]
  by_cases h6 : cost = 6
  · subst cost
    norm_num [uniformIndex_apply, Function.comp_def]
  · by_cases h7 : cost = 7
    · subst cost
      norm_num [uniformIndex_apply, Function.comp_def]
    · simp [uniformIndex_apply, Function.comp_def, h6, h7]

/-- The midpoint pivot gives two singleton children; either endpoint gives a
size-two child. The right-hand finite law is proved equal to the actual law. -/
theorem three_key_exercise_law :
    exerciseLaw natLt [0, 1, 2] =
      PMF.map (fun i : Fin 3 => if i = 1 then 21 else 25) (uniformIndex 2) := by
  rw [exerciseLaw_cons, PMF.map]
  apply congrArg (PMF.bind _)
  funext i
  fin_cases i <;> simp [pair_exercise, Function.comp_def]

theorem three_key_exercise_mass (cost : Nat) :
    exerciseLaw natLt [0, 1, 2] cost =
      if cost = 21 then (1 : ℝ≥0∞) / 3 else if cost = 25 then 2 / 3 else 0 := by
  rw [three_key_exercise_law, PMF.map_apply, tsum_fintype, Fin.sum_univ_three]
  by_cases h21 : cost = 21
  · subst cost
    norm_num [uniformIndex_apply, ← ENNReal.coe_inv, ← ENNReal.coe_div]
  · by_cases h25 : cost = 25
    · subst cost
      norm_num [uniformIndex_apply, ← ENNReal.coe_inv, ← ENNReal.coe_add,
        ← ENNReal.coe_div]
    · simp [uniformIndex_apply, h21, h25]

theorem three_key_balanced_mass :
    exerciseLaw natLt [0, 1, 2] 21 = (1 : ℝ≥0∞) / 3 := by
  rw [three_key_exercise_mass]
  simp

theorem three_key_chain_mass :
    exerciseLaw natLt [0, 1, 2] 25 = (2 : ℝ≥0∞) / 3 := by
  rw [three_key_exercise_mass]
  norm_num

/-- Equal-key payload order can change, although their costs are identical. -/
theorem equal_key_tag_execution :
    runOn (Prod.fst : Nat × Bool → Nat) [(7, false), (7, true)] =
      PMF.map (fun i : Fin 2 =>
        if i = 0 then ([(7, false), (7, true)], (13, 6))
        else ([(7, true), (7, false)], (13, 6))) (uniformIndex 1) := by
  rw [runOn, run_cons, PMF.map]
  apply congrArg (PMF.bind _)
  funext i
  fin_cases i <;> simp [Function.comp_def]

theorem equal_key_reversed_mass :
    PMF.map Prod.fst (runOn (Prod.fst : Nat × Bool → Nat) [(7, false), (7, true)])
      [(7, true), (7, false)] = (1 : ℝ≥0∞) / 2 := by
  rw [equal_key_tag_execution, PMF.map_comp, PMF.map_apply, tsum_fintype,
    Fin.sum_univ_two]
  norm_num [uniformIndex_apply, Function.comp_def]

theorem equal_key_reversed_supported :
    ([(7, true), (7, false)], (13, 6)) ∈
      (runOn (Prod.fst : Nat × Bool → Nat) [(7, false), (7, true)]).support := by
  rw [equal_key_tag_execution]
  apply (PMF.mem_support_map_iff _ _ _).mpr
  refine ⟨(1 : Fin 2), mem_support_uniformIndex 1 _, ?_⟩
  simp

/-- A concrete supported output violates stability on equal keys. -/
theorem equal_key_instability :
    ∃ result ∈ (runOn (Prod.fst : Nat × Bool → Nat) [(7, false), (7, true)]).support,
      ¬ Stable Prod.fst [(7, false), (7, true)] result.1 := by
  refine ⟨([(7, true), (7, false)], (13, 6)), equal_key_reversed_supported, ?_⟩
  intro hs
  have h := hs 7
  simp at h

theorem all_equal_three :
    runOn (id : Nat → Nat) [2, 2, 2] = PMF.pure ([2, 2, 2], (25, 9)) := by
  simpa using runOn_replicate (id : Nat → Nat) 2 3

/-- The quadratic duplicate family persists at every size and every payload
universe; no equality, finiteness, or measurable-space instance is supplied. -/
theorem duplicate_payload_family {α : Type u} (tag : α) (n : Nat) :
    runOn (Prod.fst : Nat × α → Nat) (List.replicate n (7, tag)) =
      PMF.pure (List.replicate n (7, tag), (2 * n ^ 2 + 2 * n + 1, 3 * n)) :=
  runOn_replicate Prod.fst (7, tag) n

/-- Distinct tags with the same key do not restore the distinct-key mean regime. -/
theorem constant_key_payload_law {α : Type u} (tags : List α) :
    PMF.map Prod.snd
        (runOn (Prod.fst : Nat × α → Nat) (tags.map (fun tag => (7, tag)))) =
      PMF.pure (2 * tags.length ^ 2 + 2 * tags.length + 1, 3 * tags.length) := by
  have h := jointCostLaw_of_constant_key (Prod.fst : Nat × α → Nat)
    (tags.map (fun tag => (7, tag))) 7 (by
      intro x hx
      obtain ⟨tag, _, rfl⟩ := List.mem_map.mp hx
      rfl)
  simpa only [List.length_map] using h

theorem arbitrary_payload_correct {α : Type u} (xs : List (Nat × α))
    (result : Measured (List (Nat × α)) (Nat × Nat))
    (hr : result ∈ (runOn Prod.fst xs).support) :
    KeySorted Prod.fst result.1 ∧ result.1.Perm xs :=
  runOn_correct Prod.fst xs result hr

theorem arbitrary_payload_exercise_bound {α : Type u} (xs : List (Nat × α))
    (result : Measured (List (Nat × α)) (Nat × Nat))
    (hr : result ∈ (runOn Prod.fst xs).support) :
    result.2.1 ≤ 2 * xs.length ^ 2 + 2 * xs.length + 1 :=
  exerciseCost_le _ xs result hr

theorem arbitrary_payload_append_bridge {α : Type u} (xs : List (Nat × α))
    (result : Measured (List (Nat × α)) (Nat × Nat))
    (hr : result ∈ (runOn Prod.fst xs).support) :
    result.2.1 ≤ result.2.1 + result.2.2 ∧
      result.2.1 + result.2.2 ≤ 2 * result.2.1 :=
  literalCost_comparison _ xs result hr

theorem arbitrary_payload_finite_cost_support {α : Type u} (xs : List (Nat × α)) :
    (exerciseLaw (fun a b => decide (a.1 < b.1)) xs).support.Finite :=
  exerciseLaw_support_finite _ xs

theorem source_append_association :
    QuickSort.appendPivotRun [0, 1] (2 : Nat) [3] = ([0, 1, 2, 3], 5) := by
  simpa using QuickSort.appendPivotRun_exact [0, 1] (2 : Nat) [3]

theorem different_append_association :
    Resources.bind (ListReversal.appendRun [0, 1] [2])
      (fun middle => ListReversal.appendRun middle [3]) =
        (([0, 1, 2, 3] : List Nat), 7) := by
  simp [Resources.bind, ListReversal.appendRun_exact]

end
end Examples.RandomQuickSort

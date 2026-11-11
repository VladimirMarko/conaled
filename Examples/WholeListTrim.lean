import Examples.WholeListTrimContract

/-! Checked applications of whole-list trim to independently certified ordered
prefixes. Pairwise conditions are stronger than adjacent tests. -/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.WholeListTrimExamples

open WholeListTrim WholeListTrimContract

theorem ordered_run : WholeListTrim.run nondecreasing [3, 7, 8, 2, 3] = ([3, 7, 8], 21) := by
  apply Prod.ext
  · exact value_of_spec _ _ _ ordered_spec
  · have h := work_exact nondecreasing [3, 7, 8, 2, 3]
    rw [value_of_spec _ _ _ ordered_spec] at h
    simp only [List.length_cons, List.length_nil] at h
    omega

theorem ordered_fold : foldTrim 1 nondecreasing List.cons [] [3, 7, 8, 2, 3] =
    ([3, 7, 8], 28) := by
  apply Prod.ext
  · rw [fold_value_of_spec _ _ _ _ _ _ ordered_spec]
    rfl
  · have h := fold_work_of_spec 1 nondecreasing List.cons [] _ _ ordered_spec
    simp only [List.length_cons, List.length_nil] at h
    omega

theorem distinct_run : WholeListTrim.run distinct [1, 2, 1] = ([1, 2], 8) := by
  apply Prod.ext
  · exact value_of_spec _ _ _ distinct_spec
  · have h := work_exact distinct [1, 2, 1]
    rw [value_of_spec _ _ _ distinct_spec] at h
    simp only [List.length_cons, List.length_nil] at h
    omega

theorem distinct_fold : foldTrim 1 distinct List.cons [] [1, 2, 1] = ([1, 2], 13) := by
  apply Prod.ext
  · rw [fold_value_of_spec _ _ _ _ _ _ distinct_spec]
    rfl
  · have h := fold_work_of_spec 1 distinct List.cons [] _ _ distinct_spec
    simp only [List.length_cons, List.length_nil] at h
    omega

/-- Adjacent inequality accepts the wrong full input, changing the actual result. -/
def adjacentDistinct (xs : List Nat) : Bool := decide (xs.IsChain (· ≠ ·))

theorem adjacent_wrong_answer :
    WholeListTrim.run adjacentDistinct [1, 2, 1] = ([1, 2, 1], 3) ∧
      (WholeListTrim.run adjacentDistinct [1, 2, 1]).1 ≠ (WholeListTrim.run distinct [1, 2, 1]).1 := by
  have h := run_of_accept adjacentDistinct [1, 2, 1] (Or.inr (by decide))
  constructor
  · exact h
  · rw [h, distinct_run]
    decide

/-- Neither a tail-closure premise nor monotonicity is needed for a single trim. -/
theorem non_tail_closed :
    ¬ ∀ (x : Nat) (xs : List Nat), onlyOneTwo (x :: xs) = true → Accept onlyOneTwo xs := by
  intro h
  have hbad : ¬ Accept onlyOneTwo [2] := by unfold Accept; decide
  exact hbad (h 1 [2] (by decide))

theorem non_tail_closed_trim : WholeListTrim.run onlyOneTwo [1, 2, 3] = ([1, 2], 8) := by
  apply Prod.ext
  · exact value_of_spec _ _ _ only_spec
  · have h := work_exact onlyOneTwo [1, 2, 3]
    rw [value_of_spec _ _ _ only_spec] at h
    simp only [List.length_cons, List.length_nil] at h
    omega

example : WholeListTrim.run onlyOneTwo [1, 2] = ([1, 2], 2) :=
  run_of_accept _ _ (Or.inr (by decide))

/-- Exhaustion returns empty even if the predicate itself rejects it. -/
example : WholeListTrim.run (fun _ : List Nat => false) [] = ([], 0) ∧
    (fun _ : List Nat => false) (trim (fun _ => false) []) = false :=
  ⟨run_empty _, rfl⟩

example : WholeListTrim.run (fun _ : List Nat => false) [1, 2, 3] = ([], 12) := all_false_run _
example : WholeListTrim.run (fun _ : List Nat => true) [1, 2, 3] = ([1, 2, 3], 3) := all_true_run _

example : foldTrim 1 (fun _ : List Nat => false) List.cons [] [] = ([], 1) := by
  simp [foldTrim, run_empty, bind, ListExecution.foldr]

/-- Uniform quadratic worst-family bounds refer to actual rejecting executions. -/
example (n : Nat) (hn : 0 < n) :
    n * n ≤ (WholeListTrim.run (fun _ => false) (List.replicate n (0 : Nat))).2 ∧
      (WholeListTrim.run (fun _ => false) (List.replicate n (0 : Nat))).2 ≤ 2 * n * n := by
  simpa using all_false_bounds (List.replicate n (0 : Nat)) (by simpa using hn)

/-- No eventually uniform quadratic lower bound covers every list/predicate. -/
theorem no_universal_quadratic_lower :
    ¬ ∃ C N : Nat, ∀ n, N ≤ n →
      n * n ≤ C * (WholeListTrim.run (fun _ => true) (List.replicate n (0 : Nat))).2 := by
  rintro ⟨C, N, h⟩
  obtain ⟨n, hn, hbad⟩ := quadratic_lower_obstruction C N
  exact Nat.not_le_of_gt hbad (h n hn)

end Resources.WholeListTrimExamples

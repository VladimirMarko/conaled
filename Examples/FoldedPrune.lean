import Examples.FoldedPruneContract
import Examples.WholeListTrim

/-! Ordered consumers and separating controls for tail-first whole-list pruning. -/
set_option autoImplicit false
set_option warningAsError true
namespace Resources.FoldedPruneExamples
open FoldedPrune WholeListTrimContract

/-- Actual tail-first transitions, with a rejecting middle cut. -/
theorem ordered_steps :
    cut nondecreasing 3 [] = ([3],2) ∧
    cut nondecreasing 2 [3] = ([2,3],3) ∧
    cut nondecreasing 8 [2,3] = ([8],12) ∧
    cut nondecreasing 7 [8] = ([7,8],3) ∧
    cut nondecreasing 3 [7,8] = ([3,7,8],4) := by decide +kernel

theorem ordered_budget : budget (cut nondecreasing) charge [3,7,8,2,3].reverse [] = 33 := by
  obtain ⟨h1,h2,h3,h4,h5⟩ := ordered_steps
  simp [List.reverse_cons, budget, h1,h2,h3,h4,charge]

theorem ordered_run : FoldedPrune.run nondecreasing [3,7,8,2,3] = ([3,7,8],24) := by
  have hv := value_of_spec _ _ _ FoldedPruneContract.ordered_spec
  apply Prod.ext hv
  have hw := work_exact nondecreasing [3,7,8,2,3]
  rw [hv, ordered_budget] at hw
  simp only [potential, List.length_cons, List.length_nil] at hw
  omega

theorem ordered_workload : Resources.run (cut nondecreasing) [3,2,8,7,3] [] =
    ([3,7,8],24) := by
  rw [← show [3,7,8,2,3].reverse = [3,2,8,7,3] from rfl, ← run_eq_workload]
  exact ordered_run

theorem ordered_longest : WholeListTrim.Spec nondecreasing [3,7,8,2,3] [3,7,8] := by
  have h := run_longest_prefix nondecreasing (pairwise_tailClosed (· ≤ ·)) [3,7,8,2,3]
  simpa only [ordered_run] using h

theorem ordered_fold : foldPrune 1 nondecreasing List.cons [] [3,7,8,2,3] = ([3,7,8],31) := by
  apply Prod.ext
  · rw [fold_value_of_spec _ _ _ _ _ _ FoldedPruneContract.ordered_spec]; rfl
  · have h := fold_work_of_spec 1 nondecreasing List.cons [] _ _
      FoldedPruneContract.ordered_spec
    rw [ordered_budget] at h
    simp only [potential, List.length_cons, List.length_nil] at h
    omega

theorem same_value_different_work :
    (FoldedPrune.run nondecreasing [3,7,8,2,3]).1 =
      (WholeListTrim.run nondecreasing [3,7,8,2,3]).1 ∧
    (FoldedPrune.run nondecreasing [3,7,8,2,3]).2 ≠
      (WholeListTrim.run nondecreasing [3,7,8,2,3]).2 := by
  rw [ordered_run, WholeListTrimExamples.ordered_run]
  decide +kernel

theorem distinct_steps : cut distinct 1 [] = ([1],2) ∧
    cut distinct 2 [1] = ([2,1],3) ∧ cut distinct 1 [2,1] = ([1,2],9) := by decide +kernel

theorem distinct_run : FoldedPrune.run distinct [1,2,1] = ([1,2],14) := by
  obtain ⟨h1,h2,h3⟩ := distinct_steps
  simp [FoldedPrune.run, bind, h1,h2,h3]

theorem distinct_fold : foldPrune 1 distinct List.cons [] [1,2,1] = ([1,2],19) := by
  have hv := fold_value_of_longest 1 distinct List.cons [] [1,2,1] [1,2]
    (pairwise_tailClosed (· ≠ ·)) distinct_spec
  apply Prod.ext hv
  simp [foldPrune, bind, distinct_run, ListExecution.foldr_work]

theorem adjacent_wrong :
    FoldedPrune.run WholeListTrimExamples.adjacentDistinct [1,2,1] = ([1,2,1],9) ∧
    (FoldedPrune.run WholeListTrimExamples.adjacentDistinct [1,2,1]).1 ≠
      (FoldedPrune.run distinct [1,2,1]).1 := by
  constructor
  · decide +kernel
  · rw [distinct_run]; decide +kernel

theorem closure_required : FoldedPrune.run onlyOneTwo [1,2] = ([],6) ∧
    WholeListTrim.run onlyOneTwo [1,2] = ([1,2],2) := by decide +kernel

theorem nonclosed_not_longest :
    ¬ WholeListTrim.Spec onlyOneTwo [1,2] (FoldedPrune.run onlyOneTwo [1,2]).1 := by
  rw [closure_required.1]
  intro h
  have hb := h.2.2 [1,2] List.prefix_rfl (Or.inr (by decide +kernel))
  simp at hb

example : FoldedPrune.run (fun _ : List Nat => false) [] = ([],0) := rfl
example : foldPrune 1 (fun _ : List Nat => false) List.cons [] [] = ([],1) := rfl
example : FoldedPrune.run (fun _ : List Nat => false) [1,2,3] = ([],9) := by decide +kernel
example : FoldedPrune.run (fun _ : List Nat => true) [1,2,3] = ([1,2,3],9) := by decide +kernel

/-- A nonempty initial state requires its initial square potential in the identity. -/
theorem initial_boundary :
    Resources.run (cut (fun _ : List Nat => true)) [1] [2,3] = ([1,2,3],4) ∧
    (Resources.run (cut (fun _ : List Nat => true)) [1] [2,3]).2 +
      potential (Resources.run (cut (fun _ : List Nat => true)) [1] [2,3]).1 =
      potential [2,3] + budget (cut (fun _ => true)) charge [1] [2,3] :=
  ⟨by decide +kernel, workload_exact _ _ _⟩

example (p : List Nat → Bool) (xs : List Nat) :
    budget (cut p) charge xs.reverse [] ≤ 3*xs.length*xs.length ∧
      (FoldedPrune.run p xs).2 ≤ 3*xs.length*xs.length :=
  ⟨budget_bound p xs, work_bound p xs⟩
theorem ordered_consumer_costs :
    (foldPrune 1 nondecreasing List.cons [] [3,7,8,2,3]).2 = 31 ∧
    (WholeListTrim.foldTrim 1 nondecreasing List.cons [] [3,7,8,2,3]).2 = 28 := by
  rw [ordered_fold, WholeListTrimExamples.ordered_fold]
  decide

example : (Resources.run (cut (fun _ : List Nat => true)) [1] [2,3]).2 +
    potential (Resources.run (cut (fun _ : List Nat => true)) [1] [2,3]).1 ≠
    budget (cut (fun _ => true)) charge [1] [2,3] := by decide +kernel

end Resources.FoldedPruneExamples

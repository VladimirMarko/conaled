import Applications.Resources.PricedPrune
import Examples.PricedPruneContract
import Examples.FoldedPrune
set_option autoImplicit false
set_option warningAsError true
namespace Resources.PricedPruneExamples
open PricedPrune WholeListTrimContract

theorem ordered_prune (g : Nat) : prune g nondecreasing [3,7,8,2,3] = ([3,7,8],24+7*g) := by
  apply Prod.ext
  · rw [prune_value, FoldedPruneExamples.ordered_run]
  · have h := prune_extra g nondecreasing [3,7,8,2,3]
    rw [FoldedPruneExamples.ordered_run] at h
    simp only [List.length_cons, List.length_nil] at h
    omega

theorem ordered_steps : cut 1 nondecreasing 3 [] = ([3],3) ∧
    cut 1 nondecreasing 2 [3] = ([2,3],4) ∧
    cut 1 nondecreasing 8 [2,3] = ([8],15) ∧
    cut 1 nondecreasing 7 [8] = ([7,8],4) ∧
    cut 1 nondecreasing 3 [7,8] = ([3,7,8],5) := by decide +kernel

theorem ordered_workload : Resources.run (cut 1 nondecreasing) [3,2,8,7,3] [] = ([3,7,8],31) := by
  rw [← show [3,7,8,2,3].reverse = [3,2,8,7,3] from rfl, ← prune_eq_workload]
  exact ordered_prune 1

theorem ordered_budget : budget (cut 1 nondecreasing) (charge 1) [3,7,8,2,3].reverse [] = 43 := by
  rw [budget_exact, FoldedPruneExamples.ordered_budget]; rfl

theorem ordered_fold (g : Nat) : foldPrune g 1 nondecreasing List.cons [] [3,7,8,2,3] =
    ([3,7,8],31+7*g) := by
  apply Prod.ext
  · rw [fold_value_of_spec _ _ _ _ _ _ _ FoldedPruneContract.ordered_spec]; rfl
  · have h := fold_work_of_spec g 1 nondecreasing List.cons [] _ _ FoldedPruneContract.ordered_spec
    rw [FoldedPruneExamples.ordered_budget] at h
    simp only [potential, List.length_cons, List.length_nil] at h
    omega

example : prune 1 nondecreasing [3,7,8,2,3] = ([3,7,8],31) ∧
    foldPrune 1 1 nondecreasing List.cons [] [3,7,8,2,3] = ([3,7,8],38) :=
  ⟨ordered_prune 1, ordered_fold 1⟩
example : prune 2 nondecreasing [3,7,8,2,3] = ([3,7,8],38) ∧
    foldPrune 2 1 nondecreasing List.cons [] [3,7,8,2,3] = ([3,7,8],45) :=
  ⟨ordered_prune 2, ordered_fold 2⟩

example : potential 1 (prune 1 nondecreasing [3,7,8,2,3]).1 = 12 := by
  rw [ordered_prune]; rfl

example : WholeListTrim.Spec nondecreasing [3,7,8,2,3]
    (prune 1 nondecreasing [3,7,8,2,3]).1 :=
  prune_longest _ _ (FoldedPrune.pairwise_tailClosed (· ≤ ·)) _

theorem ordered_trim : trim 1 nondecreasing [3,7,8,2,3] = ([3,7,8],24) := by
  apply Prod.ext
  · rw [trim_value, WholeListTrimExamples.ordered_run]
  · have h := trim_extra 1 nondecreasing [3,7,8,2,3]
    rw [WholeListTrimExamples.ordered_run] at h
    simp only [List.length_cons, List.length_nil] at h
    omega

example : bind (trim 1 nondecreasing [3,7,8,2,3]) (ListExecution.foldr 1 List.cons []) =
    ([3,7,8],31) := by
  rw [ordered_trim]; rfl

theorem distinct_prune : prune 1 distinct [1,2,1] = ([1,2],18) := by
  apply Prod.ext
  · rw [prune_value, FoldedPruneExamples.distinct_run]
  · have h := prune_extra 1 distinct [1,2,1]
    rw [FoldedPruneExamples.distinct_run] at h
    simp only [List.length_cons, List.length_nil] at h
    omega

example : foldPrune 1 1 distinct List.cons [] [1,2,1] = ([1,2],23) := by
  simp [foldPrune, distinct_prune, bind, ListExecution.foldr]

example : (prune 1 WholeListTrimExamples.adjacentDistinct [1,2,1]).1 = [1,2,1] ∧
    (prune 1 distinct [1,2,1]).1 = [1,2] := by
  rw [prune_value, FoldedPruneExamples.adjacent_wrong.1, distinct_prune]
  exact ⟨rfl,rfl⟩

example : prune 1 onlyOneTwo [1,2] = ([],10) ∧ trim 1 onlyOneTwo [1,2] = ([1,2],3) := by
  decide +kernel
example : ¬ WholeListTrim.Spec onlyOneTwo [1,2] (prune 1 onlyOneTwo [1,2]).1 := by
  rw [prune_value]; exact FoldedPruneExamples.nonclosed_not_longest

example (g : Nat) : trim g (fun _ : List Nat => false) [] = ([],g) := by rw [trim]
example (g : Nat) : prune g (fun _ : List Nat => false) [] = ([],0) := rfl
example (g : Nat) : foldPrune g 1 (fun _ : List Nat => false) List.cons [] [] = ([],1) := rfl

example (g : Nat) : trim g (fun _ : List Nat => true) [1,2,3] = ([1,2,3],3+g) := by
  rw [trim]; rfl
example (g : Nat) : trim g (fun _ : List Nat => false) [1,2,3] = ([],12+4*g) := by
  simp [trim]; omega
example (g : Nat) : prune g (fun _ : List Nat => true) [1,2,3] = ([1,2,3],9+3*g) := by
  simp [prune, cut, trim, bind]; omega
example (g : Nat) : prune g (fun _ : List Nat => false) [1,2,3] = ([],9+6*g) := by
  simp [prune, cut, trim, bind]; omega

example : Resources.run (cut 1 (fun _ : List Nat => true)) [1] [2,3] = ([1,2,3],5) ∧
    (Resources.run (cut 1 (fun _ : List Nat => true)) [1] [2,3]).2 +
      potential 1 (Resources.run (cut 1 (fun _ : List Nat => true)) [1] [2,3]).1 =
    potential 1 [2,3] + budget (cut 1 (fun _ => true)) (charge 1) [1] [2,3] :=
  ⟨by decide +kernel, workload_exact _ _ _ _⟩

/-- Finite all-g/all-n claim; thresholds depending on g are outside this negation. -/
theorem no_uniform_finite_coefficient :
    ¬ ∃ C : Nat, ∀ g n, (prune g (fun _ : List Nat => false) (List.replicate n 0)).2 ≤ C*n*n := by
  rintro ⟨C,h⟩
  have hb := h (C+1) 1
  simp [prune, cut, trim, bind] at hb
  omega

theorem no_positive_empty_quadratic (g : Nat) (hg : 0<g) (C : Nat) :
    ¬ (trim g (fun _ : List Nat => false) []).2 ≤ C*0*0 := by
  simp [trim]; omega

-- Archived unit-price statements are checked specializations, not a second runner.
example (p : List Nat → Bool) (xs : List Nat) :
    (trim 1 p xs).2+(WholeListTrim.run p xs).1.length =
      (WholeListTrim.run p xs).2+xs.length+1 := by simpa [Nat.add_assoc] using trim_extra 1 p xs
example (p : List Nat → Bool) (x : Nat) (xs : List Nat) :
    (cut 1 p x xs).2+(FoldedPrune.cut p x xs).1.length =
      (FoldedPrune.cut p x xs).2+xs.length+2 := by simpa [Nat.add_assoc] using cut_extra 1 p x xs
example (p : List Nat → Bool) (xs : List Nat) :
    (prune 1 p xs).2+(FoldedPrune.run p xs).1.length =
      (FoldedPrune.run p xs).2+2*xs.length := by simpa using prune_extra 1 p xs
example (p : List Nat → Bool) (xs : List Nat) :
    (prune 1 p xs).2 ≤ 5*xs.length*xs.length := prune_quadratic_bound 1 p xs
example (p : List Nat → Bool) (xs : List Nat) :
    (trim 1 p xs).2 ≤ xs.length*(xs.length+1)+xs.length+1 := by
  simpa [Nat.add_assoc] using trim_bound 1 p xs
example (p : List Nat → Bool) (xs : List Nat) :
    trim 0 p xs = WholeListTrim.run p xs ∧ prune 0 p xs = FoldedPrune.run p xs :=
  ⟨trim_zero p xs, prune_zero p xs⟩
example (p : List Nat → Bool) (xs : List Nat) :
    (prune 1 p xs).2 + (FoldedPrune.run p xs).1.length*(FoldedPrune.run p xs).1.length +
      (FoldedPrune.run p xs).1.length =
    budget (FoldedPrune.cut p) FoldedPrune.charge xs.reverse [] + 2*xs.length := by
  simpa only [potential, prune_value, Nat.one_mul, Nat.mul_one, Nat.add_assoc]
    using prune_exact 1 p xs

example : (foldPrune 1 1 distinct List.cons [] [1,2,1]).1 = [1,2] :=
  fold_value_of_longest _ _ _ _ _ _ _ (FoldedPrune.pairwise_tailClosed (· ≠ ·)) distinct_spec

end Resources.PricedPruneExamples

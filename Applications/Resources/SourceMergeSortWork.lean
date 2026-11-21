import Applications.Resources.SourceMergeSort
import Applications.Resources.ListMergeWork
import Applications.Resources.SymmetricCosts

/-!
# Complete declared source work of alternating merge sort

The length execution is reused and repriced for its entries and successors.
Splitting counts entries and cons cells. Sorting counts its own entry and Nat
length test, binds the single returned split and actual child results, then
uses the measured-comparator merge. Pattern selection, projections, pairing,
returned-list aliases and observation arithmetic cost zero. This declared
source tariff does not imply compiler-runtime, bit-cost or allocation bounds.
Its rectangle client is documented in `docs/research/fdsa-measured-rectangle-scan.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.SourceMergeSortWork

universe u
variable {α : Type u}
open Applications.Sorting.SourceMergeSort

/-- Reprice the actual existing traversal: entries plus executed successors. -/
def lengthRun (xs : List α) : Measured Nat Nat :=
  let r := SymmetricCosts.lengthRun xs
  (r.1, r.2 + r.1)

theorem lengthRun_exact (xs : List α) :
    lengthRun xs = (xs.length, 2 * xs.length + 1) := by
  simp only [lengthRun, SymmetricCosts.lengthRun_exact]
  congr 1
  omega

@[simp] theorem lengthRun_nil : lengthRun ([] : List α) = (0, 1) := rfl

/-- The repricing follows the original successor recursion without a new traversal. -/
theorem lengthRun_cons (x : α) (xs : List α) :
    lengthRun (x :: xs) = ((lengthRun xs).1 + 1, (lengthRun xs).2 + 2) := by
  simp only [lengthRun_exact, List.length_cons]
  congr 1

/-- Actual alternating halves, charging each invocation and constructed cons. -/
def splitRun : List α → Measured (List α × List α) Nat
  | [] => (([], []), 1)
  | [x] => (([x], []), 2)
  | x :: y :: xs =>
      Resources.bind (splitRun xs) (fun halves => ((x :: halves.1, y :: halves.2), 3))

@[simp] theorem splitRun_nil : splitRun ([] : List α) = (([], []), 1) := rfl

@[simp] theorem splitRun_singleton (x : α) : splitRun [x] = (([x], []), 2) := rfl

theorem splitRun_cons_cons (x y : α) (xs : List α) :
    splitRun (x :: y :: xs) =
      Resources.bind (splitRun xs) (fun halves => ((x :: halves.1, y :: halves.2), 3)) := rfl

theorem splitRun_exact (xs : List α) :
    splitRun xs = (split xs, xs.length + xs.length / 2 + 1) := by
  cases xs with
  | nil => simp [splitRun, split]
  | cons x xs =>
      cases xs with
      | nil => simp [splitRun, split]
      | cons y ys =>
          rw [splitRun_cons_cons, splitRun_exact ys]
          simp only [Resources.bind, split_cons_cons, List.length_cons]
          congr 1
          omega
termination_by xs.length

theorem splitRun_value (xs : List α) : (splitRun xs).1 = split xs := by
  rw [splitRun_exact]

theorem splitRun_cost_le (xs : List α) : (splitRun xs).2 ≤ 2 * xs.length + 1 := by
  rw [splitRun_exact]
  have h := Nat.div_le_self xs.length 2
  omega

/-- One actual length result selects the branch; one actual split supplies both
children, and their returned lists supply the actual measured merge. -/
def run (cmpRun : α → α → Measured Bool Nat) (xs : List α) : Measured (List α) Nat :=
  let size := lengthRun xs
  if h : size.1 ≤ 1 then (xs, size.2 + 2)
  else
    let divided := splitRun xs
    let sorted :=
      Resources.bind (run cmpRun divided.1.1) fun left =>
        Resources.bind (run cmpRun divided.1.2) fun right =>
          ListMergeWork.run cmpRun left right
    (sorted.1, size.2 + 2 + divided.2 + sorted.2)
termination_by xs.length
decreasing_by
  all_goals
    simp only [splitRun_value]
    have hn : 1 < xs.length := by
      change ¬ (lengthRun xs).1 ≤ 1 at h
      rw [lengthRun_exact] at h
      omega
    have hs := split_length_lt xs hn
    omega

theorem run_of_length_le (cmpRun : α → α → Measured Bool Nat) (xs : List α)
    (h : xs.length ≤ 1) : run cmpRun xs = (xs, 2 * xs.length + 3) := by
  rw [run]
  simp [lengthRun_exact, h, Nat.add_assoc]

theorem run_step (cmpRun : α → α → Measured Bool Nat) (xs : List α)
    (h : 1 < xs.length) :
    run cmpRun xs =
      let result := Resources.bind (splitRun xs) fun halves =>
        Resources.bind (run cmpRun halves.1) fun left =>
          Resources.bind (run cmpRun halves.2) fun right =>
            ListMergeWork.run cmpRun left right
      (result.1, 2 * xs.length + 3 + result.2) := by
  rw [run]
  have hn : ¬ xs.length ≤ 1 := by omega
  simp [lengthRun_exact, hn, Resources.bind, Nat.add_assoc]

@[simp] theorem run_nil (cmpRun : α → α → Measured Bool Nat) :
    run cmpRun [] = ([], 3) := by
  simpa using run_of_length_le cmpRun [] (by simp)

@[simp] theorem run_singleton (cmpRun : α → α → Measured Bool Nat) (x : α) :
    run cmpRun [x] = ([x], 5) := by
  simpa using run_of_length_le cmpRun [x] (by simp)

theorem run_value (cmpRun : α → α → Measured Bool Nat) (xs : List α) :
    (run cmpRun xs).1 = sortBy (fun x y => (cmpRun x y).1) xs := by
  by_cases h : xs.length ≤ 1
  · rw [run_of_length_le cmpRun xs h, sortBy_of_length_le _ xs h]
  · rw [run_step cmpRun xs (by omega), sortBy_step _ xs (by omega)]
    simp only [Resources.bind, splitRun_value, ListMergeWork.run_value]
    rw [run_value cmpRun (split xs).1, run_value cmpRun (split xs).2]
termination_by xs.length
decreasing_by
  all_goals have hs := split_length_lt xs (by omega); omega

theorem run_perm (cmpRun : α → α → Measured Bool Nat) (xs : List α) :
    (run cmpRun xs).1.Perm xs := by
  rw [run_value]
  exact sortBy_perm _ xs

theorem run_length (cmpRun : α → α → Measured Bool Nat) (xs : List α) :
    (run cmpRun xs).1.length = xs.length := (run_perm cmpRun xs).length_eq

/-- The exact recursive work retains the actual child results in the merge. -/
theorem run_cost_step (cmpRun : α → α → Measured Bool Nat) (xs : List α)
    (h : 1 < xs.length) :
    (run cmpRun xs).2 = 2 * xs.length + 3 + (splitRun xs).2 +
      (run cmpRun (split xs).1).2 + (run cmpRun (split xs).2).2 +
      (ListMergeWork.run cmpRun (run cmpRun (split xs).1).1
        (run cmpRun (split xs).2).1).2 := by
  simp [run_step cmpRun xs h, Resources.bind, splitRun_value, Nat.add_assoc]

/-- The complete local work is bounded using the actual children's lengths. -/
theorem run_cost_step_le (cmpRun : α → α → Measured Bool Nat) (xs : List α)
    (C : Nat) (hC : ∀ x y, (cmpRun x y).2 ≤ C) (h : 1 < xs.length) :
    (run cmpRun xs).2 ≤ (run cmpRun (split xs).1).2 +
      (run cmpRun (split xs).2).2 + (C + 6) * xs.length + 5 := by
  have merge := ListMergeWork.run_cost_le cmpRun
    (run cmpRun (split xs).1).1 (run cmpRun (split xs).2).1 C hC
  simp only [run_length, split_length_add] at merge
  have splitting := splitRun_cost_le xs
  rw [run_cost_step cmpRun xs h]
  simp only [Nat.add_mul] at merge ⊢
  omega

/-- The nonempty strengthening pays every internal node's constant overhead.
The empty input has positive work and is deliberately excluded here. -/
theorem run_cost_le_size (cmpRun : α → α → Measured Bool Nat) (xs : List α)
    (C : Nat) (hC : ∀ x y, (cmpRun x y).2 ≤ C) (positive : 0 < xs.length) :
    (run cmpRun xs).2 + 5 ≤
      (C + 6) * Resources.SourceMergeSort.splitSizeCost xs.length + 10 * xs.length := by
  by_cases short : xs.length ≤ 1
  · have one : xs.length = 1 := by omega
    rw [run_of_length_le cmpRun xs short]
    simp [one, Resources.SourceMergeSort.splitSizeCost]
  · have lengths := split_lengths xs
    have left := run_cost_le_size cmpRun (split xs).1 C hC (by omega)
    have right := run_cost_le_size cmpRun (split xs).2 C hC (by omega)
    have step := run_cost_step_le cmpRun xs C hC (by omega)
    have recurrence : Resources.SourceMergeSort.splitSizeCost xs.length =
        xs.length + Resources.SourceMergeSort.splitSizeCost (split xs).1.length +
          Resources.SourceMergeSort.splitSizeCost (split xs).2.length := by
      conv_lhs => rw [Resources.SourceMergeSort.splitSizeCost]
      simp only [dite_eq_right short, lengths.1, lengths.2]
    have ten_lengths : 10 * (split xs).1.length + 10 * (split xs).2.length =
        10 * xs.length := by
      rw [← Nat.mul_add, split_length_add]
    rw [recurrence]
    simp only [Nat.mul_add]
    omega
termination_by xs.length
decreasing_by
  all_goals have hs := split_length_lt xs (by omega); omega

private theorem splitSizeCost_le_clog (xs : List α) :
    Resources.SourceMergeSort.splitSizeCost xs.length ≤ xs.length * Nat.clog 2 xs.length := by
  simpa only [Resources.SourceMergeSort.splitVisits_eq_splitSizeCost] using
    Resources.SourceMergeSort.splitVisits_le_clog (fun (_ : α) (_ : α) => false) xs

/-- A pointwise all-input bound, including empty cost three and singleton cost five. -/
theorem run_cost_le_clog (cmpRun : α → α → Measured Bool Nat) (xs : List α)
    (C : Nat) (hC : ∀ x y, (cmpRun x y).2 ≤ C) :
    (run cmpRun xs).2 ≤ (C + 6) * xs.length * Nat.clog 2 xs.length +
      10 * xs.length + 3 := by
  by_cases empty : xs.length = 0
  · have hx : xs = [] := List.length_eq_zero_iff.mp empty
    subst xs
    simp
  · have positive : 0 < xs.length := by omega
    have hs := run_cost_le_size cmpRun xs C hC positive
    have hl := Nat.mul_le_mul_left (C + 6) (splitSizeCost_le_clog xs)
    rw [Nat.mul_assoc]
    omega

/-- Fixed uniformly bounded comparator work gives ordinary eventual n log n growth. -/
theorem run_cost_isBigO (cmpRun : α → α → Measured Bool Nat)
    (inputs : Nat → List α) (C : Nat) (hC : ∀ x y, (cmpRun x y).2 ≤ C)
    (hlen : ∀ n, (inputs n).length = n) :
    Asymptotics.IsBigO Filter.atTop (fun n => ((run cmpRun (inputs n)).2 : ℝ))
      (fun n => (n : ℝ) * Real.logb 2 n) := by
  apply Resources.isBigO_of_clog_two_bound (C := C + 16) (N := 2)
  intro n hn
  have positive : 0 < (inputs n).length := by rw [hlen]; omega
  have hs := run_cost_le_size cmpRun (inputs n) C hC positive
  have hl := Nat.mul_le_mul_left (C + 6) (splitSizeCost_le_clog (inputs n))
  rw [hlen] at hs hl
  have log_one : 1 ≤ Nat.clog 2 n := Nat.clog_pos (by decide) (by omega)
  have n_le : n ≤ n * Nat.clog 2 n := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left n log_one
  have ten := Nat.mul_le_mul_left 10 n_le
  calc
    (run cmpRun (inputs n)).2 ≤ (C + 6) * (n * Nat.clog 2 n) + 10 * n := by omega
    _ ≤ (C + 6) * (n * Nat.clog 2 n) + 10 * (n * Nat.clog 2 n) :=
      Nat.add_le_add_left ten _
    _ = (C + 16) * (n * Nat.clog 2 n) := by ring

end Resources.SourceMergeSortWork

import Applications.Sorting.SourceMergeSort
import Applications.Resources.ListMerge
import Applications.Resources.Growth
import Mathlib.Data.Nat.Log

/-!
# Executed work of the VFA alternating merge sort

The splitter traverses the actual input and returns its order-preserving
alternating halves, charging one element visit per input element. The sorting
execution uses these returned halves, recursively sorts them, and passes the
returned lists to the shared measured merge. It observes the pair
`(split element visits, merge head comparisons)`. Its base cases do not split.

These are abstract unit charges. They exclude comparator implementation work,
function-entry overhead and length-test costs. The linear splitter charge and
the comparison charge both have an all-length ceiling-log bound; their sum
therefore has the same ordinary `O(n log n)` growth. Array auxiliary-space
claims do not establish physical allocation, sharing, collection or peak live
space for this list execution.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.SourceMergeSort

universe u v
variable {α : Type u}

open Applications.Sorting.SourceMergeSort

/-- Traverse and reconstruct the actual alternating halves. Each encountered
element costs one visit; the empty case costs zero. -/
def splitRun : List α → Measured (List α × List α) Nat
  | [] => (([], []), 0)
  | [x] => (([x], []), 1)
  | x :: y :: xs =>
      bind (splitRun xs) (fun halves => ((x :: halves.1, y :: halves.2), 2))

/-- Both the returned halves and their exact element-visit count are obtained
from the recursive execution. -/
theorem splitRun_exact (xs : List α) :
    splitRun xs = (split xs, xs.length) := by
  cases xs with
  | nil => rfl
  | cons x xs =>
      cases xs with
      | nil => rfl
      | cons y ys =>
          simp [splitRun, bind, splitRun_exact ys, split, Nat.add_comm,
            Nat.add_left_comm]
termination_by xs.length

theorem splitRun_value (xs : List α) : (splitRun xs).1 = split xs := by
  rw [splitRun_exact]

theorem splitRun_visits (xs : List α) : (splitRun xs).2 = xs.length := by
  rw [splitRun_exact]

/-- One measured split supplies the recursive arguments. The let-bound result
is used for both its returned halves and its charge, and the recursive results
are bound into the actual measured merge. -/
def run (cmp : α → α → Bool) (xs : List α) : Measured (List α) (Nat × Nat) :=
  if h : xs.length ≤ 1 then pure xs
  else
    let divided := splitRun xs
    let sorted :=
      bind (run cmp divided.1.1) fun left =>
        bind (run cmp divided.1.2) fun right =>
          reweight (fun c => (0, c.1)) (ListMerge.run cmp left right)
    (sorted.1, (divided.2, 0) + sorted.2)
termination_by xs.length
decreasing_by
  · simp only [splitRun_value]
    exact (split_length_lt xs (by omega)).1
  · simp only [splitRun_value]
    exact (split_length_lt xs (by omega)).2

abbrev splitVisits (cmp : α → α → Bool) (xs : List α) : Nat := (run cmp xs).2.1

abbrev comparisons (cmp : α → α → Bool) (xs : List α) : Nat := (run cmp xs).2.2

/-- The sum of the two explicitly declared unit observations. -/
def work (cmp : α → α → Bool) (xs : List α) : Nat :=
  splitVisits cmp xs + comparisons cmp xs

theorem run_of_length_le (cmp : α → α → Bool) (xs : List α)
    (h : xs.length ≤ 1) : run cmp xs = (xs, (0, 0)) := by
  rw [run]
  split
  · rfl
  · omega

/-- The executed split is sequenced before both child executions and merge.
This equation retains the split's actual returned value in the continuation. -/
theorem run_step (cmp : α → α → Bool) (xs : List α) (h : 1 < xs.length) :
    run cmp xs =
      bind (reweight (fun n => (n, 0)) (splitRun xs)) fun halves =>
        bind (run cmp halves.1) fun left =>
          bind (run cmp halves.2) fun right =>
            reweight (fun c => (0, c.1)) (ListMerge.run cmp left right) := by
  rw [run]
  split
  · omega
  · rfl

@[simp] theorem run_nil (cmp : α → α → Bool) :
    run cmp [] = ([], (0, 0)) := run_of_length_le cmp [] (by simp)

@[simp] theorem run_singleton (cmp : α → α → Bool) (x : α) :
    run cmp [x] = ([x], (0, 0)) := run_of_length_le cmp [x] (by simp)

/-- Erasure agrees with the source's whole sorting recurrence, for every
Boolean comparator; no ordering law is needed. -/
theorem run_value (cmp : α → α → Bool) (xs : List α) :
    (run cmp xs).1 = sortBy cmp xs := by
  by_cases h : xs.length ≤ 1
  · rw [run_of_length_le cmp xs h, sortBy_of_length_le cmp xs h]
  · rw [run_step cmp xs (by omega), sortBy_step cmp xs (by omega)]
    simp only [bind_value, reweight_value, ListMerge.run_value, splitRun_value]
    rw [run_value cmp (split xs).1, run_value cmp (split xs).2]
termination_by xs.length
decreasing_by
  · exact (split_length_lt xs (by omega)).1
  · exact (split_length_lt xs (by omega)).2

theorem run_perm (cmp : α → α → Bool) (xs : List α) : (run cmp xs).1.Perm xs := by
  rw [run_value]
  exact sortBy_perm cmp xs

theorem run_length (cmp : α → α → Bool) (xs : List α) :
    (run cmp xs).1.length = xs.length := (run_perm cmp xs).length_eq

theorem splitVisits_of_length_le (cmp : α → α → Bool) (xs : List α)
    (h : xs.length ≤ 1) : splitVisits cmp xs = 0 := by
  simp only [splitVisits, run_of_length_le cmp xs h]

theorem comparisons_of_length_le (cmp : α → α → Bool) (xs : List α)
    (h : xs.length ≤ 1) : comparisons cmp xs = 0 := by
  simp only [comparisons, run_of_length_le cmp xs h]

/-- Each non-base sort traverses its entire input in the splitter. -/
theorem splitVisits_step (cmp : α → α → Bool) (xs : List α) (h : 1 < xs.length) :
    splitVisits cmp xs = xs.length + splitVisits cmp (split xs).1 +
      splitVisits cmp (split xs).2 := by
  simp [splitVisits, run_step cmp xs h, bind, reweight, splitRun_value,
    splitRun_visits, Nat.add_assoc]

/-- Independent size recurrence for all splitter visits in the sorting tree. -/
def splitSizeCost (n : Nat) : Nat :=
  if _h : n ≤ 1 then 0
  else n + splitSizeCost ((n + 1) / 2) + splitSizeCost (n / 2)
termination_by n
decreasing_by all_goals omega

/-- The actual split-visit projection realizes the independent size recurrence. -/
theorem splitVisits_eq_splitSizeCost (cmp : α → α → Bool) (xs : List α) :
    splitVisits cmp xs = splitSizeCost xs.length := by
  by_cases h : xs.length ≤ 1
  · rw [splitVisits_of_length_le cmp xs h, splitSizeCost]
    split
    · rfl
    · omega
  · rw [splitVisits_step cmp xs (by omega),
      splitVisits_eq_splitSizeCost cmp (split xs).1,
      splitVisits_eq_splitSizeCost cmp (split xs).2]
    conv_rhs => rw [splitSizeCost]
    simp only [dite_eq_right h, (split_lengths xs).1, (split_lengths xs).2]
termination_by xs.length
decreasing_by
  all_goals have hl := split_length_lt xs (by omega); omega

/-- Splitting work depends only on length, even across unrelated element types
and comparators; the comparison projection need not share this property. -/
theorem splitVisits_same_length {β : Type v} (cmp : α → α → Bool)
    (other : β → β → Bool) (xs : List α) (ys : List β)
    (h : xs.length = ys.length) : splitVisits cmp xs = splitVisits other ys := by
  rw [splitVisits_eq_splitSizeCost, splitVisits_eq_splitSizeCost, h]

/-- The comparison count consumes the actual recursively sorted halves. -/
theorem comparisons_step (cmp : α → α → Bool) (xs : List α) (h : 1 < xs.length) :
    comparisons cmp xs = comparisons cmp (split xs).1 +
      comparisons cmp (split xs).2 +
      ListMerge.comparisons cmp (sortBy cmp (split xs).1)
        (sortBy cmp (split xs).2) := by
  simp [comparisons, run_step cmp xs h, bind, reweight, splitRun_value,
    ListMerge.comparisons, run_value, Nat.add_assoc]

theorem comparisons_step_le (cmp : α → α → Bool) (xs : List α) (h : 1 < xs.length) :
    comparisons cmp xs ≤ comparisons cmp (split xs).1 +
      comparisons cmp (split xs).2 + xs.length := by
  rw [comparisons_step cmp xs h]
  have hm := ListMerge.comparisons_le cmp
    (sortBy cmp (split xs).1) (sortBy cmp (split xs).2)
  rw [sortBy_length, sortBy_length, split_length_add] at hm
  exact Nat.add_le_add_left hm _

private theorem balanced_bound (n a b ca cb : Nat) (hn : 2 ≤ n)
    (hlen : a + b = n) (ha : a ≤ (n + 1) / 2) (hb : b ≤ (n + 1) / 2)
    (hca : ca ≤ a * Nat.clog 2 a) (hcb : cb ≤ b * Nat.clog 2 b) :
    ca + cb + n ≤ n * Nat.clog 2 n := by
  have hcl := Nat.clog_mono_right 2 ha
  have hcr := Nat.clog_mono_right 2 hb
  have hrec := Nat.clog_of_two_le (b := 2) (n := n) (by decide) hn
  have heq : (n + 2 - 1) / 2 = (n + 1) / 2 := by omega
  rw [heq] at hrec
  calc
    ca + cb + n ≤ a * Nat.clog 2 a + b * Nat.clog 2 b + n :=
      Nat.add_le_add_right (Nat.add_le_add hca hcb) _
    _ ≤ a * Nat.clog 2 ((n + 1) / 2) + b * Nat.clog 2 ((n + 1) / 2) + n :=
      Nat.add_le_add_right
        (Nat.add_le_add (Nat.mul_le_mul_left _ hcl) (Nat.mul_le_mul_left _ hcr)) _
    _ = n * Nat.clog 2 n := by
      rw [← Nat.add_mul, hlen, hrec, Nat.mul_add, Nat.mul_one]

/-- Both observations have the same uniform bound for arbitrary comparators. -/
theorem costs_le_clog (cmp : α → α → Bool) (xs : List α) :
    splitVisits cmp xs ≤ xs.length * Nat.clog 2 xs.length ∧
      comparisons cmp xs ≤ xs.length * Nat.clog 2 xs.length := by
  by_cases h : xs.length ≤ 1
  · rw [splitVisits_of_length_le cmp xs h, comparisons_of_length_le cmp xs h]
    exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  · have hl := costs_le_clog cmp (split xs).1
    have hr := costs_le_clog cmp (split xs).2
    have hlen := split_length_add xs
    have hs := split_lengths xs
    have ha : (split xs).1.length ≤ (xs.length + 1) / 2 := by omega
    have hb : (split xs).2.length ≤ (xs.length + 1) / 2 := by omega
    constructor
    · rw [splitVisits_step cmp xs (by omega)]
      have bound := balanced_bound xs.length _ _ _ _ (by omega) hlen ha hb hl.1 hr.1
      omega
    · exact (comparisons_step_le cmp xs (by omega)).trans
        (balanced_bound xs.length _ _ _ _ (by omega) hlen ha hb hl.2 hr.2)
termination_by xs.length
decreasing_by
  · exact (split_length_lt xs (by omega)).1
  · exact (split_length_lt xs (by omega)).2

theorem splitVisits_le_clog (cmp : α → α → Bool) (xs : List α) :
    splitVisits cmp xs ≤ xs.length * Nat.clog 2 xs.length := (costs_le_clog cmp xs).1

theorem comparisons_le_clog (cmp : α → α → Bool) (xs : List α) :
    comparisons cmp xs ≤ xs.length * Nat.clog 2 xs.length := (costs_le_clog cmp xs).2

theorem work_le_clog (cmp : α → α → Bool) (xs : List α) :
    work cmp xs ≤ 2 * (xs.length * Nat.clog 2 xs.length) := by
  have hs := splitVisits_le_clog cmp xs
  have hc := comparisons_le_clog cmp xs
  unfold work
  omega

/-- Explicit real-log bound from length two, with both unit charges included. -/
theorem work_le_real_log (cmp : α → α → Bool) (xs : List α)
    (hlen : 2 ≤ xs.length) :
    (work cmp xs : ℝ) ≤ 4 * (xs.length : ℝ) * Real.logb 2 xs.length := by
  have hb : (work cmp xs : ℝ) ≤
      2 * ((xs.length : ℝ) * (Nat.clog 2 xs.length : ℝ)) := by
    exact_mod_cast work_le_clog cmp xs
  have hlog := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (Resources.clog_two_cast_le_two_logb xs.length hlen)
      (Nat.cast_nonneg xs.length)) (show (0 : ℝ) ≤ 2 by norm_num)
  calc
    (work cmp xs : ℝ) ≤ 2 * ((xs.length : ℝ) * (Nat.clog 2 xs.length : ℝ)) := hb
    _ ≤ 2 * ((xs.length : ℝ) * (2 * Real.logb 2 xs.length)) := hlog
    _ = 4 * (xs.length : ℝ) * Real.logb 2 xs.length := by ring

theorem splitVisits_isBigO (cmp : α → α → Bool) (inputs : Nat → List α)
    (hlen : ∀ n, (inputs n).length = n) :
    Asymptotics.IsBigO Filter.atTop (fun n => (splitVisits cmp (inputs n) : ℝ))
      (fun n => (n : ℝ) * Real.logb 2 n) := by
  apply Resources.isBigO_of_clog_two_bound (C := 1) (N := 0)
  intro n _
  simpa only [hlen, one_mul] using splitVisits_le_clog cmp (inputs n)

theorem comparisons_isBigO (cmp : α → α → Bool) (inputs : Nat → List α)
    (hlen : ∀ n, (inputs n).length = n) :
    Asymptotics.IsBigO Filter.atTop (fun n => (comparisons cmp (inputs n) : ℝ))
      (fun n => (n : ℝ) * Real.logb 2 n) := by
  apply Resources.isBigO_of_clog_two_bound (C := 1) (N := 0)
  intro n _
  simpa only [hlen, one_mul] using comparisons_le_clog cmp (inputs n)

theorem work_isBigO (cmp : α → α → Bool) (inputs : Nat → List α)
    (hlen : ∀ n, (inputs n).length = n) :
    Asymptotics.IsBigO Filter.atTop (fun n => (work cmp (inputs n) : ℝ))
      (fun n => (n : ℝ) * Real.logb 2 n) := by
  apply Resources.isBigO_of_clog_two_bound (C := 2) (N := 0)
  intro n _
  simpa only [hlen] using work_le_clog cmp (inputs n)

end Resources.SourceMergeSort

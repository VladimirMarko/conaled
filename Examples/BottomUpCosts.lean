import Applications.Resources.BottomUpSorting
import Examples.BottomUpSorting

/-!
# Connected bottom-up comparison observations

The ragged pass costs two comparisons. Three equal singleton runs cost one
comparison in either first pass; ordinary repeated merging then costs two more,
while the reversed pass costs one more. Thus their total counts are three and
two, despite equal unlabelled results. The tagged versions retain the actual
different payload orders. None of these observations counts outer traversal,
construction, allocation or compiled runtime.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.BottomUpCosts

open Applications.Sorting
open _root_.Resources.BottomUpSorting
open _root_.Examples.BottomUpSorting (natCompare raggedRuns)
universe u
variable {α : Type u}

theorem empty_and_single_run (cmp : α → α → Bool) (xs : List α) :
    allRun cmp [] = ([], 0) ∧ allRun cmp [xs] = (xs, 0) ∧
      allRevRun cmp [] = ([], 0) ∧ allRevRun cmp [xs] = (xs, 0) :=
  ⟨allRun_nil cmp, allRun_singleton cmp xs,
    allRevRun_nil cmp, allRevRun_singleton cmp xs⟩

/-- A zero-comparison sole run can still be unsorted; the run invariant matters. -/
theorem unsorted_single_run :
    allRun natCompare [[2, 1]] = ([2, 1], 0) ∧
      ¬ KeySorted id (allRun natCompare [[2, 1]]).1 := by
  refine ⟨allRun_singleton _ _, ?_⟩
  rw [allRun_value]
  exact BottomUpSorting.singleton_unsorted_run

/-- Ragged lengths, an empty run, a duplicate and an odd leftover in one actual pass. -/
theorem ragged_observation :
    pairsRun natCompare raggedRuns = ([[1, 2, 3], [0, 4], [2, 5]], 2) := by
  apply Prod.ext
  · exact (pairsRun_value natCompare raggedRuns).trans BottomUpSorting.ragged_pass_value
  · change pairsComparisons natCompare raggedRuns = 2
    simp [raggedRuns, pairsComparisons_step, natCompare,
      Resources.ListMerge.comparisons_cons_cons,
      Resources.ListMerge.comparisons_nil_left, Resources.ListMerge.comparisons_nil_right]

theorem nonempty_accumulator_observation :
    pairsRevRun natCompare [[99], [], [42, 43]] raggedRuns =
      ([[2, 5], [0, 4], [1, 2, 3], [99], [], [42, 43]], 2) := by
  rw [pairsRevRun_eq, ragged_observation]
  rfl

/-- Neither accumulator content nor its sortedness changes the executed pair comparisons. -/
theorem accumulator_cost_independent (cmp : α → α → Bool)
    (acc₁ acc₂ xss : List (List α)) :
    pairsRevComparisons cmp acc₁ xss = pairsRevComparisons cmp acc₂ xss :=
  (pairsRevComparisons_eq cmp acc₁ xss).trans (pairsRevComparisons_eq cmp acc₂ xss).symm

theorem three_equal_first_pass :
    pairsRun natCompare [[0], [0], [0]] = ([[0, 0], [0]], 1) := by
  simp [pairsRun_step, natCompare, Resources.ListMerge.run_cons_cons,
    Resources.ListMerge.run_nil_left, Resources.bind, Resources.reweight, Resources.pure]

theorem three_equal_reversed_first_pass :
    pairsRevRun natCompare [] [[0], [0], [0]] = ([[0], [0, 0]], 1) := by
  rw [pairsRevRun_eq, three_equal_first_pass]
  rfl

/-- Exactly two runs perform one measured merge and an uncharged singleton dispatch. -/
theorem all_two_runs (cmp : α → α → Bool) (xs ys : List α) :
    allRun cmp [xs, ys] = Resources.reweight Prod.fst (Resources.ListMerge.run cmp xs ys) := by
  rw [allRun_step, pairsRun_step]
  simp [Resources.bind, Resources.reweight, Resources.pure]

theorem all_reversed_two_runs (cmp : α → α → Bool) (xs ys : List α) :
    allRevRun cmp [xs, ys] = Resources.reweight Prod.fst (Resources.ListMerge.run cmp xs ys) := by
  rw [allRevRun_step, pairsRevRun_step]
  simp [Resources.bind, Resources.reweight]

/-- The first returned run is the left operand of the next ordinary merge. -/
theorem ordinary_three_run (cmp : α → α → Bool) (a b c : α) :
    run cmp [a, b, c] =
      Resources.bind (Resources.reweight Prod.fst (Resources.ListMerge.run cmp [a] [b]))
        (fun merged => Resources.reweight Prod.fst (Resources.ListMerge.run cmp merged [c])) := by
  change allRun cmp [[a], [b], [c]] = _
  rw [allRun_step, pairsRun_step]
  simp [Resources.bind, Resources.reweight, Resources.pure, all_two_runs]

/-- Reversing the pass makes that same returned run the right operand instead. -/
theorem reversed_three_run (cmp : α → α → Bool) (a b c : α) :
    revRun cmp [a, b, c] =
      Resources.bind (Resources.reweight Prod.fst (Resources.ListMerge.run cmp [a] [b]))
        (fun merged => Resources.reweight Prod.fst (Resources.ListMerge.run cmp [c] merged)) := by
  change allRevRun cmp [[a], [b], [c]] = _
  rw [allRevRun_step, pairsRevRun_step]
  simp [Resources.bind, Resources.reweight, all_reversed_two_runs]

theorem ordinary_three_equal : run natCompare [0, 0, 0] = ([0, 0, 0], 3) := by
  simp [ordinary_three_run, natCompare, Resources.ListMerge.run_cons_cons,
    Resources.ListMerge.run_nil_left, Resources.bind, Resources.reweight]

theorem reversed_three_equal : revRun natCompare [0, 0, 0] = ([0, 0, 0], 2) := by
  simp [reversed_three_run, natCompare, Resources.ListMerge.run_cons_cons,
    Resources.ListMerge.run_nil_left, Resources.bind, Resources.reweight]

/-- Equal per-pass counts do not give equal counts after the run order changes. -/
theorem same_pass_costs_different_totals :
    pairsComparisons natCompare [[0], [0], [0]] =
        pairsRevComparisons natCompare [] [[0], [0], [0]] ∧
      (run natCompare [0, 0, 0]).1 = (revRun natCompare [0, 0, 0]).1 ∧
      comparisons natCompare [0, 0, 0] ≠ revComparisons natCompare [0, 0, 0] := by
  refine ⟨(pairsRevComparisons_eq _ _ _).symm, ?_⟩
  rw [comparisons, revComparisons, ordinary_three_equal, reversed_three_equal]
  decide

theorem ordinary_tagged_equal (first middle last : α) :
    run (fun a b : Nat × α => decide (a.1 ≤ b.1))
        [(0, first), (0, middle), (0, last)] =
      ([(0, first), (0, middle), (0, last)], 3) := by
  simp [ordinary_three_run, Resources.ListMerge.run_cons_cons,
    Resources.ListMerge.run_nil_left, Resources.bind, Resources.reweight]

theorem reversed_tagged_equal (first middle last : α) :
    revRun (fun a b : Nat × α => decide (a.1 ≤ b.1))
        [(0, first), (0, middle), (0, last)] =
      ([(0, last), (0, first), (0, middle)], 2) := by
  simp [reversed_three_run, Resources.ListMerge.run_cons_cons,
    Resources.ListMerge.run_nil_left, Resources.bind, Resources.reweight]

/-- Measured erasure retains the existing concrete failure of stability. -/
theorem measured_tail_not_stable :
    ¬ Stable Prod.fst ([(0, "first"), (0, "middle"), (0, "last")] : List (Nat × String))
      (revRun (fun a b => decide (a.1 ≤ b.1))
        [(0, "first"), (0, "middle"), (0, "last")]).1 := by
  rw [revRun_value]
  exact BottomUpSorting.tail_sort_need_not_be_stable

theorem raw_occurrences_and_bounds (cmp : α → α → Bool) (xs : List α) :
    (run cmp xs).1.Perm xs ∧
      comparisons cmp xs ≤ xs.length * Nat.clog 2 xs.length ∧
      (revRun cmp xs).1.Perm xs ∧
      revComparisons cmp xs ≤ xs.length * Nat.clog 2 xs.length :=
  ⟨run_perm cmp xs, comparisons_le_clog cmp xs,
    revRun_perm cmp xs, revComparisons_le_clog cmp xs⟩

/-- Local comparator compatibility suffices for the measured returned values as well. -/
theorem local_comparator_values :
    KeySorted Prod.fst
        (run StableSorting.nonnegativeCompare StableSorting.nonnegativeInput).1 ∧
      KeySorted Prod.fst
        (revRun StableSorting.nonnegativeCompare StableSorting.nonnegativeInput).1 := by
  rw [run_value, revRun_value]
  exact ⟨BottomUpSorting.local_comparator_ordinary, BottomUpSorting.local_comparator_tail⟩

/-- A uniform odd pass has the source budget although its leftover does not double. -/
theorem odd_uniform_budget_and_leftover :
    pairsComparisons natCompare [[1], [2], [3]] ≤ 3 ∧
      ¬ (∀ xs ∈ mergePairsBy natCompare [[1], [2], [3]], xs.length = 2) := by
  refine ⟨?_, BottomUpSorting.odd_runs_do_not_all_double⟩
  have hl : ∀ xs ∈ ([[1], [2], [3]] : List (List Nat)), xs.length = 1 := by
    intro xs hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> rfl
  simpa using pairsComparisons_le_uniform natCompare [[1], [2], [3]] 1 hl

/-- `m=0` remains meaningful: structural passes are performed with zero head comparisons. -/
theorem four_empty_runs_zero (cmp : α → α → Bool) :
    allComparisons cmp [[], [], [], []] = 0 ∧
      allRevComparisons cmp [[], [], [], []] = 0 := by
  have hl : ∀ xs ∈ ([[], [], [], []] : List (List α)), xs.length = 0 := by simp
  have ho := allComparisons_le_uniform_pow cmp [[], [], [], []] 0 2 hl (by rfl)
  have hr := allRevComparisons_le_uniform_pow cmp [[], [], [], []] 0 2 hl (by rfl)
  constructor <;> omega

/-- `k=0` allows an arbitrarily long single run, with zero merge comparisons. -/
theorem single_run_power_zero (cmp : α → α → Bool) (xs : List α) :
    allComparisons cmp [xs] ≤ 0 ∧ allRevComparisons cmp [xs] ≤ 0 := by
  have hl : ∀ ys ∈ [xs], ys.length = xs.length := by simp
  constructor
  · simpa only [Nat.mul_zero, Nat.zero_mul] using
      allComparisons_le_uniform_pow cmp [xs] xs.length 0 hl (by decide)
  · simpa only [Nat.mul_zero, Nat.zero_mul] using
      allRevComparisons_le_uniform_pow cmp [xs] xs.length 0 hl (by decide)

theorem uniform_four_runs_bound :
    allComparisons natCompare [[0, 4], [1, 5], [2, 6], [3, 7]] ≤ 16 ∧
      allRevComparisons natCompare [[0, 4], [1, 5], [2, 6], [3, 7]] ≤ 16 := by
  have hl : ∀ xs ∈ ([[0, 4], [1, 5], [2, 6], [3, 7]] : List (List Nat)),
      xs.length = 2 := by
    intro xs hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> rfl
  constructor
  · exact allComparisons_le_uniform_pow natCompare _ 2 2 hl (by decide)
  · exact allRevComparisons_le_uniform_pow natCompare _ 2 2 hl (by decide)

/-- Five nonuniform runs use total length seven and ceiling log three. -/
theorem ragged_general_bound (cmp : Nat → Nat → Bool) :
    allComparisons cmp raggedRuns ≤ 21 ∧ allRevComparisons cmp raggedRuns ≤ 21 := by
  have ho := allComparisons_le_clog cmp raggedRuns
  have hr := allRevComparisons_le_clog cmp raggedRuns
  have hlog : Nat.clog 2 5 = 3 := by decide
  change allComparisons cmp raggedRuns ≤ 7 * Nat.clog 2 5 at ho
  change allRevComparisons cmp raggedRuns ≤ 7 * Nat.clog 2 5 at hr
  simpa only [hlog] using And.intro ho hr

theorem source_ceiling_zero_one :
    ⌈Real.logb 2 (0 : ℝ)⌉ = 0 ∧ ⌈Real.logb 2 (1 : ℝ)⌉ = 0 := by
  simpa only [Nat.cast_zero, Nat.cast_one, Nat.clog_zero_right, Nat.clog_one_right] using
    And.intro (int_ceil_logb_two_nat 0) (int_ceil_logb_two_nat 1)

theorem source_half_at_five : Nat.clog 2 5 = Nat.clog 2 3 + 1 :=
  clog_two_source_half 5 (by decide)

theorem sorter_power_zero : comparisons natCompare [9] ≤ 0 ∧ revComparisons natCompare [9] ≤ 0 :=
  ⟨comparisons_le_of_length_pow natCompare [9] 0 (by decide),
    revComparisons_le_of_length_pow natCompare [9] 0 (by decide)⟩

theorem empty_payload (cmp : Empty → Empty → Bool) (xs : List Empty) :
    run cmp xs = ([], 0) ∧ revRun cmp xs = ([], 0) := by
  cases xs with
  | nil => exact ⟨run_nil cmp, revRun_nil cmp⟩
  | cons x _ => exact Empty.elim x

/-- The shared Growth bridge applies to both actual executions, uniformly in input length. -/
theorem descending_families_isBigO :
    Asymptotics.IsBigO Filter.atTop
        (fun n => (comparisons natCompare (List.range n).reverse : ℝ))
        (fun n => (n : ℝ) * Real.logb 2 n) ∧
      Asymptotics.IsBigO Filter.atTop
        (fun n => (revComparisons natCompare (List.range n).reverse : ℝ))
        (fun n => (n : ℝ) * Real.logb 2 n) := by
  constructor
  · apply comparisons_isBigO natCompare (fun n => (List.range n).reverse)
    intro n
    simp
  · apply revComparisons_isBigO natCompare (fun n => (List.range n).reverse)
    intro n
    simp

end Examples.BottomUpCosts

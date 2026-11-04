import Applications.Resources.ListCalls
import Applications.Resources.ListReversal
import Applications.Sorting.QuickSort
import Mathlib.Tactic.Linarith

/-! FDSA first-pivot quicksort under two observations of one measured execution.
The first coordinate is the Exercise 2.4 tariff: recursive entries and two
unit-predicate filter calls. The second is the additional Appendix B.1 cost
of both right-associated source appends. Their sum is the literal call count.
The cons-based suffix worker has its own execution and cost proof. None of
these deterministic observations supplies an input or pivot probability law.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.QuickSort
open Applications.Sorting
universe u v
variable {α : Type u} {κ : Type v}

private theorem unit_filter_exact (p : α → Bool) (xs : List α) :
    ListCalls.filterRun (fun x => (p x, 1)) xs = (xs.filter p, 2 * xs.length + 1) := by
  apply Prod.ext
  · exact ListCalls.filterRun_value _ _
  · exact ListCalls.filterRun_cost_of_constant _ xs 1 (fun _ _ => rfl)

/-- Retain the two source appends in their printed right association. -/
def appendPivotRun (left : List α) (pivot : α) (right : List α) :
    Measured (List α) Nat :=
  bind (ListReversal.appendRun [pivot] right) (ListReversal.appendRun left)

theorem appendPivotRun_exact (left : List α) (pivot : α) (right : List α) :
    appendPivotRun left pivot right = (left ++ ([pivot] ++ right), left.length + 3) := by
  simp only [appendPivotRun, bind, ListReversal.appendRun_exact,
    List.length_cons, List.length_nil]
  apply Prod.ext
  · rfl
  · omega

/-- Each filter's returned list is the corresponding recursive input. Assembly
uses the recursively returned values and both measured append operations. -/
def run (lt : α → α → Bool) : List α → Measured (List α) (Nat × Nat)
  | [] => ([], (1, 0))
  | pivot :: xs =>
      let leftInput := ListCalls.filterRun (fun x => (lt x pivot, 1)) xs
      let left := run lt leftInput.1
      let rightInput := ListCalls.filterRun (fun x => (!(lt x pivot), 1)) xs
      let right := run lt rightInput.1
      let assembled := appendPivotRun left.1 pivot right.1
      (assembled.1,
        (leftInput.2 + left.2.1 + rightInput.2 + right.2.1 + 1,
          left.2.2 + right.2.2 + assembled.2))
termination_by xs => xs.length
decreasing_by
  all_goals simp only [ListCalls.filterRun_value]
  all_goals exact Nat.lt_succ_of_le (List.length_filter_le _ _)

@[simp] theorem run_nil (lt : α → α → Bool) : run lt [] = ([], (1, 0)) := by
  rw [run]

/-- Derived from the measured filters and appends, not a separate numerical model. -/
theorem run_cons (lt : α → α → Bool) (pivot : α) (xs : List α) :
    run lt (pivot :: xs) =
      let left := run lt (xs.filter (fun x => lt x pivot))
      let right := run lt (xs.filter (fun x => !(lt x pivot)))
      (left.1 ++ ([pivot] ++ right.1),
        (left.2.1 + right.2.1 + 4 * xs.length + 3,
          left.2.2 + right.2.2 + left.1.length + 3)) := by
  rw [run]
  simp only [unit_filter_exact, appendPivotRun_exact]
  apply Prod.ext
  · rfl
  · apply Prod.ext <;> dsimp only <;> omega

theorem run_value (lt : α → α → Bool) (xs : List α) :
    (run lt xs).1 = quickSortBy lt xs := by
  match xs with
  | [] => simp
  | pivot :: ys =>
      simp only [run_cons, quickSortBy_cons,
        run_value lt (ys.filter (fun x => lt x pivot)),
        run_value lt (ys.filter (fun x => !(lt x pivot)))]
termination_by xs.length
decreasing_by
  all_goals exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem run_length (lt : α → α → Bool) (xs : List α) :
    (run lt xs).1.length = xs.length := by
  rw [run_value, quickSortBy_length]

/-- The exercise explicitly omits append traversal from this observation. -/
def exerciseCost (lt : α → α → Bool) (xs : List α) : Nat := (run lt xs).2.1

/-- The second coordinate counts the actual source append calls, including
their terminal empty-list calls. -/
def appendCost (lt : α → α → Bool) (xs : List α) : Nat := (run lt xs).2.2

/-- The literal source execution, including both append occurrences. -/
def literalCost (lt : α → α → Bool) (xs : List α) : Nat :=
  exerciseCost lt xs + appendCost lt xs

theorem run_exact (lt : α → α → Bool) (xs : List α) :
    run lt xs = (quickSortBy lt xs, (exerciseCost lt xs, appendCost lt xs)) :=
  Prod.ext (run_value lt xs) rfl

@[simp] theorem exerciseCost_nil (lt : α → α → Bool) : exerciseCost lt [] = 1 := by
  simp [exerciseCost]

@[simp] theorem appendCost_nil (lt : α → α → Bool) : appendCost lt [] = 0 := by
  simp [appendCost]

@[simp] theorem literalCost_nil (lt : α → α → Bool) : literalCost lt [] = 1 := by
  simp [literalCost]

theorem exerciseCost_cons (lt : α → α → Bool) (pivot : α) (xs : List α) :
    exerciseCost lt (pivot :: xs) =
      exerciseCost lt (xs.filter (fun x => lt x pivot)) +
        exerciseCost lt (xs.filter (fun x => !(lt x pivot))) + 4 * xs.length + 3 := by
  simp only [exerciseCost, run_cons]

/-- The supplied Exercise 2.4 recurrence, retaining its two unit-filter tariffs. -/
theorem exerciseCost_cons_source (lt : α → α → Bool) (pivot : α) (xs : List α) :
    exerciseCost lt (pivot :: xs) =
      exerciseCost lt (xs.filter (fun x => lt x pivot)) +
        exerciseCost lt (xs.filter (fun x => !(lt x pivot))) +
          2 * (ListCalls.filterRun (fun x => (lt x pivot, 1)) xs).2 + 1 := by
  rw [exerciseCost_cons, unit_filter_exact]
  dsimp only
  omega

/-- The source's strict-left and nonstrict-right recurrence, specialized only
on the keys. The callback tariff is one for every tail occurrence. -/
theorem exerciseCost_cons_on [LinearOrder κ] (key : α → κ) (pivot : α) (xs : List α) :
    exerciseCost (fun a b => decide (key a < key b)) (pivot :: xs) =
      exerciseCost (fun a b => decide (key a < key b))
        (xs.filter (fun x => decide (key x < key pivot))) +
      exerciseCost (fun a b => decide (key a < key b))
        (xs.filter (fun x => decide (key pivot ≤ key x))) +
      2 * (ListCalls.filterRun (fun x => (decide (key x < key pivot), 1)) xs).2 + 1 := by
  have hr : xs.filter (fun x => !(decide (key x < key pivot))) =
      xs.filter (fun x => decide (key pivot ≤ key x)) := by
    apply List.filter_congr
    intro x _
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq, not_lt]
  rw [exerciseCost_cons_source, hr]

theorem appendCost_cons (lt : α → α → Bool) (pivot : α) (xs : List α) :
    appendCost lt (pivot :: xs) =
      appendCost lt (xs.filter (fun x => lt x pivot)) +
        appendCost lt (xs.filter (fun x => !(lt x pivot))) +
          (xs.filter (fun x => lt x pivot)).length + 3 := by
  simp only [appendCost, run_cons, run_length]

theorem literalCost_cons (lt : α → α → Bool) (pivot : α) (xs : List α) :
    literalCost lt (pivot :: xs) =
      literalCost lt (xs.filter (fun x => lt x pivot)) +
        literalCost lt (xs.filter (fun x => !(lt x pivot))) +
          4 * xs.length + (xs.filter (fun x => lt x pivot)).length + 6 := by
  simp only [literalCost, exerciseCost_cons, appendCost_cons]
  omega

@[simp] theorem run_singleton (lt : α → α → Bool) (x : α) :
    run lt [x] = ([x], (5, 3)) := by
  simp [run_cons]

@[simp] theorem exerciseCost_singleton (lt : α → α → Bool) (x : α) :
    exerciseCost lt [x] = 5 := by simp [exerciseCost]

@[simp] theorem appendCost_singleton (lt : α → α → Bool) (x : α) :
    appendCost lt [x] = 3 := by simp [appendCost]

@[simp] theorem literalCost_singleton (lt : α → α → Bool) (x : α) :
    literalCost lt [x] = 8 := by simp [literalCost]

/-- The actual cons-based worker first evaluates the right recursive result,
then passes it, with the pivot prepended, to the left recursive call.
The suffix itself is returned without traversal at the empty case. -/
def accumulatorRun (lt : α → α → Bool) : List α → List α → Measured (List α) (Nat × Nat)
  | [], suffix => (suffix, (1, 0))
  | pivot :: xs, suffix =>
      let leftInput := ListCalls.filterRun (fun x => (lt x pivot, 1)) xs
      let rightInput := ListCalls.filterRun (fun x => (!(lt x pivot), 1)) xs
      let right := accumulatorRun lt rightInput.1 suffix
      let left := accumulatorRun lt leftInput.1 (pivot :: right.1)
      (left.1,
        (leftInput.2 + rightInput.2 + right.2.1 + left.2.1 + 1,
          right.2.2 + left.2.2))
termination_by xs _ => xs.length
decreasing_by
  all_goals simp only [ListCalls.filterRun_value]
  all_goals exact Nat.lt_succ_of_le (List.length_filter_le _ _)

@[simp] theorem accumulatorRun_nil (lt : α → α → Bool) (suffix : List α) :
    accumulatorRun lt [] suffix = (suffix, (1, 0)) := by rw [accumulatorRun]

theorem accumulatorRun_cons (lt : α → α → Bool) (pivot : α) (xs suffix : List α) :
    accumulatorRun lt (pivot :: xs) suffix =
      let right := accumulatorRun lt (xs.filter (fun x => !(lt x pivot))) suffix
      let left := accumulatorRun lt (xs.filter (fun x => lt x pivot)) (pivot :: right.1)
      (left.1, (left.2.1 + right.2.1 + 4 * xs.length + 3, left.2.2 + right.2.2)) := by
  rw [accumulatorRun]
  simp only [unit_filter_exact]
  apply Prod.ext
  · rfl
  · apply Prod.ext <;> dsimp only <;> omega

/-- Equality of costs is proved from the worker execution for every suffix;
it is not inferred from the pre-existing value equality. -/
theorem accumulatorRun_exact (lt : α → α → Bool) (xs suffix : List α) :
    accumulatorRun lt xs suffix = (quickSortAccBy lt xs suffix, (exerciseCost lt xs, 0)) := by
  match xs with
  | [] => simp
  | pivot :: ys =>
      simp only [accumulatorRun_cons,
        accumulatorRun_exact lt (ys.filter (fun x => !(lt x pivot))) suffix,
        accumulatorRun_exact lt (ys.filter (fun x => lt x pivot))
          (pivot :: quickSortAccBy lt (ys.filter (fun x => !(lt x pivot))) suffix),
        quickSortAccBy_cons, exerciseCost_cons, Nat.add_zero]
termination_by xs.length
decreasing_by
  all_goals exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem accumulatorRun_eq_append (lt : α → α → Bool) (xs suffix : List α) :
    accumulatorRun lt xs suffix = (quickSortBy lt xs ++ suffix, (exerciseCost lt xs, 0)) := by
  rw [accumulatorRun_exact, quickSortAccBy_eq_append]

theorem accumulatorRun_cost_independent (lt : α → α → Bool) (xs suffix other : List α) :
    (accumulatorRun lt xs suffix).2 = (accumulatorRun lt xs other).2 := by
  simp only [accumulatorRun_exact]

/-- The two filters partition occurrences, including equal or repeated values. -/
theorem partition_lengths (p : α → Bool) (xs : List α) :
    (xs.filter p).length + (xs.filter (fun x => !(p x))).length = xs.length := by
  simpa only [List.length_append] using (List.filter_append_perm p xs).length_eq

/-- Exercise 2.4's global bound needs only complementary occurrence partitions,
not an order law, distinct keys, or a probability assumption. -/
theorem exerciseCost_le (lt : α → α → Bool) (xs : List α) :
    exerciseCost lt xs ≤ 2 * xs.length ^ 2 + 2 * xs.length + 1 := by
  match xs with
  | [] => simp
  | pivot :: ys =>
      have hl := exerciseCost_le lt (ys.filter (fun x => lt x pivot))
      have hr := exerciseCost_le lt (ys.filter (fun x => !(lt x pivot)))
      have hp := partition_lengths (fun x => lt x pivot) ys
      simp only [exerciseCost_cons, List.length_cons, ← hp]
      nlinarith [Nat.zero_le
        ((ys.filter (fun x => lt x pivot)).length *
          (ys.filter (fun x => !(lt x pivot))).length)]
termination_by xs.length
decreasing_by
  all_goals exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- Every nonempty call pays two terminal append calls and the singleton copy. -/
theorem appendCost_lower (lt : α → α → Bool) (xs : List α) :
    3 * xs.length ≤ appendCost lt xs := by
  match xs with
  | [] => simp
  | pivot :: ys =>
      have hl := appendCost_lower lt (ys.filter (fun x => lt x pivot))
      have hr := appendCost_lower lt (ys.filter (fun x => !(lt x pivot)))
      have hp := partition_lengths (fun x => lt x pivot) ys
      rw [appendCost_cons, List.length_cons]
      omega
termination_by xs.length
decreasing_by
  all_goals exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- A sharp division-free upper bound for the actual right-associated appends. -/
theorem appendCost_double_le (lt : α → α → Bool) (xs : List α) :
    2 * appendCost lt xs ≤ xs.length ^ 2 + 5 * xs.length := by
  match xs with
  | [] => simp
  | pivot :: ys =>
      have hl := appendCost_double_le lt (ys.filter (fun x => lt x pivot))
      have hr := appendCost_double_le lt (ys.filter (fun x => !(lt x pivot)))
      have hp := partition_lengths (fun x => lt x pivot) ys
      simp only [appendCost_cons, List.length_cons, ← hp]
      nlinarith [Nat.zero_le
        ((ys.filter (fun x => lt x pivot)).length *
          (ys.filter (fun x => !(lt x pivot))).length)]
termination_by xs.length
decreasing_by
  all_goals exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem appendCost_le_exerciseCost (lt : α → α → Bool) (xs : List α) :
    appendCost lt xs ≤ exerciseCost lt xs := by
  match xs with
  | [] => simp
  | pivot :: ys =>
      have hl := appendCost_le_exerciseCost lt (ys.filter (fun x => lt x pivot))
      have hr := appendCost_le_exerciseCost lt (ys.filter (fun x => !(lt x pivot)))
      have hlen := List.length_filter_le (fun x => lt x pivot) ys
      rw [appendCost_cons, exerciseCost_cons]
      omega
termination_by xs.length
decreasing_by
  all_goals exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem exerciseCost_le_literalCost (lt : α → α → Bool) (xs : List α) :
    exerciseCost lt xs ≤ literalCost lt xs := Nat.le_add_right _ _

/-- This bridge may transport a later distribution-specific bound. It does
not supply that distribution or assert equality of the two observations. -/
theorem literalCost_le_twice (lt : α → α → Bool) (xs : List α) :
    literalCost lt xs ≤ 2 * exerciseCost lt xs := by
  have h := appendCost_le_exerciseCost lt xs
  dsimp only [literalCost]
  omega

theorem literalCost_double_le (lt : α → α → Bool) (xs : List α) :
    2 * literalCost lt xs ≤ 5 * xs.length ^ 2 + 9 * xs.length + 2 := by
  have ht := exerciseCost_le lt xs
  have ha := appendCost_double_le lt xs
  dsimp only [literalCost]
  omega

theorem literalCost_le (lt : α → α → Bool) (xs : List α) :
    literalCost lt xs ≤ (5 * xs.length ^ 2 + 9 * xs.length + 2) / 2 := by
  have h := literalCost_double_le lt xs
  omega

/-- The worker removes at least three counted append calls per input occurrence,
independently of the length, values or order of the suffix. -/
theorem accumulator_saving (lt : α → α → Bool) (xs suffix : List α) :
    (accumulatorRun lt xs suffix).2.1 + 3 * xs.length ≤ literalCost lt xs := by
  rw [accumulatorRun_exact]
  exact Nat.add_le_add_left (appendCost_lower lt xs) _

theorem accumulator_cost_lt (lt : α → α → Bool) (xs suffix : List α) (hne : xs ≠ []) :
    (accumulatorRun lt xs suffix).2.1 < literalCost lt xs := by
  have h := accumulator_saving lt xs suffix
  have hp := List.length_pos_iff.mpr hne
  omega

/-- Every later element goes to the right of each earlier pivot. This generic
condition includes nondecreasing keys and all-equal keys. -/
theorem costs_of_all_right (lt : α → α → Bool) (xs : List α)
    (hs : xs.Pairwise (fun a b => lt b a = false)) :
    exerciseCost lt xs = 2 * xs.length ^ 2 + 2 * xs.length + 1 ∧
      appendCost lt xs = 3 * xs.length := by
  revert hs
  induction xs with
  | nil => simp
  | cons pivot xs ih =>
      intro hs
      obtain ⟨hp, ht⟩ := List.pairwise_cons.mp hs
      obtain ⟨hct, hca⟩ := ih ht
      have hl : xs.filter (fun x => lt x pivot) = [] :=
        List.filter_eq_nil_iff.mpr (fun x hx => by simp [hp x hx])
      have hr : xs.filter (fun x => !(lt x pivot)) = xs :=
        List.filter_eq_self.mpr (fun x hx => by simp [hp x hx])
      constructor
      · simp only [exerciseCost_cons, hl, hr, exerciseCost_nil, hct, List.length_cons]
        nlinarith
      · simp only [appendCost_cons, hl, hr, appendCost_nil, hca,
          List.length_cons, List.length_nil]
        omega

theorem literalCost_of_all_right (lt : α → α → Bool) (xs : List α)
    (hs : xs.Pairwise (fun a b => lt b a = false)) :
    literalCost lt xs = 2 * xs.length ^ 2 + 5 * xs.length + 1 := by
  obtain ⟨ht, ha⟩ := costs_of_all_right lt xs hs
  simp only [literalCost, ht, ha]
  omega

/-- Strict descent sends every later occurrence to the left. Weak descent
with mixed ties does not imply this premise. -/
theorem costs_of_all_left (lt : α → α → Bool) (xs : List α)
    (hs : xs.Pairwise (fun a b => lt b a = true)) :
    exerciseCost lt xs = 2 * xs.length ^ 2 + 2 * xs.length + 1 ∧
      2 * appendCost lt xs = xs.length ^ 2 + 5 * xs.length := by
  revert hs
  induction xs with
  | nil => simp
  | cons pivot xs ih =>
      intro hs
      obtain ⟨hp, ht⟩ := List.pairwise_cons.mp hs
      obtain ⟨hct, hca⟩ := ih ht
      have hl : xs.filter (fun x => lt x pivot) = xs :=
        List.filter_eq_self.mpr (fun x hx => hp x hx)
      have hr : xs.filter (fun x => !(lt x pivot)) = [] :=
        List.filter_eq_nil_iff.mpr (fun x hx => by simp [hp x hx])
      constructor
      · simp only [exerciseCost_cons, hl, hr, exerciseCost_nil, hct, List.length_cons]
        nlinarith
      · simp only [appendCost_cons, hl, hr, appendCost_nil, List.length_cons]
        nlinarith

theorem literalCost_double_of_all_left (lt : α → α → Bool) (xs : List α)
    (hs : xs.Pairwise (fun a b => lt b a = true)) :
    2 * literalCost lt xs = 5 * xs.length ^ 2 + 9 * xs.length + 2 := by
  obtain ⟨ht, ha⟩ := costs_of_all_left lt xs hs
  dsimp only [literalCost]
  omega

theorem literalCost_of_all_left (lt : α → α → Bool) (xs : List α)
    (hs : xs.Pairwise (fun a b => lt b a = true)) :
    literalCost lt xs = (5 * xs.length ^ 2 + 9 * xs.length + 2) / 2 := by
  have h := literalCost_double_of_all_left lt xs hs
  omega

/-- The exact sorted-input polynomial requested by Exercise 2.4, with no
distinctness premise and no order or equality instance on payloads. -/
theorem costs_of_sorted [LinearOrder κ] (key : α → κ) (xs : List α)
    (hs : KeySorted key xs) :
    exerciseCost (fun a b => decide (key a < key b)) xs =
        2 * xs.length ^ 2 + 2 * xs.length + 1 ∧
      appendCost (fun a b => decide (key a < key b)) xs = 3 * xs.length := by
  apply costs_of_all_right
  exact hs.imp (fun h => by simpa only [decide_eq_false_iff_not, not_lt] using h)

theorem costs_of_strict_descent [LT κ] [DecidableLT κ] (key : α → κ) (xs : List α)
    (hs : xs.Pairwise (fun a b => key b < key a)) :
    exerciseCost (fun a b => decide (key a < key b)) xs =
        2 * xs.length ^ 2 + 2 * xs.length + 1 ∧
      2 * appendCost (fun a b => decide (key a < key b)) xs =
        xs.length ^ 2 + 5 * xs.length := by
  apply costs_of_all_left
  exact hs.imp (fun h => by simpa only [decide_eq_true_eq] using h)

/-- Equal keys form a quadratic chain in the source two-way partition. This is
the deterministic duplicate-key boundary for later probability claims. -/
theorem costs_replicate [LinearOrder κ] (key : α → κ) (x : α) (n : Nat) :
    exerciseCost (fun a b => decide (key a < key b)) (List.replicate n x) =
        2 * n ^ 2 + 2 * n + 1 ∧
      appendCost (fun a b => decide (key a < key b)) (List.replicate n x) = 3 * n := by
  have hs : KeySorted key (List.replicate n x) := by
    simp only [KeySorted, List.pairwise_replicate, le_refl, or_true]
  simpa only [List.length_replicate] using costs_of_sorted key (List.replicate n x) hs

/-- Sum of tail lengths over exactly the source pivot/partition recursion.
This is the classical one-test-per-tail-occurrence statistic, not the number
of predicate invocations in the literal two-filter execution. -/
def partitionMass (lt : α → α → Bool) : List α → Nat
  | [] => 0
  | pivot :: xs =>
      partitionMass lt (xs.filter (fun x => lt x pivot)) +
        partitionMass lt (xs.filter (fun x => !(lt x pivot))) + xs.length
termination_by xs => xs.length
decreasing_by
  all_goals simp only [List.unattach_filter, List.unattach_attach]
  all_goals exact Nat.lt_succ_of_le (List.length_filter_le _ _)

@[simp] theorem partitionMass_nil (lt : α → α → Bool) : partitionMass lt [] = 0 := by
  rw [partitionMass]

theorem partitionMass_cons (lt : α → α → Bool) (pivot : α) (xs : List α) :
    partitionMass lt (pivot :: xs) =
      partitionMass lt (xs.filter (fun x => lt x pivot)) +
        partitionMass lt (xs.filter (fun x => !(lt x pivot))) + xs.length := by
  rw [partitionMass]

@[simp] theorem partitionMass_singleton (lt : α → α → Bool) (x : α) :
    partitionMass lt [x] = 0 := by simp [partitionMass_cons]

/-- A pathwise bridge on the same pivot and partitions, before any averaging.
Repeated keys are allowed. No distribution correspondence follows from it. -/
theorem exerciseCost_eq_partitionMass (lt : α → α → Bool) (xs : List α) :
    exerciseCost lt xs = 4 * partitionMass lt xs + 4 * xs.length + 1 := by
  match xs with
  | [] => simp
  | pivot :: ys =>
      have hl := exerciseCost_eq_partitionMass lt (ys.filter (fun x => lt x pivot))
      have hr := exerciseCost_eq_partitionMass lt (ys.filter (fun x => !(lt x pivot)))
      have hp := partition_lengths (fun x => lt x pivot) ys
      rw [exerciseCost_cons, partitionMass_cons, List.length_cons, hl, hr]
      omega
termination_by xs.length
decreasing_by
  all_goals exact Nat.lt_succ_of_le (List.length_filter_le _ _)

end Resources.QuickSort
end Resources.QuickSort

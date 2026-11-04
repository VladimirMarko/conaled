import Applications.Resources.NaturalRunOperations
import Examples.NaturalSortingCosts
import Examples.DifferenceListCosts

/-!
# Connected source-operation cases

Independent branch counts give ascending scanner work 7, 13 and 19 for
lengths 2, 3 and 4; strict descent gives 6 and 9 for lengths 2 and 3.
The source's empty/single-run merger dispatch adds one. Restart examples
instead expose two or three actual runs and are outside that dispatch domain.

Supplied callback and accumulator cases preserve the worker domains. The
existing XD01 charged identity, padded empty prefix, expensive capture,
repeated application and shared self-composition examples remain imported;
additional worker connections below show why Rep alone supplies no work bound.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.NaturalRunOperations

open Applications.Sorting
open _root_.Resources
open _root_.Resources.DifferenceListCosts
open _root_.Resources.NaturalRunOperations
open Examples.NaturalRuns (natLT Record)
open Examples.NaturalSorting (natCompare)

universe u
variable {α : Type u}

theorem empty_payload :
    runsOpsBy (fun a _ : Empty => nomatch a) [] = ([], 1) := runsOpsBy_nil _

theorem empty_payload_execution :
    singleRunOpsBy (fun a _ : Empty => nomatch a) [] (by simp) = ([], 2) :=
  singleRunOpsBy_nil _ _

theorem singleton_payload (lt : α → α → Bool) (a : α) :
    runsOpsBy lt [a] = ([[a]], 3) := runsOpsBy_singleton lt a

theorem singleton_payload_execution (lt : α → α → Bool) (a : α) :
    singleRunOpsBy lt [a] (by simp) = ([a], 4) := singleRunOpsBy_singleton lt a _

theorem ascending_two : runsOpsBy natLT [1, 2] = ([[1, 2]], 7) :=
  runsOpsBy_of_sorted id [1, 2] (by decide) (by decide)

theorem ascending_three : runsOpsBy natLT [1, 2, 3] = ([[1, 2, 3]], 13) :=
  runsOpsBy_of_sorted id [1, 2, 3] (by decide) (by decide)

theorem ascending_two_execution :
    singleRunOpsBy natLT [1, 2]
      (runsOn_length_le_one_of_sorted id [1, 2] (by decide)) = ([1, 2], 8) :=
  singleRunOpsBy_of_sorted id [1, 2] (by decide) (by decide)

theorem ascending_three_execution :
    singleRunOpsBy natLT [1, 2, 3]
      (runsOn_length_le_one_of_sorted id [1, 2, 3] (by decide)) = ([1, 2, 3], 14) :=
  singleRunOpsBy_of_sorted id [1, 2, 3] (by decide) (by decide)

theorem descending_two : runsOpsBy natLT [2, 1] = ([[1, 2]], 6) := by
  simpa [natLT] using runsOpsBy_of_strictly_descending id [2, 1] (by decide) (by simp)

theorem descending_three : runsOpsBy natLT [3, 2, 1] = ([[1, 2, 3]], 9) := by
  simpa [natLT] using runsOpsBy_of_strictly_descending id [3, 2, 1] (by decide) (by simp)

theorem descending_two_execution :
    singleRunOpsBy natLT [2, 1]
      (runsOn_length_le_one_of_strictly_descending id [2, 1] (by decide)) = ([1, 2], 7) := by
  simpa [natLT] using singleRunOpsBy_of_strictly_descending id [2, 1] (by decide) (by simp)

theorem descending_three_execution :
    singleRunOpsBy natLT [3, 2, 1]
      (runsOn_length_le_one_of_strictly_descending id [3, 2, 1] (by decide)) =
        ([1, 2, 3], 10) := by
  simpa [natLT] using singleRunOpsBy_of_strictly_descending id [3, 2, 1] (by decide) (by simp)

theorem ascending_ties : runsOpsBy natLT [1, 1, 2, 3] = ([[1, 1, 2, 3]], 19) := by
  have path := runsOpsBy_buildAscending natLT 1 3 [1, 2] (by decide)
  rw [buildAscending_cost, buildAscending_apply] at path
  exact path

theorem ascending_ties_execution :
    singleRunOpsBy natLT [1, 1, 2, 3]
      (runsOn_length_le_one_of_sorted id [1, 1, 2, 3] (by decide)) =
        ([1, 1, 2, 3], 20) :=
  singleRunOpsBy_of_sorted id [1, 1, 2, 3] (by decide) (by decide)

/-- The failed descent emits [1,3], then scans the unconsumed singleton. -/
theorem three_boundary_worker : descOpsBy natLT 1 [3] [2] = ([[1, 3], [2]], 7) := by
  rw [descOpsBy_cons]
  change ([1, 3] :: (runsOpsBy natLT [2]).1, 4 + (runsOpsBy natLT [2]).2) = _
  rw [runsOpsBy_singleton]
  rfl

theorem three_boundary : runsOpsBy natLT [3, 1, 2] = ([[1, 3], [2]], 10) := by
  rw [runsOpsBy_cons_cons]
  change ((descOpsBy natLT 1 [3] [2]).1, 3 + (descOpsBy natLT 1 [3] [2]).2) = _
  rw [three_boundary_worker]
  rfl

theorem restart_worker :
    ascOpsBy natLT 3 (singleton 1) [2, 4] = ([[1, 3], [2, 4]], 12) := by
  have rest : runsOpsBy natLT [2, 4] = ([[2, 4]], 7) :=
    runsOpsBy_of_sorted id [2, 4] (by decide) (by decide)
  rw [ascOpsBy_cons]
  change ([1, 3] :: (runsOpsBy natLT [2, 4]).1,
    1 + 4 + (runsOpsBy natLT [2, 4]).2) = _
  rw [rest]
  rfl

theorem restart_boundary : runsOpsBy natLT [1, 3, 2, 4] = ([[1, 3], [2, 4]], 15) := by
  rw [runsOpsBy_cons_cons]
  change ((ascOpsBy natLT 3 (singleton 1) [2, 4]).1,
    3 + (ascOpsBy natLT 3 (singleton 1) [2, 4]).2) = _
  rw [restart_worker]
  rfl

/-- The final singleton remains an outer run; two restart boundaries are charged. -/
theorem odd_runs :
    runsOpsBy natLT [1, 3, 2, 4, 0] = ([[1, 3], [2, 4], [0]], 19) := by
  have lastWorker : ascOpsBy natLT 4 (singleton 2) [0] = ([[2, 4], [0]], 8) := by
    rw [ascOpsBy_cons]
    change ([2, 4] :: (runsOpsBy natLT [0]).1, 1 + 4 + (runsOpsBy natLT [0]).2) = _
    rw [runsOpsBy_singleton]
    rfl
  have rest : runsOpsBy natLT [2, 4, 0] = ([[2, 4], [0]], 11) := by
    rw [runsOpsBy_cons_cons]
    change ((ascOpsBy natLT 4 (singleton 2) [0]).1,
      3 + (ascOpsBy natLT 4 (singleton 2) [0]).2) = _
    rw [lastWorker]
    rfl
  have firstWorker :
      ascOpsBy natLT 3 (singleton 1) [2, 4, 0] = ([[1, 3], [2, 4], [0]], 16) := by
    rw [ascOpsBy_cons]
    change ([1, 3] :: (runsOpsBy natLT [2, 4, 0]).1,
      1 + 4 + (runsOpsBy natLT [2, 4, 0]).2) = _
    rw [rest]
    rfl
  rw [runsOpsBy_cons_cons]
  change ((ascOpsBy natLT 3 (singleton 1) [2, 4, 0]).1,
    3 + (ascOpsBy natLT 3 (singleton 1) [2, 4, 0]).2) = _
  rw [firstWorker]
  rfl

/-- A tie starts ascent; the following decrease emits both tagged occurrences. -/
theorem weak_descent_with_ties :
    runsOpsBy (fun a b : Record => decide (a.1 < b.1))
      [(3, "A"), (3, "B"), (2, "C")] =
        ([[(3, "A"), (3, "B")], [(2, "C")]], 11) := by
  have worker :
      ascOpsBy (fun a b : Record => decide (a.1 < b.1))
        (3, "B") (singleton (3, "A")) [(2, "C")] =
          ([[(3, "A"), (3, "B")], [(2, "C")]], 8) := by
    rw [ascOpsBy_cons]
    change ([(3, "A"), (3, "B")] ::
      (runsOpsBy (fun a b : Record => decide (a.1 < b.1)) [(2, "C")]).1,
        1 + 4 + (runsOpsBy (fun a b : Record => decide (a.1 < b.1)) [(2, "C")]).2) = _
    rw [runsOpsBy_singleton]
    rfl
  rw [runsOpsBy_cons_cons]
  change ((ascOpsBy (fun a b : Record => decide (a.1 < b.1))
    (3, "B") (singleton (3, "A")) [(2, "C")]).1,
      3 + (ascOpsBy (fun a b : Record => decide (a.1 < b.1))
        (3, "B") (singleton (3, "A")) [(2, "C")]).2) = _
  rw [worker]
  rfl

theorem multiple_runs_outside_dispatch :
    ¬(runsBy natLT [3, 1, 2]).length ≤ 1 ∧
      ¬(runsBy natLT [1, 3, 2, 4]).length ≤ 1 ∧
      ¬(runsBy natLT [1, 3, 2, 4, 0]).length ≤ 1 := by
  rw [← runsOpsBy_value natLT [3, 1, 2], three_boundary, ← runsOpsBy_value natLT [1, 3, 2, 4],
    restart_boundary, ← runsOpsBy_value natLT [1, 3, 2, 4, 0], odd_runs]
  decide

theorem weak_descent_outside_dispatch :
    ¬(runsOn Prod.fst ([(3, "A"), (3, "B"), (2, "C")] : List Record)).length ≤ 1 := by
  rw [NaturalRuns.weak_descent_with_ties]
  decide

/-- Earlier creation of the supplied two-singleton callback is excluded. -/
theorem arbitrary_builder_restart :
    ascOpsBy natLT 5 (compose (singleton 1) (singleton 3)) [4, 6] =
      ([[1, 3, 5], [4, 6]], 14) := by
  have rest : runsOpsBy natLT [4, 6] = ([[4, 6]], 7) :=
    runsOpsBy_of_sorted id [4, 6] (by decide) (by decide)
  rw [ascOpsBy_cons]
  change ([1, 3, 5] :: (runsOpsBy natLT [4, 6]).1,
    3 + 4 + (runsOpsBy natLT [4, 6]).2) = _
  rw [rest]
  rfl

theorem unsorted_builder_value_and_work :
    ascOpsBy natLT 3 (compose (singleton 2) (singleton 1)) [] = ([[2, 1, 3]], 6) := by
  rw [ascOpsBy_nil]
  rfl

theorem unsorted_builder_remains_unsorted :
    ¬KeySorted id (ascOpsBy natLT 3 (compose (singleton 2) (singleton 1)) []).1.flatten := by
  rw [unsorted_builder_value_and_work]
  decide

theorem arbitrary_descending_accumulator (lt : α → α → Bool) (a : α) (acc : List α) :
    descOpsBy lt a acc [] = ([a :: acc], 3) := descOpsBy_nil lt a acc

theorem arbitrary_cost_without_rep (lt : α → α → Bool) (a : α) (ys : List α) (k : Nat) :
    (ascOpsBy lt a (fun suffix => (suffix.reverse, k)) ys).2 ≤ k + 6 * ys.length + 5 :=
  ascOpsBy_work_le lt a _ ys k (fun _ => rfl)

/-- This callback is not assumed to satisfy Rep; the actual application value
is still retained by the source-path equation and the measured branch. -/
theorem arbitrary_callback_continuation :
    ascOpsBy natLT 2 (fun suffix : List Nat => (suffix.reverse, 17)) [3] = ([[3, 2]], 26) := by
  have path := ascOpsBy_buildFrom natLT 2 3
    (fun suffix : List Nat => (suffix.reverse, 17)) [] (by decide)
  rw [buildFrom_cons, buildFrom_nil] at path
  exact path

/-- Unit capture is separate from the arbitrary work of the captured callbacks. -/
theorem expensive_capture_worker (lt : α → α → Bool) (a : α) (p q : Nat) :
    let f : Builder α := fun suffix => (suffix, p)
    let g : Builder α := fun suffix => (suffix, q)
    (createCompose f g).2 = 1 ∧
      ascOpsBy lt a (createCompose f g).1 [] = ([[a]], p + q + 4) := by
  dsimp only
  constructor
  · rfl
  · rw [ascOpsBy_nil]
    apply Prod.ext
    · rfl
    · change (q + p + 1) + 3 = p + q + 4
      omega

theorem empty_outer_dispatch (cmp : α → α → Bool) :
    baseMergeOps ([] : List (List α)) (by simp) = ([], 1) ∧
      baseMergeOps ([] : List (List α)) (by simp) =
        CallCount.tick (BottomUpSorting.allRun cmp []) :=
  ⟨baseMergeOps_nil _, baseMergeOps_eq_tick_allRun cmp [] _⟩

theorem empty_inner_dispatch (cmp : α → α → Bool) :
    baseMergeOps ([[]] : List (List α)) (by simp) = ([], 1) ∧
      baseMergeOps ([[]] : List (List α)) (by simp) =
        CallCount.tick (BottomUpSorting.allRun cmp [[]]) :=
  ⟨baseMergeOps_singleton [] _, baseMergeOps_eq_tick_allRun cmp [[]] _⟩

theorem source_builder_with_suffix :
    (buildAscending (1 : Nat) [1, 2]).2 = 5 ∧
      (buildAscending (1 : Nat) [1, 2]).1 [9, 8] = ([1, 1, 2, 9, 8], 5) :=
  ⟨buildAscending_cost _ _, buildAscending_apply _ _ _⟩

/-- Two actual applications after one source construction are charged twice,
with their distinct suffixes and returned values retained. -/
theorem source_builder_two_applications (first : α) (middle leftSuffix rightSuffix : List α) :
    bind (buildAscending first middle) (fun f =>
      bind (f leftSuffix) (fun left =>
        bind (f rightSuffix) (fun right => pure (left, right)))) =
      (((first :: middle) ++ leftSuffix, (first :: middle) ++ rightSuffix),
        3 + 6 * middle.length) := by
  apply Prod.ext
  · change (((buildAscending first middle).1 leftSuffix).1,
      ((buildAscending first middle).1 rightSuffix).1) = _
    exact Prod.ext (buildAscending_rep first middle leftSuffix)
      (buildAscending_rep first middle rightSuffix)
  · change (buildAscending first middle).2 +
      (((buildAscending first middle).1 leftSuffix).2 +
        (((buildAscending first middle).1 rightSuffix).2 + 0)) = _
    rw [buildAscending_cost, buildAscending_appCost first middle leftSuffix,
      buildAscending_appCost first middle rightSuffix]
    omega

theorem charged_identity_changes_worker_work (lt : α → α → Bool) (a : α) (f : Builder α) :
    (ascOpsBy lt a (compose f empty) []).1 = (ascOpsBy lt a f []).1 ∧
      (ascOpsBy lt a (compose f empty) []).2 = (ascOpsBy lt a f []).2 + 2 := by
  have old := DifferenceListCosts.identity_value_cost f [a]
  rw [ascOpsBy_nil, ascOpsBy_nil]
  constructor
  · exact congrArg (fun xs : List α => [xs]) old.1
  · change (compose f empty [a]).2 + 3 = ((f [a]).2 + 3) + 2
    omega

/-- Rep is the same empty prefix for every n, but this worker's work is unbounded. -/
theorem padded_worker (lt : α → α → Bool) (a : α) (n : Nat) :
    ascOpsBy lt a (DifferenceListCosts.padded n) [] = ([[a]], 2 * n + 4) := by
  rw [ascOpsBy_nil]
  apply Prod.ext
  · change [(DifferenceListCosts.padded n [a]).1] = [[a]]
    rw [DifferenceListCosts.padded_rep n [a]]
    rfl
  · have count := DifferenceListCosts.padded_appCost (α := α) n [a]
    change (DifferenceListCosts.padded n [a]).2 + 3 = 2 * n + 4
    omega

theorem no_worker_bound_from_empty_prefix (lt : α → α → Bool) (a : α) (B : Nat) :
    ∃ n : Nat, Rep (DifferenceListCosts.padded n) ([] : List α) ∧
      B < (ascOpsBy lt a (DifferenceListCosts.padded n) []).2 := by
  refine ⟨B + 1, DifferenceListCosts.padded_rep _, ?_⟩
  rw [padded_worker]
  omega

/-- The existing sharing counterexample is retained without identifying its
creation count with the source's linear prefix-weight invariant. -/
theorem shared_closure_counts_retained :
    (DifferenceListCosts.doubled (α := Empty) 4).2 = 5 ∧
      ((DifferenceListCosts.doubled (α := Empty) 4).1 []).2 = 31 ∧
      DifferenceListCosts.materializeDoubled (α := Empty) 4 [] = ([], 36) := by
  refine ⟨DifferenceListCosts.doubled_creation 4, ?_, ?_⟩
  · exact DifferenceListCosts.doubled_appCost 4 []
  · exact DifferenceListCosts.materializeDoubled_eq 4 []

theorem generic_scanner_contracts (lt : α → α → Bool) (xs : List α) :
    (runsOpsBy lt xs).1.flatten.Perm xs ∧
      (runsOpsBy lt xs).1.flatten.length = xs.length ∧
      (runsOpsBy lt xs).1.length ≤ xs.length ∧
      (runsOpsBy lt xs).2 ≤ 6 * xs.length + 1 :=
  ⟨runsOpsBy_perm lt xs, runsOpsBy_flatten_length lt xs,
    runsOpsBy_length_le lt xs, runsOpsBy_work_le lt xs⟩

theorem arbitrary_payload_correct (xs : List (Nat × α))
    (h : (runsOn Prod.fst xs).length ≤ 1) :
    KeySorted Prod.fst (singleRunOpsBy (fun a b => decide (a.1 < b.1)) xs h).1 ∧
      (singleRunOpsBy (fun a b => decide (a.1 < b.1)) xs h).1.Perm xs :=
  singleRunOpsBy_correct Prod.fst xs h

theorem constant_key_domain (xs : List α) :
    (runsBy (fun _ _ => false) xs).length ≤ 1 :=
  runsOn_length_le_one_of_sorted (fun _ : α => (0 : Nat)) xs
    (List.pairwise_of_forall (fun _ _ => Nat.le_refl 0))

/-- Arbitrary payloads need no equality, order or inhabitance instance. -/
theorem repeated_payload_exact (a : α) (n : Nat) (hn : 2 ≤ n) :
    singleRunOpsBy (fun _ _ => false) (List.replicate n a)
      (constant_key_domain _) = (List.replicate n a, 6 * n - 4) := by
  have hzero : decide ((0 : Nat) < 0) = false := by decide
  simpa only [List.length_replicate, hzero] using
    singleRunOpsBy_of_sorted (fun _ : α => (0 : Nat)) (List.replicate n a)
      (List.pairwise_of_forall (fun _ _ => Nat.le_refl 0))
      (by simpa only [List.length_replicate] using hn)

theorem ascending_range_exact (n : Nat) (hn : 2 ≤ n) :
    singleRunOpsBy natLT (List.range n)
      (runsOn_length_le_one_of_sorted id (List.range n)
        (List.pairwise_lt_range.imp (fun h => Nat.le_of_lt h))) =
      (List.range n, 6 * n - 4) := by
  simpa only [natLT, id_eq, List.length_range] using
    singleRunOpsBy_of_sorted id (List.range n)
      (List.pairwise_lt_range.imp (fun h => Nat.le_of_lt h))
      (by simpa only [List.length_range] using hn)

/-- The comparison and operation observations are independently specified. -/
theorem comparison_counter_is_separate :
    _root_.Resources.NaturalRunComparisons.runsRunBy natLT [1, 2, 3] = ([[1, 2, 3]], 2) ∧
      _root_.Resources.NaturalSorting.run natLT natCompare [1, 2, 3] = ([1, 2, 3], 2) ∧
      singleRunOpsBy natLT [1, 2, 3]
        (runsOn_length_le_one_of_sorted id [1, 2, 3] (by decide)) = ([1, 2, 3], 14) := by
  refine ⟨?_, ?_, ascending_three_execution⟩
  · apply Prod.ext
    · rw [_root_.Resources.NaturalRunComparisons.runsRunBy_value]
      exact runsOn_of_sorted id [1, 2, 3] (by decide) (by simp)
    · exact _root_.Resources.NaturalRunComparisons.runsRunBy_cost_exact natLT [1, 2, 3]
  · exact _root_.Resources.NaturalSorting.run_of_sorted id natCompare [1, 2, 3]
      (by decide) (by simp)

end Examples.NaturalRunOperations

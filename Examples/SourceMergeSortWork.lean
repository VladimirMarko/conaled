import Applications.Resources.SourceMergeSortWork
import Examples.MergeSorting
import Examples.MeasuredRectangleEvents

/-!
# Full declared work of alternating merge sort and rectangle schedules

The fixed expectations distinguish comparator observations, list traversal,
construction and recursive invocation charges. Their semantic bridges use the
actual returned comparator Booleans and child lists. Arbitrary comparators still
preserve occurrences; ordering and cost correspondence have separate premises.

The rectangle pipeline uses the new measured event sorter. The earlier
constant-17 sorter fixture is a different observation model and is retained.
Neither model supplies a compiler-runtime, allocation or arithmetic-bit bound.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SourceMergeSortWork
open Search Search.RectangleSweep Resources
open Examples.RectangleEvents Examples.RectangleSweep Examples.MeasuredRectangleSweep
open Examples.MeasuredRectangleEvents
universe u v

def natUnit (a b : Nat) : Measured Bool Nat := (decide (a ≤ b), 1)
def natFree (a b : Nat) : Measured Bool Nat := (decide (a ≤ b), 0)
def asymmetric (a b : Nat) : Measured Bool Nat := (decide (a ≤ b), 10 * a + b + 1)
def alwaysTrue (_a _b : Nat) : Measured Bool Nat := (true, 1)
def alwaysFalse (_a _b : Nat) : Measured Bool Nat := (false, 1)

/-! The merge terminal returns its existing suffix without traversing or copying it. -/

theorem merge_empty_left : Resources.ListMergeWork.run natUnit [] [1, 2, 3] =
    ([1, 2, 3], 1) := Resources.ListMergeWork.run_nil_left natUnit [1, 2, 3]

theorem merge_empty_right : Resources.ListMergeWork.run natUnit [1, 2, 3] [] =
    ([1, 2, 3], 1) := Resources.ListMergeWork.run_nil_right natUnit [1, 2, 3]

theorem merge_interleaved : Resources.ListMergeWork.run natUnit [1, 3] [2, 4] =
    ([1, 2, 3, 4], 10) := by
  simp [Resources.ListMergeWork.run_cons_cons, Resources.ListMergeWork.run_nil_left,
    Resources.bind, CallCount.tick, natUnit]

theorem merge_early_left : Resources.ListMergeWork.run natUnit [1, 2] [3, 4] =
    ([1, 2, 3, 4], 7) := by
  simp [Resources.ListMergeWork.run_cons_cons, Resources.ListMergeWork.run_nil_left,
    Resources.bind, CallCount.tick, natUnit]

theorem merge_early_right : Resources.ListMergeWork.run natUnit [3, 4] [1, 2] =
    ([1, 2, 3, 4], 7) := by
  simp [Resources.ListMergeWork.run_cons_cons, Resources.ListMergeWork.run_nil_right,
    Resources.bind, CallCount.tick, natUnit]

theorem merge_asymmetric : Resources.ListMergeWork.run asymmetric [1, 3] [2, 4] =
    ([1, 2, 3, 4], 88) := by
  simp [Resources.ListMergeWork.run_cons_cons, Resources.ListMergeWork.run_nil_left,
    Resources.bind, CallCount.tick, asymmetric]

theorem merge_always_true : Resources.ListMergeWork.run alwaysTrue [2, 1] [4, 3, 0] =
    ([2, 1, 4, 3, 0], 7) := by
  simp [Resources.ListMergeWork.run_cons_cons, Resources.ListMergeWork.run_nil_left,
    Resources.bind, CallCount.tick, alwaysTrue]

theorem merge_always_false : Resources.ListMergeWork.run alwaysFalse [2, 1] [4, 3, 0] =
    ([4, 3, 0, 2, 1], 10) := by
  simp [Resources.ListMergeWork.run_cons_cons, Resources.ListMergeWork.run_nil_right,
    Resources.bind, CallCount.tick, alwaysFalse]

theorem merge_unit_exact (xs ys : List Nat) :
    (Resources.ListMergeWork.run natUnit xs ys).2 =
      3 * Resources.ListMerge.comparisons (fun a b => decide (a ≤ b)) xs ys + 1 :=
  Resources.ListMergeWork.run_cost_of_constant natUnit xs ys 1 (fun _ _ => rfl)

theorem merge_unit_bound (xs ys : List Nat) :
    (Resources.ListMergeWork.run natUnit xs ys).2 ≤ 3 * (xs.length + ys.length) + 1 :=
  Resources.ListMergeWork.run_cost_le natUnit xs ys 1 (fun _ _ => le_rfl)

theorem merge_arbitrary_contract {α : Type u}
    (cmp : α → α → Measured Bool Nat) (xs ys : List α) :
    (Resources.ListMergeWork.run cmp xs ys).1.Perm (xs ++ ys) ∧
      (Resources.ListMergeWork.run cmp xs ys).1.length = xs.length + ys.length :=
  ⟨Resources.ListMergeWork.run_perm cmp xs ys, Resources.ListMergeWork.run_length cmp xs ys⟩

theorem asymmetric_has_no_global_constant :
    ¬ ∃ C, ∀ a b, (asymmetric a b).2 ≤ C := by
  rintro ⟨C, bounded⟩
  have impossible := bounded (C + 1) 0
  change 10 * (C + 1) + 0 + 1 ≤ C at impossible
  omega

/-! Public finite recurrence clients retain the actual measured merge results. -/

theorem work_pair {α : Type u} (cmp : α → α → Measured Bool Nat) (a b : α) :
    Resources.SourceMergeSortWork.run cmp [a, b] =
      let merged := Resources.ListMergeWork.run cmp [a] [b]
      (merged.1, 21 + merged.2) := by
  rw [Resources.SourceMergeSortWork.run_step cmp [a, b] (by simp)]
  simp only [Resources.SourceMergeSortWork.splitRun_exact,
    Applications.Sorting.SourceMergeSort.split, Resources.SourceMergeSortWork.run_singleton,
    Resources.bind, List.length_cons, List.length_nil]
  congr 1
  omega

theorem work_pair_cost {α : Type u} (cmp : α → α → Measured Bool Nat) (a b : α) :
    (Resources.SourceMergeSortWork.run cmp [a, b]).2 = (cmp a b).2 + 24 := by
  rw [work_pair]
  change 21 + (Resources.ListMergeWork.run cmp [a] [b]).2 = (cmp a b).2 + 24
  rw [Resources.ListMergeWork.run_cost_cons_cons]
  simp only [Resources.ListMergeWork.run_nil_left, Resources.ListMergeWork.run_nil_right,
    ite_self]
  omega

theorem work_three {α : Type u} (cmp : α → α → Measured Bool Nat) (a b c : α) :
    Resources.SourceMergeSortWork.run cmp [a, b, c] =
      let left := Resources.ListMergeWork.run cmp [a] [c]
      let merged := Resources.ListMergeWork.run cmp left.1 [b]
      (merged.1, 40 + left.2 + merged.2) := by
  rw [Resources.SourceMergeSortWork.run_step cmp [a, b, c] (by simp)]
  simp only [Resources.SourceMergeSortWork.splitRun_exact,
    Applications.Sorting.SourceMergeSort.split, work_pair,
    Resources.SourceMergeSortWork.run_singleton, Resources.bind,
    List.length_cons, List.length_nil]
  congr 1
  omega

theorem work_four {α : Type u} (cmp : α → α → Measured Bool Nat) (a b c d : α) :
    Resources.SourceMergeSortWork.run cmp [a, b, c, d] =
      let left := Resources.ListMergeWork.run cmp [a] [c]
      let right := Resources.ListMergeWork.run cmp [b] [d]
      let merged := Resources.ListMergeWork.run cmp left.1 right.1
      (merged.1, 60 + left.2 + right.2 + merged.2) := by
  rw [Resources.SourceMergeSortWork.run_step cmp [a, b, c, d] (by simp)]
  simp only [Resources.SourceMergeSortWork.splitRun_exact,
    Applications.Sorting.SourceMergeSort.split, work_pair, Resources.bind,
    List.length_cons, List.length_nil]
  congr 1
  omega

theorem work_six {α : Type u} (cmp : α → α → Measured Bool Nat) (a b c d e f : α) :
    Resources.SourceMergeSortWork.run cmp [a, b, c, d, e, f] =
      let left := Resources.SourceMergeSortWork.run cmp [a, c, e]
      let right := Resources.SourceMergeSortWork.run cmp [b, d, f]
      let merged := Resources.ListMergeWork.run cmp left.1 right.1
      (merged.1, 25 + left.2 + right.2 + merged.2) := by
  rw [Resources.SourceMergeSortWork.run_step cmp [a, b, c, d, e, f] (by simp)]
  simp only [Resources.SourceMergeSortWork.splitRun_exact,
    Applications.Sorting.SourceMergeSort.split, Resources.bind,
    List.length_cons, List.length_nil]
  congr 1
  omega

theorem length_empty : Resources.SourceMergeSortWork.lengthRun ([] : List Empty) = (0, 1) :=
  Resources.SourceMergeSortWork.lengthRun_exact []

theorem length_five : Resources.SourceMergeSortWork.lengthRun [0, 1, 2, 3, 4] = (5, 11) :=
  Resources.SourceMergeSortWork.lengthRun_exact [0, 1, 2, 3, 4]

theorem split_odd : Resources.SourceMergeSortWork.splitRun [0, 1, 2, 3, 4] =
    (([0, 2, 4], [1, 3]), 8) := by
  rw [Resources.SourceMergeSortWork.splitRun_exact]
  rfl

theorem split_base :
    Resources.SourceMergeSortWork.splitRun ([] : List Nat) = (([], []), 1) ∧
      Resources.SourceMergeSortWork.splitRun [7] = (([7], []), 2) :=
  ⟨Resources.SourceMergeSortWork.splitRun_nil,
    Resources.SourceMergeSortWork.splitRun_singleton 7⟩

theorem split_generic_bound {α : Type u} (xs : List α) :
    (Resources.SourceMergeSortWork.splitRun xs).2 ≤ 2 * xs.length + 1 :=
  Resources.SourceMergeSortWork.splitRun_cost_le xs

theorem sort_empty : Resources.SourceMergeSortWork.run natUnit [] = ([], 3) :=
  Resources.SourceMergeSortWork.run_nil natUnit

theorem sort_singleton : Resources.SourceMergeSortWork.run natUnit [7] = ([7], 5) :=
  Resources.SourceMergeSortWork.run_singleton natUnit 7

theorem sort_pair_reversed : Resources.SourceMergeSortWork.run natUnit [2, 1] = ([1, 2], 25) := by
  rw [work_pair]
  simp [Resources.ListMergeWork.run_cons_cons, Resources.ListMergeWork.run_nil_right,
    Resources.bind, CallCount.tick, natUnit]

theorem sort_three_early : Resources.SourceMergeSortWork.run natUnit [3, 1, 2] =
    ([1, 2, 3], 48) := by
  rw [work_three]
  simp [Resources.ListMergeWork.run_cons_cons, Resources.ListMergeWork.run_nil_right,
    Resources.bind, CallCount.tick, natUnit]

theorem sort_three_reversed : Resources.SourceMergeSortWork.run natUnit [3, 2, 1] =
    ([1, 2, 3], 51) := by
  rw [work_three]
  simp [Resources.ListMergeWork.run_cons_cons, Resources.ListMergeWork.run_nil_right,
    Resources.bind, CallCount.tick, natUnit]

theorem sort_four_ascending : Resources.SourceMergeSortWork.run natUnit [0, 1, 2, 3] =
    ([0, 1, 2, 3], 78) := by
  rw [work_four]
  simp [Resources.ListMergeWork.run_cons_cons, Resources.ListMergeWork.run_nil_left,
    Resources.bind, CallCount.tick, natUnit]

theorem sort_four_duplicates : Resources.SourceMergeSortWork.run natUnit [2, 2, 2, 2] =
    ([2, 2, 2, 2], 75) := by
  rw [work_four]
  simp [Resources.ListMergeWork.run_cons_cons, Resources.ListMergeWork.run_nil_left,
    Resources.bind, CallCount.tick, natUnit]

theorem same_value_different_work :
    (Resources.SourceMergeSortWork.run natUnit [3, 1, 2]).1 =
      (Resources.SourceMergeSortWork.run natUnit [3, 2, 1]).1 ∧
      (Resources.SourceMergeSortWork.run natUnit [3, 1, 2]).2 ≠
        (Resources.SourceMergeSortWork.run natUnit [3, 2, 1]).2 := by
  rw [sort_three_early, sort_three_reversed]
  decide

theorem free_callbacks_still_work : Resources.SourceMergeSortWork.run natFree [3, 1, 2] =
    ([1, 2, 3], 46) := by
  rw [work_three]
  simp [Resources.ListMergeWork.run_cons_cons, Resources.ListMergeWork.run_nil_right,
    Resources.bind, CallCount.tick, natFree]

theorem sort_asymmetric_early : Resources.SourceMergeSortWork.run asymmetric [3, 1, 2] =
    ([1, 2, 3], 101) := by
  rw [work_three]
  simp [Resources.ListMergeWork.run_cons_cons, Resources.ListMergeWork.run_nil_right,
    Resources.bind, CallCount.tick, asymmetric]

theorem sort_asymmetric_reversed : Resources.SourceMergeSortWork.run asymmetric [3, 2, 1] =
    ([1, 2, 3], 126) := by
  rw [work_three]
  simp [Resources.ListMergeWork.run_cons_cons, Resources.ListMergeWork.run_nil_right,
    Resources.bind, CallCount.tick, asymmetric]

theorem sort_always_true : Resources.SourceMergeSortWork.run alwaysTrue [0, 1, 2] =
    ([0, 2, 1], 51) := by
  rw [work_three]
  simp [Resources.ListMergeWork.run_cons_cons, Resources.ListMergeWork.run_nil_left,
    Resources.bind, CallCount.tick, alwaysTrue]

theorem sort_always_false : Resources.SourceMergeSortWork.run alwaysFalse [0, 1, 2] =
    ([1, 2, 0], 48) := by
  rw [work_three]
  simp [Resources.ListMergeWork.run_cons_cons, Resources.ListMergeWork.run_nil_right,
    Resources.bind, CallCount.tick, alwaysFalse]

theorem arbitrary_sort_contract {α : Type u} (cmp : α → α → Measured Bool Nat) (xs : List α) :
    (Resources.SourceMergeSortWork.run cmp xs).1.Perm xs ∧
      (Resources.SourceMergeSortWork.run cmp xs).1.length = xs.length :=
  ⟨Resources.SourceMergeSortWork.run_perm cmp xs, Resources.SourceMergeSortWork.run_length cmp xs⟩

theorem keyed_sort_contract {α : Type u} {κ : Type v}
    [LE κ] [DecidableLE κ] [Std.IsLinearPreorder κ] (key : α → κ) (xs : List α) :
    Applications.Sorting.KeySorted key
        (Resources.SourceMergeSortWork.run (fun a b => (decide (key a ≤ key b), 1)) xs).1 ∧
      (Resources.SourceMergeSortWork.run (fun a b => (decide (key a ≤ key b), 1)) xs).1.Perm xs := by
  simpa only [Resources.SourceMergeSortWork.run_value] using
    Applications.Sorting.SourceMergeSort.sortOn_correct key xs

def taggedCmp (a b : Examples.MergeSorting.Record) : Measured Bool Nat :=
  (decide (a.1 ≤ b.1), 1)

theorem tagged_unstable_work :
    Resources.SourceMergeSortWork.run taggedCmp Examples.MergeSorting.records =
      (Examples.MergeSorting.afterOne, 51) := by
  rw [Examples.MergeSorting.records, work_three]
  simp [Resources.ListMergeWork.run_cons_cons, Resources.ListMergeWork.run_nil_left,
    Resources.bind, CallCount.tick, taggedCmp, Examples.MergeSorting.afterOne]

theorem tagged_not_stable :
    ¬ Applications.Sorting.Stable Prod.fst Examples.MergeSorting.records
      (Resources.SourceMergeSortWork.run taggedCmp Examples.MergeSorting.records).1 := by
  simpa only [Resources.SourceMergeSortWork.run_value, taggedCmp] using
    Examples.MergeSorting.records_not_stable

def liftedCmp (a b : ULift.{1} Nat) : Measured Bool Nat := (decide (a.down ≤ b.down), 1)

theorem lifted_pair_work :
    Resources.SourceMergeSortWork.run liftedCmp [ULift.up 2, ULift.up 1] =
      ([ULift.up 1, ULift.up 2], 25) := by
  rw [work_pair]
  simp [Resources.ListMergeWork.run_cons_cons, Resources.ListMergeWork.run_nil_right,
    Resources.bind, CallCount.tick, liftedCmp]

theorem range_work_size (n : Nat) (positive : 0 < n) :
    (Resources.SourceMergeSortWork.run natUnit (List.range n)).2 + 5 ≤
      7 * Resources.SourceMergeSort.splitSizeCost n + 10 * n := by
  have hp : 0 < (List.range n).length := by simpa only [List.length_range] using positive
  simpa only [List.length_range, Nat.reduceAdd] using
    Resources.SourceMergeSortWork.run_cost_le_size natUnit (List.range n) 1
      (fun _ _ => le_rfl) hp

theorem range_work_clog (n : Nat) :
    (Resources.SourceMergeSortWork.run natUnit (List.range n)).2 ≤
      7 * n * Nat.clog 2 n + 10 * n + 3 := by
  simpa only [List.length_range, Nat.reduceAdd] using
    Resources.SourceMergeSortWork.run_cost_le_clog natUnit (List.range n) 1
      (fun _ _ => le_rfl)

theorem range_work_isBigO :
    Asymptotics.IsBigO Filter.atTop
      (fun n => ((Resources.SourceMergeSortWork.run natUnit (List.range n)).2 : ℝ))
      (fun n => (n : ℝ) * Real.logb 2 n) :=
  Resources.SourceMergeSortWork.run_cost_isBigO natUnit List.range 1
    (fun _ _ => le_rfl) (fun _ => List.length_range)

/-! Each reached comparator test is priced; kind is inspected before occurrence ID. -/

def event (y : Int) (kind : Kind) (id : Nat) : Event Int Int :=
  ⟨y, point.x, kind, id⟩

theorem compare_lower_y :
    eventCompareRun (event 0 .delete 99) (event 1 .insert 0) = (true, 2) := rfl

theorem compare_greater_y :
    eventCompareRun (event 1 .insert 0) (event 0 .delete 99) = (false, 3) := rfl

theorem compare_lower_kind :
    eventCompareRun (event 0 .insert 99) (event 0 .delete 0) = (true, 4) := rfl

theorem compare_greater_kind :
    eventCompareRun (event 0 .delete 0) (event 0 .insert 99) = (false, 5) := rfl

theorem compare_lower_id :
    eventCompareRun (event 0 .insert 0) (event 0 .insert 1) = (true, 6) := rfl

theorem compare_equal_id :
    eventCompareRun (event 0 .insert 0) (event 0 .insert 0) = (true, 6) := rfl

theorem compare_greater_id :
    eventCompareRun (event 0 .insert 1) (event 0 .insert 0) = (false, 6) := rfl

theorem compare_equal_keys_different_payloads :
    eventCompareRun rawA rawB = (true, 6) ∧
      eventCompareRun rawB rawA = (true, 6) ∧ rawA ≠ rawB :=
  ⟨rfl, rfl, raw_payloads_differ⟩

theorem compare_raw_le_x :
    eventCompareRun (eventFor rawPoint .insert 7) (eventFor rawPoint .delete 0) =
      (true, 2) := rfl

theorem compare_lifted_y :
    eventCompareRun (eventFor liftedPoint .insert 7) (eventFor liftedPoint .delete 0) =
      (true, 4) := rfl

theorem event_comparison_contract {α : Type u} {β : Type v} [LE α] [LinearOrder β]
    (e f : Event α β) :
    (eventCompareRun e f).1 = decide (e.key ≤ f.key) ∧
      2 ≤ (eventCompareRun e f).2 ∧ (eventCompareRun e f).2 ≤ 6 :=
  ⟨eventCompareRun_value e f, eventCompareRun_cost_bounds e f⟩

theorem event_sort_contract {α : Type u} {β : Type v} [LE α] [LinearOrder β]
    (es : List (Event α β)) :
    Applications.Sorting.KeySorted Event.key (sortEventsRun es).1 ∧
      (sortEventsRun es).1.Perm es ∧
      (sortEventsRun es).2 ≤ 12 * es.length * Nat.clog 2 es.length + 10 * es.length + 3 := by
  refine ⟨?_, sortEventsRun_perm es, sortEventsRun_cost_le es⟩
  rw [sortEventsRun_value]
  exact sortEvents_sorted es

/-! Exact carried schedules exercise the real short-circuit event comparator. -/

theorem event_sort_empty : sortEventsRun ([] : List (Event Int Int)) = ([], 3) :=
  Resources.SourceMergeSortWork.run_nil eventCompareRun

theorem event_sort_point : sortEventsRun (rawEvents [point]) =
    ([eventFor point .insert 0, eventFor point .delete 0], 28) := by
  apply Prod.ext
  · exact (sortEventsRun_value _).trans point_events_eq
  · change (Resources.SourceMergeSortWork.run eventCompareRun
      [eventFor point .insert 0, eventFor point .delete 0]).2 = 28
    rw [work_pair_cost]
    rfl

theorem event_sort_duplicate : sortEventsRun (rawEvents [square, square]) =
    ([eventFor square .insert 0, eventFor square .insert 1,
      eventFor square .delete 0, eventFor square .delete 1], 92) := by
  apply Prod.ext
  · exact (sortEventsRun_value _).trans duplicate_events_eq
  · change (Resources.SourceMergeSortWork.run eventCompareRun
      [eventFor square .insert 0, eventFor square .insert 1,
        eventFor square .delete 0, eventFor square .delete 1]).2 = 92
    rw [work_four]
    simp [Resources.ListMergeWork.run_cons_cons, Resources.ListMergeWork.run_nil_left,
      Resources.bind, Resources.pure, CallCount.tick, eventCompareRun,
      eventFor, Kind.rank, square, rect]

theorem event_sort_triple : sortEventsRun (rawEvents [square, square, square]) =
    ([eventFor square .insert 0, eventFor square .insert 1, eventFor square .insert 2,
      eventFor square .delete 0, eventFor square .delete 1, eventFor square .delete 2], 179) := by
  apply Prod.ext
  · exact (sortEventsRun_value _).trans triple_events_eq
  · change (Resources.SourceMergeSortWork.run eventCompareRun
      [eventFor square .insert 0, eventFor square .insert 1, eventFor square .insert 2,
        eventFor square .delete 0, eventFor square .delete 1, eventFor square .delete 2]).2 = 179
    rw [work_six]
    simp [work_three, Resources.ListMergeWork.run_cons_cons,
      Resources.ListMergeWork.run_nil_left, Resources.ListMergeWork.run_nil_right,
      Resources.bind, Resources.pure, CallCount.tick, eventCompareRun,
      eventFor, Kind.rank, square, rect]

theorem event_sort_x_gap : sortEventsRun (rawEvents [xGap0, xGap1]) =
    ([eventFor xGap0 .insert 0, eventFor xGap1 .insert 1,
      eventFor xGap1 .delete 1, eventFor xGap0 .delete 0], 85) := by
  apply Prod.ext
  · exact (sortEventsRun_value _).trans x_gap_events_eq
  · change (Resources.SourceMergeSortWork.run eventCompareRun
      [eventFor xGap0 .insert 0, eventFor xGap1 .insert 1,
        eventFor xGap0 .delete 0, eventFor xGap1 .delete 1]).2 = 85
    rw [work_four]
    simp [Resources.ListMergeWork.run_cons_cons, Resources.ListMergeWork.run_nil_left,
      Resources.ListMergeWork.run_nil_right, Resources.bind, Resources.pure,
      CallCount.tick, eventCompareRun, eventFor, xGap0, xGap1, rect]

theorem event_sort_y_gap : sortEventsRun (rawEvents [yGap0, yGap1]) =
    ([eventFor yGap0 .insert 0, eventFor yGap0 .delete 0,
      eventFor yGap1 .insert 1, eventFor yGap1 .delete 1], 79) := by
  apply Prod.ext
  · exact (sortEventsRun_value _).trans y_gap_events_eq
  · change (Resources.SourceMergeSortWork.run eventCompareRun
      [eventFor yGap0 .insert 0, eventFor yGap1 .insert 1,
        eventFor yGap0 .delete 0, eventFor yGap1 .delete 1]).2 = 79
    rw [work_four]
    simp [Resources.ListMergeWork.run_cons_cons, Resources.ListMergeWork.run_nil_left,
      Resources.bind, Resources.pure, CallCount.tick, eventCompareRun,
      eventFor, yGap0, yGap1, rect]

theorem event_sort_reversed_y_gap : sortEventsRun (rawEvents [yGap1, yGap0]) =
    ([eventFor yGap0 .insert 1, eventFor yGap0 .delete 1,
      eventFor yGap1 .insert 0, eventFor yGap1 .delete 0], 81) := by
  apply Prod.ext
  · exact (sortEventsRun_value _).trans reversed_y_gap_events
  · change (Resources.SourceMergeSortWork.run eventCompareRun
      [eventFor yGap1 .insert 0, eventFor yGap0 .insert 1,
        eventFor yGap1 .delete 0, eventFor yGap0 .delete 1]).2 = 81
    rw [work_four]
    simp [Resources.ListMergeWork.run_cons_cons, Resources.ListMergeWork.run_nil_left,
      Resources.ListMergeWork.run_nil_right, Resources.bind, Resources.pure,
      CallCount.tick, eventCompareRun, eventFor, yGap0, yGap1, rect]

theorem event_sort_after_deletion : sortEventsRun (rawEvents [yGap0, yGap1, yGap1]) =
    ([eventFor yGap0 .insert 0, eventFor yGap0 .delete 0,
      eventFor yGap1 .insert 1, eventFor yGap1 .insert 2,
      eventFor yGap1 .delete 1, eventFor yGap1 .delete 2], 161) := by
  apply Prod.ext
  · exact (sortEventsRun_value _).trans after_deletion_events_eq
  · change (Resources.SourceMergeSortWork.run eventCompareRun
      [eventFor yGap0 .insert 0, eventFor yGap1 .insert 1, eventFor yGap1 .insert 2,
        eventFor yGap0 .delete 0, eventFor yGap1 .delete 1, eventFor yGap1 .delete 2]).2 = 161
    rw [work_six]
    simp [work_three, Resources.ListMergeWork.run_cons_cons,
      Resources.ListMergeWork.run_nil_left, Resources.ListMergeWork.run_nil_right,
      Resources.bind, Resources.pure, CallCount.tick, eventCompareRun,
      eventFor, Kind.rank, yGap0, yGap1, rect]

/-! Full stage work is paid before a successful scan can omit its suffix. -/

def fullPipeline (rs : List (Rectangle Int Int)) : Measured Bool Nat :=
  sweepRun 2 3 canonicalMakeRun sortEventsRun listInsertRun listDeleteRun listQueryRun
    7 11 [] rs

theorem fullPipeline_value (rs : List (Rectangle Int Int)) :
    (fullPipeline rs).1 = listSweep rs :=
  sweepRun_value 2 3 listOps listQuery canonicalMakeRun sortEventsRun
    listInsertRun listDeleteRun listQueryRun 7 11 (fun _ _ _ => rfl)
    sortEventsRun_value (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rs

theorem fullPipeline_geometry (rs : List (Rectangle Int Int)) :
    (fullPipeline rs).1 = true ↔ Rectangle.HasIntersection rs := by
  rw [fullPipeline_value]
  exact listSweep_correct rs

theorem fullPipeline_cost (rs : List (Rectangle Int Int)) :
    (fullPipeline rs).2 = 21 * rs.length + 4 +
      (sortEventsRun (rawEvents rs)).2 + (measuredSweep rs).2 := by
  have cost := sweepRun_cost_of_values 2 3 canonicalMakeRun sortEventsRun
    listInsertRun listDeleteRun listQueryRun 7 11 []
    (fun _ _ _ => rfl) sortEventsRun_value rs
  change (fullPipeline rs).2 = (generate rs).2 +
    (sortEventsRun (rawEvents rs)).2 + (measuredSweep rs).2 at cost
  rw [generate_work] at cost
  exact cost

theorem fullPipeline_of_stage_costs (rs : List (Rectangle Int Int))
    (sortWork : Nat) (answer : Bool) (scanWork : Nat)
    (sorted : (sortEventsRun (rawEvents rs)).2 = sortWork)
    (scanned : measuredSweep rs = (answer, scanWork)) :
    fullPipeline rs = (answer, 21 * rs.length + 4 + sortWork + scanWork) := by
  apply Prod.ext
  · calc
      (fullPipeline rs).1 = listSweep rs := fullPipeline_value rs
      _ = (measuredSweep rs).1 := (measuredSweep_value rs).symm
      _ = answer := congrArg Prod.fst scanned
  · have cost := fullPipeline_cost rs
    rw [sorted, scanned] at cost
    exact cost

/-- The scan's constant tariffs are still a declared fixture, not concrete AVL work. -/
theorem fullPipeline_declared_bound (rs : List (Rectangle Int Int)) :
    (fullPipeline rs).2 ≤
      24 * rs.length * Nat.clog 2 (2 * rs.length) + 65 * rs.length + 18 := by
  rw [fullPipeline_cost]
  have sorted := sortEventsRun_raw_cost_le rs
  have scanned := measuredSweep_work_bound rs
  omega

theorem full_pipeline_empty : fullPipeline [] = (false, 18) :=
  fullPipeline_of_stage_costs [] 3 false 11 (congrArg Prod.snd event_sort_empty) empty_work

theorem full_pipeline_point : fullPipeline [point] = (false, 88) :=
  fullPipeline_of_stage_costs [point] 28 false 35
    (congrArg Prod.snd event_sort_point) singleton_work

theorem full_pipeline_duplicate : fullPipeline [square, square] = (true, 159) :=
  fullPipeline_of_stage_costs [square, square] 92 true 21
    (congrArg Prod.snd event_sort_duplicate) duplicate_work

theorem full_pipeline_triple : fullPipeline [square, square, square] = (true, 267) :=
  fullPipeline_of_stage_costs [square, square, square] 179 true 21
    (congrArg Prod.snd event_sort_triple) triple_work

theorem full_pipeline_x_gap : fullPipeline [xGap0, xGap1] = (false, 190) :=
  fullPipeline_of_stage_costs [xGap0, xGap1] 85 false 59
    (congrArg Prod.snd event_sort_x_gap) x_gap_work

theorem full_pipeline_y_gap : fullPipeline [yGap0, yGap1] = (false, 184) :=
  fullPipeline_of_stage_costs [yGap0, yGap1] 79 false 59
    (congrArg Prod.snd event_sort_y_gap) y_gap_work

theorem reversed_y_gap_scan : measuredSweep [yGap1, yGap0] = (false, 59) := by
  rw [measuredSweep, reversed_y_gap_events]
  rw [listScanRun_miss [] _ _ rfl (by decide)]
  decide

theorem full_pipeline_reversed_y_gap : fullPipeline [yGap1, yGap0] = (false, 186) :=
  fullPipeline_of_stage_costs [yGap1, yGap0] 81 false 59
    (congrArg Prod.snd event_sort_reversed_y_gap) reversed_y_gap_scan

theorem full_pipeline_after_deletion : fullPipeline [yGap0, yGap1, yGap1] = (true, 273) :=
  fullPipeline_of_stage_costs [yGap0, yGap1, yGap1] 161 true 45
    (congrArg Prod.snd event_sort_after_deletion) after_deletion_work

end Examples.SourceMergeSortWork

import Applications.Search.RectangleSweep.MeasuredBalanced
import Examples.BalancedIntervalTrees
import Examples.SourceMergeSortWork

/-!
# Concrete field-counted balanced updates and complete sweep observations

These literal results and stage charges were derived before implementation in
the retained balanced-operation and concrete-pipeline case sheets. They consume
the actual generic updates/query, complete-key comparator, event generator and
source sorter through the concrete balanced composition.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.MeasuredBalancedRectangleSweep
open Search Search.RectangleSweep Resources
open Examples.BalancedIntervalTrees
universe u v

def completeKey (key : NKey) (id : Nat := 0) : Key Nat := toLex (key, id)

/-- Fixture conversion preserves the full summary and is not an executed update. -/
def liftTree (t : NTree) : MeasuredBalanced.Tree Nat := t.map (fun p => (completeKey p.1, p.2))

theorem comparator_short_circuits :
    MeasuredBalanced.keyLtRun (completeKey (point 0)) (completeKey (point 1)) = (true, 2) ∧
      MeasuredBalanced.keyLtRun (completeKey (point 1)) (completeKey (point 0)) = (false, 3) ∧
      MeasuredBalanced.keyLtRun (completeKey (point 0))
        (completeKey (IntervalKey.ofBounds 0 1 (by decide))) = (true, 4) ∧
      MeasuredBalanced.keyLtRun (completeKey (IntervalKey.ofBounds 0 1 (by decide)))
        (completeKey (point 0)) = (false, 5) ∧
      MeasuredBalanced.keyLtRun (completeKey (point 0) 0) (completeKey (point 0) 1) = (true, 6) ∧
      MeasuredBalanced.keyLtRun (completeKey (point 0) 1) (completeKey (point 0) 0) = (false, 6) ∧
      MeasuredBalanced.keyLtRun (completeKey (point 0) 1) (completeKey (point 0) 1) = (false, 6) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem complete_combine :
    MeasuredBalanced.combineRun (2, 20) (completeKey (point 7)) (4, 9) = ((5, 20), 4) := rfl

theorem empty_operations :
    MeasuredBalanced.insertRun sweepKey0 .nil = (leaf keyInterval sweepKey0, 8) ∧
      MeasuredBalanced.deleteRun sweepKey0 .nil = (.nil, 1) ∧
      MeasuredBalanced.splitMaxRun (.nil : MeasuredBalanced.Tree Nat) = (none, 1) ∧
      MeasuredBalanced.queryRun (.nil : MeasuredBalanced.Tree Nat) (point 0) = (false, 1) := ⟨rfl, rfl, rfl, rfl⟩

theorem indexed_update_history :
    MeasuredBalanced.insertRun sweepKey0 .nil = (leaf keyInterval sweepKey0, 8) ∧
      MeasuredBalanced.insertRun sweepKey1 (leaf keyInterval sweepKey0) = (activePair, 34) ∧
      MeasuredBalanced.insertRun sweepKey0 activePair = (activePair, 14) ∧
      MeasuredBalanced.deleteRun sweepKey0 activePair = (leaf keyInterval sweepKey1, 14) ∧
      MeasuredBalanced.deleteRun sweepKey1 (leaf keyInterval sweepKey1) = (.nil, 14) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem indexed_update_total :
    (MeasuredBalanced.insertRun sweepKey0 .nil).2 +
      (MeasuredBalanced.insertRun sweepKey1 (leaf keyInterval sweepKey0)).2 +
      (MeasuredBalanced.insertRun sweepKey0 activePair).2 + (MeasuredBalanced.deleteRun sweepKey0 activePair).2 +
      (MeasuredBalanced.deleteRun sweepKey1 (leaf keyInterval sweepKey1)).2 = 84 := rfl

def sweepKey2 : Key Nat := toLex (Examples.RectangleSweep.natSquare.x, 2)
def activeTriple : MeasuredBalanced.Tree Nat :=
  .node (sweepKey1, (2, 1)) (leaf keyInterval sweepKey0) (leaf keyInterval sweepKey2)
def afterRootDelete : MeasuredBalanced.Tree Nat :=
  .node (sweepKey0, (2, 1)) .nil (leaf keyInterval sweepKey2)

theorem indexed_rotation_and_predecessor :
    MeasuredBalanced.insertRun sweepKey2 activePair = (activeTriple, 70) ∧
      MeasuredBalanced.deleteRun sweepKey1 activeTriple = (afterRootDelete, 27) ∧
      MeasuredBalanced.queryRun (leaf keyInterval sweepKey1) (point 1) = (true, 3) := ⟨rfl, rfl, rfl⟩

theorem singleton_update_directions :
    MeasuredBalanced.insertRun (completeKey (point 0)) (liftTree (leaf id (point 1))) =
      (liftTree (.node (point 1, (2, 1)) (leaf id (point 0)) .nil), 24) ∧
      MeasuredBalanced.insertRun (completeKey (point 2)) (liftTree (leaf id (point 1))) =
      (liftTree (.node (point 1, (2, 2)) .nil (leaf id (point 2))), 27) ∧
      MeasuredBalanced.deleteRun (completeKey (point 0)) (liftTree (leaf id (point 1))) =
      (liftTree (leaf id (point 1)), 17) ∧
      MeasuredBalanced.deleteRun (completeKey (point 2)) (liftTree (leaf id (point 1))) =
      (liftTree (leaf id (point 1)), 20) ∧
      MeasuredBalanced.deleteRun (completeKey (point 1)) (liftTree (leaf id (point 1))) = (.nil, 14) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem four_insert_rotations :
    MeasuredBalanced.insertRun (completeKey rrC) (liftTree (.node (rrA, (2, 2)) .nil (leaf id rrB))) =
      (liftTree rrExpected, 56) ∧
      MeasuredBalanced.insertRun (completeKey llA) (liftTree (.node (llC, (2, 100)) (leaf id llB) .nil)) =
      (liftTree llExpected, 50) ∧
      MeasuredBalanced.insertRun (completeKey lrB) (liftTree (.node (lrC, (2, 100)) (leaf id lrA) .nil)) =
      (liftTree lrExpected, 60) ∧
      MeasuredBalanced.insertRun (completeKey rrB) (liftTree (.node (rrA, (2, 100)) .nil (leaf id rrC))) =
      (liftTree rrExpected, 60) := ⟨rfl, rfl, rfl, rfl⟩

theorem deletion_ties :
    MeasuredBalanced.deleteRun (completeKey (point 5)) (liftTree deleteLeftInput) =
      (liftTree deleteLeftExpected, 43) ∧
      MeasuredBalanced.deleteRun (completeKey (point 1)) (liftTree deleteRightInput) =
      (liftTree deleteRightExpected, 40) := ⟨rfl, rfl⟩

theorem singleton_extraction :
    MeasuredBalanced.splitMaxRun (leaf keyInterval sweepKey0) = (some (.nil, sweepKey0), 1) := rfl

/-! The universal consumers retain arbitrary raw inputs and independent coordinate universes. -/

theorem raw_primitive_values {α : Type u} [LinearOrder α] [OrderBot α]
    (key : Key α) (t : MeasuredBalanced.Tree α) (query : IntervalKey α) :
    (MeasuredBalanced.insertRun key t).1 = (IntervalTree.Balanced.deleteOps keyInterval).insert key t ∧
      (MeasuredBalanced.deleteRun key t).1 = (IntervalTree.Balanced.deleteOps keyInterval).delete key t ∧
      (MeasuredBalanced.queryRun t query).1 = IntervalTree.Balanced.search keyInterval t query :=
  ⟨MeasuredBalanced.insertRun_value key t, MeasuredBalanced.deleteRun_value key t, MeasuredBalanced.queryRun_value t query⟩

theorem raw_shape_bounds {α : Type u} [LinearOrder α] [OrderBot α]
    (key : Key α) (t : MeasuredBalanced.Tree α) (query : IntervalKey α) :
    (MeasuredBalanced.insertRun key t).2 ≤ 43 * t.height + 8 ∧
      (MeasuredBalanced.deleteRun key t).2 ≤ 43 * t.height + 1 ∧
      (MeasuredBalanced.splitMaxRun t).2 ≤ 31 * t.height + 1 ∧
      (MeasuredBalanced.queryRun t query).2 ≤ 5 * t.height + 1 :=
  ⟨MeasuredBalanced.insertRun_cost_le key t, MeasuredBalanced.deleteRun_cost_le key t,
    MeasuredBalanced.splitMaxRun_cost_le t, MeasuredBalanced.queryRun_cost_le t query⟩

theorem valid_update_values_and_work {α : Type u} [LinearOrder α] [OrderBot α]
    (key : Key α) (t : MeasuredBalanced.Tree α) (valid : IntervalTree.Balanced.Valid keyInterval t) :
    IntervalTree.Balanced.Valid keyInterval (MeasuredBalanced.insertRun key t).1 ∧
      IntervalTree.Balanced.Valid keyInterval (MeasuredBalanced.deleteRun key t).1 ∧
      (MeasuredBalanced.insertRun key t).2 ≤ 43 * t.height + 8 ∧
      (MeasuredBalanced.deleteRun key t).2 ≤ 43 * t.height + 1 :=
  ⟨MeasuredBalanced.insertRun_valid key t valid, MeasuredBalanced.deleteRun_valid key t valid,
    MeasuredBalanced.insertRun_cost_le key t, MeasuredBalanced.deleteRun_cost_le key t⟩

theorem surviving_occurrence_still_valid :
    IntervalTree.Balanced.Valid keyInterval (MeasuredBalanced.deleteRun sweepKey0 activePair).1 ∧
      (MeasuredBalanced.queryRun (MeasuredBalanced.deleteRun sweepKey0 activePair).1 (point 1)).1 = true :=
  ⟨MeasuredBalanced.deleteRun_valid sweepKey0 activePair sweep_surviving_occurrence.1, rfl⟩

theorem exact_stage_composition {α : Type u} {β : Type v}
    [LinearOrder α] [OrderBot α] [LinearOrder β] (rs : List (Rectangle α β)) :
    (MeasuredBalanced.sweepRun rs).2 = 8 * rs.length + 4 + (sortEventsRun (rawEvents rs)).2 +
      (MeasuredBalanced.scanRun .nil (events rs)).2 := MeasuredBalanced.sweepRun_cost rs

theorem geometry_at_independent_universes {α : Type u} {β : Type v}
    [LinearOrder α] [OrderBot α] [LinearOrder β] (rs : List (Rectangle α β)) :
    (MeasuredBalanced.sweepRun rs).1 = true ↔ Rectangle.HasIntersection rs :=
  MeasuredBalanced.sweepRun_eq_true_iff_hasIntersection rs

/-- Connect literal stage results through both public value and cost laws. -/
theorem sweep_of_stages {α : Type u} {β : Type v}
    [LinearOrder α] [OrderBot α] [LinearOrder β] (rs : List (Rectangle α β))
    (answer : Bool) (sorting scanning : Nat)
    (hsort : (sortEventsRun (rawEvents rs)).2 = sorting)
    (hscan : MeasuredBalanced.scanRun .nil (events rs) = (answer, scanning)) :
    MeasuredBalanced.sweepRun rs = (answer, 8 * rs.length + 4 + sorting + scanning) := by
  apply Prod.ext
  · rw [MeasuredBalanced.sweepRun_value]
    have h := congrArg Prod.fst hscan
    rw [MeasuredBalanced.scanRun_value] at h
    exact h
  · rw [MeasuredBalanced.sweepRun_cost, hsort, hscan]

/-! Every stage below refers to the actual canonical event list and source sorter. -/

open Examples.RectangleSweep (natSquare natEdge)

def natPoint : Rectangle Nat Int :=
  ⟨IntervalKey.ofBounds 2 2 le_rfl, IntervalKey.ofBounds 3 3 le_rfl⟩

theorem sort_empty_exact : sortEventsRun (rawEvents ([] : List (Rectangle Nat Int))) =
    ([], 3) := Resources.SourceMergeSortWork.run_nil eventCompareRun

theorem sort_singleton_exact : sortEventsRun (rawEvents [natSquare]) =
    ([eventFor natSquare .insert 0, eventFor natSquare .delete 0], 26) := by
  change Resources.SourceMergeSortWork.run eventCompareRun [eventFor natSquare .insert 0, eventFor natSquare .delete 0] = _
  rw [Examples.SourceMergeSortWork.work_pair]
  simp [Resources.ListMergeWork.run_cons_cons,
    Resources.ListMergeWork.run_nil_left,     Resources.bind, Resources.pure, CallCount.tick, eventCompareRun,
    eventFor, natSquare]

theorem sort_point_exact : sortEventsRun (rawEvents [natPoint]) =
    ([eventFor natPoint .insert 0, eventFor natPoint .delete 0], 28) := by
  change Resources.SourceMergeSortWork.run eventCompareRun [eventFor natPoint .insert 0, eventFor natPoint .delete 0] = _
  rw [Examples.SourceMergeSortWork.work_pair]
  simp [Resources.ListMergeWork.run_cons_cons,
    Resources.ListMergeWork.run_nil_left,     Resources.bind, Resources.pure, CallCount.tick, eventCompareRun,
    eventFor, Kind.rank, natPoint]

theorem sort_duplicate_exact : sortEventsRun (rawEvents [natSquare, natSquare]) =
    ([eventFor natSquare .insert 0, eventFor natSquare .insert 1, eventFor natSquare .delete 0, eventFor natSquare .delete 1], 92) := by
  change Resources.SourceMergeSortWork.run eventCompareRun [eventFor natSquare .insert 0, eventFor natSquare .insert 1, eventFor natSquare .delete 0, eventFor natSquare .delete 1] = _
  rw [Examples.SourceMergeSortWork.work_four]
  simp [Resources.ListMergeWork.run_cons_cons,
    Resources.ListMergeWork.run_nil_left,     Resources.bind, Resources.pure, CallCount.tick, eventCompareRun,
    eventFor, Kind.rank, natSquare]

theorem sort_triple_exact : sortEventsRun (rawEvents [natSquare, natSquare, natSquare]) =
    ([eventFor natSquare .insert 0, eventFor natSquare .insert 1, eventFor natSquare .insert 2, eventFor natSquare .delete 0, eventFor natSquare .delete 1, eventFor natSquare .delete 2], 179) := by
  change Resources.SourceMergeSortWork.run eventCompareRun [eventFor natSquare .insert 0, eventFor natSquare .insert 1, eventFor natSquare .insert 2, eventFor natSquare .delete 0, eventFor natSquare .delete 1, eventFor natSquare .delete 2] = _
  rw [Examples.SourceMergeSortWork.work_six]
  simp [Examples.SourceMergeSortWork.work_three, Resources.ListMergeWork.run_cons_cons,
    Resources.ListMergeWork.run_nil_left, Resources.ListMergeWork.run_nil_right,
    Resources.bind, Resources.pure, CallCount.tick, eventCompareRun,
    eventFor, Kind.rank, natSquare]

theorem sort_x_gap_exact : sortEventsRun (rawEvents [natSquare, xGap]) =
    ([eventFor natSquare .insert 0, eventFor xGap .insert 1, eventFor natSquare .delete 0, eventFor xGap .delete 1], 92) := by
  change Resources.SourceMergeSortWork.run eventCompareRun [eventFor natSquare .insert 0, eventFor xGap .insert 1, eventFor natSquare .delete 0, eventFor xGap .delete 1] = _
  rw [Examples.SourceMergeSortWork.work_four]
  simp [Resources.ListMergeWork.run_cons_cons,
    Resources.ListMergeWork.run_nil_left,     Resources.bind, Resources.pure, CallCount.tick, eventCompareRun,
    eventFor, Kind.rank, natSquare, xGap]

theorem sort_y_gap_exact : sortEventsRun (rawEvents [natSquare, yGap]) =
    ([eventFor natSquare .insert 0, eventFor natSquare .delete 0, eventFor yGap .insert 1, eventFor yGap .delete 1], 79) := by
  change Resources.SourceMergeSortWork.run eventCompareRun [eventFor natSquare .insert 0, eventFor yGap .insert 1, eventFor natSquare .delete 0, eventFor yGap .delete 1] = _
  rw [Examples.SourceMergeSortWork.work_four]
  simp [Resources.ListMergeWork.run_cons_cons,
    Resources.ListMergeWork.run_nil_left,     Resources.bind, Resources.pure, CallCount.tick, eventCompareRun,
    eventFor, natSquare, yGap]

theorem sort_reversed_y_gap_exact : sortEventsRun (rawEvents [yGap, natSquare]) =
    ([eventFor natSquare .insert 1, eventFor natSquare .delete 1, eventFor yGap .insert 0, eventFor yGap .delete 0], 81) := by
  change Resources.SourceMergeSortWork.run eventCompareRun [eventFor yGap .insert 0, eventFor natSquare .insert 1, eventFor yGap .delete 0, eventFor natSquare .delete 1] = _
  rw [Examples.SourceMergeSortWork.work_four]
  simp [Resources.ListMergeWork.run_cons_cons,
    Resources.ListMergeWork.run_nil_left, Resources.ListMergeWork.run_nil_right,
    Resources.bind, Resources.pure, CallCount.tick, eventCompareRun,
    eventFor, yGap, natSquare]

theorem sort_hit_after_deletion_exact : sortEventsRun (rawEvents [natSquare, yGap, yGap]) =
    ([eventFor natSquare .insert 0, eventFor natSquare .delete 0, eventFor yGap .insert 1, eventFor yGap .insert 2, eventFor yGap .delete 1, eventFor yGap .delete 2], 161) := by
  change Resources.SourceMergeSortWork.run eventCompareRun [eventFor natSquare .insert 0, eventFor yGap .insert 1, eventFor yGap .insert 2, eventFor natSquare .delete 0, eventFor yGap .delete 1, eventFor yGap .delete 2] = _
  rw [Examples.SourceMergeSortWork.work_six]
  simp [Examples.SourceMergeSortWork.work_three, Resources.ListMergeWork.run_cons_cons,
    Resources.ListMergeWork.run_nil_left, Resources.ListMergeWork.run_nil_right,
    Resources.bind, Resources.pure, CallCount.tick, eventCompareRun,
    eventFor, Kind.rank, natSquare, yGap]

/-- Exact returned sort results identify the actual scanned list before composition. -/
theorem pipeline_of_sorted {α : Type u} {β : Type v}
    [LinearOrder α] [OrderBot α] [LinearOrder β]
    (rs : List (Rectangle α β)) (es : List (Event α β))
    (sorting : Nat) (answer : Bool) (scanning : Nat)
    (hsort : sortEventsRun (rawEvents rs) = (es, sorting))
    (hscan : MeasuredBalanced.scanRun .nil es = (answer, scanning)) :
    (rawEventsRunConst 1 1 1 1 rs).2 = 8 * rs.length + 4 ∧
      (sortEventsRun (rawEvents rs)).2 = sorting ∧
      MeasuredBalanced.scanRun .nil (events rs) = (answer, scanning) ∧
      MeasuredBalanced.sweepRun rs = (answer, 8 * rs.length + 4 + sorting + scanning) := by
  have hevents : events rs = es :=
    (sortEventsRun_value (rawEvents rs)).symm.trans (congrArg Prod.fst hsort)
  have hactual : MeasuredBalanced.scanRun .nil (events rs) = (answer, scanning) := by
    rw [hevents]
    exact hscan
  exact ⟨congrArg Prod.snd (rawEventsRunConst_exact 1 1 1 1 rs),
    congrArg Prod.snd hsort, hactual,
    sweep_of_stages rs answer sorting scanning (congrArg Prod.snd hsort) hactual⟩

theorem empty_pipeline :
    (rawEventsRunConst 1 1 1 1 ([] : List (Rectangle Nat Int))).2 = 4 ∧
      (sortEventsRun (rawEvents ([] : List (Rectangle Nat Int)))).2 = 3 ∧
      MeasuredBalanced.scanRun .nil (events ([] : List (Rectangle Nat Int))) = (false, 1) ∧
      MeasuredBalanced.sweepRun ([] : List (Rectangle Nat Int)) = (false, 8) :=
  pipeline_of_sorted ([] : List (Rectangle Nat Int)) _ 3 false 1 sort_empty_exact (by rfl)

theorem singleton_pipeline :
    (rawEventsRunConst 1 1 1 1 [natSquare]).2 = 12 ∧
      (sortEventsRun (rawEvents [natSquare])).2 = 26 ∧
      MeasuredBalanced.scanRun .nil (events [natSquare]) = (false, 26) ∧
      MeasuredBalanced.sweepRun [natSquare] = (false, 64) :=
  pipeline_of_sorted [natSquare] _ 26 false 26 sort_singleton_exact (by rfl)

theorem point_pipeline :
    (rawEventsRunConst 1 1 1 1 [natPoint]).2 = 12 ∧
      (sortEventsRun (rawEvents [natPoint])).2 = 28 ∧
      MeasuredBalanced.scanRun .nil (events [natPoint]) = (false, 26) ∧
      MeasuredBalanced.sweepRun [natPoint] = (false, 66) :=
  pipeline_of_sorted [natPoint] _ 28 false 26 sort_point_exact (by rfl)

theorem duplicate_pipeline :
    (rawEventsRunConst 1 1 1 1 [natSquare, natSquare]).2 = 20 ∧
      (sortEventsRun (rawEvents [natSquare, natSquare])).2 = 92 ∧
      MeasuredBalanced.scanRun .nil (events [natSquare, natSquare]) = (true, 14) ∧
      MeasuredBalanced.sweepRun [natSquare, natSquare] = (true, 126) :=
  pipeline_of_sorted [natSquare, natSquare] _ 92 true 14 sort_duplicate_exact (by rfl)

theorem triple_pipeline :
    (rawEventsRunConst 1 1 1 1 [natSquare, natSquare, natSquare]).2 = 28 ∧
      (sortEventsRun (rawEvents [natSquare, natSquare, natSquare])).2 = 179 ∧
      MeasuredBalanced.scanRun .nil (events [natSquare, natSquare, natSquare]) = (true, 14) ∧
      MeasuredBalanced.sweepRun [natSquare, natSquare, natSquare] = (true, 221) :=
  pipeline_of_sorted [natSquare, natSquare, natSquare] _ 179 true 14 sort_triple_exact (by rfl)

theorem x_gap_pipeline :
    (rawEventsRunConst 1 1 1 1 [natSquare, xGap]).2 = 20 ∧
      (sortEventsRun (rawEvents [natSquare, xGap])).2 = 92 ∧
      MeasuredBalanced.scanRun .nil (events [natSquare, xGap]) = (false, 73) ∧
      MeasuredBalanced.sweepRun [natSquare, xGap] = (false, 185) :=
  pipeline_of_sorted [natSquare, xGap] _ 92 false 73 sort_x_gap_exact (by rfl)

theorem y_gap_pipeline :
    (rawEventsRunConst 1 1 1 1 [natSquare, yGap]).2 = 20 ∧
      (sortEventsRun (rawEvents [natSquare, yGap])).2 = 79 ∧
      MeasuredBalanced.scanRun .nil (events [natSquare, yGap]) = (false, 51) ∧
      MeasuredBalanced.sweepRun [natSquare, yGap] = (false, 150) :=
  pipeline_of_sorted [natSquare, yGap] _ 79 false 51 sort_y_gap_exact (by rfl)

theorem reversed_y_gap_pipeline :
    (rawEventsRunConst 1 1 1 1 [yGap, natSquare]).2 = 20 ∧
      (sortEventsRun (rawEvents [yGap, natSquare])).2 = 81 ∧
      MeasuredBalanced.scanRun .nil (events [yGap, natSquare]) = (false, 51) ∧
      MeasuredBalanced.sweepRun [yGap, natSquare] = (false, 152) :=
  pipeline_of_sorted [yGap, natSquare] _ 81 false 51 sort_reversed_y_gap_exact (by rfl)

theorem hit_after_deletion_pipeline :
    (rawEventsRunConst 1 1 1 1 [natSquare, yGap, yGap]).2 = 28 ∧
      (sortEventsRun (rawEvents [natSquare, yGap, yGap])).2 = 161 ∧
      MeasuredBalanced.scanRun .nil (events [natSquare, yGap, yGap]) = (true, 39) ∧
      MeasuredBalanced.sweepRun [natSquare, yGap, yGap] = (true, 228) :=
  pipeline_of_sorted [natSquare, yGap, yGap] _ 161 true 39 sort_hit_after_deletion_exact (by rfl)

theorem positive_small_inputs :
    0 < (MeasuredBalanced.sweepRun ([] : List (Rectangle Nat Int))).2 ∧
      0 < (MeasuredBalanced.sweepRun [natSquare]).2 := by
  rw [empty_pipeline.2.2.2, singleton_pipeline.2.2.2]
  decide

theorem closed_boundary_contact : (MeasuredBalanced.sweepRun [natSquare, natEdge]).1 = true := by
  rw [MeasuredBalanced.sweepRun_value]
  exact balanced_boundary_hit

theorem duplicate_occurrences_intersect : Rectangle.HasIntersection [natSquare, natSquare] :=
  (MeasuredBalanced.sweepRun_eq_true_iff_hasIntersection _).mp
    (congrArg Prod.fst duplicate_pipeline.2.2.2)

end Examples.MeasuredBalancedRectangleSweep

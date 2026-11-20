import Applications.Search.RectangleSweep.MeasuredEvents
import Examples.MeasuredRectangleSweep
import Examples.BalancedIntervalTrees

/-!
# Measured indexing, event generation, and sweep composition

The independently chosen charges are pair 2, successor 3, insertion-event
constructor 5, and deletion-event constructor 7. Generation therefore costs
21*n+4. These are declared source-model observations, including four terminal
invocations; they do not measure compiled allocation or arithmetic bit costs.

The composition fixture assigns its sorter the observation 17. Its returned
value is the actual existing sort, but 17 is not a cost theorem for that sort.
The forged-constructor and discarding-sorter controls deliberately fail value
contracts and check that executors bind the results their callbacks return.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.MeasuredRectangleEvents
open Search Search.RectangleSweep Resources
open Examples.RectangleEvents Examples.RectangleSweep Examples.MeasuredRectangleSweep
universe u v

/-! Indexing retains each occurrence, starts at the supplied offset, and charges its final successor. -/

theorem index_empty : ListIndex.run 2 3 ([] : List Empty) 100 = ([], 1) :=
  ListIndex.run_nil 2 3 100

theorem index_singleton : ListIndex.run 2 3 [7] 4 = ([(7, 4)], 7) := by
  rw [ListIndex.run_cons, ListIndex.run_nil]
  rfl

theorem index_duplicates_offset :
    ListIndex.run 2 3 [7, 7, 2] 4 = ([(7, 4), (7, 5), (2, 6)], 19) := by
  rw [ListIndex.run_exact]
  rfl

theorem index_duplicates_zero :
    ListIndex.run 2 3 [7, 7, 2] 0 = ([(7, 0), (7, 1), (2, 2)], 19) := by
  rw [ListIndex.run_exact]
  rfl

theorem index_ids :
    (ListIndex.run 2 3 [7, 7, 2] 4).1.map Prod.snd = [4, 5, 6] := by
  rw [ListIndex.run_ids]
  rfl

theorem index_length : (ListIndex.run 2 3 [7, 7, 2] 4).1.length = 3 :=
  ListIndex.run_length 2 3 [7, 7, 2] 4

theorem index_zero_tariffs : (ListIndex.run 0 0 [7, 7, 2] 4).2 = 4 :=
  ListIndex.run_cost 0 0 [7, 7, 2] 4

theorem index_preserves_payloads {α : Type u} (xs : List α) (start : Nat) :
    (ListIndex.run 2 3 xs start).1.map Prod.fst = xs := by
  simp only [ListIndex.run_value, List.zipIdx_map_fst]

/-! These clients retain only LE on both independent coordinate carriers. -/

def canonicalMakeRun {α : Type u} {β : Type v} [LE α] [LE β]
    (kind : Kind) (r : Rectangle α β) (id : Nat) : Measured (Event α β) Nat :=
  (eventFor r kind id, match kind with | .insert => 5 | .delete => 7)

def generate {α : Type u} {β : Type v} [LE α] [LE β]
    (rs : List (Rectangle α β)) : Measured (List (Event α β)) Nat :=
  rawEventsRun 2 3 canonicalMakeRun rs

theorem generate_value {α : Type u} {β : Type v} [LE α] [LE β]
    (rs : List (Rectangle α β)) : (generate rs).1 = rawEvents rs :=
  rawEventsRun_value 2 3 canonicalMakeRun (fun _ _ _ => rfl) rs

theorem generate_length {α : Type u} {β : Type v} [LE α] [LE β]
    (rs : List (Rectangle α β)) : (generate rs).1.length = 2 * rs.length :=
  rawEventsRun_length 2 3 canonicalMakeRun rs

theorem generate_work {α : Type u} {β : Type v} [LE α] [LE β]
    (rs : List (Rectangle α β)) : (generate rs).2 = 21 * rs.length + 4 :=
  rawEventsRun_cost_of_constant 2 3 5 7 canonicalMakeRun rs
    (fun _ _ => rfl) (fun _ _ => rfl)

theorem generate_exact {α : Type u} {β : Type v} [LE α] [LE β]
    (rs : List (Rectangle α β)) : generate rs = (rawEvents rs, 21 * rs.length + 4) :=
  rawEventsRunConst_exact 2 3 5 7 rs

theorem generate_ids {α : Type u} {β : Type v} [LE α] [LE β]
    (rs : List (Rectangle α β)) :
    (generate rs).1.map Event.id = List.range rs.length ++ List.range rs.length := by
  rw [generate_value]
  exact rawEvents_ids rs

theorem generate_identity_count {α : Type u} {β : Type v} [LE α] [LE β]
    (rs : List (Rectangle α β)) (kind : Kind) (id : Nat) :
    ((generate rs).1.map Event.identity).count (kind, id) =
      if id < rs.length then 1 else 0 := by
  rw [generate_value]
  exact count_identity_rawEvents rs kind id

theorem generate_nodup {α : Type u} {β : Type v} [LE α] [LE β]
    (rs : List (Rectangle α β)) : (generate rs).1.Nodup := by
  rw [generate_value]
  exact rawEvents_nodup rs

theorem empty_generation : generate ([] : List (Rectangle Int Int)) = ([], 4) := by
  rw [generate_exact]
  rfl

theorem singleton_generation : generate [point] =
    ([eventFor point .insert 0, eventFor point .delete 0], 25) := by
  rw [generate_exact]
  rfl

theorem duplicate_generation : generate [square, square] =
    ([eventFor square .insert 0, eventFor square .insert 1,
      eventFor square .delete 0, eventFor square .delete 1], 46) := by
  rw [generate_exact]
  rfl

theorem triple_generation : generate [square, square, square] =
    ([eventFor square .insert 0, eventFor square .insert 1, eventFor square .insert 2,
      eventFor square .delete 0, eventFor square .delete 1, eventFor square .delete 2], 67) := by
  rw [generate_exact]
  rfl

theorem x_gap_generation : generate [xGap0, xGap1] =
    ([eventFor xGap0 .insert 0, eventFor xGap1 .insert 1,
      eventFor xGap0 .delete 0, eventFor xGap1 .delete 1], 46) := by
  rw [generate_exact]
  rfl

theorem y_gap_generation : generate [yGap0, yGap1] =
    ([eventFor yGap0 .insert 0, eventFor yGap1 .insert 1,
      eventFor yGap0 .delete 0, eventFor yGap1 .delete 1], 46) := by
  rw [generate_exact]
  rfl

theorem reversed_y_gap_generation : generate [yGap1, yGap0] =
    ([eventFor yGap1 .insert 0, eventFor yGap0 .insert 1,
      eventFor yGap1 .delete 0, eventFor yGap0 .delete 1], 46) := by
  rw [generate_exact]
  rfl

/-- Sorting can move occurrence 1 before occurrence 0 without assigning new IDs. -/
theorem reversed_y_gap_events : events [yGap1, yGap0] =
    [eventFor yGap0 .insert 1, eventFor yGap0 .delete 1,
      eventFor yGap1 .insert 0, eventFor yGap1 .delete 0] := by
  change Applications.Sorting.SourceMergeSort.sortBy _
    [eventFor yGap1 .insert 0, eventFor yGap0 .insert 1,
      eventFor yGap1 .delete 0, eventFor yGap0 .delete 1] = _
  rw [sort_four]
  simp [Event.key, Kind.rank, eventFor, yGap0, yGap1, rect, Prod.Lex.toLex_le_toLex]

theorem reversed_sorted_ids :
    (sortEvents (generate [yGap1, yGap0]).1).map Event.id = [1, 1, 0, 0] := by
  rw [generate_value]
  change (events [yGap1, yGap0]).map Event.id = _
  rw [reversed_y_gap_events]
  rfl

theorem zero_generation_tariffs (rs : List (Rectangle Int Int)) :
    (rawEventsRunConst 0 0 0 0 rs).2 = 4 * rs.length + 4 :=
  congrArg Prod.snd (rawEventsRunConst_exact 0 0 0 0 rs)

theorem unit_generation_tariffs (rs : List (Rectangle Int Int)) :
    (rawEventsRunConst 1 1 1 1 rs).2 = 8 * rs.length + 4 :=
  congrArg Prod.snd (rawEventsRunConst_exact 1 1 1 1 rs)

theorem raw_LE_generation : generate [rawPoint] =
    ([eventFor rawPoint .insert 0, eventFor rawPoint .delete 0], 25) := by
  rw [generate_exact]
  rfl

theorem independent_universe_generation : generate [liftedPoint] =
    ([eventFor liftedPoint .insert 0, eventFor liftedPoint .delete 0], 25) := by
  rw [generate_exact]
  rfl

/-! Constructor charges depend on the actual input occurrence IDs. -/

def idPricedMakeRun (kind : Kind) (r : Rectangle Int Int) (id : Nat) :
    Measured (Event Int Int) Nat :=
  (eventFor r kind id, match kind with | .insert => id + 2 | .delete => 10 * id + 5)

theorem id_priced_value (rs : List (Rectangle Int Int)) :
    (rawEventsRun 2 3 idPricedMakeRun rs).1 = rawEvents rs :=
  rawEventsRun_value 2 3 idPricedMakeRun (fun _ _ _ => rfl) rs

theorem id_priced_singleton : (rawEventsRun 2 3 idPricedMakeRun [point]).2 = 20 := by
  rw [rawEventsRun_cost]
  rfl

theorem id_priced_duplicate :
    (rawEventsRun 2 3 idPricedMakeRun [square, square]).2 = 47 := by
  rw [rawEventsRun_cost]
  rfl

theorem id_priced_triple :
    (rawEventsRun 2 3 idPricedMakeRun [square, square, square]).2 = 85 := by
  rw [rawEventsRun_cost]
  rfl

/-! Cost and length remain meaningful when the constructor does not erase canonically. -/

def forgedMakeRun (kind : Kind) (_r : Rectangle Int Int) (_id : Nat) :
    Measured (Event Int Int) Nat :=
  (forgedY, match kind with | .insert => 5 | .delete => 7)

theorem forged_generation_value :
    (rawEventsRun 2 3 forgedMakeRun [point]).1 = [forgedY, forgedY] := rfl

theorem forged_generation_cost : (rawEventsRun 2 3 forgedMakeRun [point]).2 = 25 :=
  rawEventsRun_cost_of_constant 2 3 5 7 forgedMakeRun [point]
    (fun _ _ => rfl) (fun _ _ => rfl)

theorem forged_generation :
    rawEventsRun 2 3 forgedMakeRun [point] = ([forgedY, forgedY], 25) :=
  Prod.ext forged_generation_value forged_generation_cost

theorem forged_generation_length : (rawEventsRun 2 3 forgedMakeRun [point]).1.length = 2 :=
  rawEventsRun_length 2 3 forgedMakeRun [point]

theorem forged_generation_not_nodup : ¬ (rawEventsRun 2 3 forgedMakeRun [point]).1.Nodup := by
  rw [forged_generation_value]
  simp

theorem forged_constructor_not_erasing :
    ¬ ∀ kind r id, (forgedMakeRun kind r id).1 = eventFor r kind id := by
  intro erases
  have wrong := congrArg Event.y (erases .insert point 0)
  change (9 : Int) = 3 at wrong
  exact (by decide : (9 : Int) ≠ 3) wrong

/-! Composition pays for all generation before the later scan can return early. -/

def nominalSortRun (es : List (Event Int Int)) : Measured (List (Event Int Int)) Nat :=
  (sortEvents es, 17)

def pipeline (rs : List (Rectangle Int Int)) : Measured Bool Nat :=
  sweepRun 2 3 canonicalMakeRun nominalSortRun listInsertRun listDeleteRun listQueryRun
    7 11 [] rs

theorem pipeline_value (rs : List (Rectangle Int Int)) : (pipeline rs).1 = listSweep rs :=
  sweepRun_value 2 3 listOps listQuery canonicalMakeRun nominalSortRun
    listInsertRun listDeleteRun listQueryRun 7 11
    (fun _ _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) rs

theorem pipeline_geometry (rs : List (Rectangle Int Int)) :
    (pipeline rs).1 = true ↔ Rectangle.HasIntersection rs := by
  rw [pipeline_value]
  exact listSweep_correct rs

theorem pipeline_cost (rs : List (Rectangle Int Int)) :
    (pipeline rs).2 = 21 * rs.length + 4 + 17 + (measuredSweep rs).2 := by
  have cost := sweepRun_cost_of_values 2 3 canonicalMakeRun nominalSortRun
    listInsertRun listDeleteRun listQueryRun 7 11 []
    (fun _ _ _ => rfl) (fun _ => rfl) rs
  change (pipeline rs).2 = (generate rs).2 + 17 +
    (measuredSweep rs).2 at cost
  rw [generate_work] at cost
  exact cost

theorem pipeline_of_scan_result (rs : List (Rectangle Int Int)) (answer : Bool) (work : Nat)
    (scan_result : measuredSweep rs = (answer, work)) :
    pipeline rs = (answer, 21 * rs.length + 4 + 17 + work) := by
  apply Prod.ext
  · calc
      (pipeline rs).1 = listSweep rs := pipeline_value rs
      _ = (measuredSweep rs).1 := (measuredSweep_value rs).symm
      _ = answer := congrArg Prod.fst scan_result
  · have cost := pipeline_cost rs
    rw [scan_result] at cost
    exact cost

theorem pipeline_empty : pipeline [] = (false, 32) :=
  pipeline_of_scan_result [] false 11 empty_work

theorem pipeline_singleton : pipeline [point] = (false, 77) :=
  pipeline_of_scan_result [point] false 35 singleton_work

theorem pipeline_duplicate : pipeline [square, square] = (true, 84) :=
  pipeline_of_scan_result [square, square] true 21 duplicate_work

theorem pipeline_triple : pipeline [square, square, square] = (true, 105) :=
  pipeline_of_scan_result [square, square, square] true 21 triple_work

def discardingSortRun (_es : List (Event Int Int)) : Measured (List (Event Int Int)) Nat :=
  ([], 17)

/-- This deliberately noncanonical sorter makes the actual scan empty, despite a true query. -/
theorem discarding_sorter_control :
    sweepRun 2 3 canonicalMakeRun discardingSortRun
      listInsertRun listDeleteRun (fun _ _ => (true, 2)) 7 11 [] [point] = (false, 53) := by
  apply Prod.ext
  · rfl
  · have cost := sweepRun_cost 2 3 canonicalMakeRun discardingSortRun
      listInsertRun listDeleteRun (fun _ _ => (true, 2)) 7 11 [] [point]
    change (sweepRun 2 3 canonicalMakeRun discardingSortRun
      listInsertRun listDeleteRun (fun _ _ => (true, 2)) 7 11 [] [point]).2 =
        (generate [point]).2 + 17 + 11 at cost
    rw [generate_work] at cost
    exact cost

/-! Concrete balanced nodes count complete keys, not merely interval images. -/

theorem balanced_prefix_nodes (rs : List (Rectangle Nat Int)) (k : Nat) :
    (stateAfter (IntervalTree.Balanced.deleteOps keyInterval) .nil
      ((events rs).take k)).numNodes ≤ rs.length :=
  balanced_stateAfter_take_numNodes_le rs k

theorem balanced_duplicate_events : events [natSquare, natSquare] =
    [eventFor natSquare .insert 0, eventFor natSquare .insert 1,
      eventFor natSquare .delete 0, eventFor natSquare .delete 1] := by
  change Applications.Sorting.SourceMergeSort.sortBy _
    [eventFor natSquare .insert 0, eventFor natSquare .insert 1,
      eventFor natSquare .delete 0, eventFor natSquare .delete 1] = _
  rw [sort_four]
  simp [Event.key, Kind.rank, eventFor, natSquare, Prod.Lex.toLex_le_toLex]

theorem balanced_duplicate_active_count :
    {i : Fin [natSquare, natSquare].length | Active [natSquare, natSquare] 2 i}.ncard = 2 := by
  rw [← balanced_stateAfter_take_numNodes_eq, balanced_duplicate_events]
  rfl

theorem balanced_duplicate_full_prefix_nodes :
    ([0, 1, 2, 3, 4].map fun k =>
      (stateAfter (IntervalTree.Balanced.deleteOps keyInterval) .nil
        ((events [natSquare, natSquare]).take k)).numNodes) = [0, 1, 2, 1, 0] := by
  rw [balanced_duplicate_events]
  rfl

theorem balanced_duplicate_observation_card :
    (Trees.setTree (Trees.Cached.erase Examples.BalancedIntervalTrees.activePair)).ncard = 2 := by
  rw [balanced_observe_ncard_eq_numNodes _
    Examples.BalancedIntervalTrees.sweep_surviving_occurrence.1.2]
  rfl

def repeatedCompleteKey : BinaryTree (Key Nat × (Nat × Nat)) :=
  .node (Examples.BalancedIntervalTrees.sweepKey0, (2, 1))
    (Examples.BalancedIntervalTrees.leaf keyInterval Examples.BalancedIntervalTrees.sweepKey0) .nil

theorem repeated_complete_key_counts : repeatedCompleteKey.numNodes = 2 ∧
    (Trees.setTree (Trees.Cached.erase repeatedCompleteKey)).ncard = 1 := by
  constructor
  · rfl
  · have contents : Trees.setTree (Trees.Cached.erase repeatedCompleteKey) =
        {Examples.BalancedIntervalTrees.sweepKey0} := by
      simp [repeatedCompleteKey, Examples.BalancedIntervalTrees.leaf,
        Trees.Cached.erase, BinaryTree.map]
    rw [contents, Set.ncard_singleton]

theorem repeated_complete_key_not_strict :
    ¬ (Trees.inorder (Trees.Cached.erase repeatedCompleteKey)).Pairwise (· < ·) := by
  intro strict
  have same := balanced_observe_ncard_eq_numNodes repeatedCompleteKey strict
  rw [repeated_complete_key_counts.1, repeated_complete_key_counts.2] at same
  exact (by decide : (1 : Nat) ≠ 2) same

end Examples.MeasuredRectangleEvents

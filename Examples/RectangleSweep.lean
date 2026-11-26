import Applications.Search.RectangleSweep.Correctness
import Applications.Search.IntervalSet.OrderedList
import Applications.Search.IntervalTree.Contract
import Examples.RectangleEvents

/-!
# Executable rectangle sweep clients and separating examples

The strict-list realization works over Int without a bottom. Full update folds
describe hypothetical states after early success; `ReachedMisses` distinguishes
the prefixes through which the actual scan continues. The final sections give
independent-universe and bare-LE specializations, and connect the existing
unbalanced interval tree without making a logarithmic-cost claim.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.RectangleSweep
open Search Search.RectangleSweep
open Examples.RectangleEvents
open Applications.Sorting
universe u v

def listOps : AbstractSet.DeleteOps (Key Int) (List (Key Int)) := OrderedList.ops
def listQuery : List (Key Int) → IntervalKey Int → Bool :=
  IntervalSet.orderedListSearch keyInterval

theorem listLaws : IntervalSet.Laws listOps listQuery keyInterval
    (fun xs key => key ∈ xs) OrderedList.Strict :=
  IntervalSet.orderedListLaws keyInterval

theorem empty_scan : scan listOps listQuery [] ([] : List (Event Int Int)) = false :=
  scan_nil _ _ _

theorem singleton_raw_scan :
    scan listOps listQuery [] [eventFor point .insert 0, eventFor point .delete 0] = false := by
  decide

def listSweep (rs : List (Rectangle Int Int)) : Bool := sweep listOps listQuery rs

theorem listSweep_correct (rs : List (Rectangle Int Int)) :
    listSweep rs = true ↔ Rectangle.HasIntersection rs :=
  sweep_eq_true_iff_hasIntersection listLaws rs

theorem empty_sweep : listSweep [] = false := by
  apply Bool.eq_false_iff.mpr
  exact fun h => Rectangle.not_hasIntersection_nil ((listSweep_correct []).mp h)

theorem singleton_sweep : listSweep [point] = false := by
  apply Bool.eq_false_iff.mpr
  exact fun h => singleton_has_no_pair ((listSweep_correct [point]).mp h)

theorem duplicate_sweep : listSweep [square, square] = true :=
  (listSweep_correct _).mpr duplicate_rectangles_intersect

theorem edge_sweep : listSweep [square, edge] = true :=
  (listSweep_correct _).mpr
    ((Rectangle.hasIntersection_pair_iff _ _).mpr ⟨(0, 1), edge_common_point⟩)

theorem corner_sweep : listSweep [square, corner] = true :=
  (listSweep_correct _).mpr
    ((Rectangle.hasIntersection_pair_iff _ _).mpr ⟨(1, 1), corner_common_point⟩)

theorem flat_sweep : listSweep [flat0, flat1] = true :=
  (listSweep_correct _).mpr
    ((Rectangle.hasIntersection_pair_iff _ _).mpr ⟨(1, 1), flat_common_point⟩)

theorem x_gap_sweep : listSweep [xGap0, xGap1] = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  exact x_gap_not_intersects
    ((Rectangle.hasIntersection_pair_iff _ _).mp ((listSweep_correct _).mp h))

theorem y_gap_sweep : listSweep [yGap0, yGap1] = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  exact y_gap_not_intersects
    ((Rectangle.hasIntersection_pair_iff _ _).mp ((listSweep_correct _).mp h))

theorem negative_sweep : listSweep [negative0, negative1] = true :=
  (listSweep_correct _).mpr
    ((Rectangle.hasIntersection_pair_iff _ _).mpr ⟨(-2, -1), negative_common_point⟩)

/-! Exact carried schedules, rather than signatures with the x payload erased. -/

theorem point_events_eq : events [point] =
    [eventFor point .insert 0, eventFor point .delete 0] := by
  change SourceMergeSort.sortBy _
    [eventFor point .insert 0, eventFor point .delete 0] = _
  rw [sort_pair]
  simp [Event.key, Kind.rank, eventFor, point, rect, Prod.Lex.toLex_le_toLex]

theorem duplicate_events_eq : events [square, square] =
    [eventFor square .insert 0, eventFor square .insert 1,
      eventFor square .delete 0, eventFor square .delete 1] := by
  change SourceMergeSort.sortBy _ [eventFor square .insert 0,
    eventFor square .insert 1, eventFor square .delete 0, eventFor square .delete 1] = _
  rw [sort_four]
  simp [Event.key, Kind.rank, eventFor, square, rect, Prod.Lex.toLex_le_toLex]

theorem flat_events_eq : events [flat0, flat1] =
    [eventFor flat0 .insert 0, eventFor flat1 .insert 1,
      eventFor flat0 .delete 0, eventFor flat1 .delete 1] := by
  change SourceMergeSort.sortBy _ [eventFor flat0 .insert 0,
    eventFor flat1 .insert 1, eventFor flat0 .delete 0, eventFor flat1 .delete 1] = _
  rw [sort_four]
  simp [Event.key, Kind.rank, eventFor, flat0, flat1, rect, Prod.Lex.toLex_le_toLex]

theorem x_gap_events_eq : events [xGap0, xGap1] =
    [eventFor xGap0 .insert 0, eventFor xGap1 .insert 1,
      eventFor xGap1 .delete 1, eventFor xGap0 .delete 0] := by
  change SourceMergeSort.sortBy _ [eventFor xGap0 .insert 0,
    eventFor xGap1 .insert 1, eventFor xGap0 .delete 0, eventFor xGap1 .delete 1] = _
  rw [sort_four]
  simp [Event.key, Kind.rank, eventFor, xGap0, xGap1, rect, Prod.Lex.toLex_le_toLex]

theorem y_gap_events_eq : events [yGap0, yGap1] =
    [eventFor yGap0 .insert 0, eventFor yGap0 .delete 0,
      eventFor yGap1 .insert 1, eventFor yGap1 .delete 1] := by
  change SourceMergeSort.sortBy _ [eventFor yGap0 .insert 0,
    eventFor yGap1 .insert 1, eventFor yGap0 .delete 0, eventFor yGap1 .delete 1] = _
  rw [sort_four]
  simp [Event.key, Kind.rank, eventFor, yGap0, yGap1, rect, Prod.Lex.toLex_le_toLex]

theorem sort_three {α : Type u} (cmp : α → α → Bool) (a b c : α) :
    SourceMergeSort.sortBy cmp [a, b, c] =
      List.merge (List.merge [a] [c] cmp) [b] cmp := by
  rw [SourceMergeSort.sortBy_step cmp [a, b, c] (by simp)]
  simp [SourceMergeSort.split, sort_pair]

theorem sort_six {α : Type u} (cmp : α → α → Bool) (a b c d e f : α) :
    SourceMergeSort.sortBy cmp [a, b, c, d, e, f] =
      List.merge (List.merge (List.merge [a] [e] cmp) [c] cmp)
        (List.merge (List.merge [b] [f] cmp) [d] cmp) cmp := by
  rw [SourceMergeSort.sortBy_step cmp [a, b, c, d, e, f] (by simp)]
  simp [SourceMergeSort.split, sort_three]

theorem after_deletion_events_eq : events [yGap0, yGap1, yGap1] =
    [eventFor yGap0 .insert 0, eventFor yGap0 .delete 0,
      eventFor yGap1 .insert 1, eventFor yGap1 .insert 2,
      eventFor yGap1 .delete 1, eventFor yGap1 .delete 2] := by
  change SourceMergeSort.sortBy _ [eventFor yGap0 .insert 0,
    eventFor yGap1 .insert 1, eventFor yGap1 .insert 2, eventFor yGap0 .delete 0,
    eventFor yGap1 .delete 1, eventFor yGap1 .delete 2] = _
  rw [sort_six]
  simp [Event.key, Kind.rank, eventFor, yGap0, yGap1, rect, Prod.Lex.toLex_le_toLex]

theorem triple_events_eq : events [square, square, square] =
    [eventFor square .insert 0, eventFor square .insert 1, eventFor square .insert 2,
      eventFor square .delete 0, eventFor square .delete 1, eventFor square .delete 2] := by
  change SourceMergeSort.sortBy _ [eventFor square .insert 0,
    eventFor square .insert 1, eventFor square .insert 2, eventFor square .delete 0,
    eventFor square .delete 1, eventFor square .delete 2] = _
  rw [sort_six]
  simp [Event.key, Kind.rank, eventFor, square, rect, Prod.Lex.toLex_le_toLex]

/-! These are all-prefix folds, including updates after a scan may have returned. -/

def prefixState (rs : List (Rectangle Int Int)) (k : Nat) : List (Key Int) :=
  stateAfter listOps [] ((events rs).take k)

def prefixIds (rs : List (Rectangle Int Int)) (k : Nat) : List Nat :=
  (prefixState rs k).map (fun key => (ofLex key).2)

theorem prefix_valid (rs : List (Rectangle Int Int)) (k : Nat) :
    OrderedList.Strict (prefixState rs k) :=
  stateAfter_take_valid listLaws.toDeleteLaws rs k

theorem prefix_contents (rs : List (Rectangle Int Int)) (k : Nat) :
    {key | key ∈ prefixState rs k} = activeKeys rs k :=
  stateAfter_take_observe listLaws.toDeleteLaws rs k

theorem active_iff_key_mem (rs : List (Rectangle Int Int)) (k : Nat)
    (i : Fin rs.length) : Active rs k i ↔ occurrenceKey rs i ∈ prefixState rs k := by
  change Active rs k i ↔ occurrenceKey rs i ∈ {key | key ∈ prefixState rs k}
  rw [prefix_contents]
  change Active rs k i ↔ occurrenceKey rs i ∈ occurrenceKey rs '' {j | Active rs k j}
  constructor
  · intro h
    exact ⟨i, h, rfl⟩
  · rintro ⟨j, hj, heq⟩
    have hji := occurrenceKey_injective rs heq
    subst j
    exact hj

theorem point_prefix_ids : (List.range 3).map (prefixIds [point]) = [[], [0], []] := by
  change [prefixIds [point] 0, prefixIds [point] 1, prefixIds [point] 2] = _
  simp only [prefixIds, prefixState, point_events_eq]
  decide

theorem duplicate_prefix_ids : (List.range 5).map (prefixIds [square, square]) =
    [[], [0], [0, 1], [1], []] := by
  change [prefixIds [square, square] 0, prefixIds [square, square] 1,
    prefixIds [square, square] 2, prefixIds [square, square] 3,
    prefixIds [square, square] 4] = _
  simp only [prefixIds, prefixState, duplicate_events_eq]
  decide

theorem x_gap_prefix_ids : (List.range 5).map (prefixIds [xGap0, xGap1]) =
    [[], [0], [0, 1], [0], []] := by
  change [prefixIds [xGap0, xGap1] 0, prefixIds [xGap0, xGap1] 1,
    prefixIds [xGap0, xGap1] 2, prefixIds [xGap0, xGap1] 3,
    prefixIds [xGap0, xGap1] 4] = _
  simp only [prefixIds, prefixState, x_gap_events_eq]
  decide

theorem y_gap_prefix_ids : (List.range 5).map (prefixIds [yGap0, yGap1]) =
    [[], [0], [], [1], []] := by
  change [prefixIds [yGap0, yGap1] 0, prefixIds [yGap0, yGap1] 1,
    prefixIds [yGap0, yGap1] 2, prefixIds [yGap0, yGap1] 3,
    prefixIds [yGap0, yGap1] 4] = _
  simp only [prefixIds, prefixState, y_gap_events_eq]
  decide

theorem empty_prefix_contents (k : Nat) :
    {key | key ∈ stateAfter listOps [] ((events ([] : List (Rectangle Int Int))).take k)} =
      (∅ : Set (Key Int)) := by
  calc
    _ = activeKeys ([] : List (Rectangle Int Int)) k :=
      stateAfter_take_observe listLaws.toDeleteLaws [] k
    _ = ∅ := activeKeys_empty_of_length_le [] (by simp)

theorem exhausted_prefix_contents (rs : List (Rectangle Int Int)) {k : Nat}
    (h : (events rs).length ≤ k) : {key | key ∈ prefixState rs k} = ∅ := by
  rw [prefix_contents, activeKeys_empty_of_length_le rs h]

theorem duplicate_excessive_prefix : prefixState [square, square] 100 = [] := by
  rw [prefixState, duplicate_events_eq]
  decide

theorem point_all_misses : ReachedMisses listOps listQuery [] (events [point]) := by
  apply (scan_eq_false_iff_reachedMisses _ _ _ _).mp
  exact singleton_sweep

theorem x_gap_all_misses : ReachedMisses listOps listQuery [] (events [xGap0, xGap1]) := by
  apply (scan_eq_false_iff_reachedMisses _ _ _ _).mp
  exact x_gap_sweep

theorem y_gap_all_misses : ReachedMisses listOps listQuery [] (events [yGap0, yGap1]) := by
  apply (scan_eq_false_iff_reachedMisses _ _ _ _).mp
  exact y_gap_sweep

theorem duplicate_prefix_two_not_reached :
    ¬ ReachedMisses listOps listQuery [] ((events [square, square]).take 2) := by
  rw [← scan_eq_false_iff_reachedMisses, duplicate_events_eq]
  decide

def duplicateKey0 : Key Int := toLex (square.x, 0)
def duplicateKey1 : Key Int := toLex (square.x, 1)

theorem duplicate_keys_ne : duplicateKey0 ≠ duplicateKey1 := by decide

theorem duplicate_prefix_two : prefixState [square, square] 2 =
    [duplicateKey0, duplicateKey1] := by
  rw [prefixState, duplicate_events_eq]
  decide

/-- The scan has already hit; this is the mathematical fold after deleting ID0. -/
theorem duplicate_prefix_three : prefixState [square, square] 3 = [duplicateKey1] := by
  rw [prefixState, duplicate_events_eq]
  decide

theorem duplicate_prefix_three_not_reached :
    ¬ ReachedMisses listOps listQuery [] ((events [square, square]).take 3) := by
  rw [← scan_eq_false_iff_reachedMisses, duplicate_events_eq]
  decide

theorem duplicate_projection_survives :
    keyInterval '' {key | key ∈ prefixState [square, square] 3} = {square.x} := by
  rw [duplicate_prefix_three]
  ext q
  simp [keyInterval, duplicateKey1]

/-- Noninjective interval projection does not commute with exact-key deletion. -/
theorem projected_deletion_fails :
    keyInterval '' (({duplicateKey0, duplicateKey1} : Set (Key Int)) \ {duplicateKey0}) ≠
      (keyInterval '' ({duplicateKey0, duplicateKey1} : Set (Key Int))) \ {square.x} := by
  intro h
  have member : square.x ∈
      keyInterval '' (({duplicateKey0, duplicateKey1} : Set (Key Int)) \ {duplicateKey0}) := by
    refine ⟨duplicateKey1, ⟨Or.inr rfl, ?_⟩, rfl⟩
    exact fun heq => duplicate_keys_ne heq.symm
  have wrong := h ▸ member
  exact wrong.2 rfl

theorem flat_partial_activity : Active [flat0, flat1] 1 0 ∧ ¬ Active [flat0, flat1] 1 1 := by
  simp only [active_iff_key_mem, prefixState, flat_events_eq]
  decide

theorem flat_both_cover_y : (1 : Int) ∈ flat0.y.toSet ∧ 1 ∈ flat1.y.toSet := by
  simp only [IntervalKey.mem_toSet]
  decide

theorem flat_after_delete_activity :
    ¬ Active [flat0, flat1] 3 0 ∧ Active [flat0, flat1] 3 1 := by
  simp only [active_iff_key_mem, prefixState, flat_events_eq]
  decide

theorem after_deletion_reached :
    ReachedMisses listOps listQuery [] ((events [yGap0, yGap1, yGap1]).take 3) := by
  apply (scan_eq_false_iff_reachedMisses _ _ _ _).mp
  rw [after_deletion_events_eq]
  decide

theorem after_deletion_state : prefixState [yGap0, yGap1, yGap1] 3 =
    [toLex (yGap1.x, 1)] := by
  rw [prefixState, after_deletion_events_eq]
  decide

theorem after_deletion_hit : listSweep [yGap0, yGap1, yGap1] = true := by
  change sweep listOps listQuery _ = true
  rw [sweep_eq_suffix_of_reachedMisses listOps listQuery _ 3 after_deletion_reached,
    after_deletion_events_eq]
  decide

theorem triple_later_witness : ∃ p : Fin (events [square, square, square]).length,
    p.val = 2 ∧ ((events [square, square, square]).get p).kind = .insert ∧
      listQuery (stateAfter listOps [] ((events [square, square, square]).take p.val))
        ((events [square, square, square]).get p).x = true := by
  rw [triple_events_eq]
  refine ⟨⟨2, by decide⟩, rfl, rfl, ?_⟩
  decide

theorem triple_hit_from_later_witness : listSweep [square, square, square] = true := by
  obtain ⟨p, _, kind, hit⟩ := triple_later_witness
  exact (scan_eq_true_iff _ _ _ _).mpr ⟨p, kind, hit⟩

theorem triple_later_not_reached :
    ¬ ReachedMisses listOps listQuery [] ((events [square, square, square]).take 2) := by
  rw [← scan_eq_false_iff_reachedMisses, triple_events_eq]
  decide

/-! Deliberately wrong programs and weakened query contracts. -/

def queryAfterInsert : List (Key Int) → List (Event Int Int) → Bool
  | _, [] => false
  | s, e :: es =>
    match e.kind with
    | .insert =>
        let next := listOps.insert e.completeKey s
        if listQuery next e.x then true else queryAfterInsert next es
    | .delete => queryAfterInsert (listOps.delete e.completeKey s) es

theorem query_after_insert_false_positive :
    queryAfterInsert [] (events [point]) = true ∧ ¬ Rectangle.HasIntersection [point] := by
  constructor
  · rw [point_events_eq]
    decide
  · exact singleton_has_no_pair

theorem yOnly_edge_scan_misses : scan listOps listQuery [] (yOnly [square, edge]) = false := by
  rw [yOnly_edge_eq]
  decide

theorem yOnly_flat_scan_misses : scan listOps listQuery [] (yOnly [flat0, flat1]) = false := by
  rw [yOnly_flat_eq]
  decide

theorem idBeforeKind_flat_scan_misses :
    scan listOps listQuery [] (idBeforeKind [flat0, flat1]) = false := by
  rw [idBeforeKind_flat_eq]
  decide

theorem raw_early_hit (s : List (Key Int)) (suffix : List (Event Int Int)) :
    scan listOps (fun _ _ => true) s (eventFor point .insert 99 :: suffix) = true := rfl

theorem raw_deletion_does_not_query (s : List (Key Int)) :
    scan listOps (fun _ _ => true) s [eventFor point .delete 99] = false := rfl

theorem constant_false_query_misses :
    sweep listOps (fun _ _ => false) [square, edge] = false := by
  apply Bool.eq_false_iff.mpr
  intro hit
  obtain ⟨_, _, impossible⟩ := (scan_eq_true_iff _ _ _ _).mp hit
  exact Bool.false_ne_true impossible

theorem constant_true_query_false_positive :
    sweep listOps (fun _ _ => true) [point] = true := by
  rw [sweep, point_events_eq]
  rfl

theorem constant_false_not_laws : ¬ IntervalSet.Laws listOps (fun _ _ => false) keyInterval
    (fun xs key => key ∈ xs) OrderedList.Strict := by
  intro laws
  have overlap := laws.overlap [duplicateKey0] (OrderedList.strict_singleton _) square.x
  have witness : IntervalSet.HasOverlap (keyInterval '' {key | key ∈ [duplicateKey0]})
      square.x :=
    ⟨square.x, ⟨duplicateKey0, by simp, rfl⟩, square.x.overlap_self⟩
  exact Bool.false_ne_true (overlap.mpr witness)

theorem constant_true_not_laws : ¬ IntervalSet.Laws listOps (fun _ _ => true) keyInterval
    (fun xs key => key ∈ xs) OrderedList.Strict := by
  intro laws
  have hit := (laws.overlap [] OrderedList.strict_nil point.x).mp rfl
  rcases hit with ⟨_, ⟨key, member, _⟩, _⟩
  exact List.not_mem_nil member

/-! The executable state can inhabit a third universe, independent of both coordinates. -/

def liftedOps : AbstractSet.DeleteOps (Key Int) (ULift.{2} (List (Key Int))) where
  empty := ⟨[]⟩
  insert key s := ⟨listOps.insert key s.down⟩
  member key s := listOps.member key s.down
  delete key s := ⟨listOps.delete key s.down⟩

def liftedQuery (s : ULift.{2} (List (Key Int))) (q : IntervalKey Int) : Bool :=
  listQuery s.down q

theorem liftedLaws : IntervalSet.Laws liftedOps liftedQuery keyInterval
    (fun s key => key ∈ s.down) (fun s => OrderedList.Strict s.down) where
  empty_valid := listLaws.empty_valid
  empty key := listLaws.empty key
  insert_valid key s h := listLaws.insert_valid key s.down h
  insert key s h other := listLaws.insert key s.down h other
  member key s h := listLaws.member key s.down h
  delete_valid key s h := listLaws.delete_valid key s.down h
  delete key s h other := listLaws.delete key s.down h other
  overlap s h q := listLaws.overlap s.down h q

theorem lifted_singleton_sweep : sweep liftedOps liftedQuery [liftedPoint] = false := by
  apply Bool.eq_false_iff.mpr
  intro hit
  exact Rectangle.not_hasIntersection_singleton liftedPoint
    ((sweep_eq_true_iff_hasIntersection liftedLaws _).mp hit)

theorem lifted_duplicate_sweep : sweep liftedOps liftedQuery [liftedPoint, liftedPoint] = true :=
  (sweep_eq_true_iff_hasIntersection liftedLaws _).mpr
    ((Rectangle.hasIntersection_pair_iff _ _).mpr (Rectangle.intersects_self _))

/-! A noncomputable semantic model exercises bare LE x, without claiming common points. -/

noncomputable def semanticOps {α : Type u} [LE α] :
    AbstractSet.DeleteOps (Key α) (Set (Key α)) := by
  classical
  exact
    { empty := ∅
      insert := fun key s => Set.insert key s
      member := fun key s => decide (key ∈ s)
      delete := fun key s => s \ {key} }

noncomputable def semanticQuery {α : Type u} [LE α]
    (s : Set (Key α)) (q : IntervalKey α) : Bool := by
  classical
  exact decide (IntervalSet.HasOverlap (keyInterval '' s) q)

theorem semanticLaws {α : Type u} [LE α] :
    IntervalSet.Laws (semanticOps (α := α)) semanticQuery keyInterval id (fun _ => True) where
  empty_valid := trivial
  empty key := Set.notMem_empty key
  insert_valid _ _ _ := trivial
  insert _ _ _ _ := Iff.rfl
  member key s _ := by
    classical
    simp [semanticOps]
    rfl
  delete_valid _ _ _ := trivial
  delete key s _ other := by
    change (other ∈ s ∧ other ≠ key) ↔ (other ≠ key ∧ other ∈ s)
    exact and_comm
  overlap s _ q := by
    classical
    simp [semanticQuery]

theorem raw_duplicate_sweep : sweep semanticOps semanticQuery [rawPoint, rawPoint] = true :=
  (sweep_eq_true_iff_overlap semanticLaws _).mpr
    ⟨0, 1, by decide, Rectangle.overlap_self rawPoint⟩

theorem raw_detection_without_between :
    sweep semanticOps semanticQuery [rawPoint, rawPoint] = true ∧
      ¬ ∃ x : RawX, RawX.lo ≤ x ∧ x ≤ RawX.hi :=
  ⟨raw_duplicate_sweep, raw_no_between⟩

/-! The existing interval tree requires a bottom for its cache; it is unbalanced. -/

theorem tree_sweep_correct {α : Type u} {β : Type v}
    [LinearOrder α] [OrderBot α] [LinearOrder β] (rs : List (Rectangle α β)) :
    sweep (IntervalTree.deleteOps keyInterval) (IntervalTree.search keyInterval) rs = true ↔
      Rectangle.HasIntersection rs :=
  sweep_eq_true_iff_hasIntersection
    (IntervalTree.intervalSetLaws keyInterval keyInterval_low_le_of_lt) rs

def natSquare : Rectangle Nat Int :=
  ⟨IntervalKey.ofBounds 0 1 (by decide), IntervalKey.ofBounds 0 1 (by decide)⟩

def natEdge : Rectangle Nat Int :=
  ⟨IntervalKey.ofBounds 0 1 (by decide), IntervalKey.ofBounds 1 2 (by decide)⟩

theorem nat_edge_common_point : (0, 1) ∈ natSquare.toSet ∩ natEdge.toSet := by
  simp only [Set.mem_inter_iff, Rectangle.mem_toSet]
  decide

theorem nat_tree_boundary_hit :
    sweep (IntervalTree.deleteOps keyInterval) (IntervalTree.search keyInterval)
      [natSquare, natEdge] = true :=
  (tree_sweep_correct _).mpr
    ((Rectangle.hasIntersection_pair_iff _ _).mpr ⟨(0, 1), nat_edge_common_point⟩)

end Examples.RectangleSweep

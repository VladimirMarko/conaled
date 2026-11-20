import Applications.Search.RectangleSweep.Events
import Mathlib.Data.Fintype.Fin
import Mathlib.Order.ULift
import Mathlib.Tactic.FinCases

/-!
# Closed rectangle witnesses and occurrence-sensitive event schedules

These cases use independent point witnesses, separated intervals, and exact
event sequences to exercise the public geometry and ordering contracts.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.RectangleEvents
open Search Search.RectangleSweep Applications.Sorting
universe u v

def rect (xl xh yl yh : Int) (hx : xl ≤ xh) (hy : yl ≤ yh) : Rectangle Int Int :=
  ⟨IntervalKey.ofBounds xl xh hx, IntervalKey.ofBounds yl yh hy⟩

def point : Rectangle Int Int := rect 2 2 3 3 (by decide) (by decide)
def square : Rectangle Int Int := rect 0 1 0 1 (by decide) (by decide)
def edge : Rectangle Int Int := rect 0 1 1 2 (by decide) (by decide)
def corner : Rectangle Int Int := rect 1 2 1 2 (by decide) (by decide)
def flat0 : Rectangle Int Int := rect 0 2 1 1 (by decide) (by decide)
def flat1 : Rectangle Int Int := rect 1 3 1 1 (by decide) (by decide)
def xGap0 : Rectangle Int Int := rect 0 1 0 3 (by decide) (by decide)
def xGap1 : Rectangle Int Int := rect 2 3 1 2 (by decide) (by decide)
def yGap0 : Rectangle Int Int := rect 0 2 0 1 (by decide) (by decide)
def yGap1 : Rectangle Int Int := rect 0 2 2 3 (by decide) (by decide)
def negative0 : Rectangle Int Int := rect (-5) (-2) (-3) (-1) (by decide) (by decide)
def negative1 : Rectangle Int Int := rect (-2) 1 (-1) 2 (by decide) (by decide)

theorem point_common_point : (2, 3) ∈ point.toSet ∩ point.toSet := by
  simp only [Set.mem_inter_iff, Rectangle.mem_toSet]
  decide

theorem point_overlap : Rectangle.Overlap point point :=
  (Rectangle.overlap_iff_intersects point point).mpr ⟨(2, 3), point_common_point⟩

theorem singleton_has_no_pair : ¬ Rectangle.HasIntersection [point] :=
  Rectangle.not_hasIntersection_singleton point

theorem duplicate_rectangles_intersect : Rectangle.HasIntersection [square, square] :=
  (Rectangle.hasIntersection_pair_iff square square).mpr (Rectangle.intersects_self square)

theorem edge_common_point : (0, 1) ∈ square.toSet ∩ edge.toSet := by
  simp only [Set.mem_inter_iff, Rectangle.mem_toSet]
  decide

theorem edge_overlap : Rectangle.Overlap square edge :=
  (Rectangle.overlap_iff_intersects square edge).mpr ⟨(0, 1), edge_common_point⟩

theorem corner_common_point : (1, 1) ∈ square.toSet ∩ corner.toSet := by
  simp only [Set.mem_inter_iff, Rectangle.mem_toSet]
  decide

theorem corner_overlap : Rectangle.Overlap square corner :=
  (Rectangle.overlap_iff_intersects square corner).mpr ⟨(1, 1), corner_common_point⟩

theorem flat_common_point : (1, 1) ∈ flat0.toSet ∩ flat1.toSet := by
  simp only [Set.mem_inter_iff, Rectangle.mem_toSet]
  decide

theorem flat_overlap : Rectangle.Overlap flat0 flat1 :=
  (Rectangle.overlap_iff_intersects flat0 flat1).mpr ⟨(1, 1), flat_common_point⟩

theorem x_gap_not_intersects : ¬ Rectangle.Intersects xGap0 xGap1 := by
  rw [← Rectangle.overlap_iff_intersects]
  intro h
  have hx := h.1.1
  change (2 : Int) ≤ 1 at hx
  omega

theorem y_gap_not_intersects : ¬ Rectangle.Intersects yGap0 yGap1 := by
  rw [← Rectangle.overlap_iff_intersects]
  intro h
  have hy := h.2.1
  change (2 : Int) ≤ 1 at hy
  omega

theorem negative_common_point : (-2, -1) ∈ negative0.toSet ∩ negative1.toSet := by
  simp only [Set.mem_inter_iff, Rectangle.mem_toSet]
  decide

theorem negative_overlap : Rectangle.Overlap negative0 negative1 :=
  (Rectangle.overlap_iff_intersects negative0 negative1).mpr
    ⟨(-2, -1), negative_common_point⟩

def signature {α : Type u} {β : Type v} [LE α] (es : List (Event α β)) :
    List (β × (Kind × Nat)) := es.map (fun e => (e.y, e.identity))

theorem sort_pair {α : Type u} (cmp : α → α → Bool) (a b : α) :
    SourceMergeSort.sortBy cmp [a, b] = List.merge [a] [b] cmp := by
  rw [SourceMergeSort.sortBy_step cmp [a, b] (by simp)]
  simp [SourceMergeSort.split]

theorem sort_four {α : Type u} (cmp : α → α → Bool) (a b c d : α) :
    SourceMergeSort.sortBy cmp [a, b, c, d] =
      List.merge (List.merge [a] [c] cmp) (List.merge [b] [d] cmp) cmp := by
  rw [SourceMergeSort.sortBy_step cmp [a, b, c, d] (by simp)]
  simp [SourceMergeSort.split, sort_pair]

theorem empty_events : signature (events ([] : List (Rectangle Int Int))) = [] := by
  simp [signature]

theorem point_schedule : signature (events [point]) =
    [(3, (.insert, 0)), (3, (.delete, 0))] := by
  change signature (SourceMergeSort.sortBy _
    [eventFor point .insert 0, eventFor point .delete 0]) = _
  rw [sort_pair]
  simp [signature, Event.key, Event.identity, Kind.rank, eventFor, point, rect,
    Prod.Lex.toLex_le_toLex]

theorem duplicate_schedule : signature (events [square, square]) =
    [(0, (.insert, 0)), (0, (.insert, 1)), (1, (.delete, 0)), (1, (.delete, 1))] := by
  change signature (SourceMergeSort.sortBy _ [eventFor square .insert 0,
    eventFor square .insert 1, eventFor square .delete 0, eventFor square .delete 1]) = _
  rw [sort_four]
  simp [signature, Event.key, Event.identity, Kind.rank, eventFor, square, rect,
    Prod.Lex.toLex_le_toLex]

theorem edge_schedule : signature (events [square, edge]) =
    [(0, (.insert, 0)), (1, (.insert, 1)), (1, (.delete, 0)), (2, (.delete, 1))] := by
  change signature (SourceMergeSort.sortBy _ [eventFor square .insert 0,
    eventFor edge .insert 1, eventFor square .delete 0, eventFor edge .delete 1]) = _
  rw [sort_four]
  simp [signature, Event.key, Event.identity, Kind.rank, eventFor, square, edge, rect,
    Prod.Lex.toLex_le_toLex]

theorem corner_schedule : signature (events [square, corner]) =
    [(0, (.insert, 0)), (1, (.insert, 1)), (1, (.delete, 0)), (2, (.delete, 1))] := by
  change signature (SourceMergeSort.sortBy _ [eventFor square .insert 0,
    eventFor corner .insert 1, eventFor square .delete 0, eventFor corner .delete 1]) = _
  rw [sort_four]
  simp [signature, Event.key, Event.identity, Kind.rank, eventFor, square, corner, rect,
    Prod.Lex.toLex_le_toLex]

theorem flat_schedule : signature (events [flat0, flat1]) =
    [(1, (.insert, 0)), (1, (.insert, 1)), (1, (.delete, 0)), (1, (.delete, 1))] := by
  change signature (SourceMergeSort.sortBy _ [eventFor flat0 .insert 0,
    eventFor flat1 .insert 1, eventFor flat0 .delete 0, eventFor flat1 .delete 1]) = _
  rw [sort_four]
  simp [signature, Event.key, Event.identity, Kind.rank, eventFor, flat0, flat1, rect,
    Prod.Lex.toLex_le_toLex]

theorem x_gap_schedule : signature (events [xGap0, xGap1]) =
    [(0, (.insert, 0)), (1, (.insert, 1)), (2, (.delete, 1)), (3, (.delete, 0))] := by
  change signature (SourceMergeSort.sortBy _ [eventFor xGap0 .insert 0,
    eventFor xGap1 .insert 1, eventFor xGap0 .delete 0, eventFor xGap1 .delete 1]) = _
  rw [sort_four]
  simp [signature, Event.key, Event.identity, Kind.rank, eventFor, xGap0, xGap1, rect,
    Prod.Lex.toLex_le_toLex]

theorem y_gap_schedule : signature (events [yGap0, yGap1]) =
    [(0, (.insert, 0)), (1, (.delete, 0)), (2, (.insert, 1)), (3, (.delete, 1))] := by
  change signature (SourceMergeSort.sortBy _ [eventFor yGap0 .insert 0,
    eventFor yGap1 .insert 1, eventFor yGap0 .delete 0, eventFor yGap1 .delete 1]) = _
  rw [sort_four]
  simp [signature, Event.key, Event.identity, Kind.rank, eventFor, yGap0, yGap1, rect,
    Prod.Lex.toLex_le_toLex]

theorem negative_schedule : signature (events [negative0, negative1]) =
    [(-3, (.insert, 0)), (-1, (.insert, 1)), (-1, (.delete, 0)), (2, (.delete, 1))] := by
  change signature (SourceMergeSort.sortBy _ [eventFor negative0 .insert 0,
    eventFor negative1 .insert 1, eventFor negative0 .delete 0, eventFor negative1 .delete 1]) = _
  rw [sort_four]
  simp [signature, Event.key, Event.identity, Kind.rank, eventFor, negative0, negative1, rect,
    Prod.Lex.toLex_le_toLex]

theorem own_positions {α : Type u} {β : Type v} [LE α] [LinearOrder β]
    (rs : List (Rectangle α β)) (i : Fin rs.length) :
    ∃ p q : Fin (events rs).length, (events rs).get p = eventAt rs .insert i ∧
      (events rs).get q = eventAt rs .delete i ∧ p < q := by
  obtain ⟨p, hp, _⟩ := existsUnique_position rs .insert i
  obtain ⟨q, hq, _⟩ := existsUnique_position rs .delete i
  exact ⟨p, q, hp, hq, own_insert_position_lt_delete rs i p q hp hq⟩

theorem point_positions : ∃ p q : Fin (events [point]).length,
    (events [point]).get p = eventAt [point] .insert 0 ∧
    (events [point]).get q = eventAt [point] .delete 0 ∧ p < q :=
  own_positions [point] 0

theorem flat_cross_positions (i j : Fin 2) :
    ∃ p q : Fin (events [flat0, flat1]).length,
      (events [flat0, flat1]).get p = eventAt [flat0, flat1] .insert i ∧
      (events [flat0, flat1]).get q = eventAt [flat0, flat1] .delete j ∧ p < q := by
  obtain ⟨p, hp, _⟩ := existsUnique_position [flat0, flat1] .insert i
  obtain ⟨q, hq, _⟩ := existsUnique_position [flat0, flat1] .delete j
  refine ⟨p, q, hp, hq, insert_position_lt_delete (events_sorted _) p q ?_ ?_ ?_⟩
  · rw [hp]; rfl
  · rw [hq]; rfl
  · rw [hp, hq]
    fin_cases i <;> fin_cases j <;> decide

theorem duplicate_distinct_insertions : eventAt [square, square] .insert 0 ≠
    eventAt [square, square] .insert 1 := by
  intro h
  have hi : (0 : Nat) = 1 := congrArg Event.id h
  omega

theorem point_counts (kind : Kind) :
    ((events [point]).map Event.identity).count (kind, 0) = 1 := by
  simpa using count_identity_events [point] kind 0

theorem point_total_count : ((events [point]).map Event.id).count 0 = 2 := by
  simpa using count_id_events [point] 0

theorem out_of_range_count (kind : Kind) :
    ((events [point]).map Event.identity).count (kind, 2) = 0 := by
  simpa using count_identity_events [point] kind 2

inductive RawX where
  | lo
  | hi

instance : LE RawX := ⟨fun a b => a = .lo ∧ b = .hi⟩

theorem raw_no_between : ¬ ∃ x : RawX, RawX.lo ≤ x ∧ x ≤ RawX.hi := by
  rintro ⟨x, ⟨_, hhi⟩, ⟨hlo, _⟩⟩
  cases hhi.symm.trans hlo

def rawPoint : Rectangle RawX Int :=
  ⟨IntervalKey.ofBounds .lo .hi ⟨rfl, rfl⟩,
    IntervalKey.ofBounds 0 1 (by decide)⟩

theorem raw_sort_contract : KeySorted Event.key (events [rawPoint]) ∧
    (events [rawPoint]).Perm (rawEvents [rawPoint]) :=
  ⟨events_sorted _, events_perm _⟩

theorem raw_payload (e : Event RawX Int) (he : e ∈ events [rawPoint]) : e.x = rawPoint.x := by
  rcases (mem_events_iff [rawPoint] e).mp he with ⟨kind, i, rfl⟩
  have hi : i = 0 := by
    apply Fin.ext
    change i.val = 0
    have h := i.isLt
    simp only [List.length_cons, List.length_nil] at h
    omega
  subst i
  rfl

theorem raw_counts (kind : Kind) :
    ((events [rawPoint]).map Event.identity).count (kind, 0) = 1 := by
  simpa using count_identity_events [rawPoint] kind 0

theorem raw_positions : ∃ p q : Fin (events [rawPoint]).length,
    (events [rawPoint]).get p = eventAt [rawPoint] .insert 0 ∧
    (events [rawPoint]).get q = eventAt [rawPoint] .delete 0 ∧ p < q :=
  own_positions [rawPoint] 0

def liftedPoint : Rectangle Int (ULift.{1} Int) :=
  ⟨point.x, IntervalKey.ofBounds ⟨3⟩ ⟨3⟩ le_rfl⟩

theorem lifted_common_point : (2, ULift.up 3) ∈ liftedPoint.toSet ∩ liftedPoint.toSet := by
  simp only [Set.mem_inter_iff, Rectangle.mem_toSet]
  decide

theorem lifted_overlap : Rectangle.Overlap liftedPoint liftedPoint :=
  (Rectangle.overlap_iff_intersects liftedPoint liftedPoint).mpr
    ⟨(2, ULift.up 3), lifted_common_point⟩

theorem lifted_counts (kind : Kind) :
    ((events [liftedPoint]).map Event.identity).count (kind, 0) = 1 := by
  simpa using count_identity_events [liftedPoint] kind 0

theorem lifted_positions : ∃ p q : Fin (events [liftedPoint]).length,
    (events [liftedPoint]).get p = eventAt [liftedPoint] .insert 0 ∧
    (events [liftedPoint]).get q = eventAt [liftedPoint] .delete 0 ∧ p < q :=
  own_positions [liftedPoint] 0

theorem edge_cross_positions : ∃ p q : Fin (events [square, edge]).length,
    (events [square, edge]).get p = eventAt [square, edge] .insert 1 ∧
    (events [square, edge]).get q = eventAt [square, edge] .delete 0 ∧ p < q := by
  obtain ⟨p, hp, _⟩ := existsUnique_position [square, edge] .insert 1
  obtain ⟨q, hq, _⟩ := existsUnique_position [square, edge] .delete 0
  refine ⟨p, q, hp, hq, insert_position_lt_delete (events_sorted _) p q ?_ ?_ ?_⟩
  · rw [hp]; rfl
  · rw [hq]; rfl
  · rw [hp, hq]; decide

def rawA : Event Int Int := ⟨0, IntervalKey.ofBounds 0 0 (by decide), .insert, 0⟩
def rawB : Event Int Int := ⟨0, IntervalKey.ofBounds 1 1 (by decide), .insert, 0⟩

theorem raw_keys_equal : rawA.key = rawB.key := rfl

theorem raw_payloads_differ : rawA ≠ rawB := by
  intro h
  have hx : (0 : Int) = 1 := congrArg (fun e : Event Int Int => e.x.low) h
  omega

theorem raw_both_comparisons : rawA.key ≤ rawB.key ∧ rawB.key ≤ rawA.key :=
  ⟨raw_keys_equal.le, raw_keys_equal.symm.le⟩

theorem raw_inconsistent_sort : KeySorted Event.key (sortEvents [rawA, rawB]) ∧
    (sortEvents [rawA, rawB]).Perm [rawA, rawB] :=
  ⟨sortEvents_sorted _, sortEvents_perm _⟩

theorem raw_repeated_identity : ¬ ([rawA, rawB].map Event.identity).Nodup := by
  simp [rawA, rawB, Event.identity]

theorem inconsistent_events_not_both_generated (rs : List (Rectangle Int Int)) :
    ¬ (rawA ∈ events rs ∧ rawB ∈ events rs) := by
  rintro ⟨ha, hb⟩
  exact raw_payloads_differ (eq_of_key_eq_of_mem_events ha hb raw_keys_equal)

/-- Intentionally incomplete comparator, used to reject a plausible wrong contract. -/
def yOnly (rs : List (Rectangle Int Int)) : List (Event Int Int) :=
  SourceMergeSort.sortOn Event.y (rawEvents rs)

def idBeforeKindKey (e : Event Int Int) : Int ×ₗ (Nat ×ₗ Nat) :=
  toLex (e.y, toLex (e.id, e.kind.rank))

/-- Intentionally wrong at shared boundaries: occurrence ID precedes event kind. -/
def idBeforeKind (rs : List (Rectangle Int Int)) : List (Event Int Int) :=
  SourceMergeSort.sortOn idBeforeKindKey (rawEvents rs)

theorem yOnly_edge_eq : yOnly [square, edge] =
    [eventFor square .insert 0, eventFor square .delete 0,
      eventFor edge .insert 1, eventFor edge .delete 1] := by
  change SourceMergeSort.sortBy _ [eventFor square .insert 0,
    eventFor edge .insert 1, eventFor square .delete 0, eventFor edge .delete 1] = _
  rw [sort_four]
  simp [eventFor, square, edge, rect]

theorem yOnly_flat_eq : yOnly [flat0, flat1] =
    [eventFor flat0 .insert 0, eventFor flat0 .delete 0,
      eventFor flat1 .insert 1, eventFor flat1 .delete 1] := by
  change SourceMergeSort.sortBy _ [eventFor flat0 .insert 0,
    eventFor flat1 .insert 1, eventFor flat0 .delete 0, eventFor flat1 .delete 1] = _
  rw [sort_four]
  simp [eventFor, flat0, flat1, rect]

theorem idBeforeKind_flat_eq : idBeforeKind [flat0, flat1] =
    [eventFor flat0 .insert 0, eventFor flat0 .delete 0,
      eventFor flat1 .insert 1, eventFor flat1 .delete 1] := by
  change SourceMergeSort.sortBy _ [eventFor flat0 .insert 0,
    eventFor flat1 .insert 1, eventFor flat0 .delete 0, eventFor flat1 .delete 1] = _
  rw [sort_four]
  simp [idBeforeKindKey, eventFor, flat0, flat1, rect, Kind.rank, Prod.Lex.toLex_le_toLex]

theorem yOnly_edge_not_insertionsFirst : ¬ InsertionsFirst (yOnly [square, edge]) := by
  rw [yOnly_edge_eq]
  intro h
  have hbad : (2 : Nat) < 1 := h ⟨2, by decide⟩ ⟨1, by decide⟩ rfl rfl rfl
  omega

theorem yOnly_flat_not_insertionsFirst : ¬ InsertionsFirst (yOnly [flat0, flat1]) := by
  rw [yOnly_flat_eq]
  intro h
  have hbad : (2 : Nat) < 1 := h ⟨2, by decide⟩ ⟨1, by decide⟩ rfl rfl rfl
  omega

theorem idBeforeKind_flat_not_insertionsFirst :
    ¬ InsertionsFirst (idBeforeKind [flat0, flat1]) := by
  rw [idBeforeKind_flat_eq]
  intro h
  have hbad : (2 : Nat) < 1 := h ⟨2, by decide⟩ ⟨1, by decide⟩ rfl rfl rfl
  omega

theorem correct_flat_insertionsFirst : InsertionsFirst (events [flat0, flat1]) :=
  events_insertionsFirst _

theorem yOnly_flat_identities_nodup :
    ((yOnly [flat0, flat1]).map Event.identity).Nodup := by
  have h := (SourceMergeSort.sortOn_correct Event.y (rawEvents [flat0, flat1])).2.map
    Event.identity
  exact h.nodup_iff.mpr (rawEvents_identities_nodup _)

theorem yOnly_flat_counts (kind : Kind) (i : Fin 2) :
    ((yOnly [flat0, flat1]).map Event.identity).count (kind, i.val) = 1 := by
  have h := ((SourceMergeSort.sortOn_correct Event.y (rawEvents [flat0, flat1])).2.map
    Event.identity).count_eq (kind, i.val)
  rw [count_identity_rawEvents] at h
  simpa [yOnly, i.isLt] using h

theorem yOnly_flat_own_positions (i : Fin 2) :
    ∃ p q : Fin (yOnly [flat0, flat1]).length,
      (yOnly [flat0, flat1]).get p = eventAt [flat0, flat1] .insert i ∧
      (yOnly [flat0, flat1]).get q = eventAt [flat0, flat1] .delete i ∧ p < q := by
  rw [yOnly_flat_eq]
  fin_cases i
  · exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩, rfl, rfl, by decide⟩
  · exact ⟨⟨2, by decide⟩, ⟨3, by decide⟩, rfl, rfl, by decide⟩

def forgedY : Event Int Int := { eventFor point .insert 0 with y := 9 }
def forgedX : Event Int Int :=
  { eventFor point .insert 0 with x := IntervalKey.ofBounds 9 9 (by decide) }

theorem forgedY_not_raw : forgedY ∉ rawEvents [point] := by
  intro h
  have hy := congrArg Event.y (eq_eventAt_of_mem_rawEvents h)
  change (9 : Int) = 3 at hy
  omega

theorem forgedY_not_sorted : forgedY ∉ events [point] := by
  intro h
  have hy := congrArg Event.y (eq_eventAt_of_mem_events h)
  change (9 : Int) = 3 at hy
  omega

theorem forgedX_not_sorted : forgedX ∉ events [point] := by
  intro h
  have hx := congrArg (fun e : Event Int Int => e.x.low) (eq_eventAt_of_mem_events h)
  change (9 : Int) = 2 at hx
  omega

theorem point_generated_payload (e : Event Int Int) (he : e ∈ events [point]) :
    e.x = point.x ∧ e.id = 0 ∧ e.y = 3 := by
  rcases (mem_events_iff [point] e).mp he with ⟨kind, i, rfl⟩
  have hi : i = 0 := by
    apply Fin.ext
    change i.val = 0
    have h := i.isLt
    simp only [List.length_cons, List.length_nil] at h
    omega
  subst i
  cases kind <;> exact ⟨rfl, rfl, rfl⟩

end Examples.RectangleEvents

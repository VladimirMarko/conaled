import Applications.Search.RectangleSweep.Measured
import Applications.Search.RectangleSweep.ActiveCardinality
import Examples.RectangleSweep
import Mathlib.Algebra.FreeMonoid.Basic

/-!
# Measured rectangle scan clients

These examples use the existing strict-list rectangle client and its exact
carried schedules. The work fixture charges 7 per visited event, 11 at the
empty suffix, and 2/3/5 for query/insertion/deletion. It is an observation model,
not a claim about the cost of list operations, event creation, or sorting.

The raw-state sentinel distinguishes the states returned by the primitives.
Its ordered observation uses the existing free additive monoid and the public
scan executor; no additional execution or trace backend is introduced.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.MeasuredRectangleSweep
open Search Search.RectangleSweep Resources
open Examples.RectangleEvents Examples.RectangleSweep

abbrev ListState := List (Key Int)

def listInsertRun (key : Key Int) (state : ListState) : Measured ListState Nat :=
  (listOps.insert key state, 3)

def listDeleteRun (key : Key Int) (state : ListState) : Measured ListState Nat :=
  (listOps.delete key state, 5)

def listQueryRun (state : ListState) (interval : IntervalKey Int) : Measured Bool Nat :=
  (listQuery state interval, 2)

def listScanRun (state : ListState) (es : List (Event Int Int)) : Measured Bool Nat :=
  scanRun listInsertRun listDeleteRun listQueryRun 7 11 state es

def measuredSweep (rs : List (Rectangle Int Int)) : Measured Bool Nat :=
  listScanRun [] (events rs)

theorem listScanRun_value (state : ListState) (es : List (Event Int Int)) :
    (listScanRun state es).1 = scan listOps listQuery state es :=
  scanRun_value listOps listQuery listInsertRun listDeleteRun listQueryRun 7 11
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) state es

/-- Exact work is determined by executed calls and whether the empty suffix is reached. -/
theorem listScanRun_exact_work (state : ListState) (es : List (Event Int Int)) :
    (listScanRun state es).2 =
      let r := scanCounts listOps listQuery state es
      r.2.1 * 2 + r.2.2.1 * 3 + r.2.2.2 * 5 +
        (r.2.1 + r.2.2.2) * 7 + if r.1 then 0 else 11 :=
  scanRun_constant_cost listOps listQuery 2 3 5 7 11 state es

theorem listScanRun_reweight (h : Nat →+ Nat) (state : ListState)
    (es : List (Event Int Int)) :
    reweight h (listScanRun state es) =
      scanRun (fun key s => (listOps.insert key s, h 3))
        (fun key s => (listOps.delete key s, h 5))
        (fun s interval => (listQuery s interval, h 2)) (h 7) (h 11) state es :=
  scanRun_reweight h listInsertRun listDeleteRun listQueryRun 7 11 state es

theorem measuredSweep_value (rs : List (Rectangle Int Int)) :
    (measuredSweep rs).1 = listSweep rs :=
  listScanRun_value [] (events rs)

theorem measuredSweep_correct (rs : List (Rectangle Int Int)) :
    (measuredSweep rs).1 = true ↔ Rectangle.HasIntersection rs := by
  rw [measuredSweep_value]
  exact listSweep_correct rs

/-- This bound is for the chosen constant observation charges, not list-operation work. -/
theorem measuredSweep_work_bound (rs : List (Rectangle Int Int)) :
    (measuredSweep rs).2 ≤
      2 * rs.length * 7 + rs.length * (2 + 3) + rs.length * 5 + 11 :=
  scanRun_events_cost_le (AddMonoidHom.id Nat)
    listInsertRun listDeleteRun listQueryRun 7 11
    (fun _ => True) (fun _ => True)
    (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial) 2 3 5
    (fun _ _ _ _ => le_rfl) (fun _ _ _ _ => le_rfl) (fun _ _ _ _ => le_rfl)
    rs (fun _ _ => trivial) [] trivial

theorem listScanRun_miss (state : ListState) (e : Event Int Int)
    (es : List (Event Int Int)) (kind : e.kind = .insert)
    (miss : listQuery state e.x = false) :
    listScanRun state (e :: es) =
      let r := listScanRun (listOps.insert e.completeKey state) es
      (r.1, 7 + (2 + (3 + r.2))) := by
  simpa only [listScanRun, listQueryRun, listInsertRun, Resources.bind] using
    scanRun_insert_miss listInsertRun listDeleteRun listQueryRun 7 11
      state e es kind miss

theorem listScanRun_hit (state : ListState) (e : Event Int Int)
    (es : List (Event Int Int)) (kind : e.kind = .insert)
    (hit : listQuery state e.x = true) : listScanRun state (e :: es) = (true, 9) :=
  scanRun_insert_hit listInsertRun listDeleteRun listQueryRun 7 11 state e es kind hit

theorem listScanRun_delete (state : ListState) (e : Event Int Int)
    (es : List (Event Int Int)) (kind : e.kind = .delete) :
    listScanRun state (e :: es) =
      let r := listScanRun (listOps.delete e.completeKey state) es
      (r.1, 7 + (5 + r.2)) := by
  simpa only [listScanRun, listDeleteRun, Resources.bind] using
    scanRun_delete listInsertRun listDeleteRun listQueryRun 7 11 state e es kind

/-! Empty input has a positive terminal observation and performs no primitive. -/

theorem empty_arbitrary_state (state : ListState) :
    listScanRun state [] = (false, 11) :=
  scanRun_nil listInsertRun listDeleteRun listQueryRun 7 11 state

theorem empty_work : measuredSweep [] = (false, 11) := by
  simp only [measuredSweep, events_nil, empty_arbitrary_state]

theorem empty_counts :
    scanCounts listOps listQuery [] ([] : List (Event Int Int)) = (false, (0, 0, 0)) :=
  scanCounts_nil listOps listQuery []

theorem positive_empty_work : 0 < (listScanRun [] []).2 := by
  rw [empty_arbitrary_state]
  decide

/-! Exact schedule clients. A duplicate hit consumes only two of four events. -/

theorem singleton_work : measuredSweep [point] = (false, 35) := by
  rw [measuredSweep, point_events_eq]
  rw [listScanRun_miss [] _ _ rfl (by decide)]
  decide

theorem duplicate_work : measuredSweep [square, square] = (true, 21) := by
  rw [measuredSweep, duplicate_events_eq]
  rw [listScanRun_miss [] _ _ rfl (by decide)]
  decide

theorem triple_work : measuredSweep [square, square, square] = (true, 21) := by
  rw [measuredSweep, triple_events_eq]
  rw [listScanRun_miss [] _ _ rfl (by decide)]
  decide

theorem x_gap_work : measuredSweep [xGap0, xGap1] = (false, 59) := by
  rw [measuredSweep, x_gap_events_eq]
  rw [listScanRun_miss [] _ _ rfl (by decide)]
  decide

theorem y_gap_work : measuredSweep [yGap0, yGap1] = (false, 59) := by
  rw [measuredSweep, y_gap_events_eq]
  rw [listScanRun_miss [] _ _ rfl (by decide)]
  decide

theorem after_deletion_work : measuredSweep [yGap0, yGap1, yGap1] = (true, 45) := by
  rw [measuredSweep, after_deletion_events_eq]
  rw [listScanRun_miss [] _ _ rfl (by decide)]
  decide

/-- Geometric nonintersection supplies the exhaustion premise of the count theorem. -/
theorem counts_of_no_hit (rs : List (Rectangle Int Int)) (miss : listSweep rs = false) :
    scanCounts listOps listQuery [] (events rs) =
      (false, (rs.length, rs.length, rs.length)) := by
  have erased : (scanCounts listOps listQuery [] (events rs)).1 = false := by
    rw [scanCounts_value]
    exact miss
  exact Prod.ext erased (scanCounts_events_of_false listOps listQuery [] rs erased)

theorem singleton_counts :
    scanCounts listOps listQuery [] (events [point]) = (false, (1, 1, 1)) :=
  counts_of_no_hit [point] singleton_sweep

theorem x_gap_counts :
    scanCounts listOps listQuery [] (events [xGap0, xGap1]) = (false, (2, 2, 2)) :=
  counts_of_no_hit [xGap0, xGap1] x_gap_sweep

theorem y_gap_counts :
    scanCounts listOps listQuery [] (events [yGap0, yGap1]) = (false, (2, 2, 2)) :=
  counts_of_no_hit [yGap0, yGap1] y_gap_sweep

theorem duplicate_counts :
    scanCounts listOps listQuery [] (events [square, square]) = (true, (2, 1, 0)) := by
  rw [duplicate_events_eq]
  rw [scanCounts_insert_miss listOps listQuery [] _ _ rfl (by decide)]
  decide

theorem triple_counts :
    scanCounts listOps listQuery [] (events [square, square, square]) = (true, (2, 1, 0)) := by
  rw [triple_events_eq]
  rw [scanCounts_insert_miss listOps listQuery [] _ _ rfl (by decide)]
  decide

theorem after_deletion_counts :
    scanCounts listOps listQuery [] (events [yGap0, yGap1, yGap1]) = (true, (3, 2, 1)) := by
  rw [after_deletion_events_eq]
  rw [scanCounts_insert_miss listOps listQuery [] _ _ rfl (by decide)]
  decide

theorem duplicate_counts_bounded :
    (scanCounts listOps listQuery [] (events [square, square])).2.1 ≤ 2 ∧
      (scanCounts listOps listQuery [] (events [square, square])).2.2.1 ≤ 2 ∧
      (scanCounts listOps listQuery [] (events [square, square])).2.2.2 ≤ 2 :=
  scanCounts_events_le listOps listQuery [] [square, square]

theorem duplicate_one_query_without_insert :
    (scanCounts listOps listQuery [] (events [square, square])).2.1 =
      (scanCounts listOps listQuery [] (events [square, square])).2.2.1 + 1 := by
  have h := scanCounts_queries_eq listOps listQuery [] (events [square, square])
  have hit : (scanCounts listOps listQuery [] (events [square, square])).1 = true := by
    rw [scanCounts_value]
    exact duplicate_sweep
  rw [hit] at h
  exact h

/-!
Cardinality describes the full mathematical update fold, including prefixes
after an earlier hit. Complete keys retain occurrence IDs; projection to just
the interval need not preserve this cardinality.
-/

theorem prefix_keys_finite (rs : List (Rectangle Int Int)) (k : Nat) :
    {key | key ∈ prefixState rs k}.Finite :=
  stateAfter_take_observe_finite list_laws.toDeleteLaws rs k

theorem prefix_card_eq_active (rs : List (Rectangle Int Int)) (k : Nat) :
    {key | key ∈ prefixState rs k}.ncard =
      {i : Fin rs.length | Active rs k i}.ncard :=
  stateAfter_take_observe_ncard_eq list_laws.toDeleteLaws rs k

theorem prefix_card_le (rs : List (Rectangle Int Int)) (k : Nat) :
    {key | key ∈ prefixState rs k}.ncard ≤ rs.length :=
  stateAfter_take_observe_ncard_le list_laws.toDeleteLaws rs k

theorem initial_prefix_card (rs : List (Rectangle Int Int)) :
    {key | key ∈ prefixState rs 0}.ncard = 0 := by
  rw [prefix_contents, activeKeys_zero]
  exact Set.ncard_empty (Key Int)

theorem exhausted_prefix_card (rs : List (Rectangle Int Int)) {k : Nat}
    (exhausted : (events rs).length ≤ k) :
    {key | key ∈ prefixState rs k}.ncard = 0 := by
  rw [exhausted_prefix_contents rs exhausted]
  exact Set.ncard_empty (Key Int)

theorem duplicate_active_keys_finite (k : Nat) :
    (activeKeys [square, square] k).Finite :=
  activeKeys_finite [square, square] k

theorem duplicate_active_card_bound (k : Nat) :
    (activeKeys [square, square] k).ncard ≤ 2 :=
  activeKeys_ncard_le [square, square] k

theorem duplicate_prefix_two_contents :
    {key | key ∈ prefixState [square, square] 2} = {duplicateKey0, duplicateKey1} := by
  rw [duplicate_prefix_two]
  ext key
  simp

theorem duplicate_prefix_two_card :
    {key | key ∈ prefixState [square, square] 2}.ncard = 2 := by
  rw [duplicate_prefix_two_contents]
  exact Set.ncard_pair duplicate_keys_ne

/-- The public injectivity bridge counts two active occurrences of equal rectangle values. -/
theorem duplicate_active_occurrences_card :
    {i : Fin [square, square].length | Active [square, square] 2 i}.ncard = 2 := by
  rw [← activeKeys_ncard_eq [square, square] 2, ← prefix_contents [square, square] 2]
  exact duplicate_prefix_two_card

theorem duplicate_interval_projection_card :
    (keyInterval '' {key | key ∈ prefixState [square, square] 2}).ncard = 1 := by
  rw [duplicate_prefix_two_contents, Set.image_insert_eq, Set.image_singleton]
  change ({square.x, square.x} : Set (IntervalKey Int)).ncard = 1
  simp

/-- The second hypothetical insertion increases cardinality, but the actual scan skips it. -/
theorem duplicate_full_prefix_and_actual_scan :
    {key | key ∈ prefixState [square, square] 2}.ncard = 2 ∧
      ¬ ReachedMisses listOps listQuery [] ((events [square, square]).take 2) ∧
      scanCounts listOps listQuery [] (events [square, square]) = (true, (2, 1, 0)) :=
  ⟨duplicate_prefix_two_card, duplicate_prefix_two_not_reached, duplicate_counts⟩

/-! Raw branch controls do not assume interval-set laws or valid event schedules. -/

theorem raw_hit_skips_insert_and_suffix (state : ListState) (suffix : List (Event Int Int)) :
    scanRun listInsertRun listDeleteRun (fun _ _ => (true, 2)) 7 11 state
      (eventFor point .insert 99 :: suffix) = (true, 9) :=
  scanRun_insert_hit listInsertRun listDeleteRun (fun _ _ => (true, 2)) 7 11
    state (eventFor point .insert 99) suffix rfl rfl

theorem raw_deletion_does_not_query (state : ListState) :
    scanRun listInsertRun listDeleteRun (fun _ _ => (true, 1000)) 7 11 state
      [eventFor point .delete 99] = (false, 23) := by
  rw [scanRun_delete listInsertRun listDeleteRun (fun _ _ => (true, 1000)) 7 11
    state (eventFor point .delete 99) [] rfl]
  rfl

theorem raw_deletion_counts (state : ListState) :
    scanCounts listOps (fun _ _ => true) state [eventFor point .delete 99] =
      (false, (0, 0, 1)) := by
  rw [scanCounts_delete listOps (fun _ _ => true) state (eventFor point .delete 99) [] rfl]
  rfl

/-- Insertion is charged even when the complete key already belongs to the set. -/
theorem repeated_key_work :
    scanRun listInsertRun listDeleteRun (fun _ _ => (false, 2)) 7 11 []
      [eventFor point .insert 0, eventFor point .insert 0, eventFor point .delete 0] =
        (false, 47) := by decide

theorem repeated_key_counts :
    scanCounts listOps (fun _ _ => false) []
      [eventFor point .insert 0, eventFor point .insert 0, eventFor point .delete 0] =
        (false, (2, 2, 1)) := by decide

/-! Stateful sentinel: actual returned states determine both the next hit and its cost. -/

def probe0 : IntervalKey Nat := IntervalKey.ofBounds 0 0 le_rfl
def probe1 : IntervalKey Nat := IntervalKey.ofBounds 1 1 le_rfl

def sentinelOps : AbstractSet.DeleteOps (Key Nat) Nat where
  empty := 0
  insert key state := 10 * state + (ofLex key).2 + 1
  member _ _ := false
  delete key state := 100 * state + (ofLex key).2 + 1

def sentinelQuery (state : Nat) (q : IntervalKey Nat) : Bool :=
  decide ((q = probe0 ∧ state = 21) ∨ (q = probe1 ∧ state = 2101))

def sentinelInsertRun (key : Key Nat) (state : Nat) : Measured Nat Nat :=
  (sentinelOps.insert key state, state + 10)

def sentinelDeleteRun (key : Key Nat) (state : Nat) : Measured Nat Nat :=
  (sentinelOps.delete key state, state + 100)

def sentinelQueryRun (state : Nat) (q : IntervalKey Nat) : Measured Bool Nat :=
  (sentinelQuery state q, state + 1)

def sentinelInsert0 : Event Nat Unit := ⟨(), probe0, .insert, 0⟩
def sentinelDelete0 : Event Nat Unit := ⟨(), probe0, .delete, 0⟩
def sentinelInsert1 : Event Nat Unit := ⟨(), probe1, .insert, 1⟩

theorem sentinel_value (state : Nat) (es : List (Event Nat Unit)) :
    (scanRun sentinelInsertRun sentinelDeleteRun sentinelQueryRun 7 11 state es).1 =
      scan sentinelOps sentinelQuery state es :=
  scanRun_value sentinelOps sentinelQuery sentinelInsertRun sentinelDeleteRun
    sentinelQueryRun 7 11 (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) state es

/-- Queries observe 2 then 2101; insertion returns 21 and deletion returns 2101. -/
theorem sentinel_work (suffix : List (Event Nat Unit)) :
    scanRun sentinelInsertRun sentinelDeleteRun sentinelQueryRun 7 11 2
      (sentinelInsert0 :: sentinelDelete0 :: sentinelInsert1 :: suffix) = (true, 2259) := by
  rw [scanRun_insert_miss sentinelInsertRun sentinelDeleteRun sentinelQueryRun 7 11 2
    sentinelInsert0 (sentinelDelete0 :: sentinelInsert1 :: suffix) rfl (by decide)]
  rfl

theorem sentinel_counts (suffix : List (Event Nat Unit)) :
    scanCounts sentinelOps sentinelQuery 2
      (sentinelInsert0 :: sentinelDelete0 :: sentinelInsert1 :: suffix) =
        (true, (2, 1, 1)) := by
  rw [scanCounts_insert_miss sentinelOps sentinelQuery 2 sentinelInsert0
    (sentinelDelete0 :: sentinelInsert1 :: suffix) rfl (by decide)]
  rfl

theorem sentinel_update_order :
    sentinelOps.delete sentinelDelete0.completeKey
        (sentinelOps.insert sentinelInsert0.completeKey 2) = 2101 ∧
      sentinelOps.insert sentinelInsert0.completeKey
        (sentinelOps.delete sentinelDelete0.completeKey 2) = 2011 := by decide

theorem sentinel_query_before_insert :
    sentinelQuery 2 probe0 = false ∧
      sentinelQuery (sentinelOps.insert sentinelInsert0.completeKey 2) probe0 = true := by
  decide

/-! Ordered tokens expose sequencing without requiring commutative observations. -/

inductive Token where
  | entry
  | terminal
  | query (state low : Nat) (hit : Bool)
  | insert (before id after : Nat)
  | delete (before id after : Nat)
  deriving DecidableEq

def traceInsertRun (key : Key Nat) (state : Nat) : Measured Nat (FreeAddMonoid Token) :=
  (sentinelOps.insert key state,
    FreeAddMonoid.of (.insert state (ofLex key).2 (sentinelOps.insert key state)))

def traceDeleteRun (key : Key Nat) (state : Nat) : Measured Nat (FreeAddMonoid Token) :=
  (sentinelOps.delete key state,
    FreeAddMonoid.of (.delete state (ofLex key).2 (sentinelOps.delete key state)))

def traceQueryRun (state : Nat) (q : IntervalKey Nat) : Measured Bool (FreeAddMonoid Token) :=
  (sentinelQuery state q, FreeAddMonoid.of (.query state q.low (sentinelQuery state q)))

theorem sentinel_ordered_observation (suffix : List (Event Nat Unit)) :
    FreeAddMonoid.toList
      (scanRun traceInsertRun traceDeleteRun traceQueryRun
        (FreeAddMonoid.of .entry) (FreeAddMonoid.of .terminal) 2
        (sentinelInsert0 :: sentinelDelete0 :: sentinelInsert1 :: suffix)).2 =
      [.entry, .query 2 0 false, .insert 2 0 21, .entry,
        .delete 21 0 2101, .entry, .query 2101 1 true] := by
  rw [scanRun_insert_miss traceInsertRun traceDeleteRun traceQueryRun
    (FreeAddMonoid.of .entry) (FreeAddMonoid.of .terminal) 2 sentinelInsert0
    (sentinelDelete0 :: sentinelInsert1 :: suffix) rfl (by decide)]
  rfl

theorem query_insert_observations_do_not_commute :
    FreeAddMonoid.of (Token.query 2 0 false) + FreeAddMonoid.of (Token.insert 2 0 21) ≠
      FreeAddMonoid.of (Token.insert 2 0 21) + FreeAddMonoid.of (Token.query 2 0 false) := by
  intro equality
  have lists := congrArg (fun t : FreeAddMonoid Token => FreeAddMonoid.toList t) equality
  change [Token.query 2 0 false, Token.insert 2 0 21] =
    [Token.insert 2 0 21, Token.query 2 0 false] at lists
  have heads : Token.query 2 0 false = Token.insert 2 0 21 := (List.cons.inj lists).1
  cases heads

/-! Coordinate, state, and observation universes need not agree. -/

theorem lifted_singleton_value :
    (scanRun
      (fun key state => (liftedOps.insert key state, (3 : Nat)))
      (fun key state => (liftedOps.delete key state, (5 : Nat)))
      (fun state q => (liftedQuery state q, (2 : Nat)))
      7 11 liftedOps.empty (events [liftedPoint])).1 = false := by
  rw [scanRun_value liftedOps liftedQuery _ _ _ 7 11
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)]
  exact lifted_singleton_sweep

end Examples.MeasuredRectangleSweep

import Applications.Resources.IntervalTree
import Applications.Resources.HeightBalance.Updates
import Applications.Search.RectangleSweep.MeasuredEvents
import Applications.Search.RectangleSweep.Balanced

/-!
# Concrete measured balanced interval operations and rectangle sweep

Complete-key comparison observes each reached low/high/occurrence test. The
complete annotation executes four unit-cost operations. The query reads only
the selected root maxima and original children. These actual operations feed
the existing once-generated, once-sorted, early-return sweep executor.

The source-event model is explicit; it does not assert bit complexity or machine
time. Raw structural-height bounds are separate from balanced-set correctness
and from the remaining finite-support/logarithmic composition.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.RectangleSweep.MeasuredBalanced
open Resources
universe u v
variable {α : Type u} {β : Type v}

abbrev Tree (α : Type u) [LE α] := BinaryTree (Key α × (Nat × α))

section Comparison
variable [LinearOrder α]

/-- Charge entry and exactly the reached strict lexicographic field tests. -/
def keyLtRun (a b : Key α) : Measured Bool Nat :=
  CallCount.tick (Resources.bind (decide ((keyInterval a).low < (keyInterval b).low), 1)
    fun lowerLow =>
      if lowerLow then Resources.pure true
      else Resources.bind (decide ((keyInterval a).low = (keyInterval b).low), 1)
        fun sameLow =>
          if sameLow then
            Resources.bind (decide ((keyInterval a).high < (keyInterval b).high), 1)
              fun lowerHigh =>
                if lowerHigh then Resources.pure true
                else Resources.bind (decide ((keyInterval a).high = (keyInterval b).high), 1)
                  fun sameHigh =>
                    if sameHigh then (decide ((ofLex a).2 < (ofLex b).2), 1)
                    else Resources.pure false
          else Resources.pure false)

theorem keyLtRun_value (a b : Key α) : (keyLtRun a b).1 = decide (a < b) := by
  have interval_eq : keyInterval a = keyInterval b ↔
      (keyInterval a).low = (keyInterval b).low ∧
        (keyInterval a).high = (keyInterval b).high := by
    constructor
    · intro h
      exact ⟨congrArg IntervalKey.low h, congrArg IntervalKey.high h⟩
    · rintro ⟨hl, hh⟩
      exact IntervalKey.ext hl hh
  have key_lt : a < b ↔
      (keyInterval a).low < (keyInterval b).low ∨
        (keyInterval a).low = (keyInterval b).low ∧
          ((keyInterval a).high < (keyInterval b).high ∨
            (keyInterval a).high = (keyInterval b).high ∧ (ofLex a).2 < (ofLex b).2) := by
    change toLex (ofLex a) < toLex (ofLex b) ↔ _
    rw [Prod.Lex.toLex_lt_toLex]
    change keyInterval a < keyInterval b ∨
      keyInterval a = keyInterval b ∧ (ofLex a).2 < (ofLex b).2 ↔ _
    rw [IntervalKey.lt_iff, interval_eq]
    tauto
  by_cases hl : (keyInterval a).low < (keyInterval b).low <;>
    by_cases he : (keyInterval a).low = (keyInterval b).low <;>
    by_cases hh : (keyInterval a).high < (keyInterval b).high <;>
    by_cases hf : (keyInterval a).high = (keyInterval b).high <;>
    simp [keyLtRun, Resources.bind, Resources.pure, CallCount.tick, hl, he, hh, hf, key_lt]

theorem keyLtRun_cost_bounds (a b : Key α) :
    2 ≤ (keyLtRun a b).2 ∧ (keyLtRun a b).2 ≤ 6 := by
  by_cases hl : (keyInterval a).low < (keyInterval b).low <;>
    by_cases he : (keyInterval a).low = (keyInterval b).low <;>
    by_cases hh : (keyInterval a).high < (keyInterval b).high <;>
    by_cases hf : (keyInterval a).high = (keyInterval b).high <;>
    simp [keyLtRun, Resources.bind, Resources.pure, CallCount.tick, hl, he, hh, hf]

theorem keyLtRun_cost_le (a b : Key α) : (keyLtRun a b).2 ≤ 6 :=
  (keyLtRun_cost_bounds a b).2

theorem keyLtRun_cost_of_low_lt (a b : Key α)
    (hl : (keyInterval a).low < (keyInterval b).low) : (keyLtRun a b).2 = 2 := by
  simp [keyLtRun, Resources.bind, Resources.pure, CallCount.tick, hl]

theorem keyLtRun_cost_of_low_ne (a b : Key α)
    (hl : ¬(keyInterval a).low < (keyInterval b).low)
    (he : (keyInterval a).low ≠ (keyInterval b).low) : (keyLtRun a b).2 = 3 := by
  simp [keyLtRun, Resources.bind, Resources.pure, CallCount.tick, hl, he]

theorem keyLtRun_cost_of_high_lt (a b : Key α)
    (he : (keyInterval a).low = (keyInterval b).low)
    (hh : (keyInterval a).high < (keyInterval b).high) : (keyLtRun a b).2 = 4 := by
  simp [keyLtRun, Resources.bind, Resources.pure, CallCount.tick, he, hh]

theorem keyLtRun_cost_of_high_ne (a b : Key α)
    (he : (keyInterval a).low = (keyInterval b).low)
    (hh : ¬(keyInterval a).high < (keyInterval b).high)
    (hf : (keyInterval a).high ≠ (keyInterval b).high) : (keyLtRun a b).2 = 5 := by
  simp [keyLtRun, Resources.bind, Resources.pure, CallCount.tick, he, hh, hf]

theorem keyLtRun_cost_of_endpoints_eq (a b : Key α)
    (he : (keyInterval a).low = (keyInterval b).low)
    (hf : (keyInterval a).high = (keyInterval b).high) : (keyLtRun a b).2 = 6 := by
  simp [keyLtRun, Resources.bind, CallCount.tick, he, hf]

end Comparison

section Operations
variable [LinearOrder α] [OrderBot α]

def heightRun (s : Nat × α) : Measured Nat Nat := (s.1, 0)

/-- Height max, successor, child maximum and payload maximum are each charged. -/
def combineRun (l : Nat × α) (a : Key α) (r : Nat × α) : Measured (Nat × α) Nat :=
  Resources.bind (max l.1 r.1, 1) fun height =>
    Resources.bind (height + 1, 1) fun nextHeight =>
      Resources.bind (max l.2 r.2, 1) fun childMaximum =>
        Resources.bind (max (keyInterval a).high childMaximum, 1) fun maximum =>
          Resources.pure (nextHeight, maximum)

theorem combineRun_value (l : Nat × α) (a : Key α) (r : Nat × α) :
    (combineRun l a r).1 = (IntervalTree.Balanced.annotation keyInterval).combine l a r := rfl

omit [OrderBot α] in
theorem combineRun_cost (l : Nat × α) (a : Key α) (r : Nat × α) :
    (combineRun l a r).2 = 4 := rfl

def insertRun (a : Key α) (t : Tree α) : Measured (Tree α) Nat :=
  Resources.HeightBalance.insertRun (0, ⊥) heightRun combineRun keyLtRun 1 a t

def splitMaxRun (t : Tree α) : Measured (Option (Tree α × Key α)) Nat :=
  Resources.HeightBalance.splitMaxRun (0, ⊥) heightRun combineRun 1 t

def deleteRun (a : Key α) (t : Tree α) : Measured (Tree α) Nat :=
  Resources.HeightBalance.deleteRun (0, ⊥) heightRun combineRun keyLtRun 1 a t

def queryRun (t : Tree α) (query : IntervalKey α) : Measured Bool Nat :=
  Resources.IntervalTree.searchRun (fun a => (keyInterval a, 0))
    (fun x y => (decide (x ≤ y), 1)) t query

theorem insertRun_value (a : Key α) (t : Tree α) :
    (insertRun a t).1 = (IntervalTree.Balanced.deleteOps keyInterval).insert a t :=
  Resources.HeightBalance.insertRun_value (IntervalTree.Balanced.annotation keyInterval)
    heightRun combineRun keyLtRun 1 a t (fun _ => rfl) combineRun_value keyLtRun_value

theorem splitMaxRun_value (t : Tree α) :
    (splitMaxRun t).1 =
      Trees.HeightBalance.splitMaxOption (IntervalTree.Balanced.annotation keyInterval) 1 t :=
  Resources.HeightBalance.splitMaxRun_value (IntervalTree.Balanced.annotation keyInterval)
    heightRun combineRun 1 t (fun _ => rfl) combineRun_value

theorem deleteRun_value (a : Key α) (t : Tree α) :
    (deleteRun a t).1 = (IntervalTree.Balanced.deleteOps keyInterval).delete a t :=
  Resources.HeightBalance.deleteRun_value (IntervalTree.Balanced.annotation keyInterval)
    heightRun combineRun keyLtRun 1 a t (fun _ => rfl) combineRun_value keyLtRun_value

theorem queryRun_value (t : Tree α) (query : IntervalKey α) :
    (queryRun t query).1 = IntervalTree.Balanced.search keyInterval t query :=
  Resources.IntervalTree.searchRun_value keyInterval (fun a => (keyInterval a, 0))
    (fun x y => (decide (x ≤ y), 1)) t query (fun _ => rfl) (fun _ _ => rfl)

theorem insertRun_cost_le (a : Key α) (t : Tree α) :
    (insertRun a t).2 ≤ 43 * t.height + 8 := by
  have h := Resources.HeightBalance.insertRun_cost_le (0, ⊥) heightRun combineRun
    keyLtRun 1 a t 0 4 6 (fun _ => le_refl _) (fun _ _ _ => le_refl _) keyLtRun_cost_le
  simpa only [insertRun, Nat.mul_zero, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd,
    Nat.add_assoc] using h

theorem splitMaxRun_cost_le (t : Tree α) : (splitMaxRun t).2 ≤ 31 * t.height + 1 := by
  simpa only [splitMaxRun, Nat.mul_zero, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd] using
    Resources.HeightBalance.splitMaxRun_cost_le (0, ⊥) heightRun combineRun 1 t 0 4
      (fun _ => le_refl _) (fun _ _ _ => le_refl _)

theorem splitMaxRun_cost_le_of_ne_nil (t : Tree α) (hne : t ≠ .nil) :
    (splitMaxRun t).2 ≤ 31 * t.height := by
  simpa only [splitMaxRun, Nat.mul_zero, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd] using
    Resources.HeightBalance.splitMaxRun_cost_le_of_ne_nil (0, ⊥) heightRun combineRun 1 t 0 4
      (fun _ => le_refl _) (fun _ _ _ => le_refl _) hne

theorem deleteRun_cost_le (a : Key α) (t : Tree α) :
    (deleteRun a t).2 ≤ 43 * t.height + 1 := by
  simpa only [deleteRun, Nat.mul_zero, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd] using
    Resources.HeightBalance.deleteRun_cost_le (0, ⊥) heightRun combineRun keyLtRun 1 a t 0 4 6
      (fun _ => le_refl _) (fun _ _ _ => le_refl _) keyLtRun_cost_le

theorem queryRun_cost_le (t : Tree α) (query : IntervalKey α) :
    (queryRun t query).2 ≤ 5 * t.height + 1 := by
  simpa only [queryRun, Nat.reduceMul, Nat.reduceAdd] using
    Resources.IntervalTree.searchRun_cost_le (fun a => (keyInterval a, 0))
      (fun x y => (decide (x ≤ y), 1)) t query 0 1
      (fun _ => le_refl _) (fun _ _ => le_refl _)

theorem insertRun_valid (a : Key α) (t : Tree α) (valid : IntervalTree.Balanced.Valid keyInterval t) :
    IntervalTree.Balanced.Valid keyInterval (insertRun a t).1 := by
  rw [insertRun_value]
  exact (IntervalTree.Balanced.set_laws keyInterval).insert_valid a t valid

theorem deleteRun_valid (a : Key α) (t : Tree α) (valid : IntervalTree.Balanced.Valid keyInterval t) :
    IntervalTree.Balanced.Valid keyInterval (deleteRun a t).1 := by
  rw [deleteRun_value]
  exact (IntervalTree.Balanced.set_laws keyInterval).delete_valid a t valid

/-- Composition adds no wrapper charge to the established early-return scan. -/
def scanRun (t : Tree α) (es : List (Event α β)) : Measured Bool Nat :=
  Search.RectangleSweep.scanRun insertRun deleteRun queryRun 1 1 t es

theorem scanRun_value (t : Tree α) (es : List (Event α β)) :
    (scanRun t es).1 = scan (IntervalTree.Balanced.deleteOps keyInterval)
      (IntervalTree.Balanced.search keyInterval) t es :=
  Search.RectangleSweep.scanRun_value (IntervalTree.Balanced.deleteOps keyInterval)
    (IntervalTree.Balanced.search keyInterval) insertRun deleteRun queryRun 1 1
    insertRun_value deleteRun_value queryRun_value t es

end Operations

section Pipeline
variable [LinearOrder α] [OrderBot α] [LinearOrder β]

def sweepRun (rs : List (Rectangle α β)) : Measured Bool Nat :=
  Search.RectangleSweep.sweepRun 1 1 (fun kind r id => (eventFor r kind id, 1))
    sortEventsRun insertRun deleteRun queryRun 1 1 .nil rs

theorem sweepRun_value (rs : List (Rectangle α β)) : (sweepRun rs).1 = balancedSweep rs :=
  Search.RectangleSweep.sweepRun_value 1 1 (IntervalTree.Balanced.deleteOps keyInterval)
    (IntervalTree.Balanced.search keyInterval) (fun kind r id => (eventFor r kind id, 1))
    sortEventsRun insertRun deleteRun queryRun 1 1 (fun _ _ _ => rfl)
    sortEventsRun_value insertRun_value deleteRun_value queryRun_value rs

theorem sweepRun_eq_true_iff_hasIntersection (rs : List (Rectangle α β)) :
    (sweepRun rs).1 = true ↔ Rectangle.HasIntersection rs := by
  rw [sweepRun_value]
  exact balancedSweep_eq_true_iff_hasIntersection rs

/-- All generation and sorting work is paid even when scanning returns early. -/
theorem sweepRun_cost (rs : List (Rectangle α β)) :
    (sweepRun rs).2 = 8 * rs.length + 4 +
      (sortEventsRun (rawEvents rs)).2 + (scanRun .nil (events rs)).2 := by
  have h := Search.RectangleSweep.sweepRun_cost_of_values 1 1
    (fun kind r id => (eventFor r kind id, 1)) sortEventsRun
    insertRun deleteRun queryRun 1 1 (.nil : Tree α)
    (fun _ _ _ => rfl) sortEventsRun_value rs
  have hg := rawEventsRun_cost_of_constant 1 1 1 1
    (fun kind r id => (eventFor r kind id, 1)) rs (by intros; rfl) (by intros; rfl)
  rw [hg] at h
  exact h

end Pipeline
end Search.RectangleSweep.MeasuredBalanced

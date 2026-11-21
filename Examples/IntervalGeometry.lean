import Applications.Search.IntervalSet
import Mathlib.Order.Interval.Lex

/-! Independent interval geometry and key-order cases for FDSA-5-67 to FDSA-5-69.
The public key order is different from containment and from Mathlib's
descending-low interval lexicographic order. Int geometry needs no bottom.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.IntervalGeometry
open Search

def outer : IntervalKey Int := IntervalKey.ofBounds 1 8 (by decide)
def inner : IntervalKey Int := IntervalKey.ofBounds 2 3 (by decide)

theorem ascending_key_order : outer < inner :=
  (IntervalKey.lt_iff outer inner).mpr (Or.inl (by decide))

theorem containment_order : inner.interval ≤ outer.interval := by decide

theorem containment_not_key_order : ¬ outer.interval ≤ inner.interval := by decide

theorem library_lex_reverses_low : toLex inner.interval < toLex outer.interval := by decide

theorem endpoint_proof_independence (h h' : (1 : Int) ≤ 8) :
    IntervalKey.ofBounds 1 8 h = IntervalKey.ofBounds 1 8 h' :=
  IntervalKey.ext rfl rfl

def lowTwo : IntervalKey Int := IntervalKey.ofBounds 1 2 (by decide)
def lowFive : IntervalKey Int := IntervalKey.ofBounds 1 5 (by decide)
def lowEight : IntervalKey Int := IntervalKey.ofBounds 1 8 (by decide)

theorem equal_low_order : lowTwo < lowFive ∧ lowFive < lowEight :=
  ⟨(IntervalKey.lt_iff _ _).mpr (Or.inr ⟨rfl, by decide⟩),
    (IntervalKey.lt_iff _ _).mpr (Or.inr ⟨rfl, by decide⟩)⟩

theorem equal_low_distinct_keys : lowTwo ≠ lowFive := by decide

theorem low_comparison_is_weak : lowTwo.low ≤ lowFive.low ∧ ¬ lowTwo.low < lowFive.low :=
  ⟨IntervalKey.low_le_of_le equal_low_order.1.le, by decide⟩

def negativeLeft : IntervalKey Int := IntervalKey.ofBounds (-4) (-1) (by decide)
def negativeShort : IntervalKey Int := IntervalKey.ofBounds (-4) (-2) (by decide)
def touchingRight : IntervalKey Int := IntervalKey.ofBounds (-1) 3 (by decide)
def negativePoint : IntervalKey Int := IntervalKey.ofBounds (-1) (-1) (by decide)

theorem touching_intersection : negativeLeft.toSet ∩ touchingRight.toSet = {-1} := by
  ext x
  change ((-4 ≤ x ∧ x ≤ -1) ∧ (-1 ≤ x ∧ x ≤ 3)) ↔ x = -1
  constructor
  · exact fun h => le_antisymm h.1.2 h.2.1
  · rintro rfl
    exact ⟨⟨by decide, le_rfl⟩, ⟨le_rfl, by decide⟩⟩

theorem touching_overlap : IntervalKey.overlap negativeLeft touchingRight := by
  apply (IntervalKey.overlap_iff_nonempty_inter _ _).mpr
  rw [touching_intersection]
  exact ⟨-1, rfl⟩

theorem touching_overlap_reverse : IntervalKey.overlap touchingRight negativeLeft :=
  (IntervalKey.overlap_comm _ _).mp touching_overlap

theorem gap_intersection : negativeShort.toSet ∩ touchingRight.toSet = ∅ := by
  ext x
  change ((-4 ≤ x ∧ x ≤ -2) ∧ (-1 ≤ x ∧ x ≤ 3)) ↔ False
  constructor
  · intro h
    exact (by decide : ¬ (-1 : Int) ≤ -2) (le_trans h.2.1 h.1.2)
  · exact False.elim

theorem gap_no_overlap : ¬ IntervalKey.overlap negativeShort touchingRight := by
  intro h
  have witness := (IntervalKey.overlap_iff_nonempty_inter _ _).mp h
  simp only [gap_intersection, Set.not_nonempty_empty] at witness

theorem singleton_touches_both :
    IntervalKey.overlap negativePoint negativeLeft ∧
      IntervalKey.overlap negativePoint touchingRight :=
  ⟨(IntervalKey.overlap_iff_nonempty_inter _ _).mpr
      ⟨-1, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩,
    (IntervalKey.overlap_iff_nonempty_inter _ _).mpr
      ⟨-1, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩⟩

theorem reversed_pair_uninhabited :
    ¬ ∃ x : IntervalKey Int, x.low = 5 ∧ x.high = 1 := by
  rintro ⟨x, hl, hh⟩
  have impossible : (5 : Int) ≤ 1 := by simpa only [hl, hh] using x.low_le_high
  exact (by decide : ¬ (5 : Int) ≤ 1) impossible

/-- Cross inequalities alone do not give common-point semantics for a reversed pair. -/
theorem reversed_pair_counterexample :
    ((0 : Int) ≤ 1 ∧ (5 : Int) ≤ 6) ∧
      Set.Icc (5 : Int) 1 ∩ Set.Icc 0 6 = ∅ := by
  refine ⟨by decide, ?_⟩
  ext x
  change ((5 ≤ x ∧ x ≤ 1) ∧ (0 ≤ x ∧ x ≤ 6)) ↔ False
  constructor
  · intro h
    exact (by decide : ¬ (5 : Int) ≤ 1) (le_trans h.1.1 h.1.2)
  · exact False.elim

open Search.IntervalSet

def positiveRight : IntervalKey Int := IntervalKey.ofBounds 1 4 (by decide)
def abstractContents : Set (IntervalKey Int) := {negativeShort, positiveRight}
def bridgeQuery : IntervalKey Int := IntervalKey.ofBounds (-2) 1 (by decide)
def gapQuery : IntervalKey Int := IntervalKey.ofBounds (-1) 0 (by decide)
def rightTouchQuery : IntervalKey Int := IntervalKey.ofBounds 0 1 (by decide)

theorem abstract_bridge_overlap : hasOverlap abstractContents bridgeQuery :=
  (hasOverlap_insert_iff _ _ _).mpr (Or.inl
    ((IntervalKey.overlap_iff_nonempty_inter _ _).mpr
      ⟨-2, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩))

theorem abstract_gap_absent : ¬ hasOverlap abstractContents gapQuery := by
  change ¬ hasOverlap (insert negativeShort {positiveRight}) gapQuery
  rw [hasOverlap_insert_iff, hasOverlap_singleton_iff]
  decide

theorem abstract_right_touch : hasOverlap abstractContents rightTouchQuery :=
  (hasOverlap_insert_iff _ _ _).mpr (Or.inr
    ((hasOverlap_singleton_iff _ _).mpr
      ((IntervalKey.overlap_iff_nonempty_inter _ _).mpr
        ⟨1, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩)))

theorem abstract_empty_absent (query : IntervalKey Int) : ¬ hasOverlap ∅ query :=
  not_hasOverlap_empty query

/-- This set is specified directly by endpoint conditions, with no finite representation. -/
def nonnegativePoints : Set (IntervalKey Int) := {x | x.low = x.high ∧ 0 ≤ x.low}

theorem unrestricted_set_touches : hasOverlap nonnegativePoints gapQuery :=
  ⟨IntervalKey.ofBounds 0 0 le_rfl, ⟨rfl, le_rfl⟩,
    (IntervalKey.overlap_iff_nonempty_inter _ _).mpr
      ⟨0, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩⟩

theorem unrestricted_set_negative_absent :
    ¬ hasOverlap nonnegativePoints (IntervalKey.ofBounds (-2) (-1) (by decide)) := by
  rintro ⟨x, hx, overlaps⟩
  exact (by decide : ¬ (0 : Int) ≤ -1) (le_trans hx.2 overlaps.2)

end Examples.IntervalGeometry

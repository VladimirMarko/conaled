import Mathlib.Order.Interval.Basic
import Mathlib.Order.Prod.Lex.Basic

/-!
# Nonempty intervals with ascending endpoint keys

The endpoint data comes from `NonemptyInterval`. Its containment order stays
unchanged; this wrapper orders first by increasing low, then increasing high,
as required by interval search trees. Geometry does not require a bottom.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search
universe u

structure IntervalKey (α : Type u) [LE α] where
  interval : NonemptyInterval α

namespace IntervalKey
variable {α : Type u}

section Endpoints
variable [LE α]

def low (x : IntervalKey α) : α := x.interval.fst

def high (x : IntervalKey α) : α := x.interval.snd

def ofBounds (low high : α) (valid : low ≤ high) : IntervalKey α :=
  ⟨⟨(low, high), valid⟩⟩

@[simp] theorem low_ofBounds (l h : α) (valid : l ≤ h) :
    (ofBounds l h valid).low = l := rfl

@[simp] theorem high_ofBounds (l h : α) (valid : l ≤ h) :
    (ofBounds l h valid).high = h := rfl

theorem low_le_high (x : IntervalKey α) : x.low ≤ x.high :=
  x.interval.fst_le_snd

def Overlap (x y : IntervalKey α) : Prop :=
  y.low ≤ x.high ∧ x.low ≤ y.high

instance [DecidableLE α] (x y : IntervalKey α) : Decidable (Overlap x y) :=
  inferInstanceAs (Decidable (y.low ≤ x.high ∧ x.low ≤ y.high))

theorem overlap_comm (x y : IntervalKey α) : Overlap x y ↔ Overlap y x := and_comm

theorem overlap_self (x : IntervalKey α) : Overlap x x :=
  ⟨x.low_le_high, x.low_le_high⟩

@[ext] theorem ext {x y : IntervalKey α}
    (hl : x.low = y.low) (hh : x.high = y.high) : x = y := by
  cases x with
  | mk x =>
      cases y with
      | mk y =>
          congr 1
          exact NonemptyInterval.toProd_injective (Prod.ext hl hh)

/-- The ordinary ascending product lexicographic presentation of a key. -/
def endpoints (x : IntervalKey α) : α ×ₗ α := toLex (x.low, x.high)

theorem endpoints_injective : Function.Injective (endpoints : IntervalKey α → α ×ₗ α) := by
  intro x y h
  exact ext (congrArg (fun p : α ×ₗ α => (ofLex p).1) h)
    (congrArg (fun p : α ×ₗ α => (ofLex p).2) h)

end Endpoints

section Preorder
variable [Preorder α]

/-- The closed endpoint set, independent of any search-tree representation. -/
def toSet (x : IntervalKey α) : Set α := Set.Icc x.low x.high

@[simp] theorem mem_toSet (x : IntervalKey α) (a : α) :
    a ∈ x.toSet ↔ x.low ≤ a ∧ a ≤ x.high := Iff.rfl

theorem toSet_eq_coe (x : IntervalKey α) : x.toSet = (x.interval : Set α) := rfl

theorem toSet_nonempty (x : IntervalKey α) : x.toSet.Nonempty :=
  ⟨x.low, le_rfl, x.low_le_high⟩

end Preorder

section Order
variable [LinearOrder α]

instance : LinearOrder (IntervalKey α) :=
  LinearOrder.lift' endpoints endpoints_injective

theorem lt_iff (x y : IntervalKey α) :
    x < y ↔ x.low < y.low ∨ x.low = y.low ∧ x.high < y.high :=
  Prod.Lex.toLex_lt_toLex

theorem le_iff (x y : IntervalKey α) :
    x ≤ y ↔ x.low < y.low ∨ x.low = y.low ∧ x.high ≤ y.high :=
  Prod.Lex.toLex_le_toLex

/-- Key comparison only gives a weak comparison of low endpoints. -/
theorem low_le_of_le {x y : IntervalKey α} (h : x ≤ y) : x.low ≤ y.low := by
  rcases (le_iff x y).mp h with h | h
  · exact h.le
  · exact h.1.le

/-- The maximum of the two lows is a common point exactly when the cross
inequalities hold. Each interval's own endpoint inequality is used. -/
theorem overlap_iff_nonempty_inter (x y : IntervalKey α) :
    Overlap x y ↔ (x.toSet ∩ y.toSet).Nonempty := by
  constructor
  · rintro ⟨hyl, hxl⟩
    exact ⟨max x.low y.low,
      ⟨le_max_left _ _, max_le x.low_le_high hyl⟩,
      ⟨le_max_right _ _, max_le hxl y.low_le_high⟩⟩
  · rintro ⟨a, hx, hy⟩
    exact ⟨le_trans hy.1 hx.2, le_trans hx.1 hy.2⟩

end Order
end IntervalKey
end Search

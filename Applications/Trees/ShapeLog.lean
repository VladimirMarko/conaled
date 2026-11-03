import Applications.Trees.Shape
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Real-logarithm and rounding corollaries of the discrete tree-shape bounds.
The logarithm always has a positive argument: nil has one external leaf.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees
universe u
variable {α : Type u}

theorem minHeight_le_logb_numLeaves (t : BinaryTree α) :
    (minHeight t : Real) ≤ Real.logb 2 (t.numLeaves : Real) := by
  have hb : (1 : Real) < 2 := by exact_mod_cast Nat.one_lt_two
  have hpos : (0 : Real) < (t.numLeaves : Real) :=
    Nat.cast_pos.mpr (BinaryTree.numLeaves_pos t)
  apply (Real.le_logb_iff_rpow_le hb hpos).2
  rw [Real.rpow_natCast]
  exact_mod_cast pow_minHeight_le_numLeaves t

theorem logb_numLeaves_le_height (t : BinaryTree α) :
    Real.logb 2 (t.numLeaves : Real) ≤ (t.height : Real) := by
  have hb : (1 : Real) < 2 := by exact_mod_cast Nat.one_lt_two
  have hpos : (0 : Real) < (t.numLeaves : Real) :=
    Nat.cast_pos.mpr (BinaryTree.numLeaves_pos t)
  apply (Real.logb_le_iff_le_rpow hb hpos).2
  rw [Real.rpow_natCast]
  exact_mod_cast numLeaves_le_pow_height t

theorem minHeight_lt_logb_numLeaves (t : BinaryTree α) (ht : ¬ Complete t) :
    (minHeight t : Real) < Real.logb 2 (t.numLeaves : Real) := by
  have hb : (1 : Real) < 2 := by exact_mod_cast Nat.one_lt_two
  have hpos : (0 : Real) < (t.numLeaves : Real) :=
    Nat.cast_pos.mpr (BinaryTree.numLeaves_pos t)
  apply (Real.lt_logb_iff_rpow_lt hb hpos).2
  rw [Real.rpow_natCast]
  exact_mod_cast pow_minHeight_lt_numLeaves t ht

theorem logb_numLeaves_lt_height (t : BinaryTree α) (ht : ¬ Complete t) :
    Real.logb 2 (t.numLeaves : Real) < (t.height : Real) := by
  have hb : (1 : Real) < 2 := by exact_mod_cast Nat.one_lt_two
  have hpos : (0 : Real) < (t.numLeaves : Real) :=
    Nat.cast_pos.mpr (BinaryTree.numLeaves_pos t)
  apply (Real.logb_lt_iff_lt_rpow hb hpos).2
  rw [Real.rpow_natCast]
  exact_mod_cast numLeaves_lt_pow_height t ht

theorem height_eq_logb_numLeaves (t : BinaryTree α) (ht : Complete t) :
    (t.height : Real) = Real.logb 2 (t.numLeaves : Real) := by
  apply le_antisymm
  · simpa only [(complete_iff_minHeight_eq_height t).1 ht] using
      minHeight_le_logb_numLeaves t
  · exact logb_numLeaves_le_height t

theorem minHeight_eq_floor_logb_numLeaves (t : BinaryTree α)
    (ht : AlmostComplete t) :
    minHeight t = ⌊Real.logb 2 (t.numLeaves : Real)⌋₊ := by
  rw [Real.natFloor_logb_natCast 2 t.numLeaves]
  exact minHeight_eq_log_numLeaves t ht

theorem height_eq_ceil_logb_numLeaves (t : BinaryTree α)
    (ht : AlmostComplete t) :
    t.height = ⌈Real.logb 2 (t.numLeaves : Real)⌉₊ := by
  rw [Real.natCeil_logb_natCast 2 t.numLeaves]
  exact height_eq_clog_numLeaves t ht

/-- The source ceiling-log intermediate identity for two almost-complete
children with the left one node larger. The cast is of the actual natural
external-leaf count plus one, including a nil right child. -/
theorem height_node_eq_ceil_logb_of_numNodes_succ (a : α) (l r : BinaryTree α)
    (hl : AlmostComplete l) (hr : AlmostComplete r)
    (hsize : l.numNodes = r.numNodes + 1) :
    (BinaryTree.node a l r).height =
      ⌈Real.logb 2 ((r.numLeaves + 1 : Nat) : Real)⌉₊ + 1 := by
  rw [Real.natCeil_logb_natCast 2 (r.numLeaves + 1)]
  exact height_node_eq_clog_of_numNodes_succ a l r hl hr hsize

/-- The corresponding source floor-log intermediate identity uses the
smaller child's positive external-leaf count, rather than its node count. -/
theorem minHeight_node_eq_floor_logb_of_numNodes_succ (a : α) (l r : BinaryTree α)
    (hl : AlmostComplete l) (hr : AlmostComplete r)
    (hsize : l.numNodes = r.numNodes + 1) :
    minHeight (BinaryTree.node a l r) =
      ⌊Real.logb 2 (r.numLeaves : Real)⌋₊ + 1 := by
  rw [Real.natFloor_logb_natCast 2 r.numLeaves]
  exact minHeight_node_eq_log_of_numNodes_succ a l r hl hr hsize

end Trees

import Applications.Arithmetic.LogarithmBounds
import Mathlib.Data.Tree.Basic
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Tactic.Ring

/-!
# Connected logarithm-bound cases

The shared sharp and strict laws are used at actual external-leaf counts and
the pairing first-pass size expressions. The skew and child-product estimates
use existing logarithm APIs directly. Exact values and false stronger claims
keep positivity, shifts, constants and natural subtraction visible.

These are scalar observations, not splay, heap, pass, potential or runtime
implementations. Source correspondence and independently calculated values:
`docs/research/fdsa-logarithm-bounds.md`.
-/

set_option autoImplicit false
set_option warningAsError true

namespace LogarithmBoundsExamples

open Arithmetic.LogarithmBounds

universe u v
variable {α : Type u} {β : Type v}

private theorem log_two : Real.logb 2 (2 : ℝ) = 1 :=
  Real.logb_self_eq_one (by norm_num)

private theorem log_four : Real.logb 2 (4 : ℝ) = 2 := by
  calc
    Real.logb 2 (4 : ℝ) = 2 * Real.logb 2 (2 : ℝ) := by
      simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using Real.logb_pow (2 : ℝ) 2 2
    _ = 2 := by norm_num [log_two]

private theorem log_half : Real.logb 2 (1 / 2 : ℝ) = -1 := by
  simpa only [one_div, log_two] using Real.logb_inv (2 : ℝ) 2

private theorem log_quarter : Real.logb 2 (1 / 4 : ℝ) = -2 := by
  simpa only [one_div, log_four] using Real.logb_inv (2 : ℝ) 4

private theorem leaf_count_pos (t : BinaryTree α) :
    0 < (t.numLeaves : ℝ) :=
  Nat.cast_pos.mpr (BinaryTree.numLeaves_pos t)

private theorem leaf_count_one_le (t : BinaryTree α) :
    1 ≤ (t.numLeaves : ℝ) := by
  rw [BinaryTree.numLeaves_eq_numNodes_succ, Nat.cast_add, Nat.cast_one]
  have hn : (0 : ℝ) ≤ (t.numNodes : ℝ) := Nat.cast_nonneg t.numNodes
  linarith

/-- Both public laws apply across independent payload universes, including nil. -/
theorem leaf_count_bounds (l : BinaryTree α) (r : BinaryTree β) :
    (Real.logb 2 (l.numLeaves : ℝ) + Real.logb 2 (r.numLeaves : ℝ) + 2 ≤
      2 * Real.logb 2 ((l.numLeaves : ℝ) + (r.numLeaves : ℝ))) ∧
    (1 + Real.logb 2 (l.numLeaves : ℝ) + Real.logb 2 (r.numLeaves : ℝ) <
      2 * Real.logb 2 ((l.numLeaves : ℝ) + (r.numLeaves : ℝ))) :=
  ⟨logb_two_sum_bound (leaf_count_pos l) (leaf_count_pos r),
    logb_two_sum_strict (leaf_count_pos l) (leaf_count_pos r)⟩

/-- With an actual root label, the sum is the node's external-leaf count. -/
theorem node_leaf_count_bounds (a : α) (l r : BinaryTree α) :
    (Real.logb 2 (l.numLeaves : ℝ) + Real.logb 2 (r.numLeaves : ℝ) + 2 ≤
      2 * Real.logb 2 ((BinaryTree.node a l r).numLeaves : ℝ)) ∧
    (1 + Real.logb 2 (l.numLeaves : ℝ) + Real.logb 2 (r.numLeaves : ℝ) <
      2 * Real.logb 2 ((BinaryTree.node a l r).numLeaves : ℝ)) := by
  simpa only [BinaryTree.numLeaves, Nat.cast_add] using leaf_count_bounds l r

/-- The unit-input bounds are obtained from nil even when no payload exists. -/
theorem nil_empty_bounds :
    (Real.logb 2 (1 : ℝ) + Real.logb 2 1 + 2 ≤ 2 * Real.logb 2 (1 + 1)) ∧
    (1 + Real.logb 2 (1 : ℝ) + Real.logb 2 1 < 2 * Real.logb 2 (1 + 1)) := by
  simpa only [BinaryTree.numLeaves, Nat.cast_one] using
    leaf_count_bounds (BinaryTree.nil : BinaryTree Empty)
      (BinaryTree.nil : BinaryTree Empty)

theorem unit_values :
    (Real.logb 2 (1 : ℝ) + Real.logb 2 1 + 2 = 2) ∧
    (1 + Real.logb 2 (1 : ℝ) + Real.logb 2 1 = 1) ∧
    (2 * Real.logb 2 (1 + 1 : ℝ) = 2) := by
  norm_num [log_two]

/-- Supplying the labels constructs the two singleton children; no inhabitance is assumed. -/
theorem singleton_leaf_bounds (a : α) (b : β) :
    (Real.logb 2 (2 : ℝ) + Real.logb 2 2 + 2 ≤ 2 * Real.logb 2 (2 + 2)) ∧
    (1 + Real.logb 2 (2 : ℝ) + Real.logb 2 2 < 2 * Real.logb 2 (2 + 2)) := by
  simpa only [BinaryTree.numLeaves, Nat.cast_add, Nat.cast_one,
    show (1 : ℝ) + 1 = 2 by norm_num] using
    leaf_count_bounds (BinaryTree.node a .nil .nil) (BinaryTree.node b .nil .nil)

theorem singleton_values :
    (Real.logb 2 (2 : ℝ) + Real.logb 2 2 + 2 = 4) ∧
    (1 + Real.logb 2 (2 : ℝ) + Real.logb 2 2 = 3) ∧
    (2 * Real.logb 2 (2 + 2 : ℝ) = 4) := by
  norm_num [log_two, log_four]

/-- Positive quarter inputs consume both public laws, although their ranks are negative. -/
theorem quarter_bounds :
    (Real.logb 2 (1 / 4 : ℝ) + Real.logb 2 (1 / 4) + 2 ≤
      2 * Real.logb 2 (1 / 4 + 1 / 4)) ∧
    (1 + Real.logb 2 (1 / 4 : ℝ) + Real.logb 2 (1 / 4) <
      2 * Real.logb 2 (1 / 4 + 1 / 4)) :=
  ⟨logb_two_sum_bound (by norm_num) (by norm_num),
    logb_two_sum_strict (by norm_num) (by norm_num)⟩

theorem quarter_values :
    (Real.logb 2 (1 / 4 : ℝ) + Real.logb 2 (1 / 4) + 2 = -2) ∧
    (1 + Real.logb 2 (1 / 4 : ℝ) + Real.logb 2 (1 / 4) = -3) ∧
    (2 * Real.logb 2 (1 / 4 + 1 / 4 : ℝ) = -2) := by
  rw [show (1 / 4 : ℝ) + 1 / 4 = 1 / 2 by norm_num]
  norm_num [log_quarter, log_half]

theorem sharp_bound_cannot_be_strict :
    ¬ (Real.logb 2 (1 : ℝ) + Real.logb 2 1 + 2 <
      2 * Real.logb 2 (1 + 1)) := by
  norm_num [log_two]

theorem no_larger_uniform_margin (c : ℝ) (hc : 2 < c) :
    ¬ (Real.logb 2 (1 : ℝ) + Real.logb 2 1 + c ≤
      2 * Real.logb 2 (1 + 1)) := by
  simpa only [Real.logb_one, zero_add,
    show (1 : ℝ) + 1 = 2 by norm_num, log_two, mul_one] using not_le_of_gt hc

/-- Target totalization at zero gives the false comparison 0 ≤ -4. -/
theorem zero_quarter_boundary :
    (Real.logb 2 (0 : ℝ) + Real.logb 2 (1 / 4) + 2 = 0) ∧
    (2 * Real.logb 2 (0 + 1 / 4 : ℝ) = -4) ∧
    ¬ (Real.logb 2 (0 : ℝ) + Real.logb 2 (1 / 4) + 2 ≤
      2 * Real.logb 2 (0 + 1 / 4)) := by
  norm_num [log_quarter]

theorem zero_unit_overclaims_fail :
    (¬ (Real.logb 2 (0 : ℝ) + Real.logb 2 1 + 2 ≤
      2 * Real.logb 2 (0 + 1))) ∧
    (¬ (1 + Real.logb 2 (0 : ℝ) + Real.logb 2 1 <
      2 * Real.logb 2 (0 + 1))) := by
  norm_num

/-- The actual first-pass arguments have sum n1+n2+m+2 after Real casts. -/
theorem pairing_sum_bound (n1 n2 m : Nat) :
    Real.logb 2 ((n1 : ℝ) + (n2 : ℝ) + 1) + Real.logb 2 ((m : ℝ) + 1) + 2 ≤
      2 * Real.logb 2 ((n1 : ℝ) + (n2 : ℝ) + (m : ℝ) + 2) := by
  have hn1 : (0 : ℝ) ≤ (n1 : ℝ) := Nat.cast_nonneg n1
  have hn2 : (0 : ℝ) ≤ (n2 : ℝ) := Nat.cast_nonneg n2
  have hx : (0 : ℝ) < (n1 : ℝ) + (n2 : ℝ) + 1 := by linarith
  have hy : (0 : ℝ) < (m : ℝ) + 1 := Nat.cast_add_one_pos m
  have h := logb_two_sum_bound hx hy
  have hsum : ((n1 : ℝ) + (n2 : ℝ) + 1) + ((m : ℝ) + 1) =
      (n1 : ℝ) + (n2 : ℝ) + (m : ℝ) + 2 := by ring
  simpa only [hsum] using h

/-- The two scalar steps in the source cancellation; k is the already-cast suffix length. -/
theorem pairing_cancellation_steps (n1 n2 m : Nat) (k : ℝ) :
    (Real.logb 2 ((n1 : ℝ) + (n2 : ℝ) + 1) -
        Real.logb 2 ((n2 : ℝ) + (m : ℝ) + 1) +
        2 * Real.logb 2 ((m : ℝ) + 1) - k + 2 ≤
      2 * Real.logb 2 ((n1 : ℝ) + (n2 : ℝ) + (m : ℝ) + 2) -
        Real.logb 2 ((n2 : ℝ) + (m : ℝ) + 1) +
        Real.logb 2 ((m : ℝ) + 1) - k) ∧
    (2 * Real.logb 2 ((n1 : ℝ) + (n2 : ℝ) + (m : ℝ) + 2) -
        Real.logb 2 ((n2 : ℝ) + (m : ℝ) + 1) +
        Real.logb 2 ((m : ℝ) + 1) - k ≤
      2 * Real.logb 2 ((n1 : ℝ) + (n2 : ℝ) + (m : ℝ) + 2) - k) := by
  have hsharp := pairing_sum_bound n1 n2 m
  have hn2 : (0 : ℝ) ≤ (n2 : ℝ) := Nat.cast_nonneg n2
  have hm : (0 : ℝ) < (m : ℝ) + 1 := Nat.cast_add_one_pos m
  have hmono := Real.logb_le_logb_of_le (show (1 : ℝ) < 2 by norm_num) hm
    (show (m : ℝ) + 1 ≤ (n2 : ℝ) + (m : ℝ) + 1 by linarith)
  constructor <;> linarith

/-- At zero sizes the corrected step is 2 ≤ 2; the printed +1 version is 2 ≤ 0. -/
theorem pairing_zero_boundary :
    (Real.logb 2 (1 : ℝ) - Real.logb 2 1 + 2 * Real.logb 2 1 - 0 + 2 ≤
      2 * Real.logb 2 2 - Real.logb 2 1 + Real.logb 2 1 - 0) ∧
    (Real.logb 2 (1 : ℝ) - Real.logb 2 1 + 2 * Real.logb 2 1 - 0 + 2 = 2) ∧
    (2 * Real.logb 2 (2 : ℝ) - Real.logb 2 1 + Real.logb 2 1 - 0 = 2) ∧
    ¬ (Real.logb 2 (1 : ℝ) - Real.logb 2 1 + 2 * Real.logb 2 1 - 0 + 2 ≤
      2 * Real.logb 2 1 - Real.logb 2 1 + Real.logb 2 1 - 0) := by
  constructor
  · simpa only [Nat.cast_zero, zero_add] using (pairing_cancellation_steps 0 0 0 0).1
  · norm_num [log_two]

/-- Skew's weaker arbitrary-base step is direct monotonicity, with its actual premises. -/
theorem skew_scalar_sum_bound (b x y : ℝ) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) :
    Real.logb b x + Real.logb b y ≤ 2 * Real.logb b (x + y) := by
  have hl := Real.logb_le_logb_of_le hb hx (le_add_of_nonneg_right (le_of_lt hy))
  have hr := Real.logb_le_logb_of_le hb hy (le_add_of_nonneg_left (le_of_lt hx))
  linarith

theorem skew_leaf_sum_bound (l : BinaryTree α) (r : BinaryTree β) :
    Real.logb 2 (l.numLeaves : ℝ) + Real.logb 2 (r.numLeaves : ℝ) ≤
      2 * Real.logb 2 ((l.numLeaves : ℝ) + (r.numLeaves : ℝ)) :=
  skew_scalar_sum_bound 2 (l.numLeaves : ℝ) (r.numLeaves : ℝ)
    (by norm_num) (leaf_count_pos l) (leaf_count_pos r)

/-- Positive external-leaf counts justify the shifted log and the three-log estimate. -/
theorem skew_shifted_leaf_bound (l : BinaryTree α) (r : BinaryTree β) :
    (0 < (l.numLeaves : ℝ) + (r.numLeaves : ℝ) - 1) ∧
    (Real.logb 2 ((l.numLeaves : ℝ) + (r.numLeaves : ℝ) - 1) ≤
      Real.logb 2 ((l.numLeaves : ℝ) + (r.numLeaves : ℝ))) ∧
    (Real.logb 2 ((l.numLeaves : ℝ) + (r.numLeaves : ℝ) - 1) +
        Real.logb 2 (l.numLeaves : ℝ) + Real.logb 2 (r.numLeaves : ℝ) ≤
      3 * Real.logb 2 ((l.numLeaves : ℝ) + (r.numLeaves : ℝ))) := by
  have hl := leaf_count_one_le l
  have hr := leaf_count_one_le r
  have hp : 0 < (l.numLeaves : ℝ) + (r.numLeaves : ℝ) - 1 := by linarith
  have hlog := Real.logb_le_logb_of_le (show (1 : ℝ) < 2 by norm_num) hp
    (show (l.numLeaves : ℝ) + (r.numLeaves : ℝ) - 1 ≤
      (l.numLeaves : ℝ) + (r.numLeaves : ℝ) by linarith)
  refine ⟨hp, hlog, ?_⟩
  have hsum := skew_leaf_sum_bound l r
  linarith

/-- The actual Nat predecessor can be cast only after proving no underflow. -/
theorem leaf_predecessor_cast (l : BinaryTree α) (r : BinaryTree β) :
    ((l.numLeaves + r.numLeaves - 1 : Nat) : ℝ) =
      (l.numLeaves : ℝ) + (r.numLeaves : ℝ) - 1 := by
  have h : 1 ≤ l.numLeaves + r.numLeaves :=
    (Nat.succ_le_of_lt (BinaryTree.numLeaves_pos l)).trans (Nat.le_add_right _ _)
  rw [Nat.cast_sub h, Nat.cast_add, Nat.cast_one]

theorem skew_empty_bounds :
    (0 < (1 : ℝ) + 1 - 1) ∧
    (Real.logb 2 (1 + 1 - 1 : ℝ) ≤ Real.logb 2 (1 + 1)) ∧
    (Real.logb 2 (1 + 1 - 1 : ℝ) + Real.logb 2 1 + Real.logb 2 1 ≤
      3 * Real.logb 2 (1 + 1)) := by
  simpa only [BinaryTree.numLeaves, Nat.cast_one] using
    skew_shifted_leaf_bound (BinaryTree.nil : BinaryTree Empty)
      (BinaryTree.nil : BinaryTree Empty)

theorem skew_empty_values :
    (Real.logb 2 (1 + 1 - 1 : ℝ) = 0) ∧
    (Real.logb 2 (1 : ℝ) + Real.logb 2 1 = 0) ∧
    (2 * Real.logb 2 (1 + 1 : ℝ) = 2) ∧
    (3 * Real.logb 2 (1 + 1 : ℝ) = 3) := by
  norm_num [log_two]

/-- Possibly empty child counts give the stronger zero-slack product estimate. -/
theorem pairing_child_product_bound (n1 n2 : Nat) :
    Real.logb 2 (1 + (n1 : ℝ) + (n2 : ℝ)) ≤
      Real.logb 2 (1 + (n1 : ℝ)) + Real.logb 2 (1 + (n2 : ℝ)) := by
  have hn1 : (0 : ℝ) ≤ (n1 : ℝ) := Nat.cast_nonneg n1
  have hn2 : (0 : ℝ) ≤ (n2 : ℝ) := Nat.cast_nonneg n2
  have h1 : (0 : ℝ) < 1 + (n1 : ℝ) := by linarith
  have h2 : (0 : ℝ) < 1 + (n2 : ℝ) := by linarith
  have hs : (0 : ℝ) < 1 + (n1 : ℝ) + (n2 : ℝ) := by linarith
  have hprod : 1 + (n1 : ℝ) + (n2 : ℝ) ≤
      (1 + (n1 : ℝ)) * (1 + (n2 : ℝ)) := by
    nlinarith [mul_nonneg hn1 hn2]
  have hlog := Real.logb_le_logb_of_le (show (1 : ℝ) < 2 by norm_num) hs hprod
  rw [Real.logb_mul (ne_of_gt h1) (ne_of_gt h2)] at hlog
  exact hlog

/-- Retain the source's extra one without interpreting it as an executed tick. -/
theorem pairing_child_source_bound (n1 n2 : Nat) :
    Real.logb 2 (1 + (n1 : ℝ) + (n2 : ℝ)) ≤
      1 + Real.logb 2 (1 + (n1 : ℝ)) + Real.logb 2 (1 + (n2 : ℝ)) := by
  have h := pairing_child_product_bound n1 n2
  linarith

theorem pairing_empty_children_bounds :
    (Real.logb 2 (1 : ℝ) ≤ Real.logb 2 1 + Real.logb 2 1) ∧
    (Real.logb 2 (1 : ℝ) ≤ 1 + Real.logb 2 1 + Real.logb 2 1) := by
  constructor
  · simpa only [Nat.cast_zero, add_zero] using pairing_child_product_bound 0 0
  · simpa only [Nat.cast_zero, add_zero] using pairing_child_source_bound 0 0

theorem pairing_empty_children_values :
    (Real.logb 2 (1 : ℝ) = 0) ∧
    (Real.logb 2 (1 : ℝ) + Real.logb 2 1 = 0) ∧
    (1 + Real.logb 2 (1 : ℝ) + Real.logb 2 1 = 1) := by
  norm_num

theorem nat_subtraction_boundary :
    (((0 + 0 - 1 : Nat) : ℝ) = 0) ∧
    ((0 : ℝ) + 0 - 1 = -1) ∧
    (((0 + 0 - 1 : Nat) : ℝ) ≠ (0 : ℝ) + 0 - 1) := by
  norm_num

private theorem log_base_four_two : Real.logb 4 (2 : ℝ) = 1 / 2 := by
  have hpow : Real.logb 4 (4 : ℝ) = 2 * Real.logb 4 (2 : ℝ) := by
    simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using Real.logb_pow (4 : ℝ) 2 2
  rw [Real.logb_self_eq_one (show (1 : ℝ) < 4 by norm_num)] at hpow
  linarith

/-- The weak general-base law holds, but the fixed base-two margin cannot be copied. -/
theorem base_four_boundary :
    (Real.logb 4 (1 : ℝ) + Real.logb 4 1 ≤ 2 * Real.logb 4 (1 + 1)) ∧
    (2 * Real.logb 4 (1 + 1 : ℝ) = 1) ∧
    ¬ (Real.logb 4 (1 : ℝ) + Real.logb 4 1 + 2 ≤
      2 * Real.logb 4 (1 + 1)) := by
  refine ⟨skew_scalar_sum_bound 4 1 1 (by norm_num) (by norm_num) (by norm_num), ?_⟩
  norm_num [log_base_four_two]

private theorem log_base_half_two : Real.logb (1 / 2) (2 : ℝ) = -1 := by
  simpa only [one_div, log_two] using Real.logb_inv_base (2 : ℝ) 2

theorem decreasing_base_overclaim_fails :
    ¬ (Real.logb (1 / 2) (1 : ℝ) + Real.logb (1 / 2) 1 ≤
      2 * Real.logb (1 / 2) (1 + 1)) := by
  norm_num [log_base_half_two]

end LogarithmBoundsExamples

import Applications.Trees.AVL.ElementaryBounds
import Applications.Trees.AVL.Height
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Connected cases for the direct elementary AVL bounds and the implication
from global almost-completeness. Fibonacci trees serve only as concrete shape
witnesses here; the universal direct argument has a separate owner.
Source and statement assessment: docs/research/fdsa-avl-elementary-bounds.md.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.AVLElementaryBounds
open Trees.AVL
universe u
variable {α : Type u}

/-! D01: nil has one external leaf, so its logarithm is zero. -/
theorem empty_observations :
    (.nil : BinaryTree Unit).height = 0 ∧
      (.nil : BinaryTree Unit).numLeaves = 1 ∧
      Trees.minHeight (.nil : BinaryTree Unit) = 0 := ⟨rfl, rfl, rfl⟩

theorem empty_bounds :
    (1 : Nat) ≤ 1 ∧ (1 : Nat) ≤ 1 ∧
      (0 : ℝ) ≤ 2 * Real.logb 2 (1 : ℝ) := by
  refine ⟨two_pow_ceil_half_height_le_numLeaves (.nil : BinaryTree Unit) balanced_nil,
    two_pow_half_height_le_numLeaves (.nil : BinaryTree Unit) balanced_nil, ?_⟩
  simpa only [BinaryTree.height, BinaryTree.numLeaves, Nat.cast_zero, Nat.cast_one] using
    height_le_two_mul_logb_numLeaves (.nil : BinaryTree Unit) balanced_nil

theorem empty_logarithm : Real.logb 2 (1 : ℝ) = 0 := by simp

/-! D02: the odd-height ceiling power is strictly stronger at a singleton. -/
theorem singleton_observations :
    (fibTree 1).height = 1 ∧ (fibTree 1).numLeaves = 2 ∧
      2 ^ ((fibTree 1).height / 2) = 1 ∧
      2 ^ (((fibTree 1).height + 1) / 2) = 2 := ⟨rfl, rfl, rfl, rfl⟩

theorem singleton_bounds :
    2 ^ (((fibTree 1).height + 1) / 2) ≤ (fibTree 1).numLeaves ∧
      2 ^ ((fibTree 1).height / 2) ≤ (fibTree 1).numLeaves ∧
      ((fibTree 1).height : ℝ) ≤ 2 * Real.logb 2 ((fibTree 1).numLeaves : ℝ) :=
  ⟨two_pow_ceil_half_height_le_numLeaves _ (balanced_fibTree 1),
    two_pow_half_height_le_numLeaves _ (balanced_fibTree 1),
    height_le_two_mul_logb_numLeaves _ (balanced_fibTree 1)⟩

/-! D03: the direct ceiling estimate need not attain the exact minimum. -/
theorem heightThree_observations :
    (fibTree 3).height = 3 ∧ (fibTree 3).numLeaves = 5 ∧
      2 ^ ((fibTree 3).height / 2) = 2 ∧
      2 ^ (((fibTree 3).height + 1) / 2) = 4 := ⟨rfl, rfl, rfl, rfl⟩

theorem heightThree_bounds :
    2 ^ (((fibTree 3).height + 1) / 2) ≤ (fibTree 3).numLeaves ∧
      2 ^ ((fibTree 3).height / 2) ≤ (fibTree 3).numLeaves ∧
      ((fibTree 3).height : ℝ) ≤ 2 * Real.logb 2 ((fibTree 3).numLeaves : ℝ) :=
  ⟨two_pow_ceil_half_height_le_numLeaves _ (balanced_fibTree 3),
    two_pow_half_height_le_numLeaves _ (balanced_fibTree 3),
    height_le_two_mul_logb_numLeaves _ (balanced_fibTree 3)⟩

theorem heightThree_strict_bound :
    2 ^ (((fibTree 3).height + 1) / 2) < (fibTree 3).numLeaves := by decide

theorem repeated_payload_observation :
    Trees.inorder (fibTree 3) = [(), (), (), ()] := rfl

/-! D04: this is an arithmetic pair, not an assertion about an AVL tree. -/
theorem arithmetic_floor_gap :
    (2 : Nat) ^ (3 / 2) ≤ 2 ∧
      ¬((3 : ℝ) ≤ 2 * Real.logb 2 (2 : ℝ)) := floor_power_log_gap

/-! D05: balance is necessary; the numerical conclusions do not characterize it. -/
def chain : Nat → BinaryTree Unit
  | 0 => .nil
  | n + 1 => .node () (chain n) .nil

@[simp] theorem height_chain (n : Nat) : (chain n).height = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [chain, BinaryTree.height, ih]

@[simp] theorem numLeaves_chain (n : Nat) : (chain n).numLeaves = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [chain, BinaryTree.numLeaves, ih]

theorem chainSix_power_failures :
    ¬2 ^ (((chain 6).height + 1) / 2) ≤ (chain 6).numLeaves ∧
      ¬2 ^ ((chain 6).height / 2) ≤ (chain 6).numLeaves := by
  norm_num [height_chain, numLeaves_chain]

private theorem logb_seven_lt_three : Real.logb 2 (7 : ℝ) < 3 := by
  have h := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (by norm_num : (0 : ℝ) < 7) (by norm_num : (7 : ℝ) < (2 : ℝ) ^ 3)
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h
  simpa using h

theorem chainSix_logarithm_fails :
    ¬((chain 6).height : ℝ) ≤ 2 * Real.logb 2 ((chain 6).numLeaves : ℝ) := by
  have h := logb_seven_lt_three
  simp only [height_chain, numLeaves_chain]
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
  linarith

theorem chainSix_not_balanced : ¬Balanced (chain 6) := by
  intro h
  exact chainSix_power_failures.1 (two_pow_ceil_half_height_le_numLeaves _ h)

theorem chainFour_not_balanced : ¬Balanced (chain 4) := by
  norm_num [chain, balanced_node, BinaryTree.height]

theorem chainFour_power_bounds :
    2 ^ (((chain 4).height + 1) / 2) ≤ (chain 4).numLeaves ∧
      2 ^ ((chain 4).height / 2) ≤ (chain 4).numLeaves := by
  norm_num [height_chain, numLeaves_chain]

private theorem two_le_logb_five : (2 : ℝ) ≤ Real.logb 2 (5 : ℝ) := by
  have h : Real.logb 2 ((2 : ℝ) ^ 2) ≤ Real.logb 2 (5 : ℝ) :=
    (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2)
      (by positivity) (by norm_num : (0 : ℝ) < 5)).mpr (by norm_num)
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h
  simpa using h

theorem chainFour_logarithm_bound :
    ((chain 4).height : ℝ) ≤ 2 * Real.logb 2 ((chain 4).numLeaves : ℝ) := by
  have h := two_le_logb_five
  simp only [height_chain, numLeaves_chain]
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
  linarith

/-! D06: global almost-completeness is stronger than recursive AVL balance. -/
theorem fibFour_observations :
    Balanced (fibTree 4) ∧ (fibTree 4).height = 4 ∧
      Trees.minHeight (fibTree 4) = 2 ∧ (fibTree 4).numLeaves = 8 :=
  ⟨balanced_fibTree 4, height_fibTree 4, rfl, rfl⟩

theorem fibFour_not_almostComplete : ¬Trees.AlmostComplete (fibTree 4) := by
  change ¬4 ≤ 2 + 1
  decide

theorem children_and_local_balance_do_not_supply_global_condition :
    Trees.AlmostComplete (fibTree 3) ∧ Trees.AlmostComplete (fibTree 2) ∧
      (fibTree 3).height ≤ (fibTree 2).height + 1 ∧
      (fibTree 2).height ≤ (fibTree 3).height + 1 ∧
      ¬Trees.AlmostComplete (fibTree 4) := by
  refine ⟨?_, ?_, by decide, by decide, fibFour_not_almostComplete⟩
  · change 3 ≤ 2 + 1
    decide
  · change 2 ≤ 1 + 1
    decide

/-! D07: the global predicate imposes no left-packing convention. -/
def rightHeavy : BinaryTree Unit := .node () .nil (fibTree 1)

theorem rightHeavy_observations :
    rightHeavy.height = 2 ∧ Trees.minHeight rightHeavy = 1 ∧
      rightHeavy.numLeaves = 3 := ⟨rfl, rfl, rfl⟩

theorem rightHeavy_almostComplete : Trees.AlmostComplete rightHeavy := by
  change 2 ≤ 1 + 1
  decide

theorem rightHeavy_balanced : Balanced rightHeavy :=
  balanced_of_almostComplete rightHeavy rightHeavy_almostComplete

theorem rightHeavy_children_almostComplete :
    Trees.AlmostComplete (.nil : BinaryTree Unit) ∧ Trees.AlmostComplete (fibTree 1) :=
  Trees.almostComplete_children () .nil (fibTree 1) rightHeavy_almostComplete

theorem rightHeavy_valid_annotation : Valid (annotate rightHeavy) :=
  valid_annotate_of_almostComplete rightHeavy rightHeavy_almostComplete

theorem rightHeavy_bounds :
    2 ^ ((rightHeavy.height + 1) / 2) ≤ rightHeavy.numLeaves ∧
      (rightHeavy.height : ℝ) ≤ 2 * Real.logb 2 (rightHeavy.numLeaves : ℝ) :=
  ⟨two_pow_ceil_half_height_le_numLeaves _ rightHeavy_balanced,
    height_le_two_mul_logb_numLeaves _ rightHeavy_balanced⟩

/-! D08: shape information does not certify an arbitrary stored annotation. -/
def badThree : BinaryTree (Unit × Nat) := .node ((), 3) .nil .nil
def badFour : BinaryTree (Unit × Nat) := .node ((), 4) .nil .nil

theorem bad_cache_observations :
    ht badThree = 3 ∧ ht badFour = 4 ∧ badThree.height = 1 ∧
      badFour.height = 1 ∧ badThree.numLeaves = 2 ∧ badFour.numLeaves = 2 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem same_erased_shape : Trees.Cached.erase badThree = Trees.Cached.erase badFour := rfl

theorem badThree_erased_almostComplete :
    Trees.AlmostComplete (Trees.Cached.erase badThree) := by
  change 1 ≤ 1 + 1
  decide

theorem badThree_erased_balanced : Balanced (Trees.Cached.erase badThree) :=
  balanced_of_almostComplete _ badThree_erased_almostComplete

theorem badThree_actual_height_bound :
    2 ^ ((badThree.height + 1) / 2) ≤ badThree.numLeaves := by
  simpa only [Trees.Cached.height_erase, Trees.Cached.numLeaves_erase] using
    two_pow_ceil_half_height_le_numLeaves _ badThree_erased_balanced

theorem badThree_stored_bounds_separate :
    2 ^ (ht badThree / 2) ≤ badThree.numLeaves ∧
      ¬2 ^ ((ht badThree + 1) / 2) ≤ badThree.numLeaves := by
  norm_num [badThree, ht, Trees.Cached.read, BinaryTree.numLeaves]

theorem badFour_stored_bounds_fail :
    ¬2 ^ (ht badFour / 2) ≤ badFour.numLeaves ∧
      ¬2 ^ ((ht badFour + 1) / 2) ≤ badFour.numLeaves := by
  norm_num [badFour, ht, Trees.Cached.read, BinaryTree.numLeaves]

theorem badThree_cache_invalid : ¬CacheValid badThree := by
  intro h
  have eq := ht_eq_height_of_cacheValid badThree h
  norm_num [badThree, ht, Trees.Cached.read, BinaryTree.height] at eq

theorem badFour_cache_invalid : ¬CacheValid badFour := by
  intro h
  have eq := ht_eq_height_of_cacheValid badFour h
  norm_num [badFour, ht, Trees.Cached.read, BinaryTree.height] at eq

theorem badThree_not_valid : ¬Valid badThree := fun h => badThree_cache_invalid h.2

def repaired : BinaryTree (Unit × Nat) := annotate (Trees.Cached.erase badThree)

theorem repaired_valid : Valid repaired :=
  valid_annotate_of_almostComplete _ badThree_erased_almostComplete

theorem repaired_erasure : Trees.Cached.erase repaired = Trees.Cached.erase badThree :=
  erase_annotate _

theorem repaired_bounds :
    2 ^ ((repaired.height + 1) / 2) ≤ repaired.numLeaves ∧
      2 ^ (repaired.height / 2) ≤ repaired.numLeaves ∧
      (repaired.height : ℝ) ≤ 2 * Real.logb 2 (repaired.numLeaves : ℝ) ∧
      2 ^ ((ht repaired + 1) / 2) ≤ repaired.numLeaves ∧
      2 ^ (ht repaired / 2) ≤ repaired.numLeaves ∧
      (ht repaired : ℝ) ≤ 2 * Real.logb 2 (repaired.numLeaves : ℝ) :=
  ⟨two_pow_ceil_half_height_le_numLeaves_of_valid _ repaired_valid,
    two_pow_half_height_le_numLeaves_of_valid _ repaired_valid,
    height_le_two_mul_logb_numLeaves_of_valid _ repaired_valid,
    two_pow_ceil_half_ht_le_numLeaves _ repaired_valid,
    two_pow_half_ht_le_numLeaves _ repaired_valid,
    ht_le_two_mul_logb_numLeaves _ repaired_valid⟩

/-! D09: arbitrary payload universes include the empty type. -/
theorem empty_payload_bounds :
    2 ^ (((.nil : BinaryTree (PEmpty.{u + 1})).height + 1) / 2) ≤ 1 ∧
      2 ^ ((.nil : BinaryTree (PEmpty.{u + 1})).height / 2) ≤ 1 ∧
      ((.nil : BinaryTree (PEmpty.{u + 1})).height : ℝ) ≤ 2 * Real.logb 2 (1 : ℝ) := by
  refine ⟨two_pow_ceil_half_height_le_numLeaves
      (.nil : BinaryTree (PEmpty.{u + 1})) balanced_nil,
    two_pow_half_height_le_numLeaves (.nil : BinaryTree (PEmpty.{u + 1})) balanced_nil, ?_⟩
  simpa only [BinaryTree.numLeaves, Nat.cast_one] using
    height_le_two_mul_logb_numLeaves (.nil : BinaryTree (PEmpty.{u + 1})) balanced_nil

theorem empty_payload_almostComplete :
    Trees.AlmostComplete (.nil : BinaryTree (PEmpty.{u + 1})) := Trees.almostComplete_nil

theorem empty_payload_balanced : Balanced (.nil : BinaryTree (PEmpty.{u + 1})) :=
  balanced_of_almostComplete (.nil : BinaryTree (PEmpty.{u + 1})) empty_payload_almostComplete

theorem empty_payload_valid_annotation :
    Valid (annotate (.nil : BinaryTree (PEmpty.{u + 1}))) :=
  valid_annotate_of_almostComplete
    (.nil : BinaryTree (PEmpty.{u + 1})) empty_payload_almostComplete

theorem empty_payload_cached_bounds :
    2 ^ ((ht (.nil : BinaryTree (PEmpty.{u + 1} × Nat)) + 1) / 2) ≤ 1 ∧
      2 ^ (ht (.nil : BinaryTree (PEmpty.{u + 1} × Nat)) / 2) ≤ 1 ∧
      (ht (.nil : BinaryTree (PEmpty.{u + 1} × Nat)) : ℝ) ≤ 2 * Real.logb 2 (1 : ℝ) := by
  refine ⟨two_pow_ceil_half_ht_le_numLeaves
      (.nil : BinaryTree (PEmpty.{u + 1} × Nat)) valid_nil,
    two_pow_half_ht_le_numLeaves (.nil : BinaryTree (PEmpty.{u + 1} × Nat)) valid_nil, ?_⟩
  simpa only [BinaryTree.numLeaves, Nat.cast_one] using
    ht_le_two_mul_logb_numLeaves (.nil : BinaryTree (PEmpty.{u + 1} × Nat)) valid_nil

theorem empty_payload_height (t : BinaryTree (PEmpty.{u + 1})) : t.height = 0 := by
  cases t with
  | nil => rfl
  | node a _ _ => exact PEmpty.elim a

theorem empty_payload_no_positive_height (n : Nat) (positive : 0 < n) :
    ¬∃ t : BinaryTree (PEmpty.{u + 1}), t.height = n := by
  rintro ⟨t, height⟩
  exact (Nat.ne_of_gt positive) (height.symm.trans (empty_payload_height t))

theorem arbitrary_payload_bounds (t : BinaryTree α) (h : Balanced t) :
    2 ^ ((t.height + 1) / 2) ≤ t.numLeaves ∧ 2 ^ (t.height / 2) ≤ t.numLeaves ∧
      (t.height : ℝ) ≤ 2 * Real.logb 2 (t.numLeaves : ℝ) :=
  ⟨two_pow_ceil_half_height_le_numLeaves t h, two_pow_half_height_le_numLeaves t h,
    height_le_two_mul_logb_numLeaves t h⟩

theorem prescribed_height_bounds (t : BinaryTree α) (h : Balanced t)
    (n : Nat) (height : t.height = n) :
    2 ^ ((n + 1) / 2) ≤ t.numLeaves ∧ 2 ^ (n / 2) ≤ t.numLeaves := by
  constructor
  · simpa only [height] using two_pow_ceil_half_height_le_numLeaves t h
  · simpa only [height] using two_pow_half_height_le_numLeaves t h

theorem arbitrary_global_consequences (t : BinaryTree α) (h : Trees.AlmostComplete t) :
    Balanced t ∧ Valid (annotate t) ∧
      (t.height : ℝ) ≤ 2 * Real.logb 2 (t.numLeaves : ℝ) :=
  ⟨balanced_of_almostComplete t h, valid_annotate_of_almostComplete t h,
    height_le_two_mul_logb_numLeaves t (balanced_of_almostComplete t h)⟩

theorem arbitrary_cached_bounds (t : BinaryTree (α × Nat)) (h : Valid t) :
    2 ^ ((t.height + 1) / 2) ≤ t.numLeaves ∧ 2 ^ (t.height / 2) ≤ t.numLeaves ∧
      (t.height : ℝ) ≤ 2 * Real.logb 2 (t.numLeaves : ℝ) ∧
      2 ^ ((ht t + 1) / 2) ≤ t.numLeaves ∧ 2 ^ (ht t / 2) ≤ t.numLeaves ∧
      (ht t : ℝ) ≤ 2 * Real.logb 2 (t.numLeaves : ℝ) :=
  ⟨two_pow_ceil_half_height_le_numLeaves_of_valid t h,
    two_pow_half_height_le_numLeaves_of_valid t h,
    height_le_two_mul_logb_numLeaves_of_valid t h,
    two_pow_ceil_half_ht_le_numLeaves t h, two_pow_half_ht_le_numLeaves t h,
    ht_le_two_mul_logb_numLeaves t h⟩

theorem prescribed_stored_height_bound (t : BinaryTree (α × Nat)) (h : Valid t)
    (n : Nat) (height : ht t = n) : 2 ^ (n / 2) ≤ t.numLeaves := by
  simpa only [height] using two_pow_half_ht_le_numLeaves t h

end Examples.AVLElementaryBounds

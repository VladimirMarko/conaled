import Applications.Resources.HeightBalance.Updates
import Applications.Resources.AVL
import Examples.BalancedIntervalTrees
import Examples.HeightUpdates

/-!
# Connected complete-annotation repair and update observations

The exact values and tariffs were fixed independently before the measured
programs, as recorded in `docs/research/fdsa-height-updates.md`. These clients
use the existing literal interval-tree and ordinary-height fixtures. Product
combination charges four declared arithmetic operations; atomic strict-key
comparison charges one. These are source observations, not bit or host costs.
The field-counted key comparator and measured interval query have their separate
public owners and connected cases. Word observations remain parameters, without
an invented bound. Ordinary callbacks below reuse the public measured AVL owner.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.MeasuredHeightUpdates
open Trees Resources Resources.HeightBalance Search Search.IntervalTree
open Examples.BalancedIntervalTrees
open Examples.IntervalTreeFoundations
  (IndexedKey indexedInterval indexedZero indexedOne rootEight)
universe u v
variable {α : Type u} {σ : Type v}

/-- Height projection is free; the enclosing root read still costs one. -/
def productHeight (s : Nat × Nat) : Measured Nat Nat := (s.1, 0)

/-- Height max/successor and two endpoint maxima cost four in this model. -/
def productCombine (iv : α → IntervalKey Nat) (l : Nat × Nat) (a : α)
    (r : Nat × Nat) : Measured (Nat × Nat) Nat :=
  ((Balanced.annotation iv).combine l a r, 4)

/-- One atomic comparison, distinct from the later field-counted comparator. -/
def atomicLt [LT α] [DecidableLT α] (a b : α) : Measured Bool Nat :=
  (decide (a < b), 1)

abbrev productBalL := balLRun (0, 0) productHeight (productCombine (id : NKey → NKey)) 1
abbrev productBalR := balRRun (0, 0) productHeight (productCombine (id : NKey → NKey)) 1
abbrev productInsert :=
  insertRun (0, 0) productHeight (productCombine (id : NKey → NKey)) atomicLt 1
abbrev productDelete :=
  deleteRun (0, 0) productHeight (productCombine (id : NKey → NKey)) atomicLt 1
abbrev productSplit :=
  splitMaxRun (0, 0) productHeight (productCombine (id : NKey → NKey)) 1

/-! The root reader observes stored height, even on a malformed summary. -/
theorem empty_and_malformed_reads :
    TreeCache.readRun (0, 0) (.nil : NTree) = ((0, 0), 1) ∧
      htRun (0, 0) productHeight (.nil : NTree) = (0, 1) ∧
      htRun (0, 0) productHeight malformed = (99, 1) ∧
      malformed.height = 1 := ⟨rfl, rfl, rfl, rfl⟩

theorem singleton_construction :
    TreeCache.nodeRun (0, 0) (productCombine id) .nil (point 2) .nil =
      (leaf id (point 2), 7) := rfl

theorem actual_combine_result :
    TreeCache.nodeRun (0, 0) (fun _ (_ : NKey) _ => ((7, 99), 11))
      .nil (point 2) .nil =
      (.node (point 2, (7, 99)) .nil .nil, 14) := rfl

/-! Both direct orientations, including all single and double repairs. -/
theorem empty_repairs :
    productBalL .nil (point 2) .nil = (leaf id (point 2), 13) ∧
      productBalR .nil (point 2) .nil = (leaf id (point 2), 13) := ⟨rfl, rfl⟩

theorem four_repairs :
    productBalR .nil rrA rrRight = (rrExpected, 23) ∧
      productBalL llLeft llC .nil = (llExpected, 23) ∧
      productBalL lrLeft lrC .nil = (lrExpected, 30) ∧
      productBalR .nil rrA rlRight = (rrExpected, 30) := ⟨rfl, rfl, rfl, rfl⟩

def badRight : NTree := .node (rrB, (99, 100)) .nil (leaf id rrC)

theorem malformed_height_changes_branch :
    productBalR .nil rrA badRight =
      (.node (rrA, (100, 100)) .nil badRight, 13) ∧
      (.node (rrA, (100, 100)) .nil badRight : NTree).height = 3 := ⟨rfl, rfl⟩

theorem retained_child_is_not_repaired :
    TreeCache.nodeRun (0, 0) (productCombine id) staleLeft rrB (leaf id rrC) =
      (staleRotated, 7) ∧
      productBalL staleLeft rrB (leaf id rrC) = (staleRotated, 13) := ⟨rfl, rfl⟩

/-- False returned heights deliberately violate the erasure contract. -/
theorem actual_height_result_controls_branch :
    balRRun (0, 0) (fun _ => (0, 0)) (productCombine id) 1 .nil rrA rrRight =
      (.node (rrA, (3, 100)) .nil rrRight, 13) := rfl

def heavyFallbackHeight (s : Nat × Nat) : Measured Nat Nat :=
  (if s = (0, 0) then 2 else 0, 0)

def middleFallbackHeight (s : Nat × Nat) : Measured Nat Nat :=
  (if s = (2, 1) then 3 else if s = (0, 0) then 1 else 0, 0)

def missingMiddle : NTree := .node (point 1, (2, 1)) (leaf id (point 0)) .nil

/-- Both total fallback arms are observable through non-erasing callbacks. -/
theorem total_fallback_controls :
    balLRun (0, 0) heavyFallbackHeight (productCombine id) 1 .nil (point 2)
        (leaf id (point 3)) =
      (.node (point 2, (2, 3)) .nil (leaf id (point 3)), 13) ∧
      balLRun (0, 0) middleFallbackHeight (productCombine id) 1
        missingMiddle (point 2) .nil =
      (.node (point 2, (3, 2)) missingMiddle .nil, 16) ∧
      productBalL missingMiddle (point 2) .nil =
      (.node (point 1, (2, 2)) (leaf id (point 0)) (leaf id (point 2)), 23) :=
  ⟨rfl, rfl, rfl⟩

/-- Truthful but input-dependent height work has no global constant bound. -/
def heightCharged (s : Nat × Nat) : Measured Nat Nat := (s.1, s.1)

theorem reached_height_observations :
    balRRun (0, 0) heightCharged (productCombine id) 1 .nil rrA rrRight =
      (rrExpected, 26) := rfl

theorem height_callback_unbounded : ¬ ∃ H, ∀ s, (heightCharged s).2 ≤ H := by
  rintro ⟨H, hH⟩
  have h := hH (H + 1, 0)
  change H + 1 ≤ H at h
  omega

/-! Base calls, equal raw return, and absent-key reconstruction differ. -/
theorem empty_updates_and_extraction :
    productInsert (point 2) .nil = (leaf id (point 2), 8) ∧
      productDelete (point 2) .nil = (.nil, 1) ∧
      productSplit .nil = (none, 1) ∧
      productSplit (leaf id (point 2)) = (some (.nil, point 2), 1) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem extraction_reuses_left_without_terminal_nil :
    productSplit (.node (point 2, (99, 77)) (leaf id (point 1)) .nil) =
      (some (leaf id (point 1), point 2), 1) := rfl

theorem equal_insert_preserves_raw_cache :
    productInsert (point 2) (leaf id (point 2)) = (leaf id (point 2), 4) ∧
      productInsert rootEight malformed = (malformed, 4) := ⟨rfl, rfl⟩

theorem singleton_insert_directions :
    productInsert (point 0) (leaf id (point 1)) =
      (.node (point 1, (2, 1)) (leaf id (point 0)) .nil, 23) ∧
      productInsert (point 2) (leaf id (point 1)) =
      (.node (point 1, (2, 2)) .nil (leaf id (point 2)), 24) := ⟨rfl, rfl⟩

theorem singleton_delete_branches :
    productDelete (point 0) (leaf id (point 1)) = (leaf id (point 1), 16) ∧
      productDelete (point 2) (leaf id (point 1)) = (leaf id (point 1), 17) ∧
      productDelete (point 1) (leaf id (point 1)) = (.nil, 4) := ⟨rfl, rfl, rfl⟩

theorem absent_delete_reconstructs_malformed_cache :
    productDelete (point 1) malformed = (leaf id rootEight, 16) ∧
      productDelete (point 9) malformed = (leaf id rootEight, 17) := ⟨rfl, rfl⟩

def perfectThree : NTree :=
  .node (point 2, (2, 3)) (leaf id (point 1)) (leaf id (point 3))
def perfectSeven : NTree :=
  .node (point 4, (3, 7)) perfectThree
    (.node (point 6, (2, 7)) (leaf id (point 5)) (leaf id (point 7)))

theorem duplicate_descent_still_rebuilds :
    productInsert (point 1) perfectThree = (perfectThree, 19) ∧
      productInsert (point 3) perfectThree = (perfectThree, 20) := ⟨rfl, rfl⟩

theorem three_node_extraction_and_root_deletion :
    productSplit perfectThree =
      (some (.node (point 2, (2, 2)) (leaf id (point 1)) .nil, point 3), 15) ∧
      productDelete (point 2) perfectThree =
      (.node (point 1, (2, 3)) .nil (leaf id (point 3)), 17) := ⟨rfl, rfl⟩

/-- Rightmost is an unconditional observation; greatest requires order. -/
theorem unordered_extraction_is_rightmost :
    productSplit (.node (point 10, (2, 10)) .nil (leaf id (point 1))) =
      (some (leaf id (point 10), point 1), 15) := rfl

theorem four_insert_rotations :
    productInsert rrC (.node (rrA, (2, 2)) .nil (leaf id rrB)) =
      (rrExpected, 50) ∧
      productInsert llA (.node (llC, (2, 100)) (leaf id llB) .nil) =
      (llExpected, 48) ∧
      productInsert lrB (.node (lrC, (2, 100)) (leaf id lrA) .nil) =
      (lrExpected, 56) ∧
      productInsert rrB (.node (rrA, (2, 100)) .nil (leaf id rrC)) =
      (rrExpected, 56) := ⟨rfl, rfl, rfl, rfl⟩

/-- Equality of inner and outer heights selects a single rotation. -/
theorem deletion_ties :
    productDelete (point 5) deleteLeftInput = (deleteLeftExpected, 30) ∧
      productDelete (point 1) deleteRightInput = (deleteRightExpected, 29) := ⟨rfl, rfl⟩

def predecessorResult : NTree :=
  .node (point 3, (3, 7)) (.node (point 2, (2, 2)) (leaf id (point 1)) .nil)
    (.node (point 6, (2, 7)) (leaf id (point 5)) (leaf id (point 7)))
def prefixPredecessorResult : NTree :=
  .node (point 4, (3, 7)) (.node (point 1, (2, 3)) .nil (leaf id (point 3)))
    (.node (point 6, (2, 7)) (leaf id (point 5)) (leaf id (point 7)))

theorem predecessor_and_search_prefix :
    productDelete (point 4) perfectSeven = (predecessorResult, 31) ∧
      productDelete (point 2) perfectSeven = (prefixPredecessorResult, 32) := ⟨rfl, rfl⟩

def unchangedHeightBefore : NTree :=
  .node (point 4, (3, 6)) (leaf id (point 2))
    (.node (point 6, (2, 6)) (leaf id (point 5)) .nil)
def unchangedHeightAfter : NTree :=
  .node (point 4, (3, 7)) (leaf id (point 2))
    (.node (point 6, (2, 7)) (leaf id (point 5)) (leaf id (point 7)))

theorem unchanged_heights_fresh_complete_annotations :
    productInsert (point 7) unchangedHeightBefore = (unchangedHeightAfter, 40) ∧
      productDelete (point 7) unchangedHeightAfter = (unchangedHeightBefore, 36) ∧
      unchangedHeightBefore.height = unchangedHeightAfter.height ∧
      Cached.read (0, 0) unchangedHeightBefore = (3, 6) ∧
      Cached.read (0, 0) unchangedHeightAfter = (3, 7) := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! Deliberately false Booleans expose the actual selected insertion branch. -/
theorem actual_comparison_result_controls_insert :
    insertRun (0, 0) productHeight (productCombine id) (fun _ _ => (false, 1))
      1 (point 2) (leaf id (point 1)) = (leaf id (point 1), 4) ∧
      insertRun (0, 0) productHeight (productCombine id) (fun _ _ => (true, 1))
      1 (point 2) (leaf id (point 1)) =
      (.node (point 1, (2, 2)) (leaf id (point 2)) .nil, 23) := ⟨rfl, rfl⟩

def asymmetricLt (a b : NKey) : Measured Bool Nat :=
  (decide (a < b), if a < b then 2 else 5)

theorem actual_comparison_observations :
    insertRun (0, 0) productHeight (productCombine id) asymmetricLt
      1 (point 0) (leaf id (point 1)) =
      (.node (point 1, (2, 1)) (leaf id (point 0)) .nil, 24) ∧
      insertRun (0, 0) productHeight (productCombine id) asymmetricLt
      1 (point 2) (leaf id (point 1)) =
      (.node (point 1, (2, 2)) .nil (leaf id (point 2)), 29) ∧
      insertRun (0, 0) productHeight (productCombine id) asymmetricLt
      1 (point 1) (leaf id (point 1)) = (leaf id (point 1), 12) := ⟨rfl, rfl, rfl⟩

/-! Higher-universe complete keys retain their distinct occurrence IDs. -/
abbrev indexedInsert :=
  insertRun (0, 0) productHeight (productCombine indexedInterval) atomicLt 1
abbrev indexedDelete :=
  deleteRun (0, 0) productHeight (productCombine indexedInterval) atomicLt 1

theorem indexed_update_observations :
    indexedInsert indexedZero .nil = (indexedFirst, 8) ∧
      indexedInsert indexedOne indexedFirst = (indexedBoth, 24) ∧
      indexedInsert indexedZero indexedBoth = (indexedBoth, 4) ∧
      indexedDelete indexedZero indexedBoth = (indexedLast, 4) ∧
      indexedDelete indexedOne indexedLast = (.nil, 4) := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem indexed_rotation_and_predecessor_observations :
    indexedInsert indexedTwo indexedBoth = (indexedTriple, 50) ∧
      splitMaxRun (0, 0) productHeight (productCombine indexedInterval) 1
        (leaf indexedInterval indexedZero) = (some (.nil, indexedZero), 1) ∧
      indexedDelete indexedOne indexedTriple = (indexedAfterRootDelete, 17) :=
  ⟨rfl, rfl, rfl⟩

/-! Ordinary complete height annotations have their own K=2 specialization. -/
def ordinaryHeight (h : Nat) : Measured Nat Nat := Resources.AVL.heightRun h
def ordinaryCombine (l : Nat) (a : Nat) (r : Nat) : Measured Nat Nat :=
  Resources.AVL.combineRun l a r
abbrev ordinaryInsert := insertRun 0 ordinaryHeight ordinaryCombine atomicLt 1
abbrev ordinaryDelete := deleteRun 0 ordinaryHeight ordinaryCombine atomicLt 1
abbrev ordinarySplit := splitMaxRun 0 ordinaryHeight ordinaryCombine 1

theorem ordinary_base_tariffs :
    ordinaryInsert 2 .nil = (Examples.HeightUpdates.heightSingleton 2, 6) ∧
      ordinarySplit (.nil : Examples.HeightUpdates.HTree) = (none, 1) ∧
      ordinarySplit (Examples.HeightUpdates.heightSingleton 2) = (some (.nil, 2), 1) ∧
      ordinaryDelete 2 .nil = (.nil, 1) := ⟨rfl, rfl, rfl, rfl⟩

theorem ordinary_predecessor_tariff :
    ordinaryDelete 4 Examples.HeightUpdates.perfectSeven =
      (Examples.HeightUpdates.deletePredecessorOutput, 27) := rfl

/-! Public repair contracts: raw trees and independent element universes. -/
theorem product_height_value (iv : α → IntervalKey Nat)
    (t : BinaryTree (α × (Nat × Nat))) :
    (htRun (0, 0) productHeight t).1 =
      Trees.HeightBalance.ht (Balanced.annotation iv) t :=
  htRun_value (Balanced.annotation iv) productHeight t (fun _ => rfl)

theorem product_repair_values (iv : α → IntervalKey Nat) (d : Nat)
    (l : BinaryTree (α × (Nat × Nat))) (a : α) (r : BinaryTree (α × (Nat × Nat))) :
    (balLRun (0, 0) productHeight (productCombine iv) d l a r).1 =
        Trees.HeightBalance.balL (Balanced.annotation iv) d l a r ∧
      (balRRun (0, 0) productHeight (productCombine iv) d l a r).1 =
        Trees.HeightBalance.balR (Balanced.annotation iv) d l a r :=
  ⟨balLRun_value (Balanced.annotation iv) productHeight (productCombine iv)
      d l a r (fun _ => rfl) (fun _ _ _ => rfl),
    balRRun_value (Balanced.annotation iv) productHeight (productCombine iv)
      d l a r (fun _ => rfl) (fun _ _ _ => rfl)⟩

/-- No validity, order, positive tolerance or height-erasure premise is used. -/
theorem product_repair_bounds (iv : α → IntervalKey Nat) (d : Nat)
    (l : BinaryTree (α × (Nat × Nat))) (a : α) (r : BinaryTree (α × (Nat × Nat))) :
    (balLRun (0, 0) productHeight (productCombine iv) d l a r).2 ≤ 30 ∧
      (balRRun (0, 0) productHeight (productCombine iv) d l a r).2 ≤ 30 :=
  ⟨balLRun_cost_le (0, 0) productHeight (productCombine iv) d l a r 0 4
      (fun _ => Nat.le_refl 0) (fun _ _ _ => Nat.le_refl 4),
    balRRun_cost_le (0, 0) productHeight (productCombine iv) d l a r 0 4
      (fun _ => Nat.le_refl 0) (fun _ _ _ => Nat.le_refl 4)⟩

theorem exact_height_test_tariffs (d : Nat) (l r : NTree) :
    (excessRun (0, 0) productHeight d l r).2 = 5 ∧
      (leHeightRun (0, 0) productHeight l r).2 = 3 :=
  ⟨excessRun_cost (0, 0) productHeight d l r,
    leHeightRun_cost (0, 0) productHeight l r⟩

/-- An intermediate returned summary can be absent from every original root. -/
def intermediateChargedCombine (l : Nat × Nat) (a : NKey) (r : Nat × Nat) :
    Measured (Nat × Nat) Nat :=
  (natAnn.combine l a r, if l = (1, 1) then 11 else 4)

theorem newly_constructed_summary_is_observed :
    (1, 1) ∉ ([(0, 0), (2, 100), (1, 100)] : List (Nat × Nat)) ∧
      balRRun (0, 0) productHeight intermediateChargedCombine 1 .nil rrA rrRight =
        (rrExpected, 30) := ⟨by decide, rfl⟩

/-- Separate annotation and payload universes do not require payload inhabitants. -/
theorem empty_independent_universes (empty : σ) (heightRun : σ → Measured Nat Nat)
    (combineRun : σ → ULift.{u} PEmpty → σ → Measured σ Nat) (d : Nat) :
    splitMaxRun empty heightRun combineRun d .nil = (none, 1) := rfl

/-! The generic complete-summary contracts apply without cache/order premises. -/
theorem product_insert_erasure [LT α] [DecidableLT α]
    (iv : α → IntervalKey Nat) (d : Nat) (x : α)
    (t : BinaryTree (α × (Nat × Nat))) :
    (insertRun (0, 0) productHeight (productCombine iv) atomicLt d x t).1 =
      Trees.HeightBalance.insert (Balanced.annotation iv) d x t :=
  insertRun_value (Balanced.annotation iv) productHeight (productCombine iv) atomicLt
    d x t (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)

theorem product_delete_erasure [LT α] [DecidableLT α]
    (iv : α → IntervalKey Nat) (d : Nat) (x : α)
    (t : BinaryTree (α × (Nat × Nat))) :
    (deleteRun (0, 0) productHeight (productCombine iv) atomicLt d x t).1 =
      Trees.HeightBalance.delete (Balanced.annotation iv) d x t :=
  deleteRun_value (Balanced.annotation iv) productHeight (productCombine iv) atomicLt
    d x t (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)

theorem product_extraction_erasure (iv : α → IntervalKey Nat) (d : Nat)
    (t : BinaryTree (α × (Nat × Nat))) :
    (splitMaxRun (0, 0) productHeight (productCombine iv) d t).1 =
      Trees.HeightBalance.splitMaxOption (Balanced.annotation iv) d t :=
  splitMaxRun_value (Balanced.annotation iv) productHeight (productCombine iv)
    d t (fun _ => rfl) (fun _ _ _ => rfl)

/-- These arithmetic constants follow from global H=0, K=4, C=1 bounds. -/
theorem product_insert_bound [LT α] [DecidableLT α]
    (iv : α → IntervalKey Nat) (d : Nat) (x : α)
    (t : BinaryTree (α × (Nat × Nat))) :
    (insertRun (0, 0) productHeight (productCombine iv) atomicLt d x t).2 ≤
      33 * t.height + 8 :=
  insertRun_cost_le (0, 0) productHeight (productCombine iv) atomicLt d x t 0 4 1
    (fun _ => Nat.le_refl 0) (fun _ _ _ => Nat.le_refl 4) (fun _ _ => Nat.le_refl 1)

theorem product_delete_bound [LT α] [DecidableLT α]
    (iv : α → IntervalKey Nat) (d : Nat) (x : α)
    (t : BinaryTree (α × (Nat × Nat))) :
    (deleteRun (0, 0) productHeight (productCombine iv) atomicLt d x t).2 ≤
      33 * t.height + 1 :=
  deleteRun_cost_le (0, 0) productHeight (productCombine iv) atomicLt d x t 0 4 1
    (fun _ => Nat.le_refl 0) (fun _ _ _ => Nat.le_refl 4) (fun _ _ => Nat.le_refl 1)

theorem product_extraction_bound (iv : α → IntervalKey Nat) (d : Nat)
    (t : BinaryTree (α × (Nat × Nat))) :
    (splitMaxRun (0, 0) productHeight (productCombine iv) d t).2 ≤
      31 * t.height + 1 :=
  splitMaxRun_cost_le (0, 0) productHeight (productCombine iv) d t 0 4
    (fun _ => Nat.le_refl 0) (fun _ _ _ => Nat.le_refl 4)

theorem product_nonempty_extraction_bound (iv : α → IntervalKey Nat) (d : Nat)
    (t : BinaryTree (α × (Nat × Nat))) (hne : t ≠ .nil) :
    (splitMaxRun (0, 0) productHeight (productCombine iv) d t).2 ≤ 31 * t.height :=
  splitMaxRun_cost_le_of_ne_nil (0, 0) productHeight (productCombine iv) d t 0 4
    (fun _ => Nat.le_refl 0) (fun _ _ _ => Nat.le_refl 4) hne

/-- Existing full interval-set preservation composes with measured erasure. -/
theorem measured_product_insert_valid_and_bounded (x : NKey) (t : NTree)
    (hv : Balanced.Valid id t) :
    Balanced.Valid id (productInsert x t).1 ∧
      (productInsert x t).2 ≤ 33 * t.height + 8 := by
  constructor
  · rw [product_insert_erasure]
    exact nat_contract.insert_valid x t hv
  · exact product_insert_bound id 1 x t

theorem measured_product_delete_valid_and_bounded (x : NKey) (t : NTree)
    (hv : Balanced.Valid id t) :
    Balanced.Valid id (productDelete x t).1 ∧
      (productDelete x t).2 ≤ 33 * t.height + 1 := by
  constructor
  · rw [product_delete_erasure]
    exact nat_contract.delete_valid x t hv
  · exact product_delete_bound id 1 x t

/-- Stored height 99 is irrelevant to the bound's structural input height. -/
theorem malformed_input_shape_bounds :
    (productInsert rootEight malformed).2 ≤ 41 ∧
      (productDelete (point 9) malformed).2 ≤ 34 :=
  ⟨product_insert_bound id 1 rootEight malformed,
    product_delete_bound id 1 (point 9) malformed⟩

theorem ordinary_shape_bounds (x : Nat) (t : Examples.HeightUpdates.HTree) :
    (ordinaryInsert x t).2 ≤ 27 * t.height + 6 ∧
      (ordinarySplit t).2 ≤ 25 * t.height + 1 ∧
      (ordinaryDelete x t).2 ≤ 27 * t.height + 1 :=
  ⟨insertRun_cost_le 0 ordinaryHeight ordinaryCombine atomicLt 1 x t 0 2 1
      (fun _ => Nat.le_refl 0) (fun _ _ _ => Nat.le_refl 2) (fun _ _ => Nat.le_refl 1),
    splitMaxRun_cost_le 0 ordinaryHeight ordinaryCombine 1 t 0 2
      (fun _ => Nat.le_refl 0) (fun _ _ _ => Nat.le_refl 2),
    deleteRun_cost_le 0 ordinaryHeight ordinaryCombine atomicLt 1 x t 0 2 1
      (fun _ => Nat.le_refl 0) (fun _ _ _ => Nat.le_refl 2) (fun _ _ => Nat.le_refl 1)⟩

/-! Arbitrary complete-word observations: only the value contract is supplied. -/
def wordHeight (s : Nat × List α) : Measured Nat Nat := (s.1, 0)
def wordCombine (tariff : (Nat × List α) → α → (Nat × List α) → Nat)
    (l : Nat × List α) (a : α) (r : Nat × List α) : Measured (Nat × List α) Nat :=
  ((Examples.HeightRebalance.wordAnnotation α).combine l a r, tariff l a r)

theorem word_insert_erasure [LT α] [DecidableLT α]
    (tariff : (Nat × List α) → α → (Nat × List α) → Nat)
    (d : Nat) (x : α) (t : BinaryTree (α × (Nat × List α))) :
    (insertRun (0, []) wordHeight (wordCombine tariff) atomicLt d x t).1 =
      Trees.HeightBalance.insert (Examples.HeightRebalance.wordAnnotation α) d x t :=
  insertRun_value (Examples.HeightRebalance.wordAnnotation α) wordHeight
    (wordCombine tariff) atomicLt d x t
    (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)

theorem word_delete_erasure [LT α] [DecidableLT α]
    (tariff : (Nat × List α) → α → (Nat × List α) → Nat)
    (d : Nat) (x : α) (t : BinaryTree (α × (Nat × List α))) :
    (deleteRun (0, []) wordHeight (wordCombine tariff) atomicLt d x t).1 =
      Trees.HeightBalance.delete (Examples.HeightRebalance.wordAnnotation α) d x t :=
  deleteRun_value (Examples.HeightRebalance.wordAnnotation α) wordHeight
    (wordCombine tariff) atomicLt d x t
    (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)

/-- Equal ancestor heights do not permit retaining the old word summaries. -/
theorem same_height_words_with_actual_callbacks
    (tariff : (Nat × List Nat) → Nat → (Nat × List Nat) → Nat) :
    (insertRun (0, []) wordHeight (wordCombine tariff) atomicLt
        1 7 Examples.HeightUpdates.wordBase).1 = Examples.HeightUpdates.wordWithSeven ∧
      (deleteRun (0, []) wordHeight (wordCombine tariff) atomicLt
        1 7 Examples.HeightUpdates.wordWithSeven).1 = Examples.HeightUpdates.wordBase :=
  ⟨(word_insert_erasure tariff 1 7 Examples.HeightUpdates.wordBase).trans
      Examples.HeightUpdates.same_height_word_insert.1,
    (word_delete_erasure tariff 1 7 Examples.HeightUpdates.wordWithSeven).trans
      Examples.HeightUpdates.same_height_word_delete.1⟩

end Examples.MeasuredHeightUpdates

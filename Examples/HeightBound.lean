import Applications.Trees.HeightBalance.HeightBound
import Applications.Trees.HeightBalance.SetRefinement
import Applications.Trees.AVL.Height
import Applications.Trees.AVL.Rebalance
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Dedup

/-! Checked clients of the fixed-tolerance height bound. The expected measures,
counterexamples and public theorem connections are described in
`docs/research/fdsa-height-bound.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.HeightBound
open Trees Trees.HeightBalance
universe u v
variable {α : Type u} {σ : Type v}

/-- B01: the empty shape uses external leaves, so its logarithm is defined at one. -/
theorem empty_shape_bounds (d : Nat) :
    2 ^ (((.nil : BinaryTree α).height + d) / (d + 1)) ≤
        (.nil : BinaryTree α).numLeaves ∧
      ((.nil : BinaryTree α).height : ℝ) ≤
        ((d : ℝ) + 1) * Real.logb 2 ((.nil : BinaryTree α).numLeaves : ℝ) ∧
      ((.nil : BinaryTree α).height : ℝ) ≤
        ((d : ℝ) + 1) * Real.logb 2 (((.nil : BinaryTree α).numNodes : ℝ) + 1) :=
  ⟨two_pow_ceil_height_le_numLeaves d .nil (balancedD_nil d),
    height_le_mul_logb_numLeaves d .nil (balancedD_nil d),
    height_le_mul_logb_numNodes_add_one d .nil (balancedD_nil d)⟩

/-- B01: neither the payload nor annotation universe needs an inhabitant. -/
theorem empty_cached_bounds (ann : HeightAnnotation α σ) (d : Nat) :
    2 ^ ((ht ann .nil + d) / (d + 1)) ≤ (.nil : BinaryTree (α × σ)).numLeaves ∧
      (ht ann .nil : ℝ) ≤ ((d : ℝ) + 1) *
        Real.logb 2 ((.nil : BinaryTree (α × σ)).numLeaves : ℝ) ∧
      (ht ann .nil : ℝ) ≤ ((d : ℝ) + 1) *
        Real.logb 2 (((.nil : BinaryTree (α × σ)).numNodes : ℝ) + 1) :=
  ⟨two_pow_ceil_ht_le_numLeaves ann d .nil (validD_nil ann d),
    ht_le_mul_logb_numLeaves ann d .nil (validD_nil ann d),
    ht_le_mul_logb_numNodes_add_one ann d .nil (validD_nil ann d)⟩

theorem empty_carrier_bounds (ann : HeightAnnotation PEmpty σ) (d : Nat) :
    ((.nil : BinaryTree PEmpty).height : ℝ) ≤
        ((d : ℝ) + 1) * Real.logb 2 ((.nil : BinaryTree PEmpty).numLeaves : ℝ) ∧
      (ht ann .nil : ℝ) ≤ ((d : ℝ) + 1) *
        Real.logb 2 ((.nil : BinaryTree (PEmpty × σ)).numLeaves : ℝ) :=
  ⟨(empty_shape_bounds (α := PEmpty) d).2.1, (empty_cached_bounds ann d).2.1⟩

private def perfect : Nat → BinaryTree Unit
  | 0 => .nil
  | n + 1 => .node () (perfect n) (perfect n)

/-- B02: zero tolerance admits perfect shapes; no zero-tolerance update is asserted. -/
theorem perfect_three_balanced_zero : BalancedD 0 (perfect 3) := by
  simp [perfect, BalancedD, BinaryTree.height]

theorem perfect_three_measures :
    (perfect 3).height = 3 ∧ (perfect 3).numLeaves = 8 ∧ (perfect 3).numNodes = 7 := by
  decide

theorem perfect_three_power :
    2 ^ (((perfect 3).height + 0) / (0 + 1)) ≤ (perfect 3).numLeaves :=
  two_pow_ceil_height_le_numLeaves 0 (perfect 3) perfect_three_balanced_zero

theorem perfect_three_log :
    ((perfect 3).height : ℝ) ≤ ((0 : ℝ) + 1) * Real.logb 2 ((perfect 3).numLeaves : ℝ) := by
  simpa only [Nat.cast_zero] using
    height_le_mul_logb_numLeaves 0 (perfect 3) perfect_three_balanced_zero

private theorem logb_two_eight : Real.logb 2 (8 : ℝ) = 3 := by
  have eight : (8 : ℝ) = 2 ^ (3 : Nat) := by norm_num
  rw [eight, Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
  norm_num

/-- B02: the zero-tolerance example attains the logarithmic bound exactly. -/
theorem perfect_three_log_sharp :
    ((perfect 3).height : ℝ) = Real.logb 2 ((perfect 3).numLeaves : ℝ) := by
  change (3 : ℝ) = Real.logb 2 (8 : ℝ)
  exact logb_two_eight.symm

private def chain : Nat → BinaryTree Unit
  | 0 => .nil
  | n + 1 => .node () (chain n) .nil

private def ceilingBoundary : BinaryTree Unit := .node () (chain 3) (chain 1)
private def ceilingBoundaryMirror : BinaryTree Unit := .node () (chain 1) (chain 3)

/-- B03: this shape needs tolerance two; it is not an ordinary AVL shape. -/
theorem chain_three_balance : BalancedD 2 (chain 3) ∧ ¬ BalancedD 1 (chain 3) := by
  simp [chain, BalancedD, BinaryTree.height]

theorem chain_three_measures :
    (chain 3).height = 3 ∧ (chain 3).numLeaves = 4 ∧
      ((chain 3).height + 2) / (2 + 1) = 1 := by
  decide

theorem chain_three_power :
    2 ^ (((chain 3).height + 2) / (2 + 1)) ≤ (chain 3).numLeaves :=
  two_pow_ceil_height_le_numLeaves 2 (chain 3) chain_three_balance.1

/-- Both orientations satisfy the actual recursive balance predicate. -/
theorem ceiling_boundary_balance :
    BalancedD 2 ceilingBoundary ∧ BalancedD 2 ceilingBoundaryMirror := by
  simp [ceilingBoundary, ceilingBoundaryMirror, chain, BalancedD, BinaryTree.height]

theorem ceiling_boundary_measures :
    ceilingBoundary.height = 4 ∧ ceilingBoundary.numLeaves = 6 ∧
      (ceilingBoundary.height + 2) / (2 + 1) = 2 ∧
      ceilingBoundaryMirror.height = 4 ∧ ceilingBoundaryMirror.numLeaves = 6 := by
  decide

/-- Crossing the next height block exercises both the ceiling and strict-threshold APIs. -/
theorem ceiling_boundary_power :
    2 ^ ((ceilingBoundary.height + 2) / (2 + 1)) ≤ ceilingBoundary.numLeaves ∧
      2 ^ (1 + 1) ≤ ceilingBoundary.numLeaves ∧
      2 ^ ((ceilingBoundaryMirror.height + 2) / (2 + 1)) ≤
        ceilingBoundaryMirror.numLeaves :=
  ⟨two_pow_ceil_height_le_numLeaves 2 ceilingBoundary ceiling_boundary_balance.1,
    two_pow_succ_le_numLeaves_of_mul_lt_height 2 1 ceilingBoundary
      ceiling_boundary_balance.1 (by decide),
    two_pow_ceil_height_le_numLeaves 2 ceilingBoundaryMirror ceiling_boundary_balance.2⟩

/-- B04: exact ceiling exponents at zero, one block, and one level past that block. -/
theorem ceiling_block_arithmetic (d : Nat) :
    (0 + d) / (d + 1) = 0 ∧
      ((d + 1) + d) / (d + 1) = 1 ∧
      (((d + 1) + 1) + d) / (d + 1) = 2 := by
  refine ⟨?_, ?_, ?_⟩
  all_goals exact Nat.div_eq_of_lt_le (by omega) (by omega)

/-- This is an arithmetic counterexample to using a floor estimate, not a balanced tree. -/
theorem floor_power_log_gap :
    (2 : Nat) ^ (4 / 3) ≤ 2 ∧ ¬ ((4 : ℝ) ≤ 3 * Real.logb 2 (2 : ℝ)) := by
  constructor
  · decide
  · rw [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    norm_num

private def staleSingleton : BinaryTree (Unit × Nat) := .node ((), 99) .nil .nil

/-- B05: a malformed stored height leaves the actual erased shape balanced. -/
theorem stale_singleton_shape : BalancedD 1 (Cached.erase staleSingleton) := by
  simp [staleSingleton, Cached.erase_node, BalancedD, BinaryTree.height]

theorem stale_singleton_actual_bound :
    (staleSingleton.height : ℝ) ≤ ((1 : ℝ) + 1) *
      Real.logb 2 (staleSingleton.numLeaves : ℝ) := by
  simpa only [Cached.height_erase, Cached.numLeaves_erase, Nat.cast_one] using
    height_le_mul_logb_numLeaves 1 (Cached.erase staleSingleton) stale_singleton_shape

theorem stale_singleton_invalid : ¬ ValidD AVL.heightAnnotation 1 staleSingleton := by
  intro valid
  have height := ht_eq_height AVL.heightAnnotation 1 staleSingleton valid
  change (99 : Nat) = 1 at height
  omega

theorem stale_singleton_stored_bound_false :
    ¬ ((ht AVL.heightAnnotation staleSingleton : ℝ) ≤ ((1 : ℝ) + 1) *
      Real.logb 2 (staleSingleton.numLeaves : ℝ)) := by
  change ¬ ((99 : ℝ) ≤ ((1 : ℝ) + 1) * Real.logb 2 (2 : ℝ))
  rw [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
  norm_num

/-- The smart constructor supplies the entire annotation, for independent carriers. -/
theorem annotated_singleton_valid (ann : HeightAnnotation α σ) (d : Nat) (a : α) :
    ValidD ann d (node ann .nil a .nil) := by
  apply (node_validD_iff ann d .nil a .nil).mpr
  exact ⟨validD_nil ann d, validD_nil ann d, by simp [BinaryTree.height]⟩

theorem annotated_singleton_bounds (ann : HeightAnnotation α σ) (d : Nat) (a : α) :
    2 ^ ((ht ann (node ann .nil a .nil) + d) / (d + 1)) ≤
        (node ann .nil a .nil).numLeaves ∧
      (ht ann (node ann .nil a .nil) : ℝ) ≤ ((d : ℝ) + 1) *
        Real.logb 2 ((node ann .nil a .nil).numLeaves : ℝ) ∧
      ((node ann .nil a .nil).height : ℝ) ≤ ((d : ℝ) + 1) *
        Real.logb 2 (((node ann .nil a .nil).numNodes : ℝ) + 1) := by
  have valid := annotated_singleton_valid ann d a
  exact ⟨two_pow_ceil_ht_le_numLeaves ann d _ valid,
    ht_le_mul_logb_numLeaves ann d _ valid,
    height_le_mul_logb_numNodes_add_one_of_valid ann d _ valid⟩

/-- B06: balance must hold at the supplied tolerance, not just at some tolerance. -/
theorem chain_seven_balance : BalancedD 6 (chain 7) ∧ ¬ BalancedD 1 (chain 7) := by
  simp [chain, BalancedD, BinaryTree.height]

theorem chain_seven_measures : (chain 7).height = 7 ∧ (chain 7).numLeaves = 8 := by
  decide

theorem chain_seven_bound :
    ((chain 7).height : ℝ) ≤ ((6 : ℝ) + 1) * Real.logb 2 ((chain 7).numLeaves : ℝ) :=
  height_le_mul_logb_numLeaves 6 (chain 7) chain_seven_balance.1

theorem chain_seven_rejects_coefficient_two :
    ¬ (((chain 7).height : ℝ) ≤ 2 * Real.logb 2 ((chain 7).numLeaves : ℝ)) := by
  change ¬ ((7 : ℝ) ≤ 2 * Real.logb 2 (8 : ℝ))
  rw [logb_two_eight]
  norm_num

/-- B07: raw insertion needs comparison decisions but no order laws or strictness. -/
theorem insert_log_bounds [LT α] [DecidableLT α]
    (ann : HeightAnnotation α σ) (d : Nat) (x : α) (t : BinaryTree (α × σ))
    (hd : 1 ≤ d) (valid : ValidD ann d t) :
    ((Trees.HeightBalance.insert ann d x t).height : ℝ) ≤ ((d : ℝ) + 1) *
        Real.logb 2 ((Trees.HeightBalance.insert ann d x t).numLeaves : ℝ) ∧
      (ht ann (Trees.HeightBalance.insert ann d x t) : ℝ) ≤ ((d : ℝ) + 1) *
        Real.logb 2 ((Trees.HeightBalance.insert ann d x t).numLeaves : ℝ) := by
  have next := (validD_insert ann d x t hd valid).1
  exact ⟨height_le_mul_logb_numLeaves_of_valid ann d _ next,
    ht_le_mul_logb_numLeaves ann d _ next⟩

/-- The same full-cache consequence applies to the actual predecessor-deletion program. -/
theorem delete_log_bounds [LT α] [DecidableLT α]
    (ann : HeightAnnotation α σ) (d : Nat) (x : α) (t : BinaryTree (α × σ))
    (hd : 1 ≤ d) (valid : ValidD ann d t) :
    ((Trees.HeightBalance.delete ann d x t).height : ℝ) ≤ ((d : ℝ) + 1) *
        Real.logb 2 ((Trees.HeightBalance.delete ann d x t).numLeaves : ℝ) ∧
      (ht ann (Trees.HeightBalance.delete ann d x t) : ℝ) ≤ ((d : ℝ) + 1) *
        Real.logb 2 ((Trees.HeightBalance.delete ann d x t).numLeaves : ℝ) := by
  have next := (validD_delete ann d x t hd valid).1
  exact ⟨height_le_mul_logb_numLeaves_of_valid ann d _ next,
    ht_le_mul_logb_numLeaves ann d _ next⟩

/-- Every mixed word inherits a node-count bound through the existing Set laws. -/
theorem mixed_history_node_bound [LinearOrder α]
    (ann : HeightAnnotation α σ) (d : Nat) (hd : 1 ≤ d)
    (updates : List (Search.AbstractSet.Update α)) {t : BinaryTree (α × σ)}
    (valid : SetValid ann d t) :
    (ht ann (Search.AbstractSet.execute (deleteOps ann d) updates t) : ℝ) ≤
      ((d : ℝ) + 1) * Real.logb 2
        (((Search.AbstractSet.execute (deleteOps ann d) updates t).numNodes : ℝ) + 1) :=
  ht_le_mul_logb_numNodes_add_one ann d _
    ((set_laws ann d hd).execute_valid updates valid).1

/-- Prefix length is unrestricted, including lengths beyond the complete mixed word. -/
theorem mixed_prefix_log_bounds [LinearOrder α]
    (ann : HeightAnnotation α σ) (d : Nat) (hd : 1 ≤ d)
    (updates : List (Search.AbstractSet.Update α)) (n : Nat) {t : BinaryTree (α × σ)}
    (valid : SetValid ann d t) :
    ((Search.AbstractSet.execute (deleteOps ann d) (updates.take n) t).height : ℝ) ≤
        ((d : ℝ) + 1) * Real.logb 2
          ((Search.AbstractSet.execute (deleteOps ann d) (updates.take n) t).numLeaves : ℝ) ∧
      (ht ann (Search.AbstractSet.execute (deleteOps ann d) (updates.take n) t) : ℝ) ≤
        ((d : ℝ) + 1) * Real.logb 2
          ((Search.AbstractSet.execute (deleteOps ann d) (updates.take n) t).numLeaves : ℝ) := by
  have next := ((set_laws ann d hd).prefix_valid updates n valid).1
  exact ⟨height_le_mul_logb_numLeaves_of_valid ann d _ next,
    ht_le_mul_logb_numLeaves ann d _ next⟩

/-- The positive-integer representative is both positive and exactly the supplied integer. -/
theorem positive_integer_shape_bound (D : Int) (hD : 1 ≤ D) (t : BinaryTree α)
    (balanced : BalancedD D.toNat t) :
    1 ≤ D.toNat ∧ (D.toNat : Int) = D ∧
      (t.height : ℝ) ≤ ((D.toNat : ℝ) + 1) * Real.logb 2 (t.numLeaves : ℝ) := by
  have bridge := int_tolerance_toNat D hD
  exact ⟨bridge.1, bridge.2, height_le_mul_logb_numLeaves D.toNat t balanced⟩

/-- The bridge's positive part discharges the actual insertion's validity premise. -/
theorem positive_integer_insert_bound [LT α] [DecidableLT α]
    (ann : HeightAnnotation α σ) (D : Int) (hD : 1 ≤ D) (x : α)
    (t : BinaryTree (α × σ)) (valid : ValidD ann D.toNat t) :
    1 ≤ D.toNat ∧ (D.toNat : Int) = D ∧
      (ht ann (Trees.HeightBalance.insert ann D.toNat x t) : ℝ) ≤
        ((D.toNat : ℝ) + 1) *
          Real.logb 2 ((Trees.HeightBalance.insert ann D.toNat x t).numLeaves : ℝ) := by
  have bridge := int_tolerance_toNat D hD
  exact ⟨bridge.1, bridge.2, (insert_log_bounds ann D.toNat x t bridge.1 valid).2⟩

/-- B08: the generalized coefficient two and the sharper ordinary result both remain usable. -/
theorem ordinary_avl_bounds (t : BinaryTree (α × Nat)) (valid : AVL.Valid t) :
    (t.height : ℝ) ≤ 2 * Real.logb 2 (t.numLeaves : ℝ) ∧
      (t.height : ℝ) ≤ (1 / Real.logb 2 Real.goldenRatio) *
        Real.logb 2 (t.numLeaves : ℝ) ∧
      (1440 / 1000 : ℝ) < 1 / Real.logb 2 Real.goldenRatio ∧
      1 / Real.logb 2 Real.goldenRatio < (1441 / 1000 : ℝ) := by
  have generic := height_le_mul_logb_numLeaves_of_valid AVL.heightAnnotation 1 t
    ((AVL.validD_one_iff t).mpr valid)
  have coefficient : ((1 : Nat) : ℝ) + 1 = 2 := by norm_num
  rw [coefficient] at generic
  exact ⟨generic, AVL.height_le_logb_numLeaves_of_valid t valid,
    AVL.height_coefficient_bounds.1, AVL.height_coefficient_bounds.2⟩

theorem repeated_key_shape_balanced_one : BalancedD 1 (perfect 3) := by
  simp [perfect, BalancedD, BinaryTree.height]

/-- Seven repeated nodes represent just one distinct label in the inorder observation. -/
theorem repeated_key_distinct_size : (Trees.inorder (perfect 3)).toFinset.card = 1 := by
  decide

theorem repeated_key_node_bound :
    ((perfect 3).height : ℝ) ≤ ((1 : ℝ) + 1) *
      Real.logb 2 (((perfect 3).numNodes : ℝ) + 1) := by
  simpa only [Nat.cast_one] using
    height_le_mul_logb_numNodes_add_one 1 (perfect 3) repeated_key_shape_balanced_one

/-- Replacing node count by distinct-key size is false without an additional uniqueness bridge. -/
theorem distinct_size_cannot_replace_nodes :
    ¬ (((perfect 3).height : ℝ) ≤ 2 *
      Real.logb 2 (((Trees.inorder (perfect 3)).toFinset.card : ℝ) + 1)) := by
  rw [repeated_key_distinct_size, Nat.cast_one, perfect_three_measures.1]
  have two : (1 : ℝ) + 1 = 2 := by norm_num
  rw [two, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
  norm_num

end Examples.HeightBound

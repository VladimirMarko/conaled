import Applications.Resources.AVL.Logarithmic
import Applications.Trees.SetCardinality
import Examples.HeightUpdates
import Examples.MeasuredBalancedComplexity

/-!
# Actual cached membership and ordinary AVL work

The independent cases precede these adapters. Lookup returns the original
annotation and charges the one reached path; membership only observes that
Option. Ordinary updates reuse the existing d=1 programs and complete tariff.
Shape bounds, callback erasure, full validity and strict-set observations are
kept separate. All costs are declared source observations.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.MeasuredAVL
open Trees Search Resources
open Examples.HeightUpdates
  (heightNode heightSingleton perfectSeven three deletePredecessorOutput withoutSeven)
open Examples.HeightRebalance
  (leaf leftStrict leftTie rightStrict rightTie leftDouble rightDouble doubleResult perfect)
universe u v

abbrev unitLt := Resources.AVL.ltRun (α := Nat)

def annotatedTwo {σ : Type v} (summary : σ) : BinaryTree (Nat × σ) :=
  .node (2, summary) .nil .nil

/-! Exact lookup paths do not inspect or constrain the annotation. -/

theorem empty_lookup {α : Type u} {σ : Type v}
    (ltRun : α → α → Measured Bool Nat) (q : α) :
    Resources.HeightBalance.lookupRun (σ := σ) ltRun q .nil = (none, 1) ∧
      Resources.HeightBalance.memberRun (σ := σ) ltRun q .nil = (false, 1) :=
  ⟨Resources.HeightBalance.lookupRun_nil ltRun q,
    Resources.HeightBalance.memberRun_nil ltRun q⟩

theorem empty_annotation_carrier :
    Resources.HeightBalance.lookupRun unitLt 2
      (.nil : BinaryTree (Nat × ULift.{v} PEmpty)) = (none, 1) :=
  Resources.HeightBalance.lookupRun_nil unitLt 2

theorem singleton_lookup_paths {σ : Type v} (summary : σ) :
    Resources.HeightBalance.lookupRun unitLt 2 (annotatedTwo summary) = (some summary, 3) ∧
      Resources.HeightBalance.lookupRun unitLt 1 (annotatedTwo summary) = (none, 3) ∧
      Resources.HeightBalance.lookupRun unitLt 3 (annotatedTwo summary) = (none, 4) ∧
      Resources.HeightBalance.memberRun unitLt 2 (annotatedTwo summary) = (true, 3) ∧
      Resources.HeightBalance.memberRun unitLt 1 (annotatedTwo summary) = (false, 3) ∧
      Resources.HeightBalance.memberRun unitLt 3 (annotatedTwo summary) = (false, 4) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem false_comparisons_return_original_annotation {σ : Type v} (summary : σ) :
    Resources.HeightBalance.lookupRun (fun _ _ : Nat => (false, 1))
        9 (annotatedTwo summary) = (some summary, 3) ∧
      Resources.HeightBalance.memberRun (fun _ _ : Nat => (false, 1))
        9 (annotatedTwo summary) = (true, 3) ∧
      OrderedMap.lookup 9 (annotatedTwo summary) = none := ⟨rfl, rfl, rfl⟩

/-- The public recurrence exposes the selected child and skipped second comparison. -/
theorem lookup_selected_left {α : Type u} {σ : Type v}
    (ltRun : α → α → Measured Bool Nat) (q a : α) (summary : σ)
    (l r : BinaryTree (α × σ)) (first : (ltRun q a).1 = true) :
    Resources.HeightBalance.lookupRun ltRun q (.node (a, summary) l r) =
      ((Resources.HeightBalance.lookupRun ltRun q l).1,
        1 + (ltRun q a).2 + (Resources.HeightBalance.lookupRun ltRun q l).2) := by
  rw [Resources.HeightBalance.lookupRun_node]
  simp [first]

theorem lookup_selected_right {α : Type u} {σ : Type v}
    (ltRun : α → α → Measured Bool Nat) (q a : α) (summary : σ)
    (l r : BinaryTree (α × σ)) (first : (ltRun q a).1 = false)
    (second : (ltRun a q).1 = true) :
    Resources.HeightBalance.lookupRun ltRun q (.node (a, summary) l r) =
      ((Resources.HeightBalance.lookupRun ltRun q r).1,
        1 + (ltRun q a).2 + (ltRun a q).2 +
          (Resources.HeightBalance.lookupRun ltRun q r).2) := by
  rw [Resources.HeightBalance.lookupRun_node]
  simp [first, second]

def varyingLt (a b : Nat) : Measured Bool Nat :=
  (decide (a < b), if a < b then 2 else 5)

theorem varying_comparison_paths {σ : Type v} (summary : σ) :
    Resources.HeightBalance.lookupRun varyingLt 1 (annotatedTwo summary) = (none, 4) ∧
      Resources.HeightBalance.lookupRun varyingLt 3 (annotatedTwo summary) = (none, 9) ∧
      Resources.HeightBalance.lookupRun varyingLt 2 (annotatedTwo summary) = (some summary, 11) :=
  ⟨rfl, rfl, rfl⟩

theorem varying_comparison_bound (a b : Nat) : (varyingLt a b).2 ≤ 5 := by
  by_cases h : a < b <;> simp [varyingLt, h]

def summedLt (a b : Nat) : Measured Bool Nat := (decide (a < b), a + b)

/-- For query 1 and key 2 the sole comparison costs 3, plus one node and one final nil. -/
theorem input_local_cost_without_global_bound {σ : Type v} (summary : σ) :
    Resources.HeightBalance.lookupRun summedLt 1 (annotatedTwo summary) = (none, 5) ∧
      (Resources.HeightBalance.lookupRun summedLt 1 (annotatedTwo summary)).2 ≤ 8 ∧
      ¬ ∃ C, ∀ a b, (summedLt a b).2 ≤ C := by
  refine ⟨rfl, ?_, ?_⟩
  · exact Resources.HeightBalance.lookupRun_cost_le_of_local summedLt 1 _ 3
      (by simp [OrderedTree.All, annotatedTwo, summedLt])
  · rintro ⟨C, bound⟩
    have impossible := bound (C + 1) 0
    change C + 1 + 0 ≤ C at impossible
    omega

/-- Raw erasure needs only decidable LT and the two local callback orientations. -/
theorem local_raw_erasure {α : Type u} {σ : Type v} [LT α] [DecidableLT α]
    (ltRun : α → α → Measured Bool Nat) (q : α) (t : BinaryTree (α × σ))
    (values : OrderedTree.All (fun b =>
      (ltRun q b.1).1 = decide (q < b.1) ∧
      (ltRun b.1 q).1 = decide (b.1 < q)) t) :
    (Resources.HeightBalance.lookupRun ltRun q t).1 = OrderedMap.lookup q t :=
  Resources.HeightBalance.lookupRun_value ltRun q t values

theorem global_raw_erasure {α : Type u} {σ : Type v} [LT α] [DecidableLT α]
    (ltRun : α → α → Measured Bool Nat) (q : α) (t : BinaryTree (α × σ))
    (values : ∀ a b, (ltRun a b).1 = decide (a < b)) :
    (Resources.HeightBalance.lookupRun ltRun q t).1 = OrderedMap.lookup q t ∧
      (Resources.HeightBalance.memberRun ltRun q t).1 = OrderedMap.containsKey q t :=
  ⟨Resources.HeightBalance.lookupRun_value_of_global ltRun q t values,
    Resources.HeightBalance.memberRun_value ltRun q t values⟩

theorem local_membership_bound {α : Type u} {σ : Type v}
    (ltRun : α → α → Measured Bool Nat) (q : α) (t : BinaryTree (α × σ)) (C : Nat)
    (bound : OrderedTree.All (fun b =>
      (ltRun q b.1).2 ≤ C ∧ (ltRun b.1 q).2 ≤ C) t) :
    (Resources.HeightBalance.memberRun ltRun q t).2 ≤ (1 + 2 * C) * t.height + 1 :=
  Resources.HeightBalance.memberRun_cost_le_of_local ltRun q t C bound

theorem raw_lookup_and_member_bounds {α : Type u} {σ : Type v}
    (ltRun : α → α → Measured Bool Nat) (q : α) (t : BinaryTree (α × σ)) (C : Nat)
    (bound : ∀ a b, (ltRun a b).2 ≤ C) :
    (Resources.HeightBalance.lookupRun ltRun q t).2 ≤ (1 + 2 * C) * t.height + 1 ∧
      (Resources.HeightBalance.memberRun ltRun q t).2 ≤ (1 + 2 * C) * t.height + 1 :=
  ⟨Resources.HeightBalance.lookupRun_cost_le ltRun q t C bound,
    Resources.HeightBalance.memberRun_cost_le ltRun q t C bound⟩

theorem shape_logarithmic_lookup {α : Type u} {σ : Type v}
    (ltRun : α → α → Measured Bool Nat) (q : α) (t : BinaryTree (α × σ)) (d C : Nat)
    (bound : ∀ a b, (ltRun a b).2 ≤ C)
    (balanced : Trees.HeightBalance.BalancedD d (Cached.erase t)) :
    (Resources.HeightBalance.lookupRun ltRun q t).2 ≤
        (1 + 2 * C) * (d + 1) * Nat.clog 2 (t.numNodes + 1) + 1 ∧
      (Resources.HeightBalance.memberRun ltRun q t).2 ≤
        (1 + 2 * C) * (d + 1) * Nat.clog 2 (t.numNodes + 1) + 1 :=
  ⟨Resources.HeightBalance.lookupRun_cost_le_clog ltRun q t d C bound balanced,
    Resources.HeightBalance.memberRun_cost_le_clog ltRun q t d C bound balanced⟩

theorem lookup_and_membership_families {α : Type u} {σ : Type v}
    (ltRun : α → α → Measured Bool Nat) (d : Nat)
    (queries : Nat → α) (family : Nat → BinaryTree (α × σ)) (C : Nat)
    (bound : ∀ a b, (ltRun a b).2 ≤ C) (sizes : ∀ n, (family n).numNodes = n)
    (balanced : ∀ n, Trees.HeightBalance.BalancedD d (Cached.erase (family n))) :
    Asymptotics.IsBigO Filter.atTop
        (fun n => ((Resources.HeightBalance.lookupRun ltRun (queries n) (family n)).2 : ℝ))
        (fun n => Real.logb 2 (n + 1 : Nat)) ∧
      Asymptotics.IsBigO Filter.atTop
        (fun n => ((Resources.HeightBalance.memberRun ltRun (queries n) (family n)).2 : ℝ))
        (fun n => Real.logb 2 (n + 1 : Nat)) :=
  ⟨Resources.HeightBalance.lookupRun_isBigO ltRun d queries family C bound sizes balanced,
    Resources.HeightBalance.memberRun_isBigO ltRun d queries family C bound sizes balanced⟩

theorem generic_membership_correct_without_cache {α : Type u} {σ : Type v}
    [LinearOrder α] (ltRun : α → α → Measured Bool Nat) (q : α)
    (t : BinaryTree (α × σ)) (values : ∀ a b, (ltRun a b).1 = decide (a < b))
    (strict : (inorder (Cached.erase t)).Pairwise (· < ·)) :
    (Resources.HeightBalance.memberRun ltRun q t).1 = true ↔ q ∈ setTree (Cached.erase t) :=
  Resources.HeightBalance.memberRun_correct ltRun q t values strict

/-! Ordinary exact costs reuse the previously fixed pure cached trees. -/

theorem ordinary_reader_and_constructor :
    Resources.AVL.htRun (annotatedTwo 99) = (99, 1) ∧
      Resources.AVL.nodeRun .nil 2 .nil = (heightSingleton 2, 5) ∧
      Resources.AVL.combineRun 2 7 4 = (5, 2) := ⟨rfl, rfl, rfl⟩

/-- Tolerance one preserves the two actual additions in both trigger outcomes. -/
theorem ordinary_outer_trigger_tariff :
    Resources.HeightBalance.excessRun 0 Resources.AVL.heightRun 1 leftStrict .nil =
        (true, 5) ∧
      Resources.HeightBalance.excessRun 0 Resources.AVL.heightRun 1 (leaf 2) .nil =
        (false, 5) := ⟨rfl, rfl⟩

theorem ordinary_empty_repairs :
    Resources.AVL.balLRun (.nil : BinaryTree (Nat × Nat)) 2 .nil = (leaf 2, 11) ∧
      Resources.AVL.balRRun (.nil : BinaryTree (Nat × Nat)) 2 .nil = (leaf 2, 11) :=
  ⟨Resources.AVL.balLRun_of_ne .nil 2 .nil (by decide),
    Resources.AVL.balRRun_of_ne .nil 2 .nil (by decide)⟩

theorem ordinary_single_repairs :
    Resources.AVL.balLRun leftStrict 3 .nil = (three, 19) ∧
      Resources.AVL.balRRun .nil 1 rightStrict = (three, 19) :=
  ⟨Resources.AVL.balLRun_single (leaf 1) 2 2 .nil 3 .nil (by decide) (by decide),
    Resources.AVL.balRRun_single .nil 1 .nil 2 2 (leaf 3) (by decide) (by decide)⟩

theorem ordinary_double_repairs :
    Resources.AVL.balLRun (leftDouble (leaf 3) .nil) 6 (leaf 7) =
        (doubleResult (leaf 3) .nil, 24) ∧
      Resources.AVL.balRRun (leaf 1) 2 (rightDouble .nil (leaf 5)) =
        (doubleResult .nil (leaf 5), 24) :=
  ⟨Resources.AVL.balLRun_double (leaf 1) 2 3 (leaf 3) 4 2 .nil 6 (leaf 7)
      (by decide) (by decide),
    Resources.AVL.balRRun_double (leaf 1) 2 .nil 4 2 (leaf 5) 6 3 (leaf 7)
      (by decide) (by decide)⟩

/-- Equal inner heights select the public single-rotation law on both sides. -/
theorem ordinary_deletion_tie_repairs :
    Resources.AVL.balLRun leftTie 4 .nil =
        (Trees.AVL.node (leaf 1) 2 (Trees.AVL.node (leaf 3) 4 .nil), 19) ∧
      Resources.AVL.balRRun .nil 1 rightTie =
        (Trees.AVL.node (Trees.AVL.node .nil 1 (leaf 2)) 3 (leaf 4), 19) :=
  ⟨Resources.AVL.balLRun_single (leaf 1) 2 2 (leaf 3) 4 .nil (by decide) (by decide),
    Resources.AVL.balRRun_single .nil 1 (leaf 2) 3 2 (leaf 4) (by decide) (by decide)⟩

theorem ordinary_base_operations :
    Resources.AVL.insertRun 2 .nil = (heightSingleton 2, 6) ∧
      Resources.AVL.splitMaxRun (.nil : BinaryTree (Nat × Nat)) = (none, 1) ∧
      Resources.AVL.deleteRun 2 .nil = (.nil, 1) ∧
      Resources.AVL.splitMaxRun (heightSingleton 2) = (some (.nil, 2), 1) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem ordinary_singleton_update_paths :
    Resources.AVL.insertRun 2 (heightSingleton 2) = (heightSingleton 2, 4) ∧
      Resources.AVL.insertRun 1 (heightSingleton 2) =
        (heightNode 2 (heightSingleton 1) .nil, 19) ∧
      Resources.AVL.insertRun 3 (heightSingleton 2) =
        (heightNode 2 .nil (heightSingleton 3), 20) ∧
      Resources.AVL.deleteRun 1 (heightSingleton 2) = (heightSingleton 2, 14) ∧
      Resources.AVL.deleteRun 3 (heightSingleton 2) = (heightSingleton 2, 15) ∧
      Resources.AVL.deleteRun 2 (heightSingleton 2) = (.nil, 4) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ordinary_insertion_rotations :
    Resources.AVL.insertRun 3 (heightNode 1 .nil (heightSingleton 2)) = (three, 42) ∧
      Resources.AVL.insertRun 1 (heightNode 3 (heightSingleton 2) .nil) = (three, 40) ∧
      Resources.AVL.insertRun 2 (heightNode 3 (heightSingleton 1) .nil) = (three, 46) ∧
      Resources.AVL.insertRun 2 (heightNode 1 .nil (heightSingleton 3)) = (three, 46) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Two right-path repairs cost 11 each, three extraction entries cost 3; no final nil. -/
theorem ordinary_predecessor_and_extraction :
    Resources.AVL.splitMaxRun perfectSeven = (some (withoutSeven, 7), 25) ∧
      Resources.AVL.deleteRun 4 perfectSeven = (deletePredecessorOutput, 27) := ⟨rfl, rfl⟩

/-! Raw exact transport and work consumers do not assume a valid cache. -/

theorem ordinary_is_exact_generic_one {α : Type u} [LT α] [DecidableLT α]
    (x : α) (t : BinaryTree (α × Nat)) :
    Resources.AVL.lookupRun x t =
        Resources.HeightBalance.lookupRun Resources.AVL.ltRun x t ∧
      Resources.AVL.memberRun x t =
        Resources.HeightBalance.memberRun Resources.AVL.ltRun x t ∧
      Resources.AVL.insertRun x t = Resources.HeightBalance.insertRun
        0 Resources.AVL.heightRun Resources.AVL.combineRun Resources.AVL.ltRun 1 x t ∧
      Resources.AVL.splitMaxRun t = Resources.HeightBalance.splitMaxRun
        0 Resources.AVL.heightRun Resources.AVL.combineRun 1 t ∧
      Resources.AVL.deleteRun x t = Resources.HeightBalance.deleteRun
        0 Resources.AVL.heightRun Resources.AVL.combineRun Resources.AVL.ltRun 1 x t :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem ordinary_raw_erasure {α : Type u} [LT α] [DecidableLT α]
    (x : α) (t : BinaryTree (α × Nat)) :
    (Resources.AVL.lookupRun x t).1 = OrderedMap.lookup x t ∧
      (Resources.AVL.memberRun x t).1 = OrderedMap.containsKey x t ∧
      (Resources.AVL.insertRun x t).1 = Trees.AVL.insert x t ∧
      (Resources.AVL.splitMaxRun t).1 = Trees.AVL.splitMaxOption t ∧
      (Resources.AVL.deleteRun x t).1 = Trees.AVL.delete x t :=
  ⟨Resources.AVL.lookupRun_value x t, Resources.AVL.memberRun_value x t,
    Resources.AVL.insertRun_value x t, Resources.AVL.splitMaxRun_value t,
    Resources.AVL.deleteRun_value x t⟩

theorem ordinary_structural_work {α : Type u} [LT α] [DecidableLT α]
    (x : α) (t : BinaryTree (α × Nat)) :
    (Resources.AVL.memberRun x t).2 ≤ 3 * t.height + 1 ∧
      (Resources.AVL.insertRun x t).2 ≤ 27 * t.height + 6 ∧
      (Resources.AVL.splitMaxRun t).2 ≤ 25 * t.height + 1 ∧
      (Resources.AVL.deleteRun x t).2 ≤ 27 * t.height + 1 :=
  ⟨Resources.AVL.memberRun_cost_le x t, Resources.AVL.insertRun_cost_le x t,
    Resources.AVL.splitMaxRun_cost_le t, Resources.AVL.deleteRun_cost_le x t⟩

theorem ordinary_shape_logarithmic_work {α : Type u} [LT α] [DecidableLT α]
    (x : α) (t : BinaryTree (α × Nat)) (balanced : Trees.AVL.Balanced (Cached.erase t)) :
    (Resources.AVL.memberRun x t).2 ≤ 6 * Nat.clog 2 (t.numNodes + 1) + 1 ∧
      (Resources.AVL.insertRun x t).2 ≤ 54 * Nat.clog 2 (t.numNodes + 1) + 6 ∧
      (Resources.AVL.splitMaxRun t).2 ≤ 50 * Nat.clog 2 (t.numNodes + 1) + 1 ∧
      (Resources.AVL.deleteRun x t).2 ≤ 54 * Nat.clog 2 (t.numNodes + 1) + 1 :=
  ⟨Resources.AVL.memberRun_cost_le_clog x t balanced,
    Resources.AVL.insertRun_cost_le_clog x t balanced,
    Resources.AVL.splitMaxRun_cost_le_clog t balanced,
    Resources.AVL.deleteRun_cost_le_clog x t balanced⟩

theorem nonempty_extraction_omits_terminal {α : Type u}
    (t : BinaryTree (α × Nat)) (balanced : Trees.AVL.Balanced (Cached.erase t))
    (nonempty : t ≠ .nil) :
    (Resources.AVL.splitMaxRun t).2 ≤ 25 * t.height ∧
      (Resources.AVL.splitMaxRun t).2 ≤ 50 * Nat.clog 2 (t.numNodes + 1) :=
  ⟨Resources.AVL.splitMaxRun_cost_le_of_ne_nil t nonempty,
    Resources.AVL.splitMaxRun_cost_le_clog_of_ne_nil t balanced nonempty⟩

theorem malformed_height_still_has_shape_cost (x : Nat) :
    ¬ Trees.AVL.CacheValid (annotatedTwo 99) ∧
      Trees.AVL.Balanced (Cached.erase (annotatedTwo 99)) ∧
      (Resources.AVL.insertRun x (annotatedTwo 99)).2 ≤
        54 * Nat.clog 2 ((annotatedTwo 99).numNodes + 1) + 6 ∧
      ((Resources.AVL.memberRun x (annotatedTwo 99)).1 = true ↔
        x ∈ setTree (Cached.erase (annotatedTwo 99))) := by
  have balanced : Trees.AVL.Balanced (Cached.erase (annotatedTwo 99)) := by
    simp [annotatedTwo, Trees.AVL.Balanced, BinaryTree.height]
  refine ⟨?_, balanced, Resources.AVL.insertRun_cost_le_clog x _ balanced, ?_⟩
  · intro valid
    have impossible := Trees.AVL.ht_eq_height_of_cacheValid _ valid
    change 99 = 1 at impossible
    omega
  · exact Resources.AVL.memberRun_correct x _ (by
      change ([2] : List Nat).Pairwise (· < ·)
      decide)

theorem ordinary_families {α : Type u} [LT α] [DecidableLT α]
    (keys : Nat → α) (family : Nat → BinaryTree (α × Nat))
    (sizes : ∀ n, (family n).numNodes = n)
    (balanced : ∀ n, Trees.AVL.Balanced (Cached.erase (family n))) :
    Asymptotics.IsBigO Filter.atTop
        (fun n => ((Resources.AVL.memberRun (keys n) (family n)).2 : ℝ))
        (fun n => Real.logb 2 (n + 1 : Nat)) ∧
      Asymptotics.IsBigO Filter.atTop
        (fun n => ((Resources.AVL.insertRun (keys n) (family n)).2 : ℝ))
        (fun n => Real.logb 2 (n + 1 : Nat)) ∧
      Asymptotics.IsBigO Filter.atTop
        (fun n => ((Resources.AVL.splitMaxRun (family n)).2 : ℝ))
        (fun n => Real.logb 2 (n + 1 : Nat)) ∧
      Asymptotics.IsBigO Filter.atTop
        (fun n => ((Resources.AVL.deleteRun (keys n) (family n)).2 : ℝ))
        (fun n => Real.logb 2 (n + 1 : Nat)) :=
  ⟨Resources.AVL.memberRun_isBigO keys family sizes balanced,
    Resources.AVL.insertRun_isBigO keys family sizes balanced,
    Resources.AVL.splitMaxRun_isBigO family sizes balanced,
    Resources.AVL.deleteRun_isBigO keys family sizes balanced⟩

/-! The original exact golden-ratio height coefficient is a separate public bridge. -/

theorem ordinary_exact_golden_ratio_work {α : Type u} [LT α] [DecidableLT α]
    (x : α) (t : BinaryTree (α × Nat)) (valid : Trees.AVL.Valid t) :
    ((Resources.AVL.memberRun x t).2 : ℝ) ≤
        (3 * (1 / Real.logb 2 Real.goldenRatio)) * Real.logb 2 ((t.numNodes : ℝ) + 1) + 1 ∧
      ((Resources.AVL.insertRun x t).2 : ℝ) ≤
        (27 * (1 / Real.logb 2 Real.goldenRatio)) * Real.logb 2 ((t.numNodes : ℝ) + 1) + 6 ∧
      ((Resources.AVL.splitMaxRun t).2 : ℝ) ≤
        (25 * (1 / Real.logb 2 Real.goldenRatio)) * Real.logb 2 ((t.numNodes : ℝ) + 1) + 1 ∧
      ((Resources.AVL.deleteRun x t).2 : ℝ) ≤
        (27 * (1 / Real.logb 2 Real.goldenRatio)) * Real.logb 2 ((t.numNodes : ℝ) + 1) + 1 :=
  ⟨Resources.AVL.memberRun_cost_le_logb x t valid,
    Resources.AVL.insertRun_cost_le_logb x t valid,
    Resources.AVL.splitMaxRun_cost_le_logb t valid,
    Resources.AVL.deleteRun_cost_le_logb x t valid⟩

theorem rounded_coefficient_is_not_an_upper_bound :
    ¬ 1 / Real.logb 2 Real.goldenRatio ≤ (1440 / 1000 : ℝ) :=
  not_le.mpr Trees.AVL.height_coefficient_bounds.1

/-! Actual returned trees inherit the existing simultaneous invariant/height laws. -/

theorem ordinary_actual_update_validity {α : Type u} [LT α] [DecidableLT α]
    (x : α) (t : BinaryTree (α × Nat)) (valid : Trees.AVL.Valid t) :
    (Trees.AVL.Valid (Resources.AVL.insertRun x t).1 ∧
      ((Resources.AVL.insertRun x t).1.height = t.height ∨
        (Resources.AVL.insertRun x t).1.height = t.height + 1)) ∧
      (Trees.AVL.Valid (Resources.AVL.deleteRun x t).1 ∧
        (t.height = (Resources.AVL.deleteRun x t).1.height ∨
          t.height = (Resources.AVL.deleteRun x t).1.height + 1)) :=
  ⟨Resources.AVL.insertRun_valid x t valid, Resources.AVL.deleteRun_valid x t valid⟩

theorem ordinary_actual_extraction_validity {α : Type u}
    (t out : BinaryTree (α × Nat)) (m : α)
    (returned : (Resources.AVL.splitMaxRun t).1 = some (out, m))
    (valid : Trees.AVL.Valid t) :
    Trees.AVL.Valid out ∧ (t.height = out.height ∨ t.height = out.height + 1) :=
  Resources.AVL.splitMaxRun_valid t out m returned valid

theorem three_valid : Trees.AVL.Valid three :=
  Examples.HeightUpdates.insert_left_single.2.1

theorem three_strict : OrderedList.Strict (inorder (Cached.erase three)) := by
  change ([1, 2, 3] : List Nat).Pairwise (· < ·)
  decide

theorem three_set_valid : Trees.AVL.SetValid three := ⟨three_valid, three_strict⟩

theorem nonempty_actual_set_updates (x y : Nat) :
    Trees.AVL.SetValid (Resources.AVL.insertRun x three).1 ∧
      Trees.AVL.SetValid (Resources.AVL.deleteRun x three).1 ∧
      (y ∈ setTree (Cached.erase (Resources.AVL.insertRun x three).1) ↔
        y = x ∨ y ∈ setTree (Cached.erase three)) ∧
      (y ∈ setTree (Cached.erase (Resources.AVL.deleteRun x three).1) ↔
        y ≠ x ∧ y ∈ setTree (Cached.erase three)) :=
  ⟨Resources.AVL.insertRun_setValid x three three_set_valid,
    Resources.AVL.deleteRun_setValid x three three_set_valid,
    Resources.AVL.insertRun_mem x three three_set_valid y,
    Resources.AVL.deleteRun_mem x three three_set_valid y⟩

theorem empty_set_insert_valid {α : Type u} [LinearOrder α] (x : α) :
    Trees.AVL.SetValid (Resources.AVL.insertRun x .nil).1 :=
  Resources.AVL.insertRun_setValid x .nil Trees.AVL.setValid_nil

/-! Distinct observation cardinality requires occurrence injectivity. -/

theorem arbitrary_labels_cardinality {α : Type u} (t : BinaryTree α)
    (distinct : (inorder t).Nodup) : (setTree t).ncard = t.numNodes :=
  Trees.setTree_ncard_eq_numNodes t distinct

theorem three_observation_cardinality : (setTree (Cached.erase three)).ncard = 3 :=
  Resources.AVL.observe_ncard_eq_numNodes three three_strict

theorem strict_set_size_work {α : Type u} [LinearOrder α]
    (x : α) (t : BinaryTree (α × Nat))
    (balanced : Trees.AVL.Balanced (Cached.erase t))
    (strict : OrderedList.Strict (inorder (Cached.erase t))) :
    (setTree (Cached.erase t)).ncard = t.numNodes ∧
      (Resources.AVL.memberRun x t).2 ≤
        6 * Nat.clog 2 ((setTree (Cached.erase t)).ncard + 1) + 1 ∧
      (Resources.AVL.insertRun x t).2 ≤
        54 * Nat.clog 2 ((setTree (Cached.erase t)).ncard + 1) + 6 ∧
      (Resources.AVL.splitMaxRun t).2 ≤
        50 * Nat.clog 2 ((setTree (Cached.erase t)).ncard + 1) + 1 ∧
      (Resources.AVL.deleteRun x t).2 ≤
        54 * Nat.clog 2 ((setTree (Cached.erase t)).ncard + 1) + 1 :=
  ⟨Resources.AVL.observe_ncard_eq_numNodes t strict,
    Resources.AVL.memberRun_cost_le_clog_set x t balanced strict,
    Resources.AVL.insertRun_cost_le_clog_set x t balanced strict,
    Resources.AVL.splitMaxRun_cost_le_clog_set t balanced strict,
    Resources.AVL.deleteRun_cost_le_clog_set x t balanced strict⟩

theorem strict_exact_golden_ratio_set_work {α : Type u} [LinearOrder α]
    (x : α) (t : BinaryTree (α × Nat)) (valid : Trees.AVL.Valid t)
    (strict : OrderedList.Strict (inorder (Cached.erase t))) :
    ((Resources.AVL.insertRun x t).2 : ℝ) ≤
      (27 * (1 / Real.logb 2 Real.goldenRatio)) *
        Real.logb 2 (((setTree (Cached.erase t)).ncard : ℝ) + 1) + 6 :=
  Resources.AVL.insertRun_cost_le_logb_set x t valid strict

theorem repeated_keys_separate_nodes_from_set_size :
    Trees.AVL.Valid (perfect 3) ∧ (perfect 3).height = 3 ∧
      (perfect 3).numNodes = 7 ∧ (setTree (Cached.erase (perfect 3))).ncard = 1 ∧
      ¬ OrderedList.Strict (inorder (Cached.erase (perfect 3))) := by
  have observation : setTree (Cached.erase (perfect 3)) = ({0} : Set Nat) := by
    ext x
    simp [perfect]
  refine ⟨(Trees.AVL.validD_one_iff _).mp (Examples.HeightRebalance.perfect_valid 1 3),
    Examples.HeightRebalance.height_perfect 3, rfl, ?_, ?_⟩
  · rw [observation]
    exact Set.ncard_singleton 0
  · change ¬ ([0, 0, 0, 0, 0, 0, 0] : List Nat).Pairwise (· < ·)
    decide

theorem original_comparison_only_observation_is_distinct :
    OrderedTree.memberRun 2 (Cached.erase (annotatedTwo 99)) = (true, 2) ∧
      Resources.AVL.memberRun 2 (annotatedTwo 99) = (true, 3) := ⟨rfl, rfl⟩

end Examples.MeasuredAVL

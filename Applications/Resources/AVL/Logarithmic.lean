import Applications.Resources.AVL
import Applications.Resources.HeightBalance.Logarithmic
import Applications.Trees.AVL.Height
import Applications.Trees.SetCardinality

/-!
# Ordinary AVL operation work in terms of size

The integer and family bounds need actual shape balance, not correct cached
heights or search ordering. The explicit golden-ratio bounds reuse the original
valid-state AVL height theorem. Strict search ordering separately identifies
the distinct observed set cardinality with structural node count. All bounds
refer to the actual measured source programs and their declared arithmetic
tariff, including the two additions in each reached outer repair test.
Correspondence: `docs/research/fdsa-avl-continuation.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.AVL
universe u
variable {α : Type u}

theorem lookupRun_cost_le_clog [LT α] [DecidableLT α] (x : α)
    (t : BinaryTree (α × Nat)) (balanced : Trees.AVL.Balanced (Trees.Cached.erase t)) :
    (lookupRun x t).2 ≤ 6 * Nat.clog 2 (t.numNodes + 1) + 1 := by
  simpa only [lookupRun] using
    HeightBalance.lookupRun_cost_le_clog ltRun x t 1 1 (fun _ _ => Nat.le_refl _)
      ((Trees.AVL.balancedD_one_iff _).2 balanced)

theorem memberRun_cost_le_clog [LT α] [DecidableLT α] (x : α)
    (t : BinaryTree (α × Nat)) (balanced : Trees.AVL.Balanced (Trees.Cached.erase t)) :
    (memberRun x t).2 ≤ 6 * Nat.clog 2 (t.numNodes + 1) + 1 := by
  simpa only [memberRun] using
    HeightBalance.memberRun_cost_le_clog ltRun x t 1 1 (fun _ _ => Nat.le_refl _)
      ((Trees.AVL.balancedD_one_iff _).2 balanced)

theorem insertRun_cost_le_clog [LT α] [DecidableLT α] (x : α)
    (t : BinaryTree (α × Nat)) (balanced : Trees.AVL.Balanced (Trees.Cached.erase t)) :
    (insertRun x t).2 ≤ 54 * Nat.clog 2 (t.numNodes + 1) + 6 := by
  simpa only [insertRun, Nat.add_assoc] using
    HeightBalance.insertRun_cost_le_clog 0 heightRun combineRun ltRun 1 x t 0 2 1
      (fun _ => Nat.le_refl _) (fun _ _ _ => Nat.le_refl _) (fun _ _ => Nat.le_refl _)
      ((Trees.AVL.balancedD_one_iff _).2 balanced)

theorem splitMaxRun_cost_le_clog (t : BinaryTree (α × Nat))
    (balanced : Trees.AVL.Balanced (Trees.Cached.erase t)) :
    (splitMaxRun t).2 ≤ 50 * Nat.clog 2 (t.numNodes + 1) + 1 := by
  simpa only [splitMaxRun] using
    HeightBalance.splitMaxRun_cost_le_clog 0 heightRun combineRun 1 t 0 2
      (fun _ => Nat.le_refl _) (fun _ _ _ => Nat.le_refl _)
      ((Trees.AVL.balancedD_one_iff _).2 balanced)

theorem splitMaxRun_cost_le_clog_of_ne_nil (t : BinaryTree (α × Nat))
    (balanced : Trees.AVL.Balanced (Trees.Cached.erase t)) (hne : t ≠ .nil) :
    (splitMaxRun t).2 ≤ 50 * Nat.clog 2 (t.numNodes + 1) := by
  simpa only [splitMaxRun] using
    HeightBalance.splitMaxRun_cost_le_clog_of_ne_nil 0 heightRun combineRun 1 t 0 2
      (fun _ => Nat.le_refl _) (fun _ _ _ => Nat.le_refl _)
      ((Trees.AVL.balancedD_one_iff _).2 balanced) hne

theorem deleteRun_cost_le_clog [LT α] [DecidableLT α] (x : α)
    (t : BinaryTree (α × Nat)) (balanced : Trees.AVL.Balanced (Trees.Cached.erase t)) :
    (deleteRun x t).2 ≤ 54 * Nat.clog 2 (t.numNodes + 1) + 1 := by
  simpa only [deleteRun] using
    HeightBalance.deleteRun_cost_le_clog 0 heightRun combineRun ltRun 1 x t 0 2 1
      (fun _ => Nat.le_refl _) (fun _ _ _ => Nat.le_refl _) (fun _ _ => Nat.le_refl _)
      ((Trees.AVL.balancedD_one_iff _).2 balanced)

theorem lookupRun_isBigO [LT α] [DecidableLT α] (keys : Nat → α)
    (family : Nat → BinaryTree (α × Nat)) (sizes : ∀ n, (family n).numNodes = n)
    (balanced : ∀ n, Trees.AVL.Balanced (Trees.Cached.erase (family n))) :
    Asymptotics.IsBigO Filter.atTop
      (fun n => ((lookupRun (keys n) (family n)).2 : ℝ))
      (fun n => Real.logb 2 (n + 1 : Nat)) :=
  HeightBalance.lookupRun_isBigO ltRun 1 keys family 1 (fun _ _ => Nat.le_refl _) sizes
    (fun n => (Trees.AVL.balancedD_one_iff _).2 (balanced n))

theorem memberRun_isBigO [LT α] [DecidableLT α] (keys : Nat → α)
    (family : Nat → BinaryTree (α × Nat)) (sizes : ∀ n, (family n).numNodes = n)
    (balanced : ∀ n, Trees.AVL.Balanced (Trees.Cached.erase (family n))) :
    Asymptotics.IsBigO Filter.atTop
      (fun n => ((memberRun (keys n) (family n)).2 : ℝ))
      (fun n => Real.logb 2 (n + 1 : Nat)) :=
  HeightBalance.memberRun_isBigO ltRun 1 keys family 1 (fun _ _ => Nat.le_refl _) sizes
    (fun n => (Trees.AVL.balancedD_one_iff _).2 (balanced n))

theorem insertRun_isBigO [LT α] [DecidableLT α] (keys : Nat → α)
    (family : Nat → BinaryTree (α × Nat)) (sizes : ∀ n, (family n).numNodes = n)
    (balanced : ∀ n, Trees.AVL.Balanced (Trees.Cached.erase (family n))) :
    Asymptotics.IsBigO Filter.atTop
      (fun n => ((insertRun (keys n) (family n)).2 : ℝ))
      (fun n => Real.logb 2 (n + 1 : Nat)) :=
  HeightBalance.insertRun_isBigO 0 heightRun combineRun ltRun 1 keys family 0 2 1
    (fun _ => Nat.le_refl _) (fun _ _ _ => Nat.le_refl _) (fun _ _ => Nat.le_refl _)
    sizes (fun n => (Trees.AVL.balancedD_one_iff _).2 (balanced n))

theorem splitMaxRun_isBigO (family : Nat → BinaryTree (α × Nat))
    (sizes : ∀ n, (family n).numNodes = n)
    (balanced : ∀ n, Trees.AVL.Balanced (Trees.Cached.erase (family n))) :
    Asymptotics.IsBigO Filter.atTop
      (fun n => ((splitMaxRun (family n)).2 : ℝ))
      (fun n => Real.logb 2 (n + 1 : Nat)) :=
  HeightBalance.splitMaxRun_isBigO 0 heightRun combineRun 1 family 0 2
    (fun _ => Nat.le_refl _) (fun _ _ _ => Nat.le_refl _)
    sizes (fun n => (Trees.AVL.balancedD_one_iff _).2 (balanced n))

theorem deleteRun_isBigO [LT α] [DecidableLT α] (keys : Nat → α)
    (family : Nat → BinaryTree (α × Nat)) (sizes : ∀ n, (family n).numNodes = n)
    (balanced : ∀ n, Trees.AVL.Balanced (Trees.Cached.erase (family n))) :
    Asymptotics.IsBigO Filter.atTop
      (fun n => ((deleteRun (keys n) (family n)).2 : ℝ))
      (fun n => Real.logb 2 (n + 1 : Nat)) :=
  HeightBalance.deleteRun_isBigO 0 heightRun combineRun ltRun 1 keys family 0 2 1
    (fun _ => Nat.le_refl _) (fun _ _ _ => Nat.le_refl _) (fun _ _ => Nat.le_refl _)
    sizes (fun n => (Trees.AVL.balancedD_one_iff _).2 (balanced n))

/-- Reuse the exact original AVL coefficient, without decimal rounding. -/
private theorem work_le_logb (t : BinaryTree (α × Nat)) (valid : Trees.AVL.Valid t)
    (work A B : Nat) (bound : work ≤ A * t.height + B) :
    (work : ℝ) ≤ ((A : ℝ) * (1 / Real.logb 2 Real.goldenRatio)) *
      Real.logb 2 ((t.numNodes : ℝ) + 1) + (B : ℝ) := by
  have real_bound : (work : ℝ) ≤ (A : ℝ) * (t.height : ℝ) + (B : ℝ) := by
    exact_mod_cast bound
  have height := Trees.AVL.height_le_logb_numNodes_add_one_of_valid t valid
  calc
    (work : ℝ) ≤ (A : ℝ) * (t.height : ℝ) + (B : ℝ) := real_bound
    _ ≤ (A : ℝ) * ((1 / Real.logb 2 Real.goldenRatio) *
        Real.logb 2 ((t.numNodes : ℝ) + 1)) + (B : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left height (Nat.cast_nonneg A)) (le_refl (B : ℝ))
    _ = _ := by ring

theorem lookupRun_cost_le_logb [LT α] [DecidableLT α] (x : α)
    (t : BinaryTree (α × Nat)) (valid : Trees.AVL.Valid t) :
    ((lookupRun x t).2 : ℝ) ≤ (3 * (1 / Real.logb 2 Real.goldenRatio)) *
      Real.logb 2 ((t.numNodes : ℝ) + 1) + 1 := by
  simpa using work_le_logb t valid _ 3 1 (lookupRun_cost_le x t)

theorem memberRun_cost_le_logb [LT α] [DecidableLT α] (x : α)
    (t : BinaryTree (α × Nat)) (valid : Trees.AVL.Valid t) :
    ((memberRun x t).2 : ℝ) ≤ (3 * (1 / Real.logb 2 Real.goldenRatio)) *
      Real.logb 2 ((t.numNodes : ℝ) + 1) + 1 := by
  simpa using work_le_logb t valid _ 3 1 (memberRun_cost_le x t)

theorem insertRun_cost_le_logb [LT α] [DecidableLT α] (x : α)
    (t : BinaryTree (α × Nat)) (valid : Trees.AVL.Valid t) :
    ((insertRun x t).2 : ℝ) ≤ (27 * (1 / Real.logb 2 Real.goldenRatio)) *
      Real.logb 2 ((t.numNodes : ℝ) + 1) + 6 := by
  simpa using work_le_logb t valid _ 27 6 (insertRun_cost_le x t)

theorem splitMaxRun_cost_le_logb (t : BinaryTree (α × Nat)) (valid : Trees.AVL.Valid t) :
    ((splitMaxRun t).2 : ℝ) ≤ (25 * (1 / Real.logb 2 Real.goldenRatio)) *
      Real.logb 2 ((t.numNodes : ℝ) + 1) + 1 := by
  simpa using work_le_logb t valid _ 25 1 (splitMaxRun_cost_le t)

theorem splitMaxRun_cost_le_logb_of_ne_nil (t : BinaryTree (α × Nat))
    (valid : Trees.AVL.Valid t) (hne : t ≠ .nil) :
    ((splitMaxRun t).2 : ℝ) ≤ (25 * (1 / Real.logb 2 Real.goldenRatio)) *
      Real.logb 2 ((t.numNodes : ℝ) + 1) := by
  simpa using work_le_logb t valid _ 25 0 (by simpa using splitMaxRun_cost_le_of_ne_nil t hne)

theorem deleteRun_cost_le_logb [LT α] [DecidableLT α] (x : α)
    (t : BinaryTree (α × Nat)) (valid : Trees.AVL.Valid t) :
    ((deleteRun x t).2 : ℝ) ≤ (27 * (1 / Real.logb 2 Real.goldenRatio)) *
      Real.logb 2 ((t.numNodes : ℝ) + 1) + 1 := by
  simpa using work_le_logb t valid _ 27 1 (deleteRun_cost_le x t)

/-- Distinct search keys, without cache or balance, justify changing the size. -/
theorem observe_ncard_eq_numNodes [LinearOrder α] (t : BinaryTree (α × Nat))
    (strict : Search.OrderedList.Strict (Trees.inorder (Trees.Cached.erase t))) :
    (Trees.setTree (Trees.Cached.erase t)).ncard = t.numNodes := by
  simpa only [Trees.Cached.numNodes_erase] using
    Trees.setTree_ncard_eq_numNodes (Trees.Cached.erase t) strict.nodup

theorem lookupRun_cost_le_clog_set [LinearOrder α] (x : α) (t : BinaryTree (α × Nat))
    (balanced : Trees.AVL.Balanced (Trees.Cached.erase t))
    (strict : Search.OrderedList.Strict (Trees.inorder (Trees.Cached.erase t))) :
    (lookupRun x t).2 ≤ 6 * Nat.clog 2 ((Trees.setTree (Trees.Cached.erase t)).ncard + 1) + 1 := by
  rw [observe_ncard_eq_numNodes t strict]
  exact lookupRun_cost_le_clog x t balanced

theorem memberRun_cost_le_clog_set [LinearOrder α] (x : α) (t : BinaryTree (α × Nat))
    (balanced : Trees.AVL.Balanced (Trees.Cached.erase t))
    (strict : Search.OrderedList.Strict (Trees.inorder (Trees.Cached.erase t))) :
    (memberRun x t).2 ≤ 6 * Nat.clog 2 ((Trees.setTree (Trees.Cached.erase t)).ncard + 1) + 1 := by
  rw [observe_ncard_eq_numNodes t strict]
  exact memberRun_cost_le_clog x t balanced

theorem insertRun_cost_le_clog_set [LinearOrder α] (x : α) (t : BinaryTree (α × Nat))
    (balanced : Trees.AVL.Balanced (Trees.Cached.erase t))
    (strict : Search.OrderedList.Strict (Trees.inorder (Trees.Cached.erase t))) :
    (insertRun x t).2 ≤ 54 * Nat.clog 2 ((Trees.setTree (Trees.Cached.erase t)).ncard + 1) + 6 := by
  rw [observe_ncard_eq_numNodes t strict]
  exact insertRun_cost_le_clog x t balanced

theorem splitMaxRun_cost_le_clog_set (t : BinaryTree (α × Nat)) [LinearOrder α]
    (balanced : Trees.AVL.Balanced (Trees.Cached.erase t))
    (strict : Search.OrderedList.Strict (Trees.inorder (Trees.Cached.erase t))) :
    (splitMaxRun t).2 ≤ 50 * Nat.clog 2 ((Trees.setTree (Trees.Cached.erase t)).ncard + 1) + 1 := by
  rw [observe_ncard_eq_numNodes t strict]
  exact splitMaxRun_cost_le_clog t balanced

theorem deleteRun_cost_le_clog_set [LinearOrder α] (x : α) (t : BinaryTree (α × Nat))
    (balanced : Trees.AVL.Balanced (Trees.Cached.erase t))
    (strict : Search.OrderedList.Strict (Trees.inorder (Trees.Cached.erase t))) :
    (deleteRun x t).2 ≤ 54 * Nat.clog 2 ((Trees.setTree (Trees.Cached.erase t)).ncard + 1) + 1 := by
  rw [observe_ncard_eq_numNodes t strict]
  exact deleteRun_cost_le_clog x t balanced

theorem lookupRun_cost_le_logb_set [LinearOrder α] (x : α) (t : BinaryTree (α × Nat))
    (valid : Trees.AVL.Valid t)
    (strict : Search.OrderedList.Strict (Trees.inorder (Trees.Cached.erase t))) :
    ((lookupRun x t).2 : ℝ) ≤ (3 * (1 / Real.logb 2 Real.goldenRatio)) *
      Real.logb 2 (((Trees.setTree (Trees.Cached.erase t)).ncard : ℝ) + 1) + 1 := by
  rw [observe_ncard_eq_numNodes t strict]
  exact lookupRun_cost_le_logb x t valid

theorem memberRun_cost_le_logb_set [LinearOrder α] (x : α) (t : BinaryTree (α × Nat))
    (valid : Trees.AVL.Valid t)
    (strict : Search.OrderedList.Strict (Trees.inorder (Trees.Cached.erase t))) :
    ((memberRun x t).2 : ℝ) ≤ (3 * (1 / Real.logb 2 Real.goldenRatio)) *
      Real.logb 2 (((Trees.setTree (Trees.Cached.erase t)).ncard : ℝ) + 1) + 1 := by
  rw [observe_ncard_eq_numNodes t strict]
  exact memberRun_cost_le_logb x t valid

theorem insertRun_cost_le_logb_set [LinearOrder α] (x : α) (t : BinaryTree (α × Nat))
    (valid : Trees.AVL.Valid t)
    (strict : Search.OrderedList.Strict (Trees.inorder (Trees.Cached.erase t))) :
    ((insertRun x t).2 : ℝ) ≤ (27 * (1 / Real.logb 2 Real.goldenRatio)) *
      Real.logb 2 (((Trees.setTree (Trees.Cached.erase t)).ncard : ℝ) + 1) + 6 := by
  rw [observe_ncard_eq_numNodes t strict]
  exact insertRun_cost_le_logb x t valid

theorem splitMaxRun_cost_le_logb_set (t : BinaryTree (α × Nat)) [LinearOrder α]
    (valid : Trees.AVL.Valid t)
    (strict : Search.OrderedList.Strict (Trees.inorder (Trees.Cached.erase t))) :
    ((splitMaxRun t).2 : ℝ) ≤ (25 * (1 / Real.logb 2 Real.goldenRatio)) *
      Real.logb 2 (((Trees.setTree (Trees.Cached.erase t)).ncard : ℝ) + 1) + 1 := by
  rw [observe_ncard_eq_numNodes t strict]
  exact splitMaxRun_cost_le_logb t valid

theorem deleteRun_cost_le_logb_set [LinearOrder α] (x : α) (t : BinaryTree (α × Nat))
    (valid : Trees.AVL.Valid t)
    (strict : Search.OrderedList.Strict (Trees.inorder (Trees.Cached.erase t))) :
    ((deleteRun x t).2 : ℝ) ≤ (27 * (1 / Real.logb 2 Real.goldenRatio)) *
      Real.logb 2 (((Trees.setTree (Trees.Cached.erase t)).ncard : ℝ) + 1) + 1 := by
  rw [observe_ncard_eq_numNodes t strict]
  exact deleteRun_cost_le_logb x t valid

end Resources.AVL

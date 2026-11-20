import Applications.Resources.ListAppend
import Applications.Resources.TreeTraversalWork
import Applications.Resources.TreeAccumulator
import Applications.Resources.Growth
import Applications.Trees.ShapeLog
import Applications.Search.OrderedMap.Enumeration

/-!
# Actual executions of the two SearchTree enumerations

`copyRun` executes the source's two right-associated appends, charging one
copied list cell per cell in each first argument. The singleton append really
runs, so its one copy is retained. Tree inspection and singleton construction
are not append-copy charges. `accumulatorRun` instead observes constructor
visits (including nil) and cons operations as a pair. Its right traversal feeds
its actual returned suffix to the left traversal through the common measured
accumulator node operation. Neither observation asserts physical sharing,
constant stack usage, compiled running time, or a concrete heap model.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.TreeEnumeration
universe u v
variable {α : Type u}

/-- Execute `[a] ++ right` and then `left ++` its returned list. -/
def copyStep (left : List α) (a : α) (right : List α) : Measured (List α) Nat :=
  bind (ListAppend.copies [a] right) (fun tail => ListAppend.copies left tail)

theorem copyStep_exact (left : List α) (a : α) (right : List α) :
    copyStep left a right = (left ++ a :: right, left.length + 1) := by
  simp [copyStep, ListAppend.copies_exact, bind, Nat.add_comm]

/-- Both recursive traversals and both actual appends use the shared fold. -/
def copyRun (t : BinaryTree α) : Measured (List α) Nat :=
  TreeFold.run 0 [] copyStep t

@[simp] theorem copyRun_nil : copyRun (.nil : BinaryTree α) = ([], 0) := rfl

theorem copyRun_node (a : α) (l r : BinaryTree α) :
    copyRun (.node a l r) =
      ((copyRun l).1 ++ a :: (copyRun r).1,
        (copyRun l).2 + (copyRun r).2 + (copyRun l).1.length + 1) := by
  simp only [copyRun, TreeFold.run_node, copyStep_exact, Nat.add_zero]
  congr 1
  omega

theorem copyRun_value (t : BinaryTree α) : (copyRun t).1 = Trees.inorder t := by
  exact TreeFold.run_value_of 0 [] copyStep (fun l a r => l ++ a :: r)
    (fun l a r => congrArg Prod.fst (copyStep_exact l a r)) t

/-- Every source node contributes its left-subtree size and its singleton copy. -/
theorem copyRun_copies (t : BinaryTree α) :
    (copyRun t).2 = Trees.leftSizeSum t + t.numNodes := by
  have h := TreeFold.run_cost_leftSizeSum 0 ([] : List α) copyStep 1 1
    (fun l a r => by
      rw [copyStep_exact]
      change (copyRun l).1.length + 1 = 1 * l.numNodes + 1
      rw [copyRun_value, Trees.inorder_length, Nat.one_mul]) t
  simpa only [copyRun, Nat.zero_mul, Nat.zero_add, Nat.one_mul] using h

theorem copyRun_exact (t : BinaryTree α) :
    copyRun t = (Trees.inorder t, Trees.leftSizeSum t + t.numNodes) :=
  Prod.ext (copyRun_value t) (copyRun_copies t)

theorem copyRun_entries (t : BinaryTree α) :
    (copyRun t).1 = Search.OrderedTree.entries t := copyRun_value t

theorem copyRun_node_copies (a : α) (l r : BinaryTree α) :
    (copyRun (.node a l r)).2 =
      (copyRun l).2 + (copyRun r).2 + l.numNodes + 1 := by
  rw [copyRun_node, copyRun_value, Trees.inorder_length]

theorem size_le_copies (t : BinaryTree α) : t.numNodes ≤ (copyRun t).2 := by
  rw [copyRun_copies]
  omega

theorem copies_le_square (t : BinaryTree α) : (copyRun t).2 ≤ t.numNodes ^ 2 := by
  rw [copyRun_copies]
  exact Trees.leftSizeSum_add_size_le t

/-- The triangular upper bound is sharp on every left chain. -/
theorem twice_copies_le (t : BinaryTree α) :
    2 * (copyRun t).2 ≤ t.numNodes * (t.numNodes + 1) := by
  rw [copyRun_copies]
  have h := Trees.twice_leftSizeSum_add_size_le t
  nlinarith

theorem leftChain_copies (a : α) (n : Nat) :
    (copyRun (Trees.leftChain a n)).2 = n * (n + 1) / 2 := by
  rw [copyRun_copies, Trees.leftChain_numNodes]
  have h := Trees.twice_leftSizeSum_leftChain a n
  have he : 2 * (Trees.leftSizeSum (Trees.leftChain a n) + n) = n * (n + 1) := by
    nlinarith
  omega

theorem rightChain_copies (a : α) (n : Nat) :
    (copyRun (Trees.rightChain a n)).2 = n := by
  simp [copyRun_copies]

/-- A height bound is useful even when the tree is not balanced. -/
theorem copies_le_height_mul_size (t : BinaryTree α) :
    (copyRun t).2 ≤ t.height * t.numNodes := by
  induction t with
  | nil => simp [BinaryTree.height]
  | node a l r ihl ihr =>
      rw [copyRun_node_copies]
      have hl := Nat.mul_le_mul_right l.numNodes (Nat.le_max_left l.height r.height)
      have hr := Nat.mul_le_mul_right r.numNodes (Nat.le_max_right l.height r.height)
      simp only [BinaryTree.height, BinaryTree.numNodes]
      calc
        (copyRun l).2 + (copyRun r).2 + l.numNodes + 1 ≤
            max l.height r.height * l.numNodes +
              max l.height r.height * r.numNodes + l.numNodes + 1 := by omega
        _ ≤ max l.height r.height * l.numNodes +
              max l.height r.height * r.numNodes + l.numNodes + 1 +
              (max l.height r.height + r.numNodes) := Nat.le_add_right _ _
        _ = (max l.height r.height + 1) * (l.numNodes + r.numNodes + 1) := by ring

/-- Perfect trees have the exact full capacity, including the height-zero case. -/
theorem complete_size (t : BinaryTree α) (ht : Trees.Complete t) :
    t.numNodes + 1 = 2 ^ t.height := by
  simpa only [BinaryTree.numLeaves_eq_numNodes_succ] using
    Trees.numLeaves_eq_pow_height t ht

theorem complete_numNodes (t : BinaryTree α) (ht : Trees.Complete t) :
    t.numNodes = 2 ^ t.height - 1 := by
  have h := complete_size t ht
  omega

/-- The doubled form has no truncated predecessor and also covers nil. -/
theorem complete_twice_copies (t : BinaryTree α) (ht : Trees.Complete t) :
    2 * (copyRun t).2 = t.height * 2 ^ t.height := by
  induction t with
  | nil => simp [BinaryTree.height]
  | node a l r ihl ihr =>
      rcases ht with ⟨hh, hl, hr⟩
      have hnl := complete_size l hl
      have hnr := complete_size r hr
      have hcl := ihl hl
      have hcr := ihr hr
      rw [hh] at hnl hcl
      rw [copyRun_node_copies]
      simp only [BinaryTree.height, hh, max_self, Nat.pow_succ]
      nlinarith

/-- Exactly `h * 2^(h-1)` copied cells; at height zero both sides are zero. -/
theorem complete_copies (t : BinaryTree α) (ht : Trees.Complete t) :
    (copyRun t).2 = t.height * 2 ^ (t.height - 1) := by
  have h := complete_twice_copies t ht
  cases hh : t.height with
  | zero => simp only [hh, Nat.zero_mul] at h ⊢; omega
  | succ k =>
      simp only [hh, Nat.add_sub_cancel, Nat.pow_succ] at h ⊢
      nlinarith

theorem copies_le_of_height_bound (t : BinaryTree α) (H : Nat)
    (height_bound : t.height ≤ H * Nat.clog 2 (t.numNodes + 1)) :
    (copyRun t).2 ≤ H * (t.numNodes * Nat.clog 2 (t.numNodes + 1)) := by
  calc
    (copyRun t).2 ≤ t.height * t.numNodes := copies_le_height_mul_size t
    _ ≤ (H * Nat.clog 2 (t.numNodes + 1)) * t.numNodes :=
      Nat.mul_le_mul_right _ height_bound
    _ = H * (t.numNodes * Nat.clog 2 (t.numNodes + 1)) := by ring

/-- Almost completeness supplies the logarithmic-height premise; arbitrary
search-tree insertion supplies no such balancing invariant. -/
theorem almostComplete_copies (t : BinaryTree α) (ht : Trees.AlmostComplete t) :
    (copyRun t).2 ≤ t.numNodes * Nat.clog 2 (t.numNodes + 1) := by
  have hh := Trees.height_eq_clog_numLeaves t ht
  rw [BinaryTree.numLeaves_eq_numNodes_succ] at hh
  simpa only [Nat.one_mul] using copies_le_of_height_bound t 1 (by omega)

/-- Conditional growth for any indexed family with the stated size and height
contracts. The comparator is the real-cast discrete `n log(n+1)` measure. -/
theorem copyRun_isBigO (family : Nat → BinaryTree α) (H : Nat)
    (sizes : ∀ n, (family n).numNodes = n)
    (heights : ∀ n, (family n).height ≤ H * Nat.clog 2 (n + 1)) :
    Asymptotics.IsBigO Filter.atTop (fun n => ((copyRun (family n)).2 : ℝ))
      (fun n => ((n * Nat.clog 2 (n + 1) : Nat) : ℝ)) := by
  apply isBigO_of_nat_bound _ _ H 0
  intro n _
  simpa only [sizes n] using copies_le_of_height_bound (family n) H (by
    simpa only [sizes n] using heights n)

/-- An external size parameter may be an upper bound, for example the number
of external leaves. This gives the ordinary real `O(n log₂ n)` conclusion. -/
theorem copyRun_log_isBigO (family : Nat → BinaryTree α) (H N : Nat)
    (sizes : ∀ n, N ≤ n → (family n).numNodes ≤ n)
    (heights : ∀ n, N ≤ n → (family n).height ≤ H * Nat.clog 2 n) :
    Asymptotics.IsBigO Filter.atTop (fun n => ((copyRun (family n)).2 : ℝ))
      (fun n => (n : ℝ) * Real.logb 2 n) := by
  apply isBigO_of_clog_two_bound _ H N
  intro n hn
  calc
    (copyRun (family n)).2 ≤ (family n).height * (family n).numNodes :=
      copies_le_height_mul_size (family n)
    _ ≤ (H * Nat.clog 2 n) * n := Nat.mul_le_mul (heights n hn) (sizes n hn)
    _ = H * (n * Nat.clog 2 n) := by ring

theorem copyRun_quadratic_isBigO (family : Nat → BinaryTree α)
    (sizes : ∀ n, (family n).numNodes = n) :
    Asymptotics.IsBigO Filter.atTop (fun n => ((copyRun (family n)).2 : ℝ))
      (fun n => ((n ^ 2 : Nat) : ℝ)) := by
  apply isBigO_of_nat_bound _ _ 1 0
  intro n _
  simpa only [sizes n, Nat.one_mul] using copies_le_square (family n)

/-- Nil is visited once and builds no cons. Every node builds one cons. The
common `nodeRun` evaluates the right suffix before passing its actual result
under the node's cons to the left traversal. -/
def accumulatorRun (t : BinaryTree α) (suffix : List α) :
    Measured (List α) (Nat × Nat) :=
  Trees.fold (fun acc => (acc, (1, 0))) (TreeAccumulator.nodeRun (1, 1)) t suffix

@[simp] theorem accumulatorRun_nil (suffix : List α) :
    accumulatorRun .nil suffix = (suffix, (1, 0)) := rfl

theorem accumulatorRun_node (a : α) (l r : BinaryTree α) (suffix : List α) :
    accumulatorRun (.node a l r) suffix =
      TreeAccumulator.nodeRun (1, 1) (accumulatorRun l) a (accumulatorRun r) suffix := rfl

/-- Erasure retains the entire arbitrary suffix, not only an initially empty one. -/
theorem accumulatorRun_value (t : BinaryTree α) (suffix : List α) :
    (accumulatorRun t suffix).1 = Trees.inorder t ++ suffix := by
  induction t generalizing suffix with
  | nil => rfl
  | node a l r ihl ihr =>
      simp only [accumulatorRun_node, TreeAccumulator.nodeRun, bind_value, ihr, ihl,
        Trees.inorder_node, List.append_assoc, List.cons_append]

theorem accumulatorRun_work (t : BinaryTree α) (suffix : List α) :
    (accumulatorRun t suffix).2 = (2 * t.numNodes + 1, t.numNodes) := by
  induction t generalizing suffix with
  | nil => rfl
  | node a l r ihl ihr =>
      simp only [accumulatorRun_node, TreeAccumulator.nodeRun, bind, ihr, ihl,
        BinaryTree.numNodes]
      apply Prod.ext <;> dsimp <;> omega

theorem accumulatorRun_exact (t : BinaryTree α) (suffix : List α) :
    accumulatorRun t suffix =
      (Trees.inorder t ++ suffix, (2 * t.numNodes + 1, t.numNodes)) :=
  Prod.ext (accumulatorRun_value t suffix) (accumulatorRun_work t suffix)

/-- The measured generic traversal erases to the source map accumulator with
independent universes for keys and payloads. -/
theorem accumulatorRun_fastEntriesAcc {κ : Type u} {ν : Type v}
    (t : BinaryTree (κ × ν)) (suffix : List (κ × ν)) :
    (accumulatorRun t suffix).1 = Search.OrderedMap.fastEntriesAcc t suffix := by
  rw [accumulatorRun_value, Search.OrderedMap.fastEntriesAcc_eq]
  rfl

theorem accumulatorRun_work_independent (t : BinaryTree α) (xs ys : List α) :
    (accumulatorRun t xs).2 = (accumulatorRun t ys).2 := by
  rw [accumulatorRun_work, accumulatorRun_work]

theorem accumulatorRun_length (t : BinaryTree α) (suffix : List α) :
    (accumulatorRun t suffix).1.length = t.numNodes + suffix.length := by
  rw [accumulatorRun_value, List.length_append, Trees.inorder_length]

theorem accumulatorRun_visits_isBigO (family : Nat → BinaryTree α)
    (suffixes : Nat → List α) (sizes : ∀ n, (family n).numNodes = n) :
    Asymptotics.IsBigO Filter.atTop
      (fun n => ((accumulatorRun (family n) (suffixes n)).2.1 : ℝ))
      (fun n => (n : ℝ)) := by
  apply isBigO_of_nat_bound _ _ 3 1
  intro n hn
  simp only [accumulatorRun_work, sizes n]
  omega

end Resources.TreeEnumeration

import Applications.Trees.Observations
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Shape observations for the work of traversals that append a left result.
The ordinary fold below is a mathematical observation of an input tree, not
an additional pass in any measured execution. Exact source correspondence,
independent expectations and statement assessment:
`docs/research/fdsa-tree-traversal-work.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees
universe u v
variable {α : Type u} {β : Type v}

private def leftSummary (t : BinaryTree α) : Nat × Nat :=
  fold (0, 0) (fun l (_ : α) r =>
    (l.1 + r.1 + 1, l.2 + r.2 + l.1)) t

private theorem leftSummary_size (t : BinaryTree α) :
    (leftSummary t).1 = t.numNodes := by
  calc
    (leftSummary t).1 = fold 0 (fun l (_ : α) r => l + r + 1) t :=
      fold_fusion (0, 0)
        (fun (l : Nat × Nat) (_ : α) r => (l.1 + r.1 + 1, l.2 + r.2 + l.1))
        0 (fun l (_ : α) r => l + r + 1) Prod.fst rfl (fun _ _ _ => rfl) t
    _ = t.numNodes := fold_numNodes t

/-- Sum the sizes of left subtrees over node occurrences. Equal subtrees
and labels retain their occurrences; this is not a physical storage count. -/
def leftSizeSum (t : BinaryTree α) : Nat := (leftSummary t).2

@[simp] theorem leftSizeSum_nil : leftSizeSum (.nil : BinaryTree α) = 0 := rfl

@[simp] theorem leftSizeSum_node (a : α) (l r : BinaryTree α) :
    leftSizeSum (.node a l r) = leftSizeSum l + leftSizeSum r + l.numNodes := by
  change (leftSummary l).2 + (leftSummary r).2 + (leftSummary l).1 =
    (leftSummary l).2 + (leftSummary r).2 + l.numNodes
  rw [leftSummary_size]

/-- Mapping given labels does not collapse repeated occurrences. -/
theorem leftSizeSum_map (label : α → β) (t : BinaryTree α) :
    leftSizeSum (t.map label) = leftSizeSum t := by
  unfold leftSizeSum leftSummary
  rw [fold_map]

theorem leftSizeSum_repeated (a : α) (t : BinaryTree α) :
    leftSizeSum (.node a t t) = 2 * leftSizeSum t + t.numNodes := by
  rw [leftSizeSum_node]
  ring

/-- A division-free sharp bound, including empty and one-node trees. -/
theorem twice_leftSizeSum_add_size_le (t : BinaryTree α) :
    2 * leftSizeSum t + t.numNodes ≤ t.numNodes ^ 2 := by
  induction t with
  | nil => simp
  | node a l r ihl ihr =>
      simp only [leftSizeSum_node, BinaryTree.numNodes]
      nlinarith [Nat.zero_le (l.numNodes * r.numNodes), Nat.zero_le r.numNodes]

theorem leftSizeSum_add_size_le (t : BinaryTree α) :
    leftSizeSum t + t.numNodes ≤ t.numNodes ^ 2 := by
  have h := twice_leftSizeSum_add_size_le t
  nlinarith [Nat.zero_le (leftSizeSum t)]

private theorem twice_choose_two_add (n : Nat) : 2 * n.choose 2 + n = n ^ 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Nat.choose_succ_succ' n 1, Nat.choose_one_right]
      nlinarith

theorem leftSizeSum_le_choose (t : BinaryTree α) :
    leftSizeSum t ≤ t.numNodes.choose 2 := by
  have h := twice_leftSizeSum_add_size_le t
  have hc := twice_choose_two_add t.numNodes
  nlinarith

/-- An explicit label supplies a left-chain input at every natural size. -/
def leftChain (a : α) : Nat → BinaryTree α
  | 0 => .nil
  | n + 1 => .node a (leftChain a n) .nil

/-- The corresponding right-chain input family. -/
def rightChain (a : α) : Nat → BinaryTree α
  | 0 => .nil
  | n + 1 => .node a .nil (rightChain a n)

@[simp] theorem leftChain_numNodes (a : α) (n : Nat) :
    (leftChain a n).numNodes = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [leftChain, BinaryTree.numNodes, ih]

@[simp] theorem rightChain_numNodes (a : α) (n : Nat) :
    (rightChain a n).numNodes = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rightChain, BinaryTree.numNodes, ih]

@[simp] theorem leftChain_height (a : α) (n : Nat) :
    (leftChain a n).height = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [leftChain, BinaryTree.height, ih]

@[simp] theorem rightChain_height (a : α) (n : Nat) :
    (rightChain a n).height = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rightChain, BinaryTree.height, ih]

theorem inorder_leftChain (a : α) (n : Nat) :
    inorder (leftChain a n) = List.replicate n a := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [leftChain, inorder_node, inorder_nil, ih, List.replicate_succ']

theorem inorder_rightChain (a : α) (n : Nat) :
    inorder (rightChain a n) = List.replicate n a := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [rightChain, inorder_node, inorder_nil, ih,
        List.nil_append, List.replicate_succ]

theorem leftSizeSum_leftChain (a : α) (n : Nat) :
    leftSizeSum (leftChain a n) = n.choose 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [leftChain, leftSizeSum_node, leftSizeSum_nil,
        leftChain_numNodes, ih, Nat.add_zero]
      rw [Nat.choose_succ_succ' n 1, Nat.choose_one_right]
      exact Nat.add_comm _ _

theorem twice_leftSizeSum_leftChain (a : α) (n : Nat) :
    2 * leftSizeSum (leftChain a n) + n = n ^ 2 := by
  rw [leftSizeSum_leftChain]
  exact twice_choose_two_add n

@[simp] theorem leftSizeSum_rightChain (a : α) (n : Nat) :
    leftSizeSum (rightChain a n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rightChain, ih, BinaryTree.numNodes]

end Trees

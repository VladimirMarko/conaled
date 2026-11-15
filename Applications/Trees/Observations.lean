import Mathlib.Data.Tree.Basic
import Mathlib.Data.List.Basic

/-! Ordinary folds and ordered observations of Mathlib's node-labelled trees.
The empty result and node operation are explicit parameters; no algebraic
laws on the node operation are required. Source and statement assessment:
`docs/research/fdsa-tree-cache.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees
universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

/-- Fold a finite binary tree using both child summaries and its node label. -/
def fold (empty : β) (combine : β → α → β → β) : BinaryTree α → β
  | .nil => empty
  | .node a l r => combine (fold empty combine l) a (fold empty combine r)

@[simp] theorem fold_nil (empty : β) (combine : β → α → β → β) :
    fold empty combine .nil = empty := rfl

@[simp] theorem fold_node (empty : β) (combine : β → α → β → β)
    (a : α) (l r : BinaryTree α) :
    fold empty combine (.node a l r) =
      combine (fold empty combine l) a (fold empty combine r) := rfl

/-- Label transport requires no injectivity and leaves child positions intact. -/
theorem fold_map (empty : β) (combine : β → γ → β → β)
    (label : α → γ) (t : BinaryTree α) :
    fold empty combine (t.map label) =
      fold empty (fun l a r => combine l (label a) r) t := by
  induction t with
  | nil => rfl
  | node a l r ihl ihr =>
      simp only [BinaryTree.map, fold_node, ihl, ihr]

/-- A map of summaries transports a fold when it preserves the supplied
empty value and node operation. No monoid or commutativity is involved. -/
theorem fold_fusion (empty : β) (combine : β → α → β → β)
    (empty' : γ) (combine' : γ → α → γ → γ) (observe : β → γ)
    (h_empty : observe empty = empty')
    (h_node : ∀ l a r, observe (combine l a r) =
      combine' (observe l) a (observe r)) (t : BinaryTree α) :
    observe (fold empty combine t) = fold empty' combine' t := by
  induction t with
  | nil => exact h_empty
  | node a l r ihl ihr =>
      rw [fold_node, fold_node, h_node, ihl, ihr]

theorem fold_numNodes (t : BinaryTree α) :
    fold (0 : Nat) (fun l (_ : α) r => l + r + 1) t = t.numNodes := by
  induction t with
  | nil => rfl
  | node a l r ihl ihr =>
      simp only [fold_node, BinaryTree.numNodes, ihl, ihr]

theorem fold_height (t : BinaryTree α) :
    fold (0 : Nat) (fun l (_ : α) r => max l r + 1) t = t.height := by
  induction t with
  | nil => rfl
  | node a l r ihl ihr =>
      simp only [fold_node, BinaryTree.height, ihl, ihr]

/-- The ordered list of node labels, with duplicates retained. This is a value
observation; its equation alone makes no assertion about append costs. -/
def inorder (t : BinaryTree α) : List α :=
  fold [] (fun l a r => l ++ (a :: r)) t

@[simp] theorem inorder_nil : inorder (.nil : BinaryTree α) = [] := rfl

@[simp] theorem inorder_node (a : α) (l r : BinaryTree α) :
    inorder (.node a l r) = inorder l ++ (a :: inorder r) := rfl

theorem inorder_length (t : BinaryTree α) : (inorder t).length = t.numNodes := by
  induction t with
  | nil => rfl
  | node a l r ihl ihr =>
      simp [inorder_node, ihl, ihr, BinaryTree.numNodes, Nat.add_assoc]

theorem inorder_map (label : α → β) (t : BinaryTree α) :
    inorder (t.map label) = (inorder t).map label := by
  induction t with
  | nil => rfl
  | node a l r ihl ihr =>
      simp [BinaryTree.map, inorder_node, ihl, ihr]

theorem numNodes_map (label : α → β) (t : BinaryTree α) :
    (t.map label).numNodes = t.numNodes := by
  induction t with
  | nil => rfl
  | node a l r ihl ihr =>
      simp only [BinaryTree.map, BinaryTree.numNodes, ihl, ihr]

theorem numLeaves_map (label : α → β) (t : BinaryTree α) :
    (t.map label).numLeaves = t.numLeaves := by
  simp only [BinaryTree.numLeaves_eq_numNodes_succ, numNodes_map]

theorem height_map (label : α → β) (t : BinaryTree α) :
    (t.map label).height = t.height := by
  induction t with
  | nil => rfl
  | node a l r ihl ihr =>
      simp only [BinaryTree.map, BinaryTree.height, ihl, ihr]

end Trees

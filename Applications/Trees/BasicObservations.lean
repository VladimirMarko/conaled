import Applications.Trees.Observations
import Mathlib.Data.Set.Insert

/-! Element sets, preorder and structural subtrees for FDSA Chapter 4.
The set observation is independent of the traversal lists. Structural
containment retains whole rooted subtrees, including the empty tree; it does
not identify trees merely because their labels have the same set.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees
universe u v
variable {α : Type u} {β : Type v}

/-- The set of labels, defined structurally without decidable equality. -/
def setTree : BinaryTree α → Set α :=
  fold ∅ (fun l a r => l ∪ {a} ∪ r)

@[simp] theorem setTree_nil : setTree (.nil : BinaryTree α) = ∅ := rfl

@[simp] theorem setTree_node (a : α) (l r : BinaryTree α) :
    setTree (.node a l r) = setTree l ∪ {a} ∪ setTree r := rfl

/-- Root, left subtree, then right subtree, with repeated labels retained. -/
def preorder : BinaryTree α → List α :=
  fold [] (fun l a r => a :: (l ++ r))

@[simp] theorem preorder_nil : preorder (.nil : BinaryTree α) = [] := rfl

@[simp] theorem preorder_node (a : α) (l r : BinaryTree α) :
    preorder (.node a l r) = a :: (preorder l ++ preorder r) := rfl

/-- Inorder and the independent set observation have the same members. -/
theorem mem_inorder_iff_mem_setTree (x : α) (t : BinaryTree α) :
    x ∈ inorder t ↔ x ∈ setTree t := by
  induction t with
  | nil => simp
  | node a l r ihl ihr =>
      simp only [inorder_node, List.mem_append, List.mem_cons, ihl, ihr,
        setTree_node, Set.mem_union, Set.mem_singleton_iff, or_assoc]

/-- Preorder forgets order and multiplicity only when observed as membership. -/
theorem mem_preorder_iff_mem_setTree (x : α) (t : BinaryTree α) :
    x ∈ preorder t ↔ x ∈ setTree t := by
  induction t with
  | nil => simp
  | node a l r ihl ihr =>
      simp only [preorder_node, List.mem_cons, List.mem_append, ihl, ihr,
        setTree_node, Set.mem_union, Set.mem_singleton_iff, or_assoc]
      exact or_left_comm

theorem preorder_length (t : BinaryTree α) :
    (preorder t).length = t.numNodes := by
  induction t with
  | nil => rfl
  | node a l r ihl ihr =>
      simp [ihl, ihr, BinaryTree.numNodes]

/-- Label transport may identify labels; no injectivity is required. -/
theorem preorder_map (label : α → β) (t : BinaryTree α) :
    preorder (t.map label) = (preorder t).map label := by
  induction t with
  | nil => rfl
  | node a l r ihl ihr =>
      simp [BinaryTree.map, ihl, ihr]

/-- A whole rooted descendant subtree. The smaller tree is the first argument. -/
inductive Subtree : BinaryTree α → BinaryTree α → Prop where
  | refl (t : BinaryTree α) : Subtree t t
  | left {s l r : BinaryTree α} (a : α) :
      Subtree s l → Subtree s (.node a l r)
  | right {s l r : BinaryTree α} (a : α) :
      Subtree s r → Subtree s (.node a l r)

/-- Empty leaves ensure that every finite binary tree contains the empty tree. -/
theorem nil_subtree (t : BinaryTree α) : Subtree .nil t := by
  induction t with
  | nil => exact Subtree.refl .nil
  | node a _ _ ihl _ => exact Subtree.left a ihl

@[simp] theorem subtree_nil_iff (s : BinaryTree α) :
    Subtree s .nil ↔ s = .nil := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    subst s
    exact Subtree.refl .nil

/-- A structural subtree of a node is the node itself or a child subtree. -/
theorem subtree_node_iff (s : BinaryTree α) (a : α) (l r : BinaryTree α) :
    Subtree s (.node a l r) ↔
      s = .node a l r ∨ Subtree s l ∨ Subtree s r := by
  constructor
  · intro h
    cases h with
    | refl => exact Or.inl rfl
    | left _ h => exact Or.inr (Or.inl h)
    | right _ h => exact Or.inr (Or.inr h)
  · intro h
    rcases h with h | h | h
    · subst s
      exact Subtree.refl _
    · exact Subtree.left a h
    · exact Subtree.right a h

/-- Structural containment composes without comparing labels or trees. -/
theorem Subtree.trans {s t u : BinaryTree α}
    (hst : Subtree s t) (htu : Subtree t u) : Subtree s u := by
  induction htu with
  | refl => exact hst
  | left a _ ih => exact Subtree.left a ih
  | right a _ ih => exact Subtree.right a ih

/-- All whole rooted descendant subtrees, including the tree itself. -/
def subtrees (t : BinaryTree α) : Set (BinaryTree α) := {s | Subtree s t}

@[simp] theorem mem_subtrees_iff {s t : BinaryTree α} :
    s ∈ subtrees t ↔ Subtree s t := Iff.rfl

@[simp] theorem subtrees_nil : subtrees (.nil : BinaryTree α) = {.nil} := by
  ext s
  simpa only [mem_subtrees_iff, Set.mem_singleton_iff] using subtree_nil_iff s

theorem subtrees_node (a : α) (l r : BinaryTree α) :
    subtrees (.node a l r) = {.node a l r} ∪ subtrees l ∪ subtrees r := by
  ext s
  simp only [Set.mem_union, Set.mem_singleton_iff, mem_subtrees_iff,
    subtree_node_iff, or_assoc]

theorem self_mem_subtrees (t : BinaryTree α) : t ∈ subtrees t :=
  Subtree.refl t

theorem nil_mem_subtrees (t : BinaryTree α) :
    (.nil : BinaryTree α) ∈ subtrees t := nil_subtree t

end Trees

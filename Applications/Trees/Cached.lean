import Applications.Trees.Observations

/-! Root observations and recursively valid cached folds on the existing
product-labelled BinaryTree carrier. Erasure is an observation used in the
proofs, not an execution performed by the local smart constructor.
Source and statement assessment: `docs/research/fdsa-tree-cache.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees.Cached
universe u v
variable {α : Type u} {β : Type v}

def erase (t : BinaryTree (α × β)) : BinaryTree α := t.map Prod.fst

@[simp] theorem erase_nil : erase (.nil : BinaryTree (α × β)) = .nil := rfl

@[simp] theorem erase_node (a : α) (b : β) (l r : BinaryTree (α × β)) :
    erase (.node (a, b) l r) = .node a (erase l) (erase r) := rfl

/-- Inspect only the empty/node constructor and the root annotation. -/
def read (empty : β) : BinaryTree (α × β) → β
  | .nil => empty
  | .node (_, b) _ _ => b

@[simp] theorem read_nil (empty : β) :
    read empty (.nil : BinaryTree (α × β)) = empty := rfl

@[simp] theorem read_node (empty : β) (a : α) (b : β)
    (l r : BinaryTree (α × β)) : read empty (.node (a, b) l r) = b := rfl

/-- Reuse both children and compute only the new root's annotation. -/
def smartNode (empty : β) (combine : β → α → β → β)
    (l : BinaryTree (α × β)) (a : α) (r : BinaryTree (α × β)) :
    BinaryTree (α × β) :=
  .node (a, combine (read empty l) a (read empty r)) l r

@[simp] theorem read_smartNode (empty : β) (combine : β → α → β → β)
    (l : BinaryTree (α × β)) (a : α) (r : BinaryTree (α × β)) :
    read empty (smartNode empty combine l a r) =
      combine (read empty l) a (read empty r) := rfl

@[simp] theorem erase_smartNode (empty : β) (combine : β → α → β → β)
    (l : BinaryTree (α × β)) (a : α) (r : BinaryTree (α × β)) :
    erase (smartNode empty combine l a r) = .node a (erase l) (erase r) := rfl

/-- Every stored annotation must be locally correct, including descendants. -/
def Valid (empty : β) (combine : β → α → β → β) :
    BinaryTree (α × β) → Prop
  | .nil => True
  | .node (a, b) l r =>
      Valid empty combine l ∧ Valid empty combine r ∧
        b = combine (read empty l) a (read empty r)

@[simp] theorem valid_nil (empty : β) (combine : β → α → β → β) :
    Valid empty combine .nil := trivial

@[simp] theorem valid_node (empty : β) (combine : β → α → β → β)
    (a : α) (b : β) (l r : BinaryTree (α × β)) :
    Valid empty combine (.node (a, b) l r) ↔
      Valid empty combine l ∧ Valid empty combine r ∧
        b = combine (read empty l) a (read empty r) := Iff.rfl

/-- The new root is repaired; pre-existing child validity is still necessary. -/
theorem smartNode_valid_iff (empty : β) (combine : β → α → β → β)
    (l : BinaryTree (α × β)) (a : α) (r : BinaryTree (α × β)) :
    Valid empty combine (smartNode empty combine l a r) ↔
      Valid empty combine l ∧ Valid empty combine r := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1⟩
  · rintro ⟨hl, hr⟩
    exact ⟨hl, hr, rfl⟩

/-- The independent fold ignores annotations and recomputes the meaning. -/
theorem read_eq_fold (empty : β) (combine : β → α → β → β)
    (t : BinaryTree (α × β)) (ht : Valid empty combine t) :
    read empty t = Trees.fold empty combine (erase t) := by
  induction t with
  | nil => rfl
  | node ab l r ihl ihr =>
      rcases ab with ⟨a, b⟩
      rcases ht with ⟨hl, hr, hb⟩
      change b = combine (Trees.fold empty combine (erase l)) a
        (Trees.fold empty combine (erase r))
      rw [hb, ihl hl, ihr hr]

theorem inorder_erase (t : BinaryTree (α × β)) :
    Trees.inorder (erase t) = (Trees.inorder t).map Prod.fst :=
  Trees.inorder_map Prod.fst t

theorem numNodes_erase (t : BinaryTree (α × β)) :
    (erase t).numNodes = t.numNodes := Trees.numNodes_map Prod.fst t

theorem numLeaves_erase (t : BinaryTree (α × β)) :
    (erase t).numLeaves = t.numLeaves := Trees.numLeaves_map Prod.fst t

theorem height_erase (t : BinaryTree (α × β)) :
    (erase t).height = t.height := Trees.height_map Prod.fst t

/-- Bottom-up annotation is itself an ordinary fold using the smart node. -/
def annotate (empty : β) (combine : β → α → β → β)
    (t : BinaryTree α) : BinaryTree (α × β) :=
  Trees.fold .nil (fun l a r => smartNode empty combine l a r) t

@[simp] theorem annotate_nil (empty : β) (combine : β → α → β → β) :
    annotate empty combine .nil = .nil := rfl

@[simp] theorem annotate_node (empty : β) (combine : β → α → β → β)
    (a : α) (l r : BinaryTree α) :
    annotate empty combine (.node a l r) =
      smartNode empty combine (annotate empty combine l) a
        (annotate empty combine r) := rfl

theorem annotate_valid (empty : β) (combine : β → α → β → β)
    (t : BinaryTree α) : Valid empty combine (annotate empty combine t) := by
  induction t with
  | nil => trivial
  | node a l r ihl ihr =>
      exact (smartNode_valid_iff empty combine _ a _).2 ⟨ihl, ihr⟩

theorem erase_annotate (empty : β) (combine : β → α → β → β)
    (t : BinaryTree α) : erase (annotate empty combine t) = t := by
  induction t with
  | nil => rfl
  | node a l r ihl ihr =>
      simp only [annotate_node, erase_smartNode, ihl, ihr]

theorem read_annotate (empty : β) (combine : β → α → β → β)
    (t : BinaryTree α) :
    read empty (annotate empty combine t) = Trees.fold empty combine t := by
  rw [read_eq_fold empty combine _ (annotate_valid empty combine t), erase_annotate]

end Trees.Cached

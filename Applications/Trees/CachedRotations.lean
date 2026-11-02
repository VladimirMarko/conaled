import Applications.Trees.Rotations
import Applications.Trees.Cached

/-! Rebuild the two changed roots of a legal rotation using existing smart nodes.
Recursive cache validity, erased payload order and equality of root summaries
remain separate contracts. No whole-tree reannotation is executed.
Source and statement assessment: `docs/research/fdsa-tree-rotations.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees.Cached
universe u v
variable {α : Type u} {β : Type v}

def rebuildLeft (empty : β) (combine : β → α → β → β)
    (A : BinaryTree (α × β)) (x : α) (B : BinaryTree (α × β)) (y : α)
    (C : BinaryTree (α × β)) : BinaryTree (α × β) :=
  smartNode empty combine (smartNode empty combine A x B) y C

def rebuildRight (empty : β) (combine : β → α → β → β)
    (A : BinaryTree (α × β)) (x : α) (B : BinaryTree (α × β)) (y : α)
    (C : BinaryTree (α × β)) : BinaryTree (α × β) :=
  smartNode empty combine A x (smartNode empty combine B y C)

@[simp] theorem read_rebuildLeft (empty : β) (combine : β → α → β → β)
    (A : BinaryTree (α × β)) (x : α) (B : BinaryTree (α × β)) (y : α)
    (C : BinaryTree (α × β)) :
    read empty (rebuildLeft empty combine A x B y C) =
      combine (combine (read empty A) x (read empty B)) y (read empty C) := rfl

@[simp] theorem read_rebuildRight (empty : β) (combine : β → α → β → β)
    (A : BinaryTree (α × β)) (x : α) (B : BinaryTree (α × β)) (y : α)
    (C : BinaryTree (α × β)) :
    read empty (rebuildRight empty combine A x B y C) =
      combine (read empty A) x (combine (read empty B) y (read empty C)) := rfl

@[simp] theorem erase_rebuildLeft (empty : β) (combine : β → α → β → β)
    (A : BinaryTree (α × β)) (x : α) (B : BinaryTree (α × β)) (y : α)
    (C : BinaryTree (α × β)) :
    erase (rebuildLeft empty combine A x B y C) =
      .node y (.node x (erase A) (erase B)) (erase C) := rfl

@[simp] theorem erase_rebuildRight (empty : β) (combine : β → α → β → β)
    (A : BinaryTree (α × β)) (x : α) (B : BinaryTree (α × β)) (y : α)
    (C : BinaryTree (α × β)) :
    erase (rebuildRight empty combine A x B y C) =
      .node x (erase A) (.node y (erase B) (erase C)) := rfl

/-- Repairing the two roots is equivalent to validity of every retained fringe. -/
@[simp] theorem rebuildLeft_valid_iff (empty : β) (combine : β → α → β → β)
    (A : BinaryTree (α × β)) (x : α) (B : BinaryTree (α × β)) (y : α)
    (C : BinaryTree (α × β)) :
    Valid empty combine (rebuildLeft empty combine A x B y C) ↔
      Valid empty combine A ∧ Valid empty combine B ∧ Valid empty combine C := by
  simp only [rebuildLeft, smartNode_valid_iff, and_assoc]

@[simp] theorem rebuildRight_valid_iff (empty : β) (combine : β → α → β → β)
    (A : BinaryTree (α × β)) (x : α) (B : BinaryTree (α × β)) (y : α)
    (C : BinaryTree (α × β)) :
    Valid empty combine (rebuildRight empty combine A x B y C) ↔
      Valid empty combine A ∧ Valid empty combine B ∧ Valid empty combine C := by
  simp only [rebuildRight, smartNode_valid_iff]

theorem rotateLeft?_erase_rebuildRight (empty : β) (combine : β → α → β → β)
    (A : BinaryTree (α × β)) (x : α) (B : BinaryTree (α × β)) (y : α)
    (C : BinaryTree (α × β)) :
    Trees.rotateLeft? (erase (rebuildRight empty combine A x B y C)) =
      some (erase (rebuildLeft empty combine A x B y C)) := rfl

theorem rotateRight?_erase_rebuildLeft (empty : β) (combine : β → α → β → β)
    (A : BinaryTree (α × β)) (x : α) (B : BinaryTree (α × β)) (y : α)
    (C : BinaryTree (α × β)) :
    Trees.rotateRight? (erase (rebuildLeft empty combine A x B y C)) =
      some (erase (rebuildRight empty combine A x B y C)) := rfl

theorem inorder_erase_rebuildLeft (empty : β) (combine : β → α → β → β)
    (A : BinaryTree (α × β)) (x : α) (B : BinaryTree (α × β)) (y : α)
    (C : BinaryTree (α × β)) :
    Trees.inorder (erase (rebuildLeft empty combine A x B y C)) =
      Trees.inorder (erase A) ++
        (x :: (Trees.inorder (erase B) ++ (y :: Trees.inorder (erase C)))) := by
  simp only [erase_rebuildLeft, Trees.inorder_node, List.append_assoc, List.cons_append]

theorem inorder_erase_rebuildRight (empty : β) (combine : β → α → β → β)
    (A : BinaryTree (α × β)) (x : α) (B : BinaryTree (α × β)) (y : α)
    (C : BinaryTree (α × β)) :
    Trees.inorder (erase (rebuildRight empty combine A x B y C)) =
      Trees.inorder (erase A) ++
        (x :: (Trees.inorder (erase B) ++ (y :: Trees.inorder (erase C)))) := by
  simp only [erase_rebuildRight, Trees.inorder_node]

/-- Payload order agrees even though the two sets of stored annotations may differ. -/
theorem inorder_erase_rebuildLeft_eq_rebuildRight (empty : β)
    (combine : β → α → β → β)
    (A : BinaryTree (α × β)) (x : α) (B : BinaryTree (α × β)) (y : α)
    (C : BinaryTree (α × β)) :
    Trees.inorder (erase (rebuildLeft empty combine A x B y C)) =
      Trees.inorder (erase (rebuildRight empty combine A x B y C)) :=
  Trees.inorder_of_rotateLeft? _ _
    (rotateLeft?_erase_rebuildRight empty combine A x B y C)

theorem read_rebuildLeft_eq_fold (empty : β) (combine : β → α → β → β)
    (A : BinaryTree (α × β)) (x : α) (B : BinaryTree (α × β)) (y : α)
    (C : BinaryTree (α × β))
    (hA : Valid empty combine A) (hB : Valid empty combine B)
    (hC : Valid empty combine C) :
    read empty (rebuildLeft empty combine A x B y C) =
      Trees.fold empty combine (.node y (.node x (erase A) (erase B)) (erase C)) := by
  simpa only [erase_rebuildLeft] using
    read_eq_fold empty combine _
      ((rebuildLeft_valid_iff empty combine A x B y C).2 ⟨hA, hB, hC⟩)

theorem read_rebuildRight_eq_fold (empty : β) (combine : β → α → β → β)
    (A : BinaryTree (α × β)) (x : α) (B : BinaryTree (α × β)) (y : α)
    (C : BinaryTree (α × β))
    (hA : Valid empty combine A) (hB : Valid empty combine B)
    (hC : Valid empty combine C) :
    read empty (rebuildRight empty combine A x B y C) =
      Trees.fold empty combine (.node x (erase A) (.node y (erase B) (erase C))) := by
  simpa only [erase_rebuildRight] using
    read_eq_fold empty combine _
      ((rebuildRight_valid_iff empty combine A x B y C).2 ⟨hA, hB, hC⟩)

/-- Summary agreement needs only this equation at the actual cached fringe reads.
It is not a claim that a discarded old root annotation was correct. -/
theorem read_rebuildLeft_eq_read_rebuildRight (empty : β)
    (combine : β → α → β → β)
    (A : BinaryTree (α × β)) (x : α) (B : BinaryTree (α × β)) (y : α)
    (C : BinaryTree (α × β))
    (hassoc : combine (read empty A) x (combine (read empty B) y (read empty C)) =
      combine (combine (read empty A) x (read empty B)) y (read empty C)) :
    read empty (rebuildLeft empty combine A x B y C) =
      read empty (rebuildRight empty combine A x B y C) :=
  hassoc.symm

end Trees.Cached

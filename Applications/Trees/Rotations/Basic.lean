import Applications.Trees.BasicObservations
import Applications.Trees.Direction

/-!
# Legal root rotations and the listification measure

The source equations have a domain. `none` marks a root whose shape does not
permit the chosen rotation; no default label or identity completion is used.
The common tree and inorder observations retain repeated, arbitrary labels.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees.Rotations
universe u
variable {α : Type u}

/-- Rotate a nonempty left child to the root, or report an illegal root step. -/
def rotateRight? : BinaryTree α → Option (BinaryTree α)
  | .node b (.node a A B) C => some (.node a A (.node b B C))
  | _ => none

/-- The opposite legal root step requires a nonempty right child. -/
def rotateLeft? : BinaryTree α → Option (BinaryTree α)
  | .node a A (.node b B C) => some (.node b (.node a A B) C)
  | _ => none

@[simp] theorem rotateRight?_node (a b : α) (A B C : BinaryTree α) :
    rotateRight? (.node b (.node a A B) C) = some (.node a A (.node b B C)) := rfl

@[simp] theorem rotateLeft?_node (a b : α) (A B C : BinaryTree α) :
    rotateLeft? (.node a A (.node b B C)) = some (.node b (.node a A B) C) := rfl

theorem rotateRight?_eq_some_iff (t s : BinaryTree α) :
    rotateRight? t = some s ↔ ∃ a b A B C,
      t = .node b (.node a A B) C ∧ s = .node a A (.node b B C) := by
  constructor
  · intro h
    cases t with
    | nil => simp [rotateRight?] at h
    | node b l C =>
        cases l with
        | nil => simp [rotateRight?] at h
        | node a A B =>
            cases h
            exact ⟨a, b, A, B, C, rfl, rfl⟩
  · rintro ⟨a, b, A, B, C, rfl, rfl⟩
    rfl

theorem rotateLeft?_eq_some_iff (t s : BinaryTree α) :
    rotateLeft? t = some s ↔ ∃ a b A B C,
      t = .node a A (.node b B C) ∧ s = .node b (.node a A B) C := by
  constructor
  · intro h
    cases t with
    | nil => simp [rotateLeft?] at h
    | node a A r =>
        cases r with
        | nil => simp [rotateLeft?] at h
        | node b B C =>
            cases h
            exact ⟨a, b, A, B, C, rfl, rfl⟩
  · rintro ⟨a, b, A, B, C, rfl, rfl⟩
    rfl

theorem rotateLeft?_undo {t s : BinaryTree α} (h : rotateRight? t = some s) :
    rotateLeft? s = some t := by
  obtain ⟨a, b, A, B, C, rfl, rfl⟩ := (rotateRight?_eq_some_iff t s).mp h
  rfl

theorem rotateRight?_undo {t s : BinaryTree α} (h : rotateLeft? t = some s) :
    rotateRight? s = some t := by
  obtain ⟨a, b, A, B, C, rfl, rfl⟩ := (rotateLeft?_eq_some_iff t s).mp h
  rfl

theorem rotateRight?_inorder {t s : BinaryTree α} (h : rotateRight? t = some s) :
    inorder s = inorder t := by
  obtain ⟨a, b, A, B, C, rfl, rfl⟩ := (rotateRight?_eq_some_iff t s).mp h
  simp only [inorder_node, List.append_assoc, List.cons_append]

theorem rotateLeft?_inorder {t s : BinaryTree α} (h : rotateLeft? t = some s) :
    inorder s = inorder t := (rotateRight?_inorder (rotateRight?_undo h)).symm

theorem numNodes_eq_of_inorder_eq {s t : BinaryTree α} (h : inorder s = inorder t) :
    s.numNodes = t.numNodes := by
  simpa only [inorder_length] using congrArg List.length h

theorem setTree_eq_of_inorder_eq {s t : BinaryTree α} (h : inorder s = inorder t) :
    setTree s = setTree t := by
  ext x
  simp only [← mem_inorder_iff_mem_setTree, h]

theorem rotateRight?_numNodes {t s : BinaryTree α} (h : rotateRight? t = some s) :
    s.numNodes = t.numNodes := numNodes_eq_of_inorder_eq (rotateRight?_inorder h)

theorem rotateLeft?_numNodes {t s : BinaryTree α} (h : rotateLeft? t = some s) :
    s.numNodes = t.numNodes := numNodes_eq_of_inorder_eq (rotateLeft?_inorder h)

theorem rotateRight?_setTree {t s : BinaryTree α} (h : rotateRight? t = some s) :
    setTree s = setTree t := setTree_eq_of_inorder_eq (rotateRight?_inorder h)

theorem rotateLeft?_setTree {t s : BinaryTree α} (h : rotateLeft? t = some s) :
    setTree s = setTree t := setTree_eq_of_inorder_eq (rotateLeft?_inorder h)

/-- A right spine, including the empty tree; the labels need no equality test. -/
def IsList : BinaryTree α → Prop
  | .nil => True
  | .node _ l r => l = .nil ∧ IsList r

instance instDecidableIsList : (t : BinaryTree α) → Decidable (IsList t)
  | .nil => isTrue True.intro
  | .node _ .nil r =>
      match instDecidableIsList r with
      | isTrue h => isTrue ⟨rfl, h⟩
      | isFalse h => isFalse (fun hl => h hl.2)
  | .node _ (.node _ _ _) _ => isFalse (by intro h; cases h.1)

@[simp] theorem isList_nil : IsList (.nil : BinaryTree α) := True.intro

@[simp] theorem isList_node (a : α) (l r : BinaryTree α) :
    IsList (.node a l r) ↔ l = .nil ∧ IsList r := Iff.rfl

/-- The number of node occurrences on the right spine, independent of labels. -/
def rightLength : BinaryTree α → Nat
  | .nil => 0
  | .node _ _ r => rightLength r + 1

@[simp] theorem rightLength_nil : rightLength (.nil : BinaryTree α) = 0 := rfl

@[simp] theorem rightLength_node (a : α) (l r : BinaryTree α) :
    rightLength (.node a l r) = rightLength r + 1 := rfl

theorem rightLength_le_numNodes (t : BinaryTree α) : rightLength t ≤ t.numNodes := by
  induction t with
  | nil => rfl
  | node a l r _ ihr =>
      simp only [rightLength_node, BinaryTree.numNodes]
      omega

theorem rightLength_eq_numNodes {t : BinaryTree α} (h : IsList t) :
    rightLength t = t.numNodes := by
  induction t with
  | nil => rfl
  | node a l r _ ihr =>
      rcases h with ⟨rfl, hr⟩
      simp only [rightLength_node, BinaryTree.numNodes, Nat.zero_add, ihr hr]

/-- This measure decreases both when rotating and when descending the spine. -/
def measure (t : BinaryTree α) : Nat := 2 * t.numNodes - rightLength t

theorem measure_rotate (a b : α) (A B C : BinaryTree α) :
    measure (.node a A (.node b B C)) < measure (.node b (.node a A B) C) := by
  have h := rightLength_le_numNodes C
  simp only [measure, rightLength_node, BinaryTree.numNodes]
  omega

theorem measure_descend (a : α) (r : BinaryTree α) :
    measure r < measure (.node a .nil r) := by
  have h := rightLength_le_numNodes r
  simp only [measure, rightLength_node, BinaryTree.numNodes]
  omega

/-- The tempting smaller expression is equal, not smaller, on spine descent. -/
theorem deficit_descend (a : α) (r : BinaryTree α) :
    (BinaryTree.node a .nil r).numNodes - rightLength (.node a .nil r) =
      r.numNodes - rightLength r := by
  simp only [BinaryTree.numNodes, rightLength_node]
  omega

theorem rotateRight?_rightLength {t s : BinaryTree α} (h : rotateRight? t = some s) :
    rightLength s = rightLength t + 1 := by
  obtain ⟨a, b, A, B, C, rfl, rfl⟩ := (rotateRight?_eq_some_iff t s).mp h
  rfl

end Trees.Rotations

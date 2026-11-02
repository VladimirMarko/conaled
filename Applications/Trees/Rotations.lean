import Applications.Trees.Observations

/-! Single root rotations on the existing node-labelled tree. Failure records a
missing pivot explicitly. Ordered observations and conditional fold preservation
are separate from balance, cache correctness and execution costs.
Source and statement assessment: `docs/research/fdsa-tree-rotations.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees
universe u v
variable {α : Type u} {β : Type v}

/-- Rotate a root with a nonempty right child; other shapes have no such rotation. -/
def rotateLeft? : BinaryTree α → Option (BinaryTree α)
  | .node x A (.node y B C) => some (.node y (.node x A B) C)
  | _ => none

/-- Rotate a root with a nonempty left child; other shapes have no such rotation. -/
def rotateRight? : BinaryTree α → Option (BinaryTree α)
  | .node y (.node x A B) C => some (.node x A (.node y B C))
  | _ => none

@[simp] theorem rotateLeft?_nil : rotateLeft? (.nil : BinaryTree α) = none := rfl

@[simp] theorem rotateLeft?_node_nil (A : BinaryTree α) (x : α) :
    rotateLeft? (.node x A .nil) = none := rfl

@[simp] theorem rotateLeft?_node_node (A : BinaryTree α) (x : α)
    (B : BinaryTree α) (y : α) (C : BinaryTree α) :
    rotateLeft? (.node x A (.node y B C)) = some (.node y (.node x A B) C) := rfl

@[simp] theorem rotateRight?_nil : rotateRight? (.nil : BinaryTree α) = none := rfl

@[simp] theorem rotateRight?_nil_node (y : α) (C : BinaryTree α) :
    rotateRight? (.node y .nil C) = none := rfl

@[simp] theorem rotateRight?_node_node (A : BinaryTree α) (x : α)
    (B : BinaryTree α) (y : α) (C : BinaryTree α) :
    rotateRight? (.node y (.node x A B) C) = some (.node x A (.node y B C)) := rfl

theorem rotateLeft?_eq_none_iff (t : BinaryTree α) :
    rotateLeft? t = none ↔ t = .nil ∨ ∃ x A, t = .node x A .nil := by
  cases t with
  | nil => simp [rotateLeft?]
  | node x A r =>
      cases r with
      | nil => simp [rotateLeft?]
      | node y B C => simp [rotateLeft?]

theorem rotateRight?_eq_none_iff (t : BinaryTree α) :
    rotateRight? t = none ↔ t = .nil ∨ ∃ y C, t = .node y .nil C := by
  cases t with
  | nil => simp [rotateRight?]
  | node y l C =>
      cases l with
      | nil => simp [rotateRight?]
      | node x A B => simp [rotateRight?]

/-- The inverse is a claim about a successful rotation, including its actual result. -/
theorem rotateRight?_of_rotateLeft? (t t' : BinaryTree α)
    (h : rotateLeft? t = some t') : rotateRight? t' = some t := by
  cases t with
  | nil => simp [rotateLeft?] at h
  | node x A r =>
      cases r with
      | nil => simp [rotateLeft?] at h
      | node y B C =>
          cases Option.some.inj h
          rfl

theorem rotateLeft?_of_rotateRight? (t t' : BinaryTree α)
    (h : rotateRight? t = some t') : rotateLeft? t' = some t := by
  cases t with
  | nil => simp [rotateRight?] at h
  | node y l C =>
      cases l with
      | nil => simp [rotateRight?] at h
      | node x A B =>
          cases Option.some.inj h
          rfl

/-- Rotation preserves every label occurrence and its order, without an order on labels. -/
theorem inorder_of_rotateLeft? (t t' : BinaryTree α)
    (h : rotateLeft? t = some t') : inorder t' = inorder t := by
  cases t with
  | nil => simp [rotateLeft?] at h
  | node x A r =>
      cases r with
      | nil => simp [rotateLeft?] at h
      | node y B C =>
          cases Option.some.inj h
          simp only [inorder_node, List.append_assoc, List.cons_append]

theorem inorder_of_rotateRight? (t t' : BinaryTree α)
    (h : rotateRight? t = some t') : inorder t' = inorder t :=
  (inorder_of_rotateLeft? t' t (rotateLeft?_of_rotateRight? t t' h)).symm

theorem numNodes_of_rotateLeft? (t t' : BinaryTree α)
    (h : rotateLeft? t = some t') : t'.numNodes = t.numNodes := by
  simpa only [inorder_length] using congrArg List.length (inorder_of_rotateLeft? t t' h)

theorem numNodes_of_rotateRight? (t t' : BinaryTree α)
    (h : rotateRight? t = some t') : t'.numNodes = t.numNodes := by
  simpa only [inorder_length] using congrArg List.length (inorder_of_rotateRight? t t' h)

theorem numLeaves_of_rotateLeft? (t t' : BinaryTree α)
    (h : rotateLeft? t = some t') : t'.numLeaves = t.numLeaves := by
  rw [BinaryTree.numLeaves_eq_numNodes_succ, BinaryTree.numLeaves_eq_numNodes_succ,
    numNodes_of_rotateLeft? t t' h]

theorem numLeaves_of_rotateRight? (t t' : BinaryTree α)
    (h : rotateRight? t = some t') : t'.numLeaves = t.numLeaves := by
  rw [BinaryTree.numLeaves_eq_numNodes_succ, BinaryTree.numLeaves_eq_numNodes_succ,
    numNodes_of_rotateRight? t t' h]

/-- Every label map commutes with the operation, including failure and noninjective maps. -/
theorem map_rotateLeft? (label : α → β) (t : BinaryTree α) :
    Option.map (BinaryTree.map label) (rotateLeft? t) = rotateLeft? (t.map label) := by
  cases t with
  | nil => rfl
  | node x A r =>
      cases r with
      | nil => rfl
      | node y B C => rfl

theorem map_rotateRight? (label : α → β) (t : BinaryTree α) :
    Option.map (BinaryTree.map label) (rotateRight? t) = rotateRight? (t.map label) := by
  cases t with
  | nil => rfl
  | node y l C =>
      cases l with
      | nil => rfl
      | node x A B => rfl

/-- Only the reassociation equation at these actual three fringe folds is needed. -/
theorem fold_rotateLeft (empty : β) (combine : β → α → β → β)
    (A : BinaryTree α) (x : α) (B : BinaryTree α) (y : α) (C : BinaryTree α)
    (hassoc : combine (fold empty combine A) x
        (combine (fold empty combine B) y (fold empty combine C)) =
      combine (combine (fold empty combine A) x (fold empty combine B)) y
        (fold empty combine C)) :
    fold empty combine (.node y (.node x A B) C) =
      fold empty combine (.node x A (.node y B C)) :=
  hassoc.symm

theorem fold_rotateRight (empty : β) (combine : β → α → β → β)
    (A : BinaryTree α) (x : α) (B : BinaryTree α) (y : α) (C : BinaryTree α)
    (hassoc : combine (fold empty combine A) x
        (combine (fold empty combine B) y (fold empty combine C)) =
      combine (combine (fold empty combine A) x (fold empty combine B)) y
        (fold empty combine C)) :
    fold empty combine (.node x A (.node y B C)) =
      fold empty combine (.node y (.node x A B) C) :=
  hassoc

/-- A uniform algebra law is a sufficient convenience, separate from the weaker local rule. -/
theorem fold_of_rotateLeft? (empty : β) (combine : β → α → β → β)
    (hassoc : ∀ (a : β) (x : α) (b : β) (y : α) (c : β),
      combine a x (combine b y c) = combine (combine a x b) y c)
    (t t' : BinaryTree α) (h : rotateLeft? t = some t') :
    fold empty combine t' = fold empty combine t := by
  cases t with
  | nil => simp [rotateLeft?] at h
  | node x A r =>
      cases r with
      | nil => simp [rotateLeft?] at h
      | node y B C =>
          cases Option.some.inj h
          exact fold_rotateLeft empty combine A x B y C (hassoc _ _ _ _ _)

theorem fold_of_rotateRight? (empty : β) (combine : β → α → β → β)
    (hassoc : ∀ (a : β) (x : α) (b : β) (y : α) (c : β),
      combine a x (combine b y c) = combine (combine a x b) y c)
    (t t' : BinaryTree α) (h : rotateRight? t = some t') :
    fold empty combine t' = fold empty combine t :=
  (fold_of_rotateLeft? empty combine hassoc t' t
    (rotateLeft?_of_rotateRight? t t' h)).symm

end Trees

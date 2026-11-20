import Applications.Trees.Rotations.Position

/-!
# The three source recursions

Each function actually recurses on the rotated tree when the left child is
nonempty. Descending an empty-left root contributes no rotation. The resulting
tree, emitted position schedule and charged count are separate definitions;
their agreement is proved below, not imposed by their definitions.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees.Rotations
open Search.SharedTree (Branch)
universe u
variable {α : Type u}

/-- Root-rotate until the root has no left child, then normalize its right child. -/
def listOf : BinaryTree α → BinaryTree α
  | .nil => .nil
  | .node a .nil r => .node a .nil (listOf r)
  | .node b (.node a A B) C => listOf (.node a A (.node b B C))
termination_by t => measure t
decreasing_by
  all_goals first | apply measure_descend | apply measure_rotate

/-- Record each actual root rotation; lift the recursive schedule on descent. -/
def rightPositions : BinaryTree α → List (List Branch)
  | .nil => []
  | .node _ .nil r => (rightPositions r).map (Branch.right :: ·)
  | .node b (.node a A B) C => [] :: rightPositions (.node a A (.node b B C))
termination_by t => measure t
decreasing_by
  all_goals first | apply measure_descend | apply measure_rotate

/-- Charge one only for a rotation, independently of both the schedule and formula. -/
def countRots : BinaryTree α → Nat
  | .nil => 0
  | .node _ .nil r => countRots r
  | .node b (.node a A B) C => 1 + countRots (.node a A (.node b B C))
termination_by t => measure t
decreasing_by
  all_goals first | apply measure_descend | apply measure_rotate

@[simp] theorem listOf_nil : listOf (.nil : BinaryTree α) = .nil := by rw [listOf]

@[simp] theorem listOf_descend (a : α) (r : BinaryTree α) :
    listOf (.node a .nil r) = .node a .nil (listOf r) := by rw [listOf]

@[simp] theorem listOf_rotate (a b : α) (A B C : BinaryTree α) :
    listOf (.node b (.node a A B) C) = listOf (.node a A (.node b B C)) := by rw [listOf]

@[simp] theorem rightPositions_nil : rightPositions (.nil : BinaryTree α) = [] := by
  rw [rightPositions]

@[simp] theorem rightPositions_descend (a : α) (r : BinaryTree α) :
    rightPositions (.node a .nil r) = (rightPositions r).map (Branch.right :: ·) := by
  rw [rightPositions]

@[simp] theorem rightPositions_rotate (a b : α) (A B C : BinaryTree α) :
    rightPositions (.node b (.node a A B) C) = [] :: rightPositions (.node a A (.node b B C)) := by
  rw [rightPositions]

@[simp] theorem countRots_nil : countRots (.nil : BinaryTree α) = 0 := by rw [countRots]

@[simp] theorem countRots_descend (a : α) (r : BinaryTree α) :
    countRots (.node a .nil r) = countRots r := by rw [countRots]

@[simp] theorem countRots_rotate (a b : α) (A B C : BinaryTree α) :
    countRots (.node b (.node a A B) C) = 1 + countRots (.node a A (.node b B C)) := by
  rw [countRots]

theorem listOf_isList (t : BinaryTree α) : IsList (listOf t) := by
  induction t using listOf.induct with
  | case1 => simpa only [listOf_nil] using (isList_nil (α := α))
  | case2 a r ih => rw [listOf_descend]; exact ⟨rfl, ih⟩
  | case3 b a A B C ih => simpa only [listOf_rotate] using ih

theorem listOf_inorder (t : BinaryTree α) : inorder (listOf t) = inorder t := by
  induction t using listOf.induct with
  | case1 => rw [listOf_nil]
  | case2 a r ih => simp only [listOf_descend, inorder_node, ih]
  | case3 b a A B C ih =>
      rw [listOf_rotate, ih]
      exact rotateRight?_inorder rfl

/-- In particular every position is legal when reached in the emitted schedule. -/
theorem apply_rightPositions (t : BinaryTree α) :
    applyAts? rotateRight? (rightPositions t) t = some (listOf t) := by
  induction t using rightPositions.induct with
  | case1 => rw [rightPositions_nil, applyAts?_nil, listOf_nil]
  | case2 a r ih =>
      rw [rightPositions_descend, applyAts?_map_right, ih, listOf_descend]
      rfl
  | case3 b a A B C ih =>
      simpa only [rightPositions_rotate, listOf_rotate, applyAts?_cons,
        applyAt?_root, rotateRight?_node, Option.bind_some] using ih

theorem rightPositions_length (t : BinaryTree α) :
    (rightPositions t).length = t.numNodes - rightLength t := by
  induction t using rightPositions.induct with
  | case1 => rw [rightPositions_nil]; rfl
  | case2 a r ih =>
      rw [rightPositions_descend, List.length_map, ih]
      exact (deficit_descend a r).symm
  | case3 b a A B C ih =>
      rw [rightPositions_rotate, List.length_cons, ih]
      have h := rightLength_le_numNodes C
      simp only [BinaryTree.numNodes, rightLength_node]
      omega

theorem countRots_eq_deficit (t : BinaryTree α) :
    countRots t = t.numNodes - rightLength t := by
  induction t using countRots.induct with
  | case1 => rw [countRots_nil]; rfl
  | case2 a r ih =>
      rw [countRots_descend, ih]
      exact (deficit_descend a r).symm
  | case3 b a A B C ih =>
      rw [countRots_rotate, ih]
      have h := rightLength_le_numNodes C
      simp only [BinaryTree.numNodes, rightLength_node]
      omega

theorem countRots_eq_length (t : BinaryTree α) :
    countRots t = (rightPositions t).length := by
  rw [countRots_eq_deficit, rightPositions_length]

end Trees.Rotations

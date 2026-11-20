import Applications.Trees.Join
import Applications.Trees.Shape

/-!
# Sharp structural bounds for the two joins

These bounds hold without order, distinctness, or balance premises. The
complete-input equality includes nil and unequal heights. Its root-elimination
corollary states exactly when the simpler join can increase height.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees
universe u
variable {α : Type u}

theorem height_join_le (l r : BinaryTree α) :
    (join l r).height ≤ max l.height r.height + 1 := by
  induction l generalizing r with
  | nil => simp [BinaryTree.height]
  | node a l m _ ihm =>
      cases r with
      | nil => simp [BinaryTree.height]
      | node b n r =>
          have ih := ihm n
          cases h : join m n with
          | nil =>
              rw [join_node_node, h]
              simp only [BinaryTree.height]
              omega
          | node x p q =>
              rw [h] at ih
              rw [join_node_node, h]
              simp only [BinaryTree.height] at ih ⊢
              omega

theorem height_join0_le (l r : BinaryTree α) :
    (join0 l r).height ≤ l.height + r.height := by
  induction l generalizing r with
  | nil => simp [BinaryTree.height]
  | node a l m _ ihm =>
      cases r with
      | nil => simp [BinaryTree.height]
      | node b n r =>
          have ih := ihm n
          rw [join0_node_node]
          simp only [BinaryTree.height]
          omega

theorem height_join0_of_complete (l r : BinaryTree α) :
    Complete l → Complete r → (join0 l r).height = l.height + r.height := by
  induction l generalizing r with
  | nil => intro _ _; simp [BinaryTree.height]
  | node a l m _ ihm =>
      intro hl hr
      cases r with
      | nil => simp [BinaryTree.height]
      | node b n r =>
          have ih := ihm n hl.2.2 hr.2.1
          have hleft := hl.1
          have hright := hr.1
          rw [join0_node_node]
          simp only [BinaryTree.height]
          omega

/-- Equal-height complete children expose the exact root-elimination change.
The statement includes height zero rather than hiding Nat boundary cases. -/
theorem join0_root_heights (a : α) (l r : BinaryTree α) (k : Nat)
    (hl : Complete l) (hr : Complete r) (hlk : l.height = k) (hrk : r.height = k) :
    (BinaryTree.node a l r).height = k + 1 ∧ (join0 l r).height = 2 * k := by
  constructor
  · simp [BinaryTree.height, hlk, hrk]
  · rw [height_join0_of_complete l r hl hr, hlk, hrk]
    omega

theorem join0_root_height_increases_iff (a : α) (l r : BinaryTree α) (k : Nat)
    (hl : Complete l) (hr : Complete r) (hlk : l.height = k) (hrk : r.height = k) :
    (BinaryTree.node a l r).height < (join0 l r).height ↔ 1 < k := by
  have heights := join0_root_heights a l r k hl hr hlk hrk
  rw [heights.1, heights.2]
  omega

end Trees

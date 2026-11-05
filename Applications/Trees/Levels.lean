import Applications.Trees.Observations

/-! Ordered levels of a finite binary tree. The level-by-level collector visits
each tree structurally once and merges the already collected child levels.
Appending lists within that merge has its usual cost; no total-time bound is
claimed here. The collector itself has no depth argument or arithmetic.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees
universe u
variable {α : Type u}

/-- The ordered labels at the requested depth, with repeated labels retained. -/
def level : BinaryTree α → Nat → List α
  | .nil, _ => []
  | .node a _ _, 0 => [a]
  | .node _ l r, k + 1 => level l k ++ level r k

@[simp] theorem level_nil (k : Nat) : level (.nil : BinaryTree α) k = [] := rfl

@[simp] theorem level_node_zero (a : α) (l r : BinaryTree α) :
    level (.node a l r) 0 = [a] := rfl

@[simp] theorem level_node_succ (a : α) (l r : BinaryTree α) (k : Nat) :
    level (.node a l r) (k + 1) = level l k ++ level r k := rfl

/-- Append corresponding levels, keeping an unmatched suffix from either side. -/
def mergeLevels : List (List α) → List (List α) → List (List α)
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x ++ y) :: mergeLevels xs ys

/-- Collect all levels by one structural traversal of the input tree. -/
def levels : BinaryTree α → List (List α)
  | .nil => []
  | .node a l r => [a] :: mergeLevels (levels l) (levels r)

@[simp] theorem levels_nil : levels (.nil : BinaryTree α) = [] := rfl

@[simp] theorem levels_node (a : α) (l r : BinaryTree α) :
    levels (.node a l r) = [a] :: mergeLevels (levels l) (levels r) := rfl

theorem mergeLevels_length (xs ys : List (List α)) :
    (mergeLevels xs ys).length = max xs.length ys.length := by
  induction xs generalizing ys with
  | nil => simp [mergeLevels]
  | cons x xs ih =>
      cases ys with
      | nil => simp [mergeLevels]
      | cons y ys => simp [mergeLevels, ih, Nat.succ_max_succ]

/-- Missing levels on either side contribute the empty list. -/
theorem mergeLevels_getD (xs ys : List (List α)) (k : Nat) :
    (mergeLevels xs ys).getD k [] = xs.getD k [] ++ ys.getD k [] := by
  induction xs generalizing ys k with
  | nil => simp [mergeLevels]
  | cons x xs ih =>
      cases ys with
      | nil => simp [mergeLevels]
      | cons y ys =>
          cases k with
          | zero => simp [mergeLevels, List.getD_cons_zero]
          | succ k => simp [mergeLevels, List.getD_cons_succ, ih]

theorem levels_length (t : BinaryTree α) : (levels t).length = t.height := by
  induction t with
  | nil => rfl
  | node a l r ihl ihr =>
      simp [levels_node, mergeLevels_length, ihl, ihr, BinaryTree.height]

/-- An index beyond the collected levels has the same empty result as `level`. -/
theorem levels_getD (t : BinaryTree α) (k : Nat) :
    (levels t).getD k [] = level t k := by
  induction t generalizing k with
  | nil => simp [levels, level]
  | node a l r ihl ihr =>
      cases k with
      | zero => simp [levels, level, List.getD_cons_zero]
      | succ k =>
          simp [levels, level, List.getD_cons_succ, mergeLevels_getD, ihl, ihr]

/-- Within the tree height, the actual list lookup returns the requested level. -/
theorem levels_getElem? (t : BinaryTree α) (k : Nat) (hk : k < t.height) :
    (levels t)[k]? = some (level t k) := by
  have hk' : k < (levels t).length := by simpa only [levels_length] using hk
  rw [List.getElem?_eq_getElem hk']
  apply congrArg some
  have h := levels_getD t k
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk'] using h

end Trees

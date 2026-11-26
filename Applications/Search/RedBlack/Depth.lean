import Applications.Search.RedBlack.Shape
import Applications.Search.RedBlack.Observations
import Batteries.Recycling.RBTree.Depth

/-!
# Source minimum depth and balanced maximum depth

Maximum depth is the provider's existing node-counting depth. Minimum depth
counts the shortest root-to-empty path by the same convention. The bounds are
structural theorems; they make no claim about native timings or allocations.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Search.RedBlack

open RBTree RBTree.RBColor RBTree.RBNode

universe u v
variable {κ : Type u} {ν : Type v}

/-- Source maximum depth, reusing the existing colored-tree observation. -/
abbrev height (t : Tree κ ν) : Nat := t.depth

/-- Number of nodes on a shortest root-to-empty path. -/
def mindepth : Tree κ ν → Nat
  | .nil => 0
  | .node _ l _ r => min (mindepth l) (mindepth r) + 1

@[simp] theorem height_nil : height (.nil : Tree κ ν) = 0 := rfl

theorem height_node (color : RBColor) (l : Tree κ ν) (key : κ) (value : ν)
    (r : Tree κ ν) :
    height (.node color l (key, value) r) = max (height l) (height r) + 1 := rfl

@[simp] theorem mindepth_nil : mindepth (.nil : Tree κ ν) = 0 := rfl

theorem mindepth_node (color : RBColor) (l : Tree κ ν) (key : κ) (value : ν)
    (r : Tree κ ν) :
    mindepth (.node color l (key, value) r) = min (mindepth l) (mindepth r) + 1 := rfl

theorem mindepth_le_height (t : Tree κ ν) : mindepth t ≤ height t := by
  induction t with
  | nil => exact Nat.le_refl _
  | node color l binding r ihl ihr =>
      exact Nat.add_le_add_right
        (Nat.le_trans (Nat.min_le_left _ _)
          (Nat.le_trans ihl (Nat.le_max_left _ _))) 1

/-- Every path contains at least the common black height. -/
theorem RB.black_height_le_mindepth {t : Tree κ ν} {parent : RBColor} {n : Nat}
    (h : RB t parent n) : n ≤ mindepth t := by
  obtain ⟨root, hb⟩ := h.balanced
  clear h
  induction hb with
  | nil => exact Nat.le_refl _
  | red hl hr ihl ihr =>
      exact Nat.le_trans (Nat.le_min.2 ⟨ihl, ihr⟩) (Nat.le_succ _)
  | black hl hr ihl ihr =>
      exact Nat.add_le_add_right (Nat.le_min.2 ⟨ihl, ihr⟩) 1

/-- Either root color permits at most one extra red node beyond twice the height. -/
theorem RB.height_le_twice_black_height_add_one {t : Tree κ ν} {parent : RBColor} {n : Nat}
    (h : RB t parent n) : height t ≤ 2 * n + 1 := by
  obtain ⟨root, h⟩ := h.balanced
  exact Nat.le_trans h.depth_le (RBNode.depthUB_le root n)

/-- A red hypothetical parent forces a black root or nil, removing the extra one. -/
theorem RB.height_le_twice_black_height {t : Tree κ ν} {n : Nat}
    (h : RB t RBColor.red n) : height t ≤ 2 * n :=
  RBNode.Balanced.depth_le h

/-- The source advanced exercise, for either hypothetical parent color. -/
theorem redblack_balanced {t : Tree κ ν} {parent : RBColor} {n : Nat}
    (h : RB t parent n) : height t ≤ 2 * mindepth t + 1 :=
  Nat.le_trans h.height_le_twice_black_height_add_one
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 h.black_height_le_mindepth) 1)

/-- The provider's root-color-sensitive lower bound implies the source one. -/
theorem RB.two_pow_black_height_le_size_add_one {t : Tree κ ν} {parent : RBColor} {n : Nat}
    (h : RB t parent n) : 2 ^ n ≤ t.size + 1 := by
  obtain ⟨root, h⟩ := h.balanced
  exact Nat.le_trans
    (Nat.pow_le_pow_right (by decide) (RBNode.depthLB_le root n)) h.le_size

/-- The actual provider bound includes `size + 1`, including nil and singleton. -/
theorem RB.height_log_bound {t : Tree κ ν} {parent : RBColor} {n : Nat}
    (h : RB t parent n) : height t ≤ 2 * (t.size + 1).log2 := by
  obtain ⟨root, h⟩ := h.balanced
  exact h.depth_bound

/-- The same bound reaches the ordinary tree through the proved erasure observations. -/
theorem RB.erased_height_log_bound {t : Tree κ ν} {parent : RBColor} {n : Nat}
    (h : RB t parent n) :
    BinaryTree.height (eraseColors t) ≤
      2 * (BinaryTree.numNodes (eraseColors t) + 1).log2 := by
  rw [eraseColors_height, eraseColors_numNodes]
  exact h.height_log_bound

end Search.RedBlack

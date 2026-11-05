import Mathlib.Data.Tree.Basic
import Mathlib.Tactic.Ring

/-! Natural weighted path lengths for FDSA Exercise 4.3.
The depth-parameter definition charges each labelled node its weight times
one plus its depth. The independent subtree-sum definition gives the same
value. This correspondence makes no runtime-improvement claim.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees

/-- The sum of all node weights, retaining every occurrence. -/
def sumTree : BinaryTree Nat → Nat
  | .nil => 0
  | .node w l r => sumTree l + w + sumTree r

@[simp] theorem sumTree_nil : sumTree .nil = 0 := rfl

@[simp] theorem sumTree_node (w : Nat) (l r : BinaryTree Nat) :
    sumTree (.node w l r) = sumTree l + w + sumTree r := rfl

/-- Weighted path length with arbitrary incoming depth; the root contributes
`(d + 1) * w`, including its full weight when `d = 0`. -/
def wpld (d : Nat) : BinaryTree Nat → Nat
  | .nil => 0
  | .node w l r => (d + 1) * w + wpld (d + 1) l + wpld (d + 1) r

@[simp] theorem wpld_nil (d : Nat) : wpld d .nil = 0 := rfl

@[simp] theorem wpld_node (d w : Nat) (l r : BinaryTree Nat) :
    wpld d (.node w l r) =
      (d + 1) * w + wpld (d + 1) l + wpld (d + 1) r := rfl

/-- Start the depth-parameter definition at root depth zero. -/
def wpl0 (t : BinaryTree Nat) : Nat := wpld 0 t

/-- Independent recurrence summing the weight of each whole rooted subtree. -/
def wpl : BinaryTree Nat → Nat
  | .nil => 0
  | .node w l r => sumTree (.node w l r) + wpl l + wpl r

@[simp] theorem wpl_nil : wpl .nil = 0 := rfl

@[simp] theorem wpl_node (w : Nat) (l r : BinaryTree Nat) :
    wpl (.node w l r) = sumTree (.node w l r) + wpl l + wpl r := rfl

/-- Raising the incoming depth by `d` adds `d` copies of the total weight.
The invariant is universal in depth, including every recursive child call. -/
theorem wpld_eq_offset (d : Nat) (t : BinaryTree Nat) :
    wpld d t = d * sumTree t + wpl t := by
  induction t generalizing d with
  | nil => simp
  | node w l r ihl ihr =>
      simp only [wpld_node, ihl, ihr, wpl_node, sumTree_node]
      ring

/-- The two definitions in Exercise 4.3 agree on every natural-weight tree. -/
theorem wpl0_eq_wpl (t : BinaryTree Nat) : wpl0 t = wpl t := by
  simpa only [wpl0, Nat.zero_mul, Nat.zero_add] using wpld_eq_offset 0 t

end Trees

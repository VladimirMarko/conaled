import Mathlib.Data.List.Basic

/-! Ordered rose trees and their mirror operation. Every node has a label and a
finite ordered list of children. Mirroring visits every descendant and reverses
the child order at every node; it does not require equality or a default label.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees
universe u

/-- A finite labelled tree with an ordered list of children at each node. -/
inductive Rose (α : Type u) where
  | node (label : α) (children : List (Rose α))

namespace Rose
variable {α : Type u}

/-- Mirror the descendants, then reverse their order. Membership attached to
each child witnesses the strict decrease needed for nested recursion. -/
def mirror (t : Rose α) : Rose α :=
  match t with
  | .node a children =>
      .node a ((children.attach.map fun child => mirror child.val).reverse)
termination_by sizeOf t
decreasing_by
  exact Nat.lt_trans (List.sizeOf_lt_of_mem child.property) (by simp +arith)

@[simp] theorem mirror_node (a : α) (children : List (Rose α)) :
    mirror (.node a children) = .node a ((children.map mirror).reverse) := by
  rw [mirror, List.attach_map_val]

/-- Nested induction over all descendants proves that mirroring is involutive. -/
theorem mirror_mirror (t : Rose α) : mirror (mirror t) = t := by
  refine (measure sizeOf).wf.induction t ?_
  intro t ih
  cases t with
  | node a children =>
      rw [mirror_node, mirror_node, List.map_reverse, List.reverse_reverse,
        List.map_map]
      apply congrArg (Rose.node a)
      calc
        children.map (mirror ∘ mirror) = children.map id := by
          apply List.map_congr_left
          intro child hchild
          exact ih child
            (Nat.lt_trans (List.sizeOf_lt_of_mem hchild) (by simp +arith))
        _ = children := List.map_id children

end Rose
end Trees

import Applications.Trees.Cached
import Applications.Resources.CallCount

/-! A declared local-access observation for cached tree construction.
Each root read and the constructor entry costs one. The actual combining
callback supplies its own observation. This differs from the source leftist
heap's selective tariff, which charges its auxiliary reader/constructor zero.
There is no claim about allocation, machine arithmetic or a full-tree traversal.
Source and statement assessment: `docs/research/fdsa-tree-cache.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.TreeCache
universe u v
variable {α : Type u} {β : Type v}

/-- Charge one local root read, without traversing a child. -/
def readRun (empty : β) (t : BinaryTree (α × β)) : Measured β Nat :=
  (Trees.Cached.read empty t, 1)

@[simp] theorem readRun_value (empty : β) (t : BinaryTree (α × β)) :
    (readRun empty t).1 = Trees.Cached.read empty t := rfl

@[simp] theorem readRun_cost (empty : β) (t : BinaryTree (α × β)) :
    (readRun empty t).2 = 1 := rfl

/-- Execute both reads and the supplied callback on their returned values.
The children are reused; the callback's actual result is the new annotation. -/
def nodeRun (empty : β) (combineRun : β → α → β → Measured β Nat)
    (l : BinaryTree (α × β)) (a : α) (r : BinaryTree (α × β)) :
    Measured (BinaryTree (α × β)) Nat :=
  CallCount.tick (bind (readRun empty l) (fun left =>
    bind (readRun empty r) (fun right =>
      bind (combineRun left a right) (fun annotation =>
        pure (.node (a, annotation) l r)))))

/-- Only the callback equation at the reached arguments is required. -/
theorem nodeRun_value (empty : β) (combine : β → α → β → β)
    (combineRun : β → α → β → Measured β Nat)
    (l : BinaryTree (α × β)) (a : α) (r : BinaryTree (α × β))
    (hvalue : (combineRun (Trees.Cached.read empty l) a
      (Trees.Cached.read empty r)).1 =
      combine (Trees.Cached.read empty l) a (Trees.Cached.read empty r)) :
    (nodeRun empty combineRun l a r).1 =
      Trees.Cached.smartNode empty combine l a r := by
  change BinaryTree.node
    (a, (combineRun (Trees.Cached.read empty l) a (Trees.Cached.read empty r)).1)
    l r = Trees.Cached.smartNode empty combine l a r
  rw [hvalue]

/-- Work is separate from callback value correctness and child validity. -/
theorem nodeRun_cost (empty : β) (combineRun : β → α → β → Measured β Nat)
    (l : BinaryTree (α × β)) (a : α) (r : BinaryTree (α × β)) :
    (nodeRun empty combineRun l a r).2 =
      (combineRun (Trees.Cached.read empty l) a (Trees.Cached.read empty r)).2 + 3 := by
  simp [nodeRun, readRun, bind, pure, CallCount.tick,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem nodeRun_le (empty : β) (combineRun : β → α → β → Measured β Nat)
    (l : BinaryTree (α × β)) (a : α) (r : BinaryTree (α × β)) (K : Nat)
    (hcost : (combineRun (Trees.Cached.read empty l) a
      (Trees.Cached.read empty r)).2 ≤ K) :
    (nodeRun empty combineRun l a r).2 ≤ K + 3 := by
  rw [nodeRun_cost]
  exact Nat.add_le_add_right hcost 3

theorem nodeRun_valid (empty : β) (combine : β → α → β → β)
    (combineRun : β → α → β → Measured β Nat)
    (l : BinaryTree (α × β)) (a : α) (r : BinaryTree (α × β))
    (hl : Trees.Cached.Valid empty combine l)
    (hr : Trees.Cached.Valid empty combine r)
    (hvalue : (combineRun (Trees.Cached.read empty l) a
      (Trees.Cached.read empty r)).1 =
      combine (Trees.Cached.read empty l) a (Trees.Cached.read empty r)) :
    Trees.Cached.Valid empty combine (nodeRun empty combineRun l a r).1 := by
  rw [nodeRun_value empty combine combineRun l a r hvalue]
  exact (Trees.Cached.smartNode_valid_iff empty combine l a r).2 ⟨hl, hr⟩

end Resources.TreeCache

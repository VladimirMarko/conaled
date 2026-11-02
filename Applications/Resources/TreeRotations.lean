import Applications.Resources.TreeCache
import Applications.Trees.CachedRotations

/-! Actual two-node compositions for local cached root rebuilding.
Each existing `nodeRun` executes two root reads and one entry, so the two
constructions contribute six units besides their actual callback observations.
The second callback consumes the first returned annotation. There is no outer
tick. Fringe preparation, failed pattern attempts, proof-observation traversals,
physical allocation and machine arithmetic are outside this count. It differs
from unit-per-rotation metrics and conventions that give nonrecursive helpers
zero cost.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.TreeRotations
universe u v
variable {α : Type u} {β : Type v}

/-- Build the lower left node first, then use its actual returned tree at the root. -/
def rebuildLeftRun (empty : β) (callback : β → α → β → Measured β Nat)
    (A : BinaryTree (α × β)) (x : α) (B : BinaryTree (α × β))
    (y : α) (C : BinaryTree (α × β)) : Measured (BinaryTree (α × β)) Nat :=
  Resources.bind (TreeCache.nodeRun empty callback A x B)
    (fun lower => TreeCache.nodeRun empty callback lower y C)

/-- Build the lower right node first, then use its actual returned tree at the root. -/
def rebuildRightRun (empty : β) (callback : β → α → β → Measured β Nat)
    (A : BinaryTree (α × β)) (x : α) (B : BinaryTree (α × β))
    (y : α) (C : BinaryTree (α × β)) : Measured (BinaryTree (α × β)) Nat :=
  Resources.bind (TreeCache.nodeRun empty callback B y C)
    (fun lower => TreeCache.nodeRun empty callback A x lower)

/-- Reading the returned node exposes the callback's actual annotation. -/
private theorem read_nodeRun (empty : β) (callback : β → α → β → Measured β Nat)
    (A : BinaryTree (α × β)) (x : α) (B : BinaryTree (α × β)) :
    Trees.Cached.read empty (TreeCache.nodeRun empty callback A x B).1 =
      (callback (Trees.Cached.read empty A) x (Trees.Cached.read empty B)).1 := rfl

/-- Value refinement needs specifications only at the two actually reached calls. -/
theorem rebuildLeftRun_value (empty : β) (combine : β → α → β → β)
    (callback : β → α → β → Measured β Nat)
    (A : BinaryTree (α × β)) (x : α) (B : BinaryTree (α × β))
    (y : α) (C : BinaryTree (α × β))
    (hfirst : (callback (Trees.Cached.read empty A) x (Trees.Cached.read empty B)).1 =
      combine (Trees.Cached.read empty A) x (Trees.Cached.read empty B))
    (hsecond : (callback
      (callback (Trees.Cached.read empty A) x (Trees.Cached.read empty B)).1
      y (Trees.Cached.read empty C)).1 =
      combine (callback (Trees.Cached.read empty A) x (Trees.Cached.read empty B)).1
        y (Trees.Cached.read empty C)) :
    (rebuildLeftRun empty callback A x B y C).1 =
      Trees.Cached.rebuildLeft empty combine A x B y C := by
  change (TreeCache.nodeRun empty callback
    (TreeCache.nodeRun empty callback A x B).1 y C).1 =
      Trees.Cached.smartNode empty combine (Trees.Cached.smartNode empty combine A x B) y C
  calc
    _ = Trees.Cached.smartNode empty combine
        (TreeCache.nodeRun empty callback A x B).1 y C :=
      TreeCache.nodeRun_value empty combine callback _ y C hsecond
    _ = _ := congrArg (fun lower => Trees.Cached.smartNode empty combine lower y C)
      (TreeCache.nodeRun_value empty combine callback A x B hfirst)

theorem rebuildRightRun_value (empty : β) (combine : β → α → β → β)
    (callback : β → α → β → Measured β Nat)
    (A : BinaryTree (α × β)) (x : α) (B : BinaryTree (α × β))
    (y : α) (C : BinaryTree (α × β))
    (hfirst : (callback (Trees.Cached.read empty B) y (Trees.Cached.read empty C)).1 =
      combine (Trees.Cached.read empty B) y (Trees.Cached.read empty C))
    (hsecond : (callback (Trees.Cached.read empty A) x
      (callback (Trees.Cached.read empty B) y (Trees.Cached.read empty C)).1).1 =
      combine (Trees.Cached.read empty A) x
        (callback (Trees.Cached.read empty B) y (Trees.Cached.read empty C)).1) :
    (rebuildRightRun empty callback A x B y C).1 =
      Trees.Cached.rebuildRight empty combine A x B y C := by
  change (TreeCache.nodeRun empty callback A x
    (TreeCache.nodeRun empty callback B y C).1).1 =
      Trees.Cached.smartNode empty combine A x (Trees.Cached.smartNode empty combine B y C)
  calc
    _ = Trees.Cached.smartNode empty combine A x
        (TreeCache.nodeRun empty callback B y C).1 :=
      TreeCache.nodeRun_value empty combine callback A x _ hsecond
    _ = _ := congrArg (fun lower => Trees.Cached.smartNode empty combine A x lower)
      (TreeCache.nodeRun_value empty combine callback B y C hfirst)

/-- Correct local callbacks produce a valid tree from three valid fringes. -/
theorem rebuildLeftRun_valid (empty : β) (combine : β → α → β → β)
    (callback : β → α → β → Measured β Nat)
    (A : BinaryTree (α × β)) (x : α) (B : BinaryTree (α × β))
    (y : α) (C : BinaryTree (α × β))
    (hA : Trees.Cached.Valid empty combine A)
    (hB : Trees.Cached.Valid empty combine B)
    (hC : Trees.Cached.Valid empty combine C)
    (hfirst : (callback (Trees.Cached.read empty A) x (Trees.Cached.read empty B)).1 =
      combine (Trees.Cached.read empty A) x (Trees.Cached.read empty B))
    (hsecond : (callback
      (callback (Trees.Cached.read empty A) x (Trees.Cached.read empty B)).1
      y (Trees.Cached.read empty C)).1 =
      combine (callback (Trees.Cached.read empty A) x (Trees.Cached.read empty B)).1
        y (Trees.Cached.read empty C)) :
    Trees.Cached.Valid empty combine (rebuildLeftRun empty callback A x B y C).1 := by
  rw [rebuildLeftRun_value empty combine callback A x B y C hfirst hsecond]
  exact (Trees.Cached.rebuildLeft_valid_iff empty combine A x B y C).2 ⟨hA, hB, hC⟩

theorem rebuildRightRun_valid (empty : β) (combine : β → α → β → β)
    (callback : β → α → β → Measured β Nat)
    (A : BinaryTree (α × β)) (x : α) (B : BinaryTree (α × β))
    (y : α) (C : BinaryTree (α × β))
    (hA : Trees.Cached.Valid empty combine A)
    (hB : Trees.Cached.Valid empty combine B)
    (hC : Trees.Cached.Valid empty combine C)
    (hfirst : (callback (Trees.Cached.read empty B) y (Trees.Cached.read empty C)).1 =
      combine (Trees.Cached.read empty B) y (Trees.Cached.read empty C))
    (hsecond : (callback (Trees.Cached.read empty A) x
      (callback (Trees.Cached.read empty B) y (Trees.Cached.read empty C)).1).1 =
      combine (Trees.Cached.read empty A) x
        (callback (Trees.Cached.read empty B) y (Trees.Cached.read empty C)).1) :
    Trees.Cached.Valid empty combine (rebuildRightRun empty callback A x B y C).1 := by
  rw [rebuildRightRun_value empty combine callback A x B y C hfirst hsecond]
  exact (Trees.Cached.rebuildRight_valid_iff empty combine A x B y C).2 ⟨hA, hB, hC⟩

/-- No cache-validity or callback-value hypothesis is needed for exact work. -/
theorem rebuildLeftRun_cost (empty : β) (callback : β → α → β → Measured β Nat)
    (A : BinaryTree (α × β)) (x : α) (B : BinaryTree (α × β))
    (y : α) (C : BinaryTree (α × β)) :
    let first := callback (Trees.Cached.read empty A) x (Trees.Cached.read empty B)
    let second := callback first.1 y (Trees.Cached.read empty C)
    (rebuildLeftRun empty callback A x B y C).2 = first.2 + second.2 + 6 := by
  dsimp only
  change (TreeCache.nodeRun empty callback A x B).2 +
    (TreeCache.nodeRun empty callback (TreeCache.nodeRun empty callback A x B).1 y C).2 = _
  rw [TreeCache.nodeRun_cost, TreeCache.nodeRun_cost, read_nodeRun]
  exact add_add_add_comm _ _ _ _

/-- The right reconstruction likewise charges the actual inner call before the outer. -/
theorem rebuildRightRun_cost (empty : β) (callback : β → α → β → Measured β Nat)
    (A : BinaryTree (α × β)) (x : α) (B : BinaryTree (α × β))
    (y : α) (C : BinaryTree (α × β)) :
    let first := callback (Trees.Cached.read empty B) y (Trees.Cached.read empty C)
    let second := callback (Trees.Cached.read empty A) x first.1
    (rebuildRightRun empty callback A x B y C).2 = first.2 + second.2 + 6 := by
  dsimp only
  change (TreeCache.nodeRun empty callback B y C).2 +
    (TreeCache.nodeRun empty callback A x (TreeCache.nodeRun empty callback B y C).1).2 = _
  rw [TreeCache.nodeRun_cost, TreeCache.nodeRun_cost, read_nodeRun]
  exact add_add_add_comm _ _ _ _

/-- Bounds are needed only for the two reached callback invocations. -/
theorem rebuildLeftRun_le (empty : β) (callback : β → α → β → Measured β Nat)
    (A : BinaryTree (α × β)) (x : α) (B : BinaryTree (α × β))
    (y : α) (C : BinaryTree (α × β)) (K₁ K₂ : Nat)
    (hfirst : (callback (Trees.Cached.read empty A) x (Trees.Cached.read empty B)).2 ≤ K₁)
    (hsecond : (callback
      (callback (Trees.Cached.read empty A) x (Trees.Cached.read empty B)).1
      y (Trees.Cached.read empty C)).2 ≤ K₂) :
    (rebuildLeftRun empty callback A x B y C).2 ≤ K₁ + K₂ + 6 := by
  rw [rebuildLeftRun_cost]
  exact Nat.add_le_add_right (Nat.add_le_add hfirst hsecond) 6

theorem rebuildRightRun_le (empty : β) (callback : β → α → β → Measured β Nat)
    (A : BinaryTree (α × β)) (x : α) (B : BinaryTree (α × β))
    (y : α) (C : BinaryTree (α × β)) (K₁ K₂ : Nat)
    (hfirst : (callback (Trees.Cached.read empty B) y (Trees.Cached.read empty C)).2 ≤ K₁)
    (hsecond : (callback (Trees.Cached.read empty A) x
      (callback (Trees.Cached.read empty B) y (Trees.Cached.read empty C)).1).2 ≤ K₂) :
    (rebuildRightRun empty callback A x B y C).2 ≤ K₁ + K₂ + 6 := by
  rw [rebuildRightRun_cost]
  exact Nat.add_le_add_right (Nat.add_le_add hfirst hsecond) 6

end Resources.TreeRotations

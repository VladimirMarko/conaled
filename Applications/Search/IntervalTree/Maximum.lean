import Applications.Search.IntervalTree.Basic
import Applications.Trees.MaximumCacheObservations

/-! Greatest-endpoint semantics by transport to the existing maximum cache.
The raw map preserves every stored annotation and every node occurrence. Its
set observation takes an image, so distinct complete keys may share a high.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.IntervalTree
universe u v
variable {α : Type u} {κ : Type v}

section Projection
variable [LE α]

/-- Project keys to highs while preserving raw annotations, including bad ones. -/
def highTree (iv : κ → IntervalKey α) (t : BinaryTree (κ × α)) :
    BinaryTree (α × α) := t.map (fun binding => ((iv binding.1).high, binding.2))

@[simp] theorem highTree_nil (iv : κ → IntervalKey α) :
    highTree iv .nil = .nil := rfl

@[simp] theorem highTree_node (iv : κ → IntervalKey α) (a : κ) (m : α)
    (l r : BinaryTree (κ × α)) :
    highTree iv (.node (a, m) l r) = .node ((iv a).high, m) (highTree iv l) (highTree iv r) :=
  rfl

theorem highTree_eq_nil_iff (iv : κ → IntervalKey α) (t : BinaryTree (κ × α)) :
    highTree iv t = .nil ↔ t = .nil := by
  cases t <;> simp [highTree, BinaryTree.map]

theorem erase_highTree (iv : κ → IntervalKey α) (t : BinaryTree (κ × α)) :
    Trees.Cached.erase (highTree iv t) = (Trees.Cached.erase t).map (fun a => (iv a).high) := by
  unfold Trees.Cached.erase highTree
  rw [← BinaryTree.comp_map, ← BinaryTree.comp_map]
  rfl

theorem inorder_erase_highTree (iv : κ → IntervalKey α) (t : BinaryTree (κ × α)) :
    Trees.inorder (Trees.Cached.erase (highTree iv t)) =
      (Trees.inorder (Trees.Cached.erase t)).map (fun a => (iv a).high) := by
  rw [erase_highTree, Trees.inorder_map]

theorem setTree_erase_highTree (iv : κ → IntervalKey α) (t : BinaryTree (κ × α)) :
    Trees.setTree (Trees.Cached.erase (highTree iv t)) =
      (fun a => (iv a).high) '' Trees.setTree (Trees.Cached.erase t) := by
  rw [erase_highTree, Trees.setTree_map]

theorem mx_highTree_of_ne_nil [Bot α] (iv : κ → IntervalKey α)
    {t : BinaryTree (κ × α)} (nonempty : t ≠ .nil) :
    Trees.MaximumCache.mx (highTree iv t) = some (maxHi t) := by
  cases t with
  | nil => exact False.elim (nonempty rfl)
  | node binding l r => rfl

end Projection

section Greatest
variable [LinearOrder α] [OrderBot α]

private theorem localMax_highTree (iv : κ → IntervalKey α)
    (l : BinaryTree (κ × α)) (a : κ) (r : BinaryTree (κ × α)) :
    Trees.MaximumCache.localMax (Trees.MaximumCache.mx (highTree iv l)) (iv a).high
      (Trees.MaximumCache.mx (highTree iv r)) = max3 iv a l r := by
  cases l <;> cases r <;>
    simp [highTree, BinaryTree.map, Trees.MaximumCache.mx, Trees.MaximumCache.localMax,
      max3, combine, maxHi, Trees.Cached.read, max_assoc]

/-- Only a representation compatibility induction; greatest-element semantics is reused. -/
theorem cacheValid_iff_invarMx (iv : κ → IntervalKey α) (t : BinaryTree (κ × α)) :
    CacheValid iv t ↔ Trees.MaximumCache.invarMx (highTree iv t) := by
  induction t with
  | nil => rfl
  | node binding l r ihl ihr =>
      rcases binding with ⟨a, m⟩
      simp only [cacheValid_node, highTree_node, Trees.MaximumCache.invarMx_node,
        ihl, ihr, localMax_highTree]

/-- A nonempty valid tree has an attained greatest high, without any BST premise. -/
theorem maxHi_spec (iv : κ → IntervalKey α) {t : BinaryTree (κ × α)}
    (valid : CacheValid iv t) (nonempty : t ≠ .nil) :
    (∃ a ∈ Trees.setTree (Trees.Cached.erase t), (iv a).high = maxHi t) ∧
      ∀ a ∈ Trees.setTree (Trees.Cached.erase t), (iv a).high ≤ maxHi t := by
  have greatest := (Trees.MaximumCache.mx_eq_some_iff (highTree iv t)
    ((cacheValid_iff_invarMx iv t).mp valid) (maxHi t)).mp
      (mx_highTree_of_ne_nil iv nonempty)
  rw [setTree_erase_highTree] at greatest
  rcases greatest.1 with ⟨a, member, attained⟩
  exact ⟨⟨a, member, attained⟩,
    fun key member => greatest.2 ((iv key).high) ⟨key, member, rfl⟩⟩

theorem maxHi_attained (iv : κ → IntervalKey α) {t : BinaryTree (κ × α)}
    (valid : CacheValid iv t) (nonempty : t ≠ .nil) :
    ∃ a ∈ Trees.setTree (Trees.Cached.erase t), (iv a).high = maxHi t :=
  (maxHi_spec iv valid nonempty).1

theorem high_le_maxHi (iv : κ → IntervalKey α) {t : BinaryTree (κ × α)}
    (valid : CacheValid iv t) {a : κ} (member : a ∈ Trees.setTree (Trees.Cached.erase t)) :
    (iv a).high ≤ maxHi t := by
  cases t with
  | nil => exact False.elim member
  | node binding l r =>
      exact (maxHi_spec iv valid (by intro h; cases h)).2 a member

end Greatest
end Search.IntervalTree

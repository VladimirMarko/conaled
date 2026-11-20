import Applications.Search.IntervalKey
import Applications.Trees.Cached

/-! Literal interval-maximum annotations on the shared product-labelled tree.
The complete key and endpoint types are independent. The raw reader and local
constructor inspect stored annotations even when those annotations are wrong.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.IntervalTree
universe u v
variable {α : Type u} {κ : Type v}

section Reader
variable [Bot α]

def maxHi (t : BinaryTree (κ × α)) : α := Trees.Cached.read ⊥ t

@[simp] theorem maxHi_nil : maxHi (.nil : BinaryTree (κ × α)) = ⊥ := rfl

@[simp] theorem maxHi_node (a : κ) (m : α) (l r : BinaryTree (κ × α)) :
    maxHi (.node (a, m) l r) = m := rfl

end Reader

section Combination
variable [LE α] [Max α]

/-- The endpoint contribution, independent of tree representation. -/
def combine (iv : κ → IntervalKey α) (left : α) (a : κ) (right : α) : α :=
  max (iv a).high (max left right)

end Combination

section Cached
variable [LE α] [Max α] [Bot α]

def max3 (iv : κ → IntervalKey α) (a : κ) (l r : BinaryTree (κ × α)) : α :=
  combine iv (maxHi l) a (maxHi r)

def node (iv : κ → IntervalKey α) (l : BinaryTree (κ × α)) (a : κ)
    (r : BinaryTree (κ × α)) : BinaryTree (κ × α) :=
  Trees.Cached.smartNode ⊥ (combine iv) l a r

/-- Exact local equations at every node, with no key-order requirement. -/
def CacheValid (iv : κ → IntervalKey α) (t : BinaryTree (κ × α)) : Prop :=
  Trees.Cached.Valid ⊥ (combine iv) t

theorem max3_eq (iv : κ → IntervalKey α) (a : κ) (l r : BinaryTree (κ × α)) :
    max3 iv a l r = max (iv a).high (max (maxHi l) (maxHi r)) := rfl

theorem node_eq (iv : κ → IntervalKey α) (l : BinaryTree (κ × α)) (a : κ)
    (r : BinaryTree (κ × α)) : node iv l a r = .node (a, max3 iv a l r) l r := rfl

@[simp] theorem maxHi_node_smart (iv : κ → IntervalKey α)
    (l : BinaryTree (κ × α)) (a : κ) (r : BinaryTree (κ × α)) :
    maxHi (node iv l a r) = max3 iv a l r :=
  Trees.Cached.read_smartNode ⊥ (combine iv) l a r

@[simp] theorem erase_node (iv : κ → IntervalKey α)
    (l : BinaryTree (κ × α)) (a : κ) (r : BinaryTree (κ × α)) :
    Trees.Cached.erase (node iv l a r) =
      .node a (Trees.Cached.erase l) (Trees.Cached.erase r) :=
  Trees.Cached.erase_smartNode ⊥ (combine iv) l a r

@[simp] theorem cacheValid_nil (iv : κ → IntervalKey α) :
    CacheValid iv .nil := Trees.Cached.valid_nil ⊥ (combine iv)

@[simp] theorem cacheValid_node (iv : κ → IntervalKey α) (a : κ) (m : α)
    (l r : BinaryTree (κ × α)) :
    CacheValid iv (.node (a, m) l r) ↔
      CacheValid iv l ∧ CacheValid iv r ∧ m = max3 iv a l r := Iff.rfl

/-- Recomputing the new root does not repair malformed descendants. -/
theorem node_cacheValid_iff (iv : κ → IntervalKey α)
    (l : BinaryTree (κ × α)) (a : κ) (r : BinaryTree (κ × α)) :
    CacheValid iv (node iv l a r) ↔ CacheValid iv l ∧ CacheValid iv r :=
  Trees.Cached.smartNode_valid_iff ⊥ (combine iv) l a r

theorem node_cacheValid (iv : κ → IntervalKey α)
    {l r : BinaryTree (κ × α)} (left : CacheValid iv l) (a : κ)
    (right : CacheValid iv r) : CacheValid iv (node iv l a r) :=
  (node_cacheValid_iff iv l a r).mpr ⟨left, right⟩

end Cached
end Search.IntervalTree

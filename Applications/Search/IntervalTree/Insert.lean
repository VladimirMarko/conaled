import Applications.Search.IntervalTree.Basic
import Applications.Search.OrderedTree.Basic

/-! Literal interval-tree insertion. The empty branch stores the inserted high;
the two search branches recompute changed ancestors, and the comparison fallback
preserves the original annotated node. Cache preservation needs no search order.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.IntervalTree
universe u v
variable {α : Type u} {κ : Type v}

section Raw
variable [LE α] [Max α] [Bot α] [LT κ] [DecidableLT κ]

def insert (iv : κ → IntervalKey α) (x : κ) : BinaryTree (κ × α) → BinaryTree (κ × α)
  | .nil => .node (x, (iv x).high) .nil .nil
  | .node (a, m) l r =>
      if x < a then node iv (insert iv x l) a r
      else if a < x then node iv l a (insert iv x r)
      else .node (a, m) l r

@[simp] theorem insert_nil (iv : κ → IntervalKey α) (x : κ) :
    insert iv x .nil = .node (x, (iv x).high) .nil .nil := rfl

theorem insert_node (iv : κ → IntervalKey α) (x a : κ) (m : α)
    (l r : BinaryTree (κ × α)) :
    insert iv x (.node (a, m) l r) =
      if x < a then node iv (insert iv x l) a r
      else if a < x then node iv l a (insert iv x r)
      else .node (a, m) l r := rfl

theorem insert_of_lt (iv : κ → IntervalKey α) {x a : κ} (h : x < a)
    (m : α) (l r : BinaryTree (κ × α)) :
    insert iv x (.node (a, m) l r) = node iv (insert iv x l) a r := by
  simp only [insert_node, ite_eq_left h]

theorem insert_of_gt (iv : κ → IntervalKey α) {x a : κ}
    (notLeft : ¬x < a) (right : a < x) (m : α) (l r : BinaryTree (κ × α)) :
    insert iv x (.node (a, m) l r) = node iv l a (insert iv x r) := by
  simp only [insert_node, ite_eq_right notLeft, ite_eq_left right]

/-- At raw comparison structure, two false comparisons need not mean equality. -/
theorem insert_of_incomparable (iv : κ → IntervalKey α) {x a : κ}
    (notLeft : ¬x < a) (notRight : ¬a < x) (m : α) (l r : BinaryTree (κ × α)) :
    insert iv x (.node (a, m) l r) = .node (a, m) l r := by
  simp only [insert_node, ite_eq_right notLeft, ite_eq_right notRight]

/-- Only the singleton equation for this inserted key is needed. -/
theorem insert_cacheValid_of_singleton (iv : κ → IntervalKey α) (x : κ)
    (singleton : (iv x).high = max (iv x).high (max ⊥ ⊥))
    {t : BinaryTree (κ × α)} (valid : CacheValid iv t) :
    CacheValid iv (insert iv x t) := by
  induction t with
  | nil =>
      exact (cacheValid_node iv x (iv x).high .nil .nil).mpr
        ⟨cacheValid_nil iv, cacheValid_nil iv, singleton⟩
  | node a l r ihl ihr =>
      rcases a with ⟨a, m⟩
      have parts := (cacheValid_node iv a m l r).mp valid
      rw [insert_node]
      split
      · exact node_cacheValid iv (ihl parts.1) a parts.2.1
      · split
        · exact node_cacheValid iv parts.1 a (ihr parts.2.1)
        · exact valid

/-- The same equation is necessary for preservation on every valid input. -/
theorem insert_preserves_cacheValid_iff (iv : κ → IntervalKey α) (x : κ) :
    (∀ t, CacheValid iv t → CacheValid iv (insert iv x t)) ↔
      (iv x).high = max (iv x).high (max ⊥ ⊥) := by
  constructor
  · intro preserves
    exact ((cacheValid_node iv x (iv x).high .nil .nil).mp
      (preserves .nil (cacheValid_nil iv))).2.2
  · intro singleton t valid
    exact insert_cacheValid_of_singleton iv x singleton valid

end Raw

section LinearKeys
variable [LE α] [Max α] [Bot α] [LinearOrder κ]

@[simp] theorem insert_eq_root (iv : κ → IntervalKey α) (a : κ) (m : α)
    (l r : BinaryTree (κ × α)) :
    insert iv a (.node (a, m) l r) = .node (a, m) l r := by
  exact insert_of_incomparable iv (lt_irrefl a) (lt_irrefl a) m l r

/-- Erasure transports the actual program; the input need not be ordered. -/
theorem erase_insert (iv : κ → IntervalKey α) (x : κ) (t : BinaryTree (κ × α)) :
    Trees.Cached.erase (insert iv x t) = OrderedTree.insert x (Trees.Cached.erase t) := by
  induction t with
  | nil => rfl
  | node a l r ihl ihr =>
      rcases a with ⟨a, m⟩
      simp only [insert_node, Trees.Cached.erase_node, OrderedTree.insert]
      split
      · simpa only [erase_node] using congrArg (fun s => BinaryTree.node a s
          (Trees.Cached.erase r)) ihl
      · split
        · simpa only [erase_node] using congrArg (fun s => BinaryTree.node a
            (Trees.Cached.erase l) s) ihr
        · rfl

end LinearKeys

section CanonicalMaximum
variable [LinearOrder α] [OrderBot α] [LT κ] [DecidableLT κ]

theorem insert_cacheValid (iv : κ → IntervalKey α) (x : κ)
    {t : BinaryTree (κ × α)} (valid : CacheValid iv t) :
    CacheValid iv (insert iv x t) :=
  insert_cacheValid_of_singleton iv x (by simp) valid

end CanonicalMaximum
end Search.IntervalTree

import Applications.Search.IntervalTree.Search

/-! Exercise 5.8 uses its own tree recursion. Only after defining it do we
relate its raw behavior to singleton-interval search and reuse semantic proofs.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.IntervalTree
universe u v
variable {α : Type u} {κ : Type v}

section Predicate
variable [LE α]

def ContainsPoint (point : α) (interval : IntervalKey α) : Prop :=
  interval.low ≤ point ∧ point ≤ interval.high

instance [DecidableLE α] (point : α) (interval : IntervalKey α) :
    Decidable (ContainsPoint point interval) :=
  inferInstanceAs (Decidable (interval.low ≤ point ∧ point ≤ interval.high))

end Predicate

theorem containsPoint_iff_mem [Preorder α] (point : α) (interval : IntervalKey α) :
    ContainsPoint point interval ↔ point ∈ interval.toSet := Iff.rfl

section Raw
variable [LE α] [Bot α] [DecidableLE α]

def searchPoint (iv : κ → IntervalKey α) : BinaryTree (κ × α) → α → Bool
  | .nil, _ => false
  | .node (a, _) l r, point =>
      if ContainsPoint point (iv a) then true
      else match l with
        | .nil => searchPoint iv r point
        | .node _ _ _ =>
            if point ≤ maxHi l then searchPoint iv l point else searchPoint iv r point

@[simp] theorem searchPoint_nil (iv : κ → IntervalKey α) (point : α) :
    searchPoint iv .nil point = false := rfl

/-- Raw LE need not be reflexive: the proof is the singleton's explicit domain. -/
theorem searchPoint_eq_search (iv : κ → IntervalKey α) (t : BinaryTree (κ × α))
    (point : α) (reflexive : point ≤ point) :
    searchPoint iv t point = search iv t (IntervalKey.ofBounds point point reflexive) := by
  induction t with
  | nil => rfl
  | node binding l r ihl ihr =>
      rcases binding with ⟨a, m⟩
      rw [searchPoint.eq_def, search.eq_def]
      simp only [IntervalKey.Overlap, IntervalKey.low_ofBounds, IntervalKey.high_ofBounds,
        ContainsPoint]
      cases l <;> simp only [ihl, ihr] <;> rfl

end Raw

section Correctness
variable [LinearOrder α] [OrderBot α]

theorem searchPoint_correct (iv : κ → IntervalKey α) {t : BinaryTree (κ × α)}
    (valid : CacheValid iv t) (ordered : LowOrdered iv t) (point : α) :
    searchPoint iv t point = true ↔
      ∃ a ∈ Trees.setTree (Trees.Cached.erase t), ContainsPoint point (iv a) := by
  rw [searchPoint_eq_search iv t point le_rfl, search_correct iv valid ordered]
  exact exists_congr (fun _ => and_congr Iff.rfl and_comm)

theorem searchPoint_correct_of_strict [LT κ] (iv : κ → IntervalKey α)
    (compatible : ∀ a b, a < b → (iv a).low ≤ (iv b).low)
    {t : BinaryTree (κ × α)} (valid : CacheValid iv t)
    (strict : (Trees.inorder (Trees.Cached.erase t)).Pairwise (· < ·)) (point : α) :
    searchPoint iv t point = true ↔
      ∃ a ∈ Trees.setTree (Trees.Cached.erase t), ContainsPoint point (iv a) :=
  searchPoint_correct iv valid (lowOrdered_of_strict iv compatible strict) point

theorem searchPoint_correct_book {t : BinaryTree (IntervalKey α × α)}
    (valid : CacheValid id t)
    (strict : (Trees.inorder (Trees.Cached.erase t)).Pairwise (· < ·)) (point : α) :
    searchPoint id t point = true ↔
      ∃ a ∈ Trees.setTree (Trees.Cached.erase t), ContainsPoint point a :=
  searchPoint_correct_of_strict id (fun _ _ h => IntervalKey.low_le_of_le h.le) valid strict point

end Correctness
end Search.IntervalTree

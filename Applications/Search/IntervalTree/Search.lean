import Applications.Search.IntervalTree.Maximum
import Applications.Search.IntervalSet

/-! The literal one-branch interval search. Its raw soundness is independent
of annotations and ordering; completeness uses separate maximum and low-order
facts. Complete keys and endpoint types need not have the same universe.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.IntervalTree
universe u v
variable {α : Type u} {κ : Type v}

section Raw
variable [LE α] [Bot α] [DecidableLE α]

/-- Inspect a constructor for the nonempty-left guard, without key equality. -/
def search (iv : κ → IntervalKey α) : BinaryTree (κ × α) → IntervalKey α → Bool
  | .nil, _ => false
  | .node (a, _) l r, query =>
      if IntervalKey.Overlap query (iv a) then true
      else match l with
        | .nil => search iv r query
        | .node _ _ _ =>
            if query.low ≤ maxHi l then search iv l query else search iv r query

@[simp] theorem search_nil (iv : κ → IntervalKey α) (query : IntervalKey α) :
    search iv .nil query = false := rfl

theorem search_node_of_overlap (iv : κ → IntervalKey α) (a : κ) (m : α)
    (l r : BinaryTree (κ × α)) (query : IntervalKey α)
    (hit : IntervalKey.Overlap query (iv a)) :
    search iv (.node (a, m) l r) query = true := by
  simp only [search, ite_eq_left hit]

theorem search_node_empty_left (iv : κ → IntervalKey α) (a : κ) (m : α)
    (r : BinaryTree (κ × α)) (query : IntervalKey α)
    (miss : ¬IntervalKey.Overlap query (iv a)) :
    search iv (.node (a, m) .nil r) query = search iv r query := by
  simp only [search, ite_eq_right miss]

theorem search_node_left (iv : κ → IntervalKey α) (a : κ) (m : α)
    (l r : BinaryTree (κ × α)) (query : IntervalKey α)
    (miss : ¬IntervalKey.Overlap query (iv a)) (nonempty : l ≠ .nil)
    (threshold : query.low ≤ maxHi l) :
    search iv (.node (a, m) l r) query = search iv l query := by
  cases l with
  | nil => exact False.elim (nonempty rfl)
  | node binding ll lr => simp only [search, ite_eq_right miss, ite_eq_left threshold]

theorem search_node_right (iv : κ → IntervalKey α) (a : κ) (m : α)
    (l r : BinaryTree (κ × α)) (query : IntervalKey α)
    (miss : ¬IntervalKey.Overlap query (iv a))
    (threshold : ¬query.low ≤ maxHi l) :
    search iv (.node (a, m) l r) query = search iv r query := by
  cases l <;> simp only [search, ite_eq_right miss, ite_eq_right threshold]

/-- A true answer supplies an original key, even on malformed or unordered trees. -/
theorem search_sound (iv : κ → IntervalKey α) {t : BinaryTree (κ × α)}
    {query : IntervalKey α} (found : search iv t query = true) :
    ∃ a ∈ Trees.setTree (Trees.Cached.erase t), IntervalKey.Overlap (iv a) query := by
  induction t with
  | nil => cases found
  | node binding l r ihl ihr =>
      rcases binding with ⟨a, m⟩
      by_cases hit : IntervalKey.Overlap query (iv a)
      · exact ⟨a, by simp, (IntervalKey.overlap_comm query (iv a)).mp hit⟩
      · cases l with
        | nil =>
            rw [search_node_empty_left iv a m r query hit] at found
            rcases ihr found with ⟨b, member, overlap⟩
            exact ⟨b, by simp only [Trees.Cached.erase_node, Trees.setTree_node,
              Set.mem_union, Set.mem_singleton_iff]; exact Or.inr member, overlap⟩
        | node binding ll lr =>
            by_cases threshold : query.low ≤ maxHi (.node binding ll lr)
            · rw [search_node_left iv a m _ r query hit (by intro h; cases h) threshold] at found
              rcases ihl found with ⟨b, member, overlap⟩
              exact ⟨b, by simp only [Trees.Cached.erase_node, Trees.setTree_node,
                Set.mem_union, Set.mem_singleton_iff]; exact Or.inl (Or.inl member), overlap⟩
            · rw [search_node_right iv a m _ r query hit threshold] at found
              rcases ihr found with ⟨b, member, overlap⟩
              exact ⟨b, by simp only [Trees.Cached.erase_node, Trees.setTree_node,
                Set.mem_union, Set.mem_singleton_iff]; exact Or.inr member, overlap⟩

end Raw

section LowOrder
variable [LE α]

/-- The search invariant permits equal projected lows and repeated complete keys. -/
def LowOrdered (iv : κ → IntervalKey α) (t : BinaryTree (κ × α)) : Prop :=
  (Trees.inorder (Trees.Cached.erase t)).Pairwise (fun a b => (iv a).low ≤ (iv b).low)

@[simp] theorem lowOrdered_nil (iv : κ → IntervalKey α) : LowOrdered iv .nil := by
  simp [LowOrdered]

theorem lowOrdered_children (iv : κ → IntervalKey α) {a : κ} {m : α}
    {l r : BinaryTree (κ × α)} (ordered : LowOrdered iv (.node (a, m) l r)) :
    LowOrdered iv l ∧ LowOrdered iv r := by
  change (Trees.inorder (Trees.Cached.erase l) ++
    a :: Trees.inorder (Trees.Cached.erase r)).Pairwise _ at ordered
  have parts := List.pairwise_append.mp ordered
  exact ⟨parts.1, (List.pairwise_cons.mp parts.2.1).2⟩

theorem lowOrdered_cross (iv : κ → IntervalKey α) {a : κ} {m : α}
    {l r : BinaryTree (κ × α)} (ordered : LowOrdered iv (.node (a, m) l r))
    {x y : κ} (left : x ∈ Trees.setTree (Trees.Cached.erase l))
    (right : y ∈ Trees.setTree (Trees.Cached.erase r)) : (iv x).low ≤ (iv y).low := by
  change (Trees.inorder (Trees.Cached.erase l) ++
    a :: Trees.inorder (Trees.Cached.erase r)).Pairwise _ at ordered
  exact (List.pairwise_append.mp ordered).2.2 x
    ((Trees.mem_inorder_iff_mem_setTree x _).mpr left) y
    (List.mem_cons_of_mem a ((Trees.mem_inorder_iff_mem_setTree y _).mpr right))

theorem lowOrdered_of_strict [LT κ] (iv : κ → IntervalKey α)
    (compatible : ∀ a b, a < b → (iv a).low ≤ (iv b).low)
    {t : BinaryTree (κ × α)}
    (strict : (Trees.inorder (Trees.Cached.erase t)).Pairwise (· < ·)) : LowOrdered iv t :=
  strict.imp (fun h => compatible _ _ h)

theorem not_overlap_nil (iv : κ → IntervalKey α) (query : IntervalKey α) :
    ¬∃ a ∈ Trees.setTree (Trees.Cached.erase (.nil : BinaryTree (κ × α))),
      IntervalKey.Overlap (iv a) query := by
  rintro ⟨_, member, _⟩
  exact member

end LowOrder

section Pruning
variable [LinearOrder α] [OrderBot α]

/-- A failed threshold uses only the upper bound, even for unordered inputs. -/
theorem not_overlap_of_maxHi_lt (iv : κ → IntervalKey α)
    {t : BinaryTree (κ × α)} {query : IntervalKey α}
    (valid : CacheValid iv t) (threshold : maxHi t < query.low) :
    ¬∃ a ∈ Trees.setTree (Trees.Cached.erase t), IntervalKey.Overlap (iv a) query := by
  rintro ⟨a, member, overlap⟩
  exact (not_le_of_gt (lt_of_le_of_lt (high_le_maxHi iv valid member) threshold)) overlap.1

/-- The left maximum is attained by an original key. No right cache premise is used. -/
theorem high_lt_low_of_left_no_overlap (iv : κ → IntervalKey α)
    {l r : BinaryTree (κ × α)} {query : IntervalKey α}
    (valid : CacheValid iv l) (nonempty : l ≠ .nil)
    (threshold : query.low ≤ maxHi l)
    (absent : ¬∃ a ∈ Trees.setTree (Trees.Cached.erase l), IntervalKey.Overlap (iv a) query)
    (cross : ∀ a ∈ Trees.setTree (Trees.Cached.erase l),
      ∀ b ∈ Trees.setTree (Trees.Cached.erase r), (iv a).low ≤ (iv b).low)
    {b : κ} (right : b ∈ Trees.setTree (Trees.Cached.erase r)) :
    query.high < (iv b).low := by
  obtain ⟨a, member, attained⟩ := maxHi_attained iv valid nonempty
  have belowHigh : query.low ≤ (iv a).high := by rw [attained]; exact threshold
  have aboveQuery : ¬(iv a).low ≤ query.high :=
    fun h => absent ⟨a, member, ⟨belowHigh, h⟩⟩
  exact lt_of_lt_of_le (lt_of_not_ge aboveQuery) (cross a member b right)

theorem not_overlap_right_of_left (iv : κ → IntervalKey α)
    {l r : BinaryTree (κ × α)} {query : IntervalKey α}
    (valid : CacheValid iv l) (nonempty : l ≠ .nil)
    (threshold : query.low ≤ maxHi l)
    (absent : ¬∃ a ∈ Trees.setTree (Trees.Cached.erase l), IntervalKey.Overlap (iv a) query)
    (cross : ∀ a ∈ Trees.setTree (Trees.Cached.erase l),
      ∀ b ∈ Trees.setTree (Trees.Cached.erase r), (iv a).low ≤ (iv b).low) :
    ¬∃ b ∈ Trees.setTree (Trees.Cached.erase r), IntervalKey.Overlap (iv b) query := by
  rintro ⟨b, member, overlap⟩
  exact (not_le_of_gt
    (high_lt_low_of_left_no_overlap iv valid nonempty threshold absent cross member)) overlap.2

end Pruning

section Correctness
variable [LinearOrder α] [OrderBot α]

theorem search_complete (iv : κ → IntervalKey α) {t : BinaryTree (κ × α)}
    {query : IntervalKey α} (valid : CacheValid iv t) (ordered : LowOrdered iv t)
    (present : ∃ a ∈ Trees.setTree (Trees.Cached.erase t), IntervalKey.Overlap (iv a) query) :
    search iv t query = true := by
  classical
  induction t with
  | nil =>
      rcases present with ⟨_, member, _⟩
      exact False.elim member
  | node binding l r ihl ihr =>
      rcases binding with ⟨a, m⟩
      have children := lowOrdered_children iv ordered
      by_cases hit : IntervalKey.Overlap query (iv a)
      · exact search_node_of_overlap iv a m l r query hit
      · have rootAbsent : ¬IntervalKey.Overlap (iv a) query :=
          fun h => hit ((IntervalKey.overlap_comm (iv a) query).mp h)
        by_cases empty : l = .nil
        · subst l
          rw [search_node_empty_left iv a m r query hit]
          apply ihr valid.2.1 children.2
          rcases present with ⟨b, member, overlap⟩
          simp only [Trees.Cached.erase_node, Trees.setTree_node,
            Set.mem_union, Set.mem_singleton_iff] at member
          rcases member with (left | rfl) | right
          · exact False.elim left
          · exact False.elim (rootAbsent overlap)
          · exact ⟨b, right, overlap⟩
        · by_cases threshold : query.low ≤ maxHi l
          · rw [search_node_left iv a m l r query hit empty threshold]
            by_cases inLeft :
                ∃ b ∈ Trees.setTree (Trees.Cached.erase l), IntervalKey.Overlap (iv b) query
            · exact ihl valid.1 children.1 inLeft
            · have rightAbsent := not_overlap_right_of_left iv valid.1 empty threshold inLeft
                (fun x hx y hy => lowOrdered_cross iv ordered hx hy)
              rcases present with ⟨b, member, overlap⟩
              simp only [Trees.Cached.erase_node, Trees.setTree_node,
                Set.mem_union, Set.mem_singleton_iff] at member
              rcases member with (left | rfl) | right
              · exact False.elim (inLeft ⟨b, left, overlap⟩)
              · exact False.elim (rootAbsent overlap)
              · exact False.elim (rightAbsent ⟨b, right, overlap⟩)
          · rw [search_node_right iv a m l r query hit threshold]
            apply ihr valid.2.1 children.2
            have leftAbsent := not_overlap_of_maxHi_lt iv valid.1 (lt_of_not_ge threshold)
            rcases present with ⟨b, member, overlap⟩
            simp only [Trees.Cached.erase_node, Trees.setTree_node,
              Set.mem_union, Set.mem_singleton_iff] at member
            rcases member with (left | rfl) | right
            · exact False.elim (leftAbsent ⟨b, left, overlap⟩)
            · exact False.elim (rootAbsent overlap)
            · exact ⟨b, right, overlap⟩

/-- Weak low order suffices; complete keys need no order or uniqueness. -/
theorem search_correct (iv : κ → IntervalKey α) {t : BinaryTree (κ × α)}
    (valid : CacheValid iv t) (ordered : LowOrdered iv t) (query : IntervalKey α) :
    search iv t query = true ↔
      ∃ a ∈ Trees.setTree (Trees.Cached.erase t), IntervalKey.Overlap (iv a) query :=
  ⟨search_sound iv, search_complete iv valid ordered⟩

theorem search_correct_of_strict [LT κ] (iv : κ → IntervalKey α)
    (compatible : ∀ a b, a < b → (iv a).low ≤ (iv b).low)
    {t : BinaryTree (κ × α)} (valid : CacheValid iv t)
    (strict : (Trees.inorder (Trees.Cached.erase t)).Pairwise (· < ·))
    (query : IntervalKey α) :
    search iv t query = true ↔
      ∃ a ∈ Trees.setTree (Trees.Cached.erase t), IntervalKey.Overlap (iv a) query :=
  search_correct iv valid (lowOrdered_of_strict iv compatible strict) query

/-- Theorem 5.3 for the book's ascending interval keys. -/
theorem search_correct_book {t : BinaryTree (IntervalKey α × α)}
    (valid : CacheValid id t)
    (strict : (Trees.inorder (Trees.Cached.erase t)).Pairwise (· < ·))
    (query : IntervalKey α) :
    search id t query = true ↔ IntervalSet.HasOverlap (Trees.setTree (Trees.Cached.erase t)) query :=
  search_correct_of_strict id (fun _ _ h => IntervalKey.low_le_of_le h.le) valid strict query

end Correctness
end Search.IntervalTree

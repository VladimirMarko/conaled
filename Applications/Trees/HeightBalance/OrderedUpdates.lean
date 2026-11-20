import Applications.Trees.HeightBalance.Updates
import Applications.Search.OrderedList.Sorted

/-!
# Ordered observations of cached height-balanced updates

The comparison paths agree with the strict-list model without a cache or
balance premise. Extraction first gives a raw rightmost/snoc identity; a
strict inorder then supplies its order-theoretic meaning. Source correspondence
and the separation of these assumptions are recorded in
`docs/research/fdsa-height-updates.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees.HeightBalance
universe u v
variable {α : Type u} {σ : Type v}

/-- Strict inorder turns raw rightmost extraction into a strict final element. -/
theorem strict_inorder_splitMaxOption [LT α]
    (ann : HeightAnnotation α σ) (d : Nat)
    (t t' : BinaryTree (α × σ)) (m : α)
    (hs : splitMaxOption ann d t = some (t', m))
    (hstrict : Search.OrderedList.Strict (Trees.inorder (Cached.erase t))) :
    Search.OrderedList.Strict (Trees.inorder (Cached.erase t')) ∧
      ∀ x ∈ Trees.inorder (Cached.erase t'), x < m := by
  apply (Search.OrderedList.strict_snoc_iff _ m).mp
  rw [inorder_splitMaxOption ann d t t' m hs]
  exact hstrict

/-- The extracted element is attained and greatest when the input is strict. -/
theorem maximal_splitMaxOption [Preorder α]
    (ann : HeightAnnotation α σ) (d : Nat)
    (t t' : BinaryTree (α × σ)) (m : α)
    (hs : splitMaxOption ann d t = some (t', m))
    (hstrict : Search.OrderedList.Strict (Trees.inorder (Cached.erase t))) :
    m ∈ Trees.inorder (Cached.erase t) ∧
      ∀ x ∈ Trees.inorder (Cached.erase t), x ≤ m := by
  have hi := inorder_splitMaxOption ann d t t' m hs
  have hp := strict_inorder_splitMaxOption ann d t t' m hs hstrict
  constructor
  · rw [← hi]
    exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
  · intro x hx
    rw [← hi] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact le_of_lt (hp.2 x hx)
    · exact le_of_eq (List.mem_singleton.mp hx)

section LinearOrder
variable [LinearOrder α]

/-- Exact strict-list insertion, independent of all stored summaries and d. -/
theorem inorder_insert (ann : HeightAnnotation α σ) (d : Nat) (x : α)
    (t : BinaryTree (α × σ))
    (hstrict : Search.OrderedList.Strict (Trees.inorder (Cached.erase t))) :
    Trees.inorder (Cached.erase (insert ann d x t)) =
      Search.OrderedList.insert x (Trees.inorder (Cached.erase t)) := by
  induction t with
  | nil => rfl
  | node label l r ihl ihr =>
      rcases label with ⟨a, s⟩
      have whole : Search.OrderedList.Strict
          (Trees.inorder (Cached.erase l) ++ a :: Trees.inorder (Cached.erase r)) := by
        simpa only [Cached.erase_node, Trees.inorder_node] using hstrict
      have parts := (Search.OrderedList.strict_middle
        (Trees.inorder (Cached.erase l)) a (Trees.inorder (Cached.erase r))).mp whole
      have hl := Search.OrderedList.strict_prefix parts.1
      have hr := Search.OrderedList.strict_tail parts.2
      change Trees.inorder (Cached.erase (insert ann d x (.node (a, s) l r))) =
        Search.OrderedList.insert x
          (Trees.inorder (Cached.erase l) ++ a :: Trees.inorder (Cached.erase r))
      by_cases hxa : x < a
      · rw [insert_of_lt ann d x a s l r hxa, inorder_balL, ihl hl,
          Search.OrderedList.insert_distribution_lt x a
            (Trees.inorder (Cached.erase l)) (Trees.inorder (Cached.erase r)) parts.1 hxa]
      · by_cases hax : a < x
        · rw [insert_of_gt ann d x a s l r hxa hax, inorder_balR, ihr hr,
            Search.OrderedList.insert_distribution_ge x a
              (Trees.inorder (Cached.erase l)) (Trees.inorder (Cached.erase r))
              parts.1 (le_of_not_gt hxa),
            Search.OrderedList.insert, ite_eq_right hxa, ite_eq_right (ne_of_gt hax)]
        · have hxeq : x = a := le_antisymm (le_of_not_gt hax) (le_of_not_gt hxa)
          subst x
          rw [insert_of_not_lt_of_not_lt ann d a a s l r (lt_irrefl a) (lt_irrefl a),
            Cached.erase_node, Trees.inorder_node,
            Search.OrderedList.insert_distribution_ge a a
              (Trees.inorder (Cached.erase l)) (Trees.inorder (Cached.erase r))
              parts.1 (le_refl a),
            Search.OrderedList.insert, ite_eq_right (lt_irrefl a), ite_eq_left rfl]

theorem strict_inorder_insert (ann : HeightAnnotation α σ) (d : Nat) (x : α)
    (t : BinaryTree (α × σ))
    (hstrict : Search.OrderedList.Strict (Trees.inorder (Cached.erase t))) :
    Search.OrderedList.Strict (Trees.inorder (Cached.erase (insert ann d x t))) := by
  rw [inorder_insert ann d x t hstrict]
  exact Search.OrderedList.strict_insert x hstrict

/-- Exact first-match list deletion, using the source predecessor recurrence. -/
theorem inorder_delete (ann : HeightAnnotation α σ) (d : Nat) (x : α)
    (t : BinaryTree (α × σ))
    (hstrict : Search.OrderedList.Strict (Trees.inorder (Cached.erase t))) :
    Trees.inorder (Cached.erase (delete ann d x t)) =
      Search.OrderedList.delete x (Trees.inorder (Cached.erase t)) := by
  induction t with
  | nil => rfl
  | node label l r ihl ihr =>
      rcases label with ⟨a, s⟩
      have whole : Search.OrderedList.Strict
          (Trees.inorder (Cached.erase l) ++ a :: Trees.inorder (Cached.erase r)) := by
        simpa only [Cached.erase_node, Trees.inorder_node] using hstrict
      have parts := (Search.OrderedList.strict_middle
        (Trees.inorder (Cached.erase l)) a (Trees.inorder (Cached.erase r))).mp whole
      have hl := Search.OrderedList.strict_prefix parts.1
      have hr := Search.OrderedList.strict_tail parts.2
      change Trees.inorder (Cached.erase (delete ann d x (.node (a, s) l r))) =
        Search.OrderedList.delete x
          (Trees.inorder (Cached.erase l) ++ a :: Trees.inorder (Cached.erase r))
      by_cases hxa : x < a
      · rw [delete_of_lt ann d x a s l r hxa, inorder_balR, ihl hl,
          Search.OrderedList.delete_distribution_lt x a
            (Trees.inorder (Cached.erase l)) (Trees.inorder (Cached.erase r)) whole hxa]
      · by_cases hax : a < x
        · rw [delete_of_gt ann d x a s l r hxa hax, inorder_balL, ihr hr,
            Search.OrderedList.delete_distribution_ge x a
              (Trees.inorder (Cached.erase l)) (Trees.inorder (Cached.erase r))
              whole (le_of_not_gt hxa), Search.OrderedList.delete, ite_eq_right (ne_of_gt hax)]
        · have hxeq : x = a := le_antisymm (le_of_not_gt hax) (le_of_not_gt hxa)
          subst x
          rw [delete_of_not_lt_of_not_lt ann d a a s l r (lt_irrefl a) (lt_irrefl a),
            Search.OrderedList.delete_distribution_ge a a
              (Trees.inorder (Cached.erase l)) (Trees.inorder (Cached.erase r))
              whole (le_refl a), Search.OrderedList.delete, ite_eq_left rfl]
          cases hs : splitMaxOption ann d l with
          | none =>
              have hnil := (splitMaxOption_eq_none_iff ann d l).mp hs
              subst l
              rfl
          | some pair =>
              rcases pair with ⟨l', m⟩
              change Trees.inorder (Cached.erase (balR ann d l' m r)) =
                Trees.inorder (Cached.erase l) ++ Trees.inorder (Cached.erase r)
              rw [inorder_balR]
              have hi := inorder_splitMaxOption ann d l l' m hs
              simpa only [List.append_assoc, List.cons_append, List.nil_append] using
                congrArg (fun xs => xs ++ Trees.inorder (Cached.erase r)) hi

theorem strict_inorder_delete (ann : HeightAnnotation α σ) (d : Nat) (x : α)
    (t : BinaryTree (α × σ))
    (hstrict : Search.OrderedList.Strict (Trees.inorder (Cached.erase t))) :
    Search.OrderedList.Strict (Trees.inorder (Cached.erase (delete ann d x t))) := by
  rw [inorder_delete ann d x t hstrict]
  exact Search.OrderedList.strict_delete x hstrict

end LinearOrder
end Trees.HeightBalance

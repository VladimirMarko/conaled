import Applications.Search.OrderedList.Basic

/-!
# The eight strict-list equations

Insertion distribution requires a strict prefix ending at the pivot and
allows an arbitrary suffix. Deletion distribution requires the entire list
to be strict, because first-match erasure scans every unequal head.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.OrderedList
universe u
variable {α : Type u}

theorem strict_cons_iff [LT α] (x : α) (xs : List α) :
    Strict (x :: xs) ↔ (∀ y ∈ xs, x < y) ∧ Strict xs := List.pairwise_cons

theorem strict_snoc_iff [LT α] (xs : List α) (x : α) :
    Strict (xs ++ [x]) ↔ Strict xs ∧ ∀ y ∈ xs, y < x := by
  simp [Strict, List.pairwise_append]

theorem strict_tail [LT α] {x : α} {xs : List α} (h : Strict (x :: xs)) :
    Strict xs := ((strict_cons_iff x xs).mp h).2

theorem strict_prefix [LT α] {xs : List α} {y : α} (h : Strict (xs ++ [y])) :
    Strict xs := ((strict_snoc_iff xs y).mp h).1

theorem strict_middle [Preorder α] (xs : List α) (y : α) (ys : List α) :
    Strict (xs ++ y :: ys) ↔ Strict (xs ++ [y]) ∧ Strict (y :: ys) := by
  constructor
  · intro h
    have hh := List.pairwise_append.mp h
    exact ⟨(strict_snoc_iff xs y).mpr ⟨hh.1,
      fun z hz => hh.2.2 z hz y (List.mem_cons_self)⟩, hh.2.1⟩
  · rintro ⟨hpre, hsuf⟩
    have hp := (strict_snoc_iff xs y).mp hpre
    have hs := (strict_cons_iff y ys).mp hsuf
    apply List.pairwise_append.mpr
    refine ⟨hp.1, hsuf, ?_⟩
    intro a ha b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hp.2 a ha
    · exact lt_trans (hp.2 a ha) (hs.1 b hb)

/-- Parentheses fix the source's four-part parsing explicitly. -/
theorem strict_four_parts [Preorder α] (x y : α) (xs ys : List α) :
    Strict (x :: (xs ++ y :: ys)) ↔
      Strict (x :: xs) ∧ x < y ∧ Strict (xs ++ [y]) ∧ Strict (y :: ys) := by
  change Strict ((x :: xs) ++ y :: ys) ↔ _
  rw [strict_middle]
  constructor
  · rintro ⟨hp, hs⟩
    have hsnoc := (strict_snoc_iff (x :: xs) y).mp hp
    exact ⟨hsnoc.1, hsnoc.2 x List.mem_cons_self, strict_tail hp, hs⟩
  · rintro ⟨hx, hxy, hp, hs⟩
    refine ⟨(strict_snoc_iff (x :: xs) y).mpr ⟨hx, ?_⟩, hs⟩
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hxy
    · exact ((strict_snoc_iff xs y).mp hp).2 z hz

section LinearOrder
variable [LinearOrder α]

theorem insert_distribution (x a : α) (xs ys : List α)
    (hprefix : Strict (xs ++ [a])) :
    insert x (xs ++ a :: ys) =
      if x < a then insert x xs ++ a :: ys else xs ++ insert x (a :: ys) := by
  induction xs with
  | nil =>
      by_cases hxa : x < a
      · simp [insert, hxa]
      · simp [hxa]
  | cons b xs ih =>
      have hba : b < a := ((strict_snoc_iff (b :: xs) a).mp hprefix).2 b List.mem_cons_self
      have tail := strict_tail hprefix
      by_cases hxb : x < b
      · have hxa := lt_trans hxb hba
        simp [List.cons_append, insert, hxb, hxa]
      · by_cases heq : x = b
        · subst x
          simp [List.cons_append, insert, hba]
        · have hi := ih tail
          by_cases hxa : x < a
          · simpa only [List.cons_append, insert, ite_eq_right hxb,
              ite_eq_right heq, ite_eq_left hxa] using congrArg (List.cons b) hi
          · simpa only [List.cons_append, insert, ite_eq_right hxb,
              ite_eq_right heq, ite_eq_right hxa] using congrArg (List.cons b) hi

theorem insert_distribution_lt (x a : α) (xs ys : List α)
    (hprefix : Strict (xs ++ [a])) (h : x < a) :
    insert x (xs ++ a :: ys) = insert x xs ++ a :: ys := by
  rw [insert_distribution x a xs ys hprefix, ite_eq_left h]

theorem insert_distribution_ge (x a : α) (xs ys : List α)
    (hprefix : Strict (xs ++ [a])) (h : a ≤ x) :
    insert x (xs ++ a :: ys) = xs ++ insert x (a :: ys) := by
  rw [insert_distribution x a xs ys hprefix, ite_eq_right (not_lt_of_ge h)]

theorem delete_distribution (x a : α) (xs ys : List α)
    (whole : Strict (xs ++ a :: ys)) :
    delete x (xs ++ a :: ys) =
      if x < a then delete x xs ++ a :: ys else xs ++ delete x (a :: ys) := by
  have parts := (strict_middle xs a ys).mp whole
  by_cases hxa : x < a
  · have absent : x ∉ a :: ys := by
      intro hx
      rcases List.mem_cons.mp hx with heq | hx
      · exact (ne_of_lt hxa) heq
      · exact lt_asymm hxa (((strict_cons_iff a ys).mp parts.2).1 x hx)
    rw [ite_eq_left hxa, delete_eq_erase, delete_eq_erase]
    by_cases hx : x ∈ xs
    · exact List.erase_append_left _ hx
    · rw [List.erase_append_right _ hx, List.erase_of_not_mem absent, List.erase_of_not_mem hx]
  · have absent : x ∉ xs := by
      intro hx
      exact hxa (((strict_snoc_iff xs a).mp parts.1).2 x hx)
    rw [ite_eq_right hxa, delete_eq_erase, delete_eq_erase]
    exact List.erase_append_right _ absent

theorem delete_distribution_lt (x a : α) (xs ys : List α)
    (whole : Strict (xs ++ a :: ys)) (h : x < a) :
    delete x (xs ++ a :: ys) = delete x xs ++ a :: ys := by
  rw [delete_distribution x a xs ys whole, ite_eq_left h]

theorem delete_distribution_ge (x a : α) (xs ys : List α)
    (whole : Strict (xs ++ a :: ys)) (h : a ≤ x) :
    delete x (xs ++ a :: ys) = xs ++ delete x (a :: ys) := by
  rw [delete_distribution x a xs ys whole, ite_eq_right (not_lt_of_ge h)]

end LinearOrder
end Search.OrderedList

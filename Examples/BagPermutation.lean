import Examples.MultisetSorting

/-!
VFA 2.1 BagPerm. Bags remain raw lists; equivalence forgets order and retains
multiplicity. The count equations and fold theorem give the literal recursive
source definition, with stored-head/query Boolean equality orientation. The
same shared occurrence inversions justify the complete backwards proof.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.BagPermutation

abbrev Bag := List Nat

abbrev count (a : Nat) (xs : Bag) : Nat := Sequences.Multiplicity.contents xs a

theorem count_nil (a : Nat) : count a [] = 0 := rfl

theorem count_cons (a b : Nat) (xs : Bag) :
    count a (b :: xs) = (if b == a then 1 else 0) + count a xs :=
  congrFun (Sequences.Multiplicity.contents_cons b xs) a

/-- All-input correspondence with BagPerm's recursive source counter. -/
theorem count_eq_foldr (a : Nat) (xs : Bag) :
    count a xs = xs.foldr (fun b rest => (if b == a then 1 else 0) + rest) 0 := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp only [List.foldr_cons, count_cons, ih]

def BagEquiv (xs ys : Bag) : Prop := ∀ a, count a xs = count a ys

theorem bagEquiv_iff_contents (xs ys : Bag) :
    BagEquiv xs ys ↔ MultisetSorting.contents xs = MultisetSorting.contents ys := by
  constructor
  · exact funext
  · intro h a
    exact congrFun h a

theorem bag_eqv_refl (xs : Bag) : BagEquiv xs xs := fun _ => rfl

theorem bag_eqv_sym (xs ys : Bag) (h : BagEquiv xs ys) : BagEquiv ys xs :=
  fun a => (h a).symm

theorem bag_eqv_trans (xs ys zs : Bag) (hxy : BagEquiv xs ys) (hyz : BagEquiv ys zs) :
    BagEquiv xs zs := fun a => (hxy a).trans (hyz a)

theorem bag_eqv_cons (a : Nat) (xs ys : Bag) (h : BagEquiv xs ys) :
    BagEquiv (a :: xs) (a :: ys) := by
  intro b
  simp only [count_cons, h b]

def IsSortingAlgorithm (f : List Nat → List Nat) : Prop :=
  ∀ xs, BagEquiv xs (f xs) ∧ InsertionSorting.Sorted (f xs)

/-- The source's insertion proof by induction, in the pointwise count presentation. -/
theorem insert_bag (a : Nat) (xs : Bag) : BagEquiv (a :: xs) (InsertionSorting.insert a xs) := by
  induction xs with
  | nil => exact bag_eqv_refl _
  | cons b xs ih =>
    rw [InsertionSorting.insert_cons]
    split_ifs with hab
    · exact bag_eqv_refl _
    · intro n
      have hn := ih n
      simp only [count_cons] at hn ⊢
      omega

theorem sort_bag (xs : Bag) : BagEquiv xs (InsertionSorting.sort xs) := by
  induction xs with
  | nil => exact bag_eqv_refl _
  | cons a xs ih =>
    exact bag_eqv_trans _ _ _ (bag_eqv_cons a _ _ ih) (insert_bag a _)

theorem insertion_sort_correct : IsSortingAlgorithm InsertionSorting.sort :=
  fun xs => ⟨sort_bag xs, InsertionSorting.sort_sorted xs⟩

/-- The shared proof preserves the source's induction on permutation evidence. -/
theorem perm_bag (xs ys : Bag) (h : xs.Perm ys) : BagEquiv xs ys :=
  (bagEquiv_iff_contents xs ys).mpr (Sequences.Multiplicity.perm_contents h)

theorem bag_nil_inv (xs : Bag) (h : BagEquiv [] xs) : xs = [] :=
  Sequences.Multiplicity.eq_nil_of_contents_zero xs (fun a => (h a).symm)

theorem bag_cons_inv (xs : Bag) (a n : Nat) (h : n + 1 = count a xs) :
    ∃ front back, xs = front ++ a :: back ∧ count a (front ++ back) = n :=
  Sequences.Multiplicity.exists_split_of_count_eq_succ xs a n h

theorem count_insert_other (front back : Bag) (x y : Nat) (h : y ≠ x) :
    count y (front ++ x :: back) = count y (front ++ back) :=
  Sequences.Multiplicity.count_insert_other front back x y h

/-- The shared reverse proof uses empty-list and occurrence-split inversions. -/
theorem bag_perm (xs ys : Bag) (h : BagEquiv xs ys) : xs.Perm ys :=
  Sequences.Multiplicity.perm_of_contents_eq ((bagEquiv_iff_contents xs ys).mp h)

theorem bag_eqv_iff_perm (xs ys : Bag) : BagEquiv xs ys ↔ xs.Perm ys :=
  ⟨bag_perm xs ys, perm_bag xs ys⟩

theorem sort_specifications_equivalent (f : List Nat → List Nat) :
    InsertionSorting.IsSortingAlgorithm f ↔ IsSortingAlgorithm f := by
  constructor
  · intro h xs
    exact ⟨perm_bag xs (f xs) (h xs).1, (h xs).2⟩
  · intro h xs
    exact ⟨bag_perm xs (f xs) (h xs).1, (h xs).2⟩

/-- These are distinct raw lists despite agreement of their complete bag observation. -/
theorem equivalent_bags_need_not_be_equal :
    BagEquiv [2, 1, 1] [1, 2, 1] ∧ ([2, 1, 1] : Bag) ≠ [1, 2, 1] :=
  ⟨perm_bag _ _ (List.Perm.swap _ _ _), by decide⟩

theorem pi_bag :
    BagEquiv [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9] := by
  simpa only [InsertionSorting.sort_pi] using sort_bag [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]

end Examples.BagPermutation

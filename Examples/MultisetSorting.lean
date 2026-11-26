import Applications.Sorting.Multiplicity
import Examples.InsertionSorting

/-!
VFA 2.1 Multiset, including every advanced inverse lemma. The source carrier is
the unrestricted Nat → Nat function space. Its recursive contents operation is
identified with the shared list observation by the empty/cons and fold equations;
no finite-support hypothesis is silently added. Source insertion and tail-first
sort are the existing exact Nat operations from InsertionSorting.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.MultisetSorting

abbrev Value := Nat
abbrev Multiset := Sequences.Multiplicity.Counts Value
abbrev empty : Multiset := Sequences.Multiplicity.empty
abbrev singleton (a : Value) : Multiset := Sequences.Multiplicity.singleton a
abbrev union (a b : Multiset) : Multiset := Sequences.Multiplicity.union a b
abbrev contents (xs : List Value) : Multiset := Sequences.Multiplicity.contents xs

theorem union_assoc (a b c : Multiset) : union a (union b c) = union (union a b) c :=
  Sequences.Multiplicity.union_assoc a b c

theorem union_comm (a b : Multiset) : union a b = union b a :=
  Sequences.Multiplicity.union_comm a b

theorem union_swap (a b c : Multiset) : union a (union b c) = union b (union a c) :=
  Sequences.Multiplicity.union_swap a b c

theorem contents_nil : contents [] = empty := rfl

theorem contents_cons (a : Value) (xs : List Value) :
    contents (a :: xs) = union (singleton a) (contents xs) :=
  Sequences.Multiplicity.contents_cons_union a xs

/-- All-input correspondence with the source's recursive empty/union definition. -/
theorem contents_eq_foldr (xs : List Value) :
    contents xs = xs.foldr (fun a rest => union (singleton a) rest) empty := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.foldr_cons, contents_cons, ih]

def IsSortingAlgorithm (f : List Nat → List Nat) : Prop :=
  ∀ xs, contents xs = contents (f xs) ∧ InsertionSorting.Sorted (f xs)

/-- Source-directed induction uses union laws, without extensionality per branch. -/
theorem insert_contents (a : Nat) (xs : List Nat) :
    contents (InsertionSorting.insert a xs) = contents (a :: xs) := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    rw [InsertionSorting.insert_cons]
    split_ifs with hab
    · rfl
    · simp only [contents_cons, ih]
      exact union_swap _ _ _

/-- Tail-first sorting preserves the function observation by list induction. -/
theorem sort_contents (xs : List Nat) :
    contents xs = contents (InsertionSorting.sort xs) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [InsertionSorting.sort_cons, insert_contents]
    simp only [contents_cons, ih]

theorem insertion_sort_correct : IsSortingAlgorithm InsertionSorting.sort :=
  fun xs => ⟨sort_contents xs, InsertionSorting.sort_sorted xs⟩

/-- The source's eleven-element example preserves all three occurrences of 5. -/
theorem sort_pi_same_contents :
    contents (InsertionSorting.sort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]) =
      contents [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] :=
  (sort_contents _).symm

theorem pi_fives :
    contents (InsertionSorting.sort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]) 5 = 3 := by
  rw [sort_pi_same_contents]
  rfl

/-- The shared forward proof inducts on the permutation evidence. -/
theorem perm_contents (xs ys : List Nat) (h : xs.Perm ys) :
    contents xs = contents ys := Sequences.Multiplicity.perm_contents h

theorem contents_nil_inv (xs : List Nat) (h : ∀ a, 0 = contents xs a) : xs = [] :=
  Sequences.Multiplicity.eq_nil_of_contents_zero xs (fun a => (h a).symm)

theorem contents_cons_inv (xs : List Nat) (a n : Nat) (h : n + 1 = contents xs a) :
    ∃ front back, xs = front ++ a :: back ∧ contents (front ++ back) a = n :=
  Sequences.Multiplicity.exists_split_of_count_eq_succ xs a n h

theorem contents_insert_other (front back : List Nat) (x y : Nat) (h : y ≠ x) :
    contents (front ++ x :: back) y = contents (front ++ back) y :=
  Sequences.Multiplicity.count_insert_other front back x y h

/-- The shared inverse proof uses all three inversion steps above. -/
theorem contents_perm (xs ys : List Nat) (h : contents xs = contents ys) :
    xs.Perm ys := Sequences.Multiplicity.perm_of_contents_eq h

theorem same_contents_iff_perm (xs ys : List Nat) :
    contents xs = contents ys ↔ xs.Perm ys :=
  ⟨contents_perm xs ys, perm_contents xs ys⟩

theorem sort_specifications_equivalent (f : List Nat → List Nat) :
    InsertionSorting.IsSortingAlgorithm f ↔ IsSortingAlgorithm f :=
  Applications.Sorting.Multiplicity.contract_equivalent InsertionSorting.Sorted f

/-- The source's unrestricted carrier contains functions no finite list represents. -/
theorem infinite_support_boundary (xs : List Nat) : contents xs ≠ fun _ => 1 :=
  Sequences.Multiplicity.constant_one_not_contents xs

/-- Inversion retains the exact number of repeated occurrences in the remainder. -/
theorem repeated_occurrence_decomposition :
    ∃ front back, ([2, 1, 2] : List Nat) = front ++ 2 :: back ∧
      contents (front ++ back) 2 = 1 :=
  contents_cons_inv [2, 1, 2] 2 1 rfl

end Examples.MultisetSorting

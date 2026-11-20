import Mathlib.Data.List.Perm.Basic

/-!
Multiplicity observations of lists, with an unrestricted function space for
specifications. Empty, singleton and union are operations on `α → Nat`; such a
function need not be the contents of a finite list. The list observation has one
owner here and reuses `List.count`. The inverse proof follows occurrence
decomposition, retaining the mathematical route of VFA Multiset and BagPerm.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Sequences.Multiplicity

universe u
variable {α : Type u}

/-- Unrestricted natural-valued functions, including infinite-support functions. -/
abbrev Counts (α : Type u) := α → Nat

def empty : Counts α := fun _ => 0

/-- The query is the first argument to Boolean equality, as in VFA Multiset. -/
def singleton [BEq α] (a : α) : Counts α := fun b => if b == a then 1 else 0

def union (a b : Counts α) : Counts α := fun x => a x + b x

theorem empty_apply (x : α) : empty x = 0 := rfl

theorem singleton_apply [BEq α] (a b : α) :
    singleton a b = if b == a then 1 else 0 := rfl

theorem union_apply (a b : Counts α) (x : α) : union a b x = a x + b x := rfl

theorem union_assoc (a b c : Counts α) : union a (union b c) = union (union a b) c := by
  funext x
  exact (Nat.add_assoc (a x) (b x) (c x)).symm

theorem union_comm (a b : Counts α) : union a b = union b a := by
  funext x
  exact Nat.add_comm (a x) (b x)

theorem union_swap (a b c : Counts α) : union a (union b c) = union b (union a c) := by
  rw [union_assoc, union_comm a b, ← union_assoc]

theorem union_empty (a : Counts α) : union a empty = a := by
  funext x
  exact Nat.add_zero (a x)

theorem empty_union (a : Counts α) : union empty a = a := by
  rw [union_comm, union_empty]

/-- The authoritative multiplicity function of a finite list. -/
def contents [BEq α] (xs : List α) : Counts α := fun a => xs.count a

theorem contents_apply [BEq α] (xs : List α) (a : α) : contents xs a = xs.count a := rfl

theorem contents_nil [BEq α] : contents ([] : List α) = empty := rfl

/-- The stored element is the first argument to Boolean equality in List.count. -/
theorem contents_cons [BEq α] (a : α) (xs : List α) :
    contents (a :: xs) = fun b => (if a == b then 1 else 0) + contents xs b := by
  funext b
  simp [contents, List.count_cons, Nat.add_comm]

/-- Lawful equality permits the query-first convention used by singleton. -/
theorem contents_cons_by_query [BEq α] [LawfulBEq α] (a : α) (xs : List α) :
    contents (a :: xs) = fun b => (if b == a then 1 else 0) + contents xs b := by
  funext b
  by_cases h : a = b
  · subst b
    simp [contents, Nat.add_comm]
  · simp [contents, h, Ne.symm h]

theorem contents_cons_union [BEq α] [LawfulBEq α] (a : α) (xs : List α) :
    contents (a :: xs) = union (singleton a) (contents xs) :=
  contents_cons_by_query a xs

theorem contents_append [BEq α] (xs ys : List α) :
    contents (xs ++ ys) = union (contents xs) (contents ys) := by
  funext a
  exact List.count_append

theorem contents_eq_iff_count [BEq α] (xs ys : List α) :
    contents xs = contents ys ↔ ∀ a, xs.count a = ys.count a := by
  constructor
  · intro h a
    exact congrFun h a
  · exact funext

/-- Forward correspondence by induction on permutation evidence. Reordering the
stored elements preserves any Boolean query, without requiring lawful equality. -/
theorem perm_contents [BEq α] {xs ys : List α} (h : xs.Perm ys) :
    contents xs = contents ys := by
  induction h with
  | nil => rfl
  | cons a _ ih =>
    rw [contents_cons, contents_cons, ih]
  | swap a b xs =>
    funext x
    simp only [contents_cons]
    exact Nat.add_left_comm _ _ _
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

section Lawful
variable [BEq α] [LawfulBEq α]

/-- Zero multiplicities characterize the empty list. -/
theorem eq_nil_of_contents_zero (xs : List α) (h : ∀ a, contents xs a = 0) :
    xs = [] := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    have ha := h a
    simp [contents] at ha

/-- Remove a specific occurrence and retain its exact residual multiplicity. -/
theorem exists_split_of_count_eq_succ (xs : List α) (a : α) (n : Nat)
    (h : n + 1 = contents xs a) :
    ∃ front back, xs = front ++ a :: back ∧ contents (front ++ back) a = n := by
  have ha : a ∈ xs := List.count_pos_iff.mp (by change 0 < contents xs a; omega)
  obtain ⟨front, back, hxs⟩ := List.mem_iff_append.mp ha
  refine ⟨front, back, hxs, ?_⟩
  subst xs
  simp only [contents, List.count_append, List.count_cons_self] at h ⊢
  omega

/-- Removing the displayed occurrence changes no other query's multiplicity. -/
theorem count_insert_other (front back : List α) (x y : α) (h : y ≠ x) :
    contents (front ++ x :: back) y = contents (front ++ back) y := by
  simp only [contents, List.count_append, List.count_cons_of_ne h.symm]

/-- Backward correspondence by the nil, occurrence-split and other-count inversions.
This does not hide that proof route behind the library's count/permutation iff. -/
theorem perm_of_contents_eq {xs ys : List α} (h : contents xs = contents ys) :
    xs.Perm ys := by
  induction xs generalizing ys with
  | nil =>
    have hy : ys = [] := eq_nil_of_contents_zero ys (fun a => by rw [← h]; rfl)
    rw [hy]
  | cons a xs ih =>
    have ha : contents xs a + 1 = contents ys a := by
      rw [← h]
      exact (List.count_cons_self).symm
    obtain ⟨front, back, hy, hrest⟩ := exists_split_of_count_eq_succ ys a (contents xs a) ha
    have heq : contents xs = contents (front ++ back) := by
      funext b
      by_cases hb : b = a
      · subst b
        exact hrest.symm
      · have hc := congrFun h b
        rw [hy] at hc
        have hl : contents (a :: xs) b = contents xs b :=
          List.count_cons_of_ne (Ne.symm hb)
        exact hl.symm.trans (hc.trans (count_insert_other front back a b hb))
    rw [hy]
    exact List.perm_cons_append_cons a (ih heq)

theorem contents_eq_iff_perm (xs ys : List α) :
    contents xs = contents ys ↔ xs.Perm ys :=
  ⟨perm_of_contents_eq, perm_contents⟩

end Lawful

/-- Every finite list of naturals omits a natural number. -/
theorem finite_contents_has_zero (xs : List Nat) : ∃ n, contents xs n = 0 := by
  have bounded : ∃ n, ∀ b ∈ xs, b < n := by
    induction xs with
    | nil => exact ⟨0, by simp⟩
    | cons a xs ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨a + n + 1, ?_⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · omega
      · have := hn b hb
        omega
  obtain ⟨n, hn⟩ := bounded
  refine ⟨n, List.count_eq_zero.mpr ?_⟩
  intro hmem
  exact Nat.lt_irrefl n (hn n hmem)

/-- Infinite-support functions belong to Counts Nat but not to the finite-list image. -/
theorem constant_one_not_contents (xs : List Nat) : contents xs ≠ fun _ => 1 := by
  obtain ⟨n, hn⟩ := finite_contents_has_zero xs
  intro h
  have hone : contents xs n = 1 := congrFun h n
  omega

end Sequences.Multiplicity

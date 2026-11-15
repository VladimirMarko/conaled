import Batteries.Data.List.Lemmas
import Batteries.Data.List.Pairwise
import Batteries.Data.List.Perm

/-!
# Draft reusable sorting specification bridges

Cross-cutting preparation for VFA Sort, Multiset and BagPerm. There are no
sorting algorithm definitions here. Existing List specifications are reused;
the source's arbitrary function space `Nat → Nat` is not restricted to finite
support. Only functions observed from finite lists are related to permutation.

Proposed integration: Applications/Sorting/Specification.lean, namespace
Applications.Sorting.Specification. Chapter acceptance remains separate.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.Sorting.Specification

universe u v
variable {α : Type u} {κ : Type v}

/-- Every pair of successful optional lookups in increasing positions is related.
This is the generic form of VFA's `sorted'`; no default value is needed. -/
def Indexed (R : α → α → Prop) (xs : List α) : Prop :=
  ∀ (i j : Nat) (a b : α), i < j → xs[i]? = some a → xs[j]? = some b → R a b

/-- The default-valued form of indexed ordering, with explicit valid bounds.
This is the generic form of VFA's `sorted''`. -/
def BoundedIndexed (R : α → α → Prop) (defaultValue : α) (xs : List α) : Prop :=
  ∀ i j : Nat, i < j → j < xs.length →
    R ((xs[i]?).getD defaultValue) ((xs[j]?).getD defaultValue)

/-- The optional-lookup presentation is also the ordinary default-valued
list lookup used by the source's `nth` specification. -/
theorem boundedIndexed_iff_getD (R : α → α → Prop)
    (defaultValue : α) (xs : List α) :
    BoundedIndexed R defaultValue xs ↔
      ∀ i j : Nat, i < j → j < xs.length →
        R (xs.getD i defaultValue) (xs.getD j defaultValue) := by
  simp only [BoundedIndexed, List.getD_eq_getElem?_getD]

/-- Indexed ordering and pairwise ordering agree without any order laws. -/
theorem pairwise_iff_indexed (R : α → α → Prop) (xs : List α) :
    xs.Pairwise R ↔ Indexed R xs := by
  constructor
  · intro hp i j a b hij hi hj
    obtain ⟨hi', ha⟩ := List.getElem?_eq_some_iff.mp hi
    obtain ⟨hj', hb⟩ := List.getElem?_eq_some_iff.mp hj
    rw [← ha, ← hb]
    exact (List.pairwise_iff_getElem.mp hp) i j hi' hj' hij
  · intro hi
    apply List.pairwise_iff_getElem.mpr
    intro i j hib hjb hij
    exact hi i j xs[i] xs[j] hij
      (List.getElem?_eq_getElem hib) (List.getElem?_eq_getElem hjb)

/-- Successful bounded lookups never consult their default value. -/
theorem pairwise_iff_boundedIndexed (R : α → α → Prop)
    (defaultValue : α) (xs : List α) :
    xs.Pairwise R ↔ BoundedIndexed R defaultValue xs := by
  constructor
  · intro hp i j hij hj
    have hi : i < xs.length := Nat.lt_trans hij hj
    simpa only [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
      Option.getD_some] using (List.pairwise_iff_getElem.mp hp) i j hi hj hij
  · intro hb
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    simpa only [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
      Option.getD_some] using hb i j hij hj

theorem indexed_iff_boundedIndexed (R : α → α → Prop)
    (defaultValue : α) (xs : List α) :
    Indexed R xs ↔ BoundedIndexed R defaultValue xs :=
  (pairwise_iff_indexed R xs).symm.trans
    (pairwise_iff_boundedIndexed R defaultValue xs)

theorem boundedIndexed_default_irrelevant (R : α → α → Prop)
    (defaultValue otherDefault : α) (xs : List α) :
    BoundedIndexed R defaultValue xs ↔ BoundedIndexed R otherDefault xs :=
  (pairwise_iff_boundedIndexed R defaultValue xs).symm.trans
    (pairwise_iff_boundedIndexed R otherDefault xs)

/-- Adjacent ordering requires transitivity to imply all earlier/later pairs.
No totality, reflexivity, decidable order, or antisymmetry is used. -/
theorem adjacent_iff_indexed (R : α → α → Prop) [Trans R R R] (xs : List α) :
    xs.IsChain R ↔ Indexed R xs :=
  List.isChain_iff_pairwise.trans (pairwise_iff_indexed R xs)

theorem adjacent_iff_boundedIndexed (R : α → α → Prop) [Trans R R R]
    (defaultValue : α) (xs : List α) :
    xs.IsChain R ↔ BoundedIndexed R defaultValue xs :=
  List.isChain_iff_pairwise.trans (pairwise_iff_boundedIndexed R defaultValue xs)

/-- This left side is definitionally the existing `Applications.Sorting.KeySorted`
contract when integrated with `Applications.Sorting.Stable`. -/
theorem keySorted_shape_iff_indexed [LE κ] (key : α → κ) (xs : List α) :
    xs.Pairwise (fun a b => key a ≤ key b) ↔
      Indexed (fun a b => key a ≤ key b) xs :=
  pairwise_iff_indexed _ xs

/-- An unrestricted function-space observation of a finite list.
The codomain is `α → Nat`, not a finite-support representation. -/
def contents [BEq α] (xs : List α) : α → Nat := fun a => xs.count a

theorem contents_nil [BEq α] : contents ([] : List α) = fun _ => 0 := by
  funext a
  rfl

/-- This equation retains the source's singleton-plus-tail order. -/
theorem contents_cons [BEq α] (a : α) (xs : List α) :
    contents (a :: xs) = fun b => (if a == b then 1 else 0) + contents xs b := by
  funext b
  simp only [contents, List.count_cons, Nat.add_comm]

/-- The function-bag source tests the query against the singleton value, whereas
List.count tests the list value against the query. Lawful equality relates them. -/
theorem contents_cons_by_query [BEq α] [LawfulBEq α] (a : α) (xs : List α) :
    contents (a :: xs) = fun b => (if b == a then 1 else 0) + contents xs b := by
  funext b
  simp only [contents, List.count_cons, beq_iff_eq]
  by_cases h : a = b
  · simp [h, Nat.add_comm]
  · simp [h, Ne.symm h]

theorem contents_append [BEq α] (xs ys : List α) :
    contents (xs ++ ys) = fun a => contents xs a + contents ys a := by
  funext a
  exact List.count_append

/-- Extensional function equality is exactly equality of every occurrence count. -/
theorem contents_eq_iff_count [BEq α] (xs ys : List α) :
    contents xs = contents ys ↔ ∀ a, xs.count a = ys.count a :=
  ⟨fun h a => congrFun h a, fun h => funext h⟩

/-- Under lawful equality, counts characterize occurrence permutation. -/
theorem contents_eq_iff_perm [BEq α] [LawfulBEq α] (xs ys : List α) :
    contents xs = contents ys ↔ xs.Perm ys :=
  (contents_eq_iff_count xs ys).trans List.perm_iff_count.symm

/-- The change of contents specification is independent of the ordering relation
and of the algorithm. This does not add a stability guarantee. -/
theorem sorting_specifications_equivalent [BEq α] [LawfulBEq α]
    (R : α → α → Prop) (f : List α → List α) :
    (∀ xs, xs.Perm (f xs) ∧ (f xs).Pairwise R) ↔
      (∀ xs, contents xs = contents (f xs) ∧ (f xs).Pairwise R) := by
  constructor
  · intro h xs
    exact ⟨(contents_eq_iff_perm _ _).mpr (h xs).1, (h xs).2⟩
  · intro h xs
    exact ⟨(contents_eq_iff_perm _ _).mp (h xs).1, (h xs).2⟩

/-- Every finite list of naturals omits a value. The proof constructs a bound,
without defining or invoking any sorting algorithm. -/
theorem finite_contents_has_zero (xs : List Nat) : ∃ n, contents xs n = 0 := by
  have bounded : ∃ n, ∀ a ∈ xs, a < n := by
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

/-- The source function space contains infinite-support values which are not
the contents of any finite list. Do not identify that whole space with Multiset. -/
theorem constant_one_not_contents (xs : List Nat) : contents xs ≠ fun _ => 1 := by
  obtain ⟨n, hn⟩ := finite_contents_has_zero xs
  intro h
  have hone : contents xs n = 1 := congrFun h n
  omega

end Applications.Sorting.Specification

namespace Examples.SortingSpecificationDraft
open Applications.Sorting.Specification

/-- The optional-index statement follows from the independent expected ordering. -/
theorem signed_indexed : Indexed (fun a b : Int => a ≤ b) [-3, -1, 2] :=
  (pairwise_iff_indexed _ _).mp (by decide)

/-- The adjacent-to-indexed bridge permits equal successive keys. -/
theorem adjacent_to_indexed : Indexed (fun a b : Nat => a ≤ b) [1, 2, 2] :=
  (adjacent_iff_indexed _ _).mp (by decide)

/-- Two very different default values produce the same valid-index contract. -/
theorem signed_defaults :
    BoundedIndexed (fun a b : Int => a ≤ b) (-999) [-3, -1, 2] ∧
      BoundedIndexed (fun a b : Int => a ≤ b) 999 [-3, -1, 2] := by
  have h := (indexed_iff_boundedIndexed _ (-999) _).mp signed_indexed
  exact ⟨h, (boundedIndexed_default_irrelevant _ (-999) 999 _).mp h⟩

/-- Without transitivity, an adjacent chain need not order the endpoints. -/
theorem nontransitive_boundary :
    ([0, 1, 2] : List Nat).IsChain (fun a b => b = a + 1) ∧
      ¬ Indexed (fun a b : Nat => b = a + 1) [0, 1, 2] := by
  refine ⟨by decide, ?_⟩
  intro h
  have wrong := h 0 2 0 2 (by decide) rfl rfl
  contradiction

/-- Dropping the valid-index bound would incorrectly reject a sorted singleton. -/
theorem index_bound_matters :
    ([1] : List Nat).Pairwise (· ≤ ·) ∧
      ¬ (∀ i j : Nat, i < j → (([1] : List Nat)[i]?).getD 0 ≤
        (([1] : List Nat)[j]?).getD 0) := by
  refine ⟨by decide, ?_⟩
  intro h
  have wrong := h 0 1 (by decide)
  contradiction

/-- Equal membership alone loses multiplicity. The function-space bridge notices it. -/
theorem multiplicities_matter :
    (∀ n : Nat, n ∈ [1, 1] ↔ n ∈ [1]) ∧
      contents ([1, 1] : List Nat) ≠ contents [1] := by
  refine ⟨by simp, ?_⟩
  intro h
  have hp := (contents_eq_iff_perm _ _).mp h
  have hlen := hp.length_eq
  contradiction

/-- This is a use of the permutation-to-function bridge, retaining duplicate 1s. -/
theorem reordered_contents :
    contents ([2, 1, 1] : List Nat) = contents [1, 2, 1] :=
  (contents_eq_iff_perm _ _).mpr (List.Perm.swap _ _ _)

/-- The function observation of concatenation adds multiplicities. -/
theorem concatenated_occurrences : contents ([1, 2] ++ [1] : List Nat) 1 = 2 := by
  rw [contents_append]
  rfl

/-- A client can switch both the ordering and contents observations without
knowing how its proposed implementation works. No implementation is assumed
correct unless the supplied observable contract holds. -/
theorem recover_pairwise_spec (f : List Int → List Int)
    (h : ∀ xs, contents xs = contents (f xs) ∧ Indexed (· ≤ ·) (f xs)) :
    ∀ xs, xs.Perm (f xs) ∧ (f xs).Pairwise (· ≤ ·) := by
  apply (sorting_specifications_equivalent (· ≤ ·) f).mpr
  intro xs
  exact ⟨(h xs).1, (pairwise_iff_indexed _ _).mpr (h xs).2⟩

/-- Records require only ordered keys, not an ordering on payloads. -/
theorem records_indexed :
    Indexed (fun a b : Nat × String => a.1 ≤ b.1)
      [(1, "small"), (2, "first"), (2, "last")] :=
  (keySorted_shape_iff_indexed Prod.fst _).mp (by decide)

/-- Sortedness and exact contents permit reordering equal-key payloads;
the existing StableSort contract must retain its separate filter observation. -/
theorem sorted_contents_do_not_imply_stability :
    Indexed (fun a b : Nat × String => a.1 ≤ b.1)
      [(2, "last"), (2, "first")] ∧
    contents ([(2, "first"), (2, "last")] : List (Nat × String)) =
      contents [(2, "last"), (2, "first")] ∧
    ([(2, "last"), (2, "first")] : List (Nat × String)).filter
      (fun r => decide (r.1 = 2)) ≠
    ([(2, "first"), (2, "last")] : List (Nat × String)).filter
      (fun r => decide (r.1 = 2)) := by
  exact ⟨(pairwise_iff_indexed _ _).mp (by decide),
    (contents_eq_iff_perm _ _).mpr (List.Perm.swap _ _ _), by decide⟩

/-- Counts under an unlawful equality test do not characterize true permutation. -/
theorem lawful_equality_matters :
    (letI : BEq Nat := ⟨fun _ _ => false⟩
     contents ([1] : List Nat) = contents []) ∧
      ¬ ([1] : List Nat).Perm [] := by
  constructor
  · funext n
    rfl
  · intro h
    have wrong := h.length_eq
    contradiction

end Examples.SortingSpecificationDraft

import Examples.FunctionalBasics
import Examples.ListLibrary
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.DivMod
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Defs

/-! Typed notation correspondences and semantic boundaries for FDSA Appendix C.
Standard binders, containers and operations are reused. Source editor escapes
are not recreated as a second parser. Coverage and statement review are in
`docs/research/fdsa-notation-map.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.FunctionalNotation
universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

theorem composition_and_eta (f : β → γ) (g : α → β) :
    (fun x => (f ∘ g) x) = (fun x => f (g x)) := rfl

/-- HOL truth-valued formulas become propositions; executable Booleans have an
explicit decidability bridge.
-/
theorem boolean_truth (P Q : Prop) [Decidable P] [Decidable Q] :
    decide (P ∧ Q) = (decide P && decide Q) ∧
    decide (P ∨ Q) = (decide P || decide Q) ∧
    decide (¬ P) = !decide P := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq]

theorem comprehension_order_and_repetition :
    ([2, 2] : List Nat).flatMap (fun x => [x, x + 10]) = [2, 12, 2, 12] := rfl

theorem set_union_intersection (A B : Set α) (x : α) :
    (x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B) ∧
    (x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B) := ⟨Iff.rfl, Iff.rfl⟩

theorem proper_subset (A B : Set α) : A ⊂ B ↔ A ⊆ B ∧ A ≠ B :=
  Set.ssubset_iff_subset_ne

theorem direct_image (f : α → β) (A : Set α) (y : β) :
    y ∈ f '' A ↔ ∃ x ∈ A, f x = y := Iff.rfl

theorem restricted_comprehension (A : Set α) (P : α → Prop) (x : α) :
    x ∈ {a | a ∈ A ∧ P a} ↔ P x ∧ x ∈ A := and_comm

theorem two_variable_comprehension (f : α → β → γ) (P : α → β → Prop) (z : γ) :
    z ∈ {z | ∃ x y, z = f x y ∧ P x y} ↔ ∃ x y, P x y ∧ f x y = z := by
  simp only [Set.mem_setOf_eq, eq_comm, and_comm]

theorem indexed_union (A : Set α) (f : α → Set β) :
    Set.sUnion (f '' A) = ⋃ x ∈ A, f x := by
  ext y
  simp

theorem set_of_sets_observations (S : Set (Set α)) (x : α) :
    (x ∈ Set.sUnion S ↔ ∃ A ∈ S, x ∈ A) ∧
    (x ∈ Set.sInter S ↔ ∀ A ∈ S, x ∈ A) := ⟨Iff.rfl, Iff.rfl⟩

theorem bounded_quantifiers (A : Set α) (P : α → Prop) :
    ((∀ x ∈ A, P x) ↔ ∀ x, x ∈ A → P x) ∧
    ((∃ x ∈ A, P x) ↔ ∃ x, x ∈ A ∧ P x) := ⟨Iff.rfl, Iff.rfl⟩

theorem product_membership (A : Set α) (B : Set β) (x : α) (y : β) :
    (x, y) ∈ A ×ˢ B ↔ x ∈ A ∧ y ∈ B := Iff.rfl

theorem all_interval_memberships [LE α] [LT α] (a b x : α) :
    (x ∈ Set.Ici a ↔ a ≤ x) ∧ (x ∈ Set.Iic b ↔ x ≤ b) ∧
    (x ∈ Set.Icc a b ↔ a ≤ x ∧ x ≤ b) ∧
    (x ∈ Set.Ico a b ↔ a ≤ x ∧ x < b) ∧
    (x ∈ Set.Ioc a b ↔ a < x ∧ x ≤ b) ∧
    (x ∈ Set.Ioo a b ↔ a < x ∧ x < b) := by
  exact ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

/-- The source's upper-interval internal-name cell says `atLeast` incorrectly. -/
theorem upper_interval_correction :
    (0 : Nat) ∈ Set.Iic 1 ∧ (0 : Nat) ∉ Set.Ici 1 ∧
    (2 : Nat) ∈ Set.Ici 1 ∧ (2 : Nat) ∉ Set.Iic 1 := by
  decide

/-- Isabelle's unrestricted integer quotient rounds down; Lean's `/` uses its
Euclidean convention. They agree under the stated divisor restriction.
-/
theorem floor_division_nonnegative (m n : Int) (hn : 0 ≤ n) :
    m.fdiv n = m / n := Int.fdiv_eq_ediv_of_nonneg m hn

theorem negative_divisor_distinguishes :
    (5 : Int).fdiv (-2) = -3 ∧ (5 : Int) / (-2) = -2 := by
  decide

theorem floor_division_zero (m : Int) : m.fdiv 0 = 0 := by
  rw [floor_division_nonnegative m 0 (by decide)]
  simp

theorem typed_arithmetic :
    (5 : Nat) / 2 = 2 ∧ 2 * ((5 : Real) / 2) = 5 ∧
    abs (-3 : Int) = 3 ∧ (2 : Nat) ^ 3 = 8 := by
  norm_num

/-- Negative values distinguish integer floor/ceiling from truncated Nat views. -/
theorem floor_and_ceiling :
    Int.floor ((-3 : Real) / 2) = -2 ∧ Int.ceil ((-3 : Real) / 2) = -1 := by
  constructor
  · apply Int.floor_eq_iff.mpr
    norm_num
  · apply Int.ceil_eq_iff.mpr
    norm_num

theorem submultiset_is_not_support_subset :
    (([1, 1] : List Nat) : Multiset Nat) ⊆ (([1] : List Nat) : Multiset Nat) ∧
    ¬ (([1, 1] : List Nat) : Multiset Nat) ≤ (([1] : List Nat) : Multiset Nat) := by
  decide

theorem repeated_sum_and_product :
    ([2, 2, 3] : List Nat).sum = 7 ∧
    (([2, 2, 3] : List Nat) : Multiset Nat).sum = 7 ∧
    ({2, 3} : Finset Nat).sum id = 5 ∧
    ([2, 2, 3] : List Nat).prod = 12 ∧
    (([2, 2, 3] : List Nat) : Multiset Nat).prod = 12 ∧
    ({2, 3} : Finset Nat).prod id = 6 := by
  decide

theorem closed_interval_fold :
    (Finset.Icc (2 : Nat) 4).sum id = 9 ∧
    (Finset.Icc (2 : Nat) 4).prod id = 24 := by
  decide

/-- The ordinary source set fold tests finiteness of the whole index set,
not finiteness of the function's nonidentity support. Standard Finset folds
provide its finite branch. No algorithm for deciding set finiteness is claimed.
-/
@[to_additive finiteIndexSum]
noncomputable def finiteIndexProduct [CommMonoid β] (s : Set α) (f : α → β) : β := by
  classical
  exact if hs : s.Finite then hs.toFinset.prod f else 1

@[to_additive finiteIndexSum_of_finite]
theorem finiteIndexProduct_of_finite [CommMonoid β] (s : Set α) (f : α → β)
    (hs : s.Finite) : finiteIndexProduct s f = hs.toFinset.prod f := by
  classical
  simp [finiteIndexProduct, hs]

@[to_additive finiteIndexSum_of_infinite]
theorem finiteIndexProduct_of_infinite [CommMonoid β] (s : Set α) (f : α → β)
    (hs : s.Infinite) : finiteIndexProduct s f = 1 := by
  classical
  simp [finiteIndexProduct, hs]

@[to_additive finiteIndexSum_of_finset]
theorem finiteIndexProduct_of_finset [CommMonoid β] (s : Finset α) (f : α → β) :
    finiteIndexProduct (s : Set α) f = s.prod f := by
  rw [finiteIndexProduct_of_finite _ _ s.finite_toSet, Finset.finite_toSet_toFinset]

theorem finite_index_values :
    finiteIndexSum ({0} : Set Nat) (fun n => if n = 0 then 7 else 0) = 7 ∧
    finiteIndexProduct ({0} : Set Nat) (fun n => if n = 0 then 7 else 1) = 7 := by
  constructor
  · simpa using finiteIndexSum_of_finset ({0} : Finset Nat)
      (fun n => if n = 0 then 7 else 0)
  · simpa using finiteIndexProduct_of_finset ({0} : Finset Nat)
      (fun n => if n = 0 then 7 else 1)

/-- A single exceptional value does not change the source's infinite-index
convention. A support-based sum/product would retain that value instead.
-/
theorem infinite_index_values :
    finiteIndexSum (Set.univ : Set Nat) (fun n => if n = 0 then 7 else 0) = 0 ∧
    finiteIndexProduct (Set.univ : Set Nat) (fun n => if n = 0 then 7 else 1) = 1 :=
  ⟨finiteIndexSum_of_infinite _ _ Set.infinite_univ,
   finiteIndexProduct_of_infinite _ _ Set.infinite_univ⟩

theorem empty_index_type :
    finiteIndexSum (∅ : Set Empty) (Empty.elim : Empty → Nat) = 0 ∧
    finiteIndexProduct (∅ : Set Empty) (Empty.elim : Empty → Nat) = 1 := by
  constructor
  · simpa using finiteIndexSum_of_finset (∅ : Finset Empty) (Empty.elim : Empty → Nat)
  · simpa using finiteIndexProduct_of_finset (∅ : Finset Empty) (Empty.elim : Empty → Nat)

/-- List-fold association preserves occurrence order and requires no
commutativity. Set/multiset folds require their separate commutative laws.
-/
theorem ordered_list_folds [Monoid α] [AddMonoid β]
    (xs ys : List α) (as bs : List β) :
    (xs ++ ys).prod = xs.prod * ys.prod ∧ (as ++ bs).sum = as.sum + bs.sum := by
  constructor <;> simp only [List.prod_append, List.sum_append]

end Examples.FunctionalNotation

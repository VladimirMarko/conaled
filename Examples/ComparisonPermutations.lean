import Applications.Sorting.FirstPair
import Applications.Checking.OrderCertificate
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic

/-!
# VFA comparisons and permutations: checked source specializations

The independent first calculation is `[3, 2, 1] ↦ [2, 3, 1]`: only the first
pair is sorted. The general results used below retain that boundary. Boolean
reflection uses Lean's `decide` equivalences, and `by_cases`/`simp`/`omega`
replace the Coq-specific `bdestruct`/`lia` tactic combination.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.ComparisonPermutations
open Applications.Sorting

/-- Compose the sorting contract with the independently implemented ordering
checker. No transitivity or ordering of the remaining suffix is assumed. -/
theorem compareSwap_checked_prefix {α : Type} (swap check : α → α → Bool)
    (R : α → α → Prop)
    (swapLaw : ∀ a b, (swap a b = true → R b a) ∧ (swap a b = false → R a b))
    (checkLaw : ∀ a b, check a b = true ↔ R a b) (xs : List α) :
    OrderCertificate.adjacent check ((compareSwap swap xs).take 2) = true :=
  (OrderCertificate.adjacent_correct checkLaw _).mpr
    ((firstPair_iff_chain_take_two R _).mp (compareSwap_firstPair swap R swapLaw xs))

def geb (n m : Nat) : Bool := decide (m ≤ n)
def gtb (n m : Nat) : Bool := decide (m < n)
def maybeSwap : List Nat → List Nat := compareSwap gtb

theorem first_calculation : maybeSwap [3, 2, 1] = [2, 3, 1] := rfl
theorem already_ordered : maybeSwap [1, 2, 3] = [1, 2, 3] := rfl

theorem truncated_subtraction : ¬ (∀ k : Nat, k > k - 3) := by
  intro h
  have hzero := h 0
  omega

theorem lia_example1 (i j k : Nat) (hij : i < j) (hkj : ¬ k - 3 ≤ j) : k > i := by
  omega

theorem lia_example2 (i j k : Nat) (hij : i < j) (hkj : ¬ k - 3 ≤ j) : k > i :=
  lia_example1 i j k hij hkj

theorem lia_example_3 (f : Nat → Nat → Nat) (a b x y : Nat)
    (h : f x y > a * b) : f x y + 3 ≥ a * b := by omega

theorem eqb_reflect (x y : Nat) : decide (x = y) = true ↔ x = y := by simp
theorem ltb_reflect (x y : Nat) : decide (x < y) = true ↔ x < y := by simp
theorem leb_reflect (x y : Nat) : decide (x ≤ y) = true ↔ x ≤ y := by simp
theorem gtb_reflect (x y : Nat) : gtb x y = true ↔ x > y := by simp [gtb]
theorem geb_reflect (x y : Nat) : geb x y = true ↔ x ≥ y := by simp [geb]

/-- Lean's existing Boolean-to-decision adapter retains proof-carrying branches. -/
def reflectedLt (a b : Nat) : Decidable (a < b) :=
  decidable_of_bool (decide (a < b)) (ltb_reflect a b)

theorem reflected_true_branch : reflectedLt 2 3 = .isTrue (by decide) := rfl
theorem reflected_false_branch : reflectedLt 3 2 = .isFalse (by decide) := rfl

theorem reflect_example1 (a : Nat) : (if decide (a < 5) then a else 2) < 6 := by
  by_cases h : a < 5
  · simpa [h] using (show a < 6 by omega)
  · simp [h]

theorem reflect_example1' (a : Nat) : (if decide (a < 5) then a else 2) < 6 :=
  reflect_example1 a

theorem reflect_example2 (a : Nat) : (if decide (a < 5) then a else 2) < 6 :=
  reflect_example1 a

theorem gtb_asymmetric (a b : Nat) (h : gtb a b = true) : gtb b a = false := by
  have hba := (gtb_reflect a b).mp h
  simp only [gtb, decide_eq_false_iff_not]
  omega

theorem gtb_order_law (a b : Nat) :
    (gtb a b = true → b ≤ a) ∧ (gtb a b = false → a ≤ b) := by
  simp only [gtb, decide_eq_true_eq, decide_eq_false_iff_not]
  omega

theorem maybe_swap_idempotent (xs : List Nat) : maybeSwap (maybeSwap xs) = maybeSwap xs :=
  compareSwap_idempotent gtb gtb_asymmetric xs

theorem maybe_swap_perm (xs : List Nat) : xs.Perm (maybeSwap xs) :=
  compareSwap_perm gtb xs

theorem maybe_swap_correct (xs : List Nat) :
    xs.Perm (maybeSwap xs) ∧ FirstPair (· ≤ ·) (maybeSwap xs) :=
  compareSwap_correct gtb (· ≤ ·) gtb_order_law xs

/-- The source calculation is connected to the general correctness theorem. -/
theorem first_calculation_spec :
    ([3, 2, 1] : List Nat).Perm [2, 3, 1] ∧ FirstPair (· ≤ ·) [2, 3, 1] :=
  maybe_swap_correct [3, 2, 1]

theorem first_calculation_idempotent : maybeSwap [2, 3, 1] = [2, 3, 1] :=
  maybe_swap_idempotent [3, 2, 1]

theorem unchanged_suffix : (maybeSwap [3, 2, 1, 0]).drop 2 = [1, 0] :=
  compareSwap_drop_two gtb [3, 2, 1, 0]

theorem empty_case : maybeSwap [] = [] ∧ FirstPair (· ≤ ·) (maybeSwap []) :=
  ⟨rfl, (maybe_swap_correct []).2⟩

theorem singleton_case (a : Nat) : maybeSwap [a] = [a] ∧ FirstPair (· ≤ ·) (maybeSwap [a]) :=
  ⟨rfl, (maybe_swap_correct [a]).2⟩

theorem repeated_values : maybeSwap [2, 2, 1] = [2, 2, 1] ∧
    ([2, 2, 1] : List Nat).Perm (maybeSwap [2, 2, 1]) :=
  ⟨rfl, maybe_swap_perm _⟩

/-- Ordering two entries is deliberately weaker than sorting the whole list. -/
theorem not_whole_list_sorted : ¬ (maybeSwap [3, 2, 1]).Pairwise (· ≤ ·) := by decide

theorem certified_prefix (xs : List Nat) :
    OrderCertificate.adjacent (fun a b => decide (a ≤ b))
      ((maybeSwap xs).take 2) = true :=
  compareSwap_checked_prefix gtb _ (· ≤ ·) gtb_order_law leb_reflect xs

/-- The arithmetic reflection lemma also describes the false comparison branch. -/
theorem false_branch_reflect (a b : Nat) : gtb a b = false ↔ a ≤ b := by
  simp only [gtb, decide_eq_false_iff_not]
  omega

section PermutationProperties
variable {α β : Type} {xs ys zs : List α}

theorem permutation_length (h : xs.Perm ys) : xs.length = ys.length := h.length_eq
theorem permutation_symmetry (h : xs.Perm ys) : ys.Perm xs := h.symm

/-- Three additional properties requested by `Permutation_properties`. -/
theorem permutation_reflexivity (xs : List α) : xs.Perm xs := List.Perm.refl xs
theorem permutation_transitivity (hxy : xs.Perm ys) (hyz : ys.Perm zs) : xs.Perm zs :=
  hxy.trans hyz
theorem permutation_membership (h : xs.Perm ys) (a : α) : a ∈ xs ↔ a ∈ ys := h.mem_iff

theorem permutation_occurrences [DecidableEq α] (h : xs.Perm ys) (a : α) :
    xs.count a = ys.count a := h.count_eq a

/-- Universal element predicates transport along occurrence-sensitive permutation. -/
theorem forall_perm (P : α → Prop) (h : xs.Perm ys) (hx : ∀ a ∈ xs, P a) :
    ∀ a ∈ ys, P a := by
  intro a ha
  exact hx a (h.mem_iff.mpr ha)

theorem permutation_map (f : α → β) (h : xs.Perm ys) : (xs.map f).Perm (ys.map f) :=
  h.map f

/-- Bridge the source's inductive `Forall` to the reusable membership contract. -/
theorem forall_perm_inductive (P : α → Prop) (h : xs.Perm ys) (hx : xs.Forall P) :
    ys.Forall P := by
  rw [List.forall_iff_forall_mem] at hx ⊢
  exact forall_perm P h hx

end PermutationProperties

theorem not_a_permutation : ¬ ([1, 1] : List Nat).Perm [1, 2] := by decide

theorem four_values_permuted : ([1, 2, 3, 4] : List Nat).Perm [3, 4, 2, 1] := by decide

theorem butterfly (b u t e r f l y : Nat) :
    ([b, u, t, t, e, r] ++ [f, l, y]).Perm ([f, l, u, t, t, e, r] ++ [b, y]) := by
  have h₁ := (List.perm_append_comm :
    ([b] ++ [u, t, t, e, r]).Perm ([u, t, t, e, r] ++ [b])).append_right [f, l, y]
  have h₂ := (List.perm_append_comm :
    (([u, t, t, e, r] ++ [b]) ++ [f, l]).Perm ([f, l] ++ ([u, t, t, e, r] ++ [b]))).append_right [y]
  exact h₁.trans (by simpa only [List.append_assoc, List.cons_append, List.nil_append] using h₂)

theorem permut_example (a b : List Nat) :
    (5 :: 6 :: a ++ b).Perm ((5 :: b) ++ (6 :: a ++ [])) := by
  simpa only [List.cons_append, List.nil_append, List.append_nil] using
    (List.perm_append_comm : ((6 :: a) ++ b).Perm (b ++ (6 :: a))).cons 5

theorem positive_after_swap (xs : List Nat) (h : ∀ a ∈ xs, 0 < a) :
    ∀ a ∈ maybeSwap xs, 0 < a := forall_perm (0 < ·) (maybe_swap_perm xs) h

/-- Payloads need no order, and the map need not be injective. -/
theorem record_map (xs : List (Nat × String)) :
    compareSwap (fun a b : Nat × Nat => gtb a.1 b.1)
      (xs.map (fun r => (r.1, r.2.length))) =
      (compareSwap (fun a b : Nat × String => gtb a.1 b.1) xs).map
        (fun r => (r.1, r.2.length)) :=
  compareSwap_map _ _ _ (fun _ _ => rfl) xs

end Examples.ComparisonPermutations

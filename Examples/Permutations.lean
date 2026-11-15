import Applications.Sequences.Permutations
import Mathlib.Data.Fintype.Defs

/-!
# Permutation observations and source derivations

Order, membership, and occurrence counts are separate observations. These
cases include repeated inputs and function values; they do not assume that
all element types admit executable equality. The search composition is in
`Examples.PermutationSearch`.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.Permutations

open Sequences.Permutations
universe u v
variable {α : Type u} {β : Type v}

theorem empty_selection : bySelection ([] : List α) = [[]] := by
  rw [bySelection_eqn]
  rfl

theorem selection_singleton (x : α) : bySelection [x] = [[x]] := by
  rw [bySelection_eqn [x]]
  simp [picks, Sequences.Occurrences.picks, empty_selection]

theorem selection_pair (x y : α) : bySelection [x, y] = [[x, y], [y, x]] := by
  rw [bySelection_eqn [x, y]]
  simp [picks, Sequences.Occurrences.picks, selection_singleton]

theorem selection_triple (x y z : α) : bySelection [x, y, z] =
    [[x, y, z], [x, z, y], [y, x, z], [y, z, x], [z, x, y], [z, y, x]] := by
  rw [bySelection_eqn [x, y, z]]
  simp [picks, Sequences.Occurrences.picks, selection_pair]

theorem insert_order : List.permutations'Aux 1 [2, 3] =
    [[1, 2, 3], [2, 1, 3], [2, 3, 1]] := rfl

theorem insertion_order : ([1, 2, 3] : List Nat).permutations' =
    [[1, 2, 3], [2, 1, 3], [2, 3, 1], [1, 3, 2], [3, 1, 2], [3, 2, 1]] := rfl

theorem selection_order : bySelection ([1, 2, 3] : List Nat) =
    [[1, 2, 3], [1, 3, 2], [2, 1, 3], [2, 3, 1], [3, 1, 2], [3, 2, 1]] :=
  selection_triple _ _ _

theorem orders_differ : ([1, 2, 3] : List Nat).permutations' ≠ bySelection [1, 2, 3] := by
  rw [insertion_order, selection_order]
  decide

theorem insertion_repeats : ([1, 1] : List Nat).permutations' = [[1, 1], [1, 1]] := rfl

/-- The universal outer permutation law supplies the count of each output value. -/
theorem same_occurrence_count [DecidableEq α] (xs ys : List α) :
    xs.permutations'.count ys = (bySelection xs).count ys :=
  (insertion_perm_selection xs).count_eq ys

theorem same_predicate_count (xs : List α) (p : List α → Bool) :
    xs.permutations'.countP p = (bySelection xs).countP p :=
  (insertion_perm_selection xs).countP_eq p

theorem repeated_selection_count : (bySelection ([1, 1, 2] : List Nat)).count [1, 2, 1] = 2 := by
  rw [← same_occurrence_count]
  rfl

theorem six_positional_outputs : (bySelection ([1, 1, 2] : List Nat)).length = 6 := by
  rw [bySelection_length]
  rfl

theorem insertion_append_context (x : α) (xs tail : List α) :
    insertsWith (fun zs => zs ++ tail) x xs =
      (List.permutations'Aux x xs).map (fun zs => zs ++ tail) :=
  insertsWith_eq_map _ _ _

theorem appended_insertions : insertsWith (fun zs : List Nat => zs ++ [9]) 1 [2, 3] =
    [[1, 2, 3, 9], [2, 1, 3, 9], [2, 3, 1, 9]] := by
  rw [insertion_append_context, insert_order]
  rfl

theorem insertsWith_identity (x : α) (xs : List α) :
    insertsWith id x xs = List.permutations'Aux x xs := by
  rw [insertsWith_eq_map, List.map_id]

theorem fold_insert_order : ([2, 3] : List Nat).foldr (insertStep 1) [[1]] =
    [[1, 2, 3], [2, 1, 3], [2, 3, 1]] := by
  rw [insertion_step_fold, insert_order]

theorem fold_insert_nonempty (x : α) (xs : List α) :
    xs.foldr (insertStep x) [[x]] ≠ [] := by
  rw [insertion_step_fold]
  intro hempty
  have h := List.length_permutations'Aux xs x
  rw [hempty] at h
  simp at h

/-- The fallback is explicit; correctness of the fold uses the reached insertion states. -/
theorem malformed_step : insertStep (1 : Nat) 2 [[]] = [] := rfl

theorem first_occurrence : ([2, 1, 3, 1] : List Nat).erase 1 = [2, 3, 1] := rfl

theorem singleton_difference [DecidableEq α] (x : α) (xs : List α) :
    [x].foldl (fun ys y => ys.erase y) xs = xs.erase x := rfl

theorem empty_erasure [DecidableEq α] : byErasure ([] : List α) = [[]] := by
  rw [byErasure_eqn]
  rfl

theorem erasure_singleton [DecidableEq α] (x : α) : byErasure [x] = [[x]] := by
  rw [byErasure_eqn [x]]
  simp [empty_erasure]

theorem erasure_repeats : byErasure ([1, 1] : List Nat) = [[1, 1], [1, 1]] := by
  rw [byErasure_eqn [1, 1]]
  simp [erasure_singleton]

theorem erasure_same_members [DecidableEq α] (xs ys : List α) :
    (ys ∈ byErasure xs ↔ ys ∈ xs.permutations') ∧
      (ys ∈ byErasure xs ↔ ys ∈ bySelection xs) := by
  simp only [byErasure_mem_iff, List.mem_permutations', bySelection_mem_iff, and_self]

theorem all_first_results [DecidableEq α] (xs : List α) :
    xs.permutations'.head? = some xs ∧ (bySelection xs).head? = some xs ∧
      (byErasure xs).head? = some xs :=
  ⟨insertion_head xs, bySelection_head xs, byErasure_head xs⟩

theorem omitted_base_incomplete [DecidableEq α] (xs : List α) :
    xs ∉ byErasureWithoutBase xs := by
  rw [byErasureWithoutBase_eq_nil]
  exact List.not_mem_nil

theorem omitted_base_example : byErasureWithoutBase ([1, 2, 3] : List Nat) = [] :=
  byErasureWithoutBase_eq_nil _

/-- Arbitrary function domains require no equality decision for insertion. -/
theorem function_insertion (xs ys : List (α → β)) :
    ys ∈ xs.permutations' ↔ ys.Perm xs := List.mem_permutations'

theorem function_selection (xs ys : List (α → β)) :
    ys ∈ bySelection xs ↔ ys.Perm xs := bySelection_mem_iff xs ys

theorem bool_function_eq_iff (f g : Bool → α) :
    f = g ↔ f false = g false ∧ f true = g true := by
  constructor
  · intro h; exact ⟨congrFun h false, congrFun h true⟩
  · rintro ⟨hfalse, htrue⟩
    funext b
    cases b <;> assumption

/-- The existing finite-domain instance needs no finiteness of the codomain. -/
theorem finite_function_erasure {ι : Type u} [Fintype ι] [DecidableEq β]
    (xs ys : List (ι → β)) : ys ∈ byErasure xs ↔ ys.Perm xs :=
  byErasure_mem_iff xs ys

private def rising : Bool → Nat := fun b => if b then 10 else 0
private def falling : Bool → Nat := fun b => if b then 0 else 10

private theorem rising_ne_falling : rising ≠ falling := by
  intro h
  have hzero := congrFun h false
  change (0 : Nat) = 10 at hzero
  cases hzero

theorem finite_function_erase_first :
    ([rising, falling, rising] : List (Bool → Nat)).erase rising = [falling, rising] :=
  List.erase_cons_head _ _

theorem finite_function_orders : byErasure [rising, falling] =
    [[rising, falling], [falling, rising]] := by
  rw [byErasure_eqn [rising, falling]]
  simp [List.erase_cons, rising_ne_falling, erasure_singleton]

/-- Composition spelling has the same actual right-fold operation. -/
theorem composed_insertion_fold (xs : List α) :
    xs.foldr (List.flatMap ∘ List.permutations'Aux) [[]] = xs.permutations' :=
  insertion_fold xs

/-- The source concatMap/map presentation uses the same ordered recursion. -/
theorem selection_mapped_equation (xs : List α) : bySelection xs =
    if xs = [] then [[]] else
      ((picks xs).map (fun p => (bySelection p.2).map (p.1 :: ·))).flatten := by
  rw [bySelection_eqn]
  rfl

theorem erasure_mapped_equation [DecidableEq α] (xs : List α) : byErasure xs =
    if xs = [] then [[]] else
      (xs.map (fun x => (byErasure ([x].foldl (fun ys y => ys.erase y) xs)).map
        (x :: ·))).flatten := by
  rw [byErasure_eqn]
  rfl

/-- The standard factorial has the same finite-product observation as the source. -/
theorem factorial_product (n : Nat) : Nat.factorial n = (List.range' 1 n).prod := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Nat.factorial_succ, List.range'_1_concat, List.prod_append, ih]
      simp [Nat.add_comm, Nat.mul_comm]

/-- Standard flatMap length and constant-map laws discharge the source helper. -/
theorem constant_branch_length (xs : List α) (f : α → List β) (n : Nat)
    (h : ∀ x ∈ xs, (f x).length = n) : (xs.flatMap f).length = xs.length * n := by
  rw [List.length_flatMap]
  have hmap : (xs.map (fun x => (f x).length)) = xs.map (fun _ => n) :=
    List.map_congr_left h
  rw [hmap]
  simp

end Examples.Permutations

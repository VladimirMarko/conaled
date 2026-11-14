import Mathlib.Data.List.Intervals
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Sort

/-! Checked interfaces for FDSA Appendix A. The standard list operations supply
the value equations; these clients retain range endpoints, multiplicity,
arbitrary relations, and explicit failure or valid-input proofs. Execution
costs belong to their separate measured realizations.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.ListLibrary
universe u
variable {α : Type u}

/-- The source's set observation requires no equality decision on payloads. -/
theorem empty_membership_set : {x : α | x ∈ ([] : List α)} = ∅ := by
  apply Set.ext
  intro x
  simp

theorem cons_membership_set (x : α) (xs : List α) :
    {y | y ∈ x :: xs} = ({x} : Set α) ∪ {y | y ∈ xs} := by
  apply Set.ext
  intro y
  simp

/-- The source conditional can inspect list shape without decidable payload equality. -/
theorem dropLast_cons_equation (x : α) (xs : List α) :
    (x :: xs).dropLast = if xs.isEmpty then [] else x :: xs.dropLast := by
  cases xs <;> rfl

/-- The source's upper endpoint is exclusive, including its empty branch. -/
theorem range_succ_equation (i j : Nat) :
    List.Ico i (j + 1) = if i ≤ j then List.Ico i j ++ [j] else [] := by
  by_cases h : i ≤ j
  · simpa [h] using List.Ico.succ_top h
  · rw [ite_eq_right h]
    exact List.Ico.eq_nil_of_le (by omega)

theorem range_zero_equation (i : Nat) : List.Ico i 0 = [] :=
  List.Ico.eq_nil_of_le (Nat.zero_le i)

theorem range_boundaries :
    List.Ico 2 5 = [2, 3, 4] ∧ List.Ico 5 2 = [] ∧ List.Ico 2 2 = [] ∧
      List.Ico 2 3 = [2] := by
  constructor
  · rw [range_succ_equation, range_succ_equation, range_succ_equation]
    decide
  constructor
  · exact List.Ico.eq_nil_of_le (by decide)
  constructor
  · exact List.Ico.self_empty
  · exact List.Ico.succ_singleton

theorem range_membership (i j k : Nat) :
    k ∈ List.Ico i j ↔ i ≤ k ∧ k < j := List.Ico.mem

/-- Optional queries agree with the existing proof-domain views on valid inputs. -/
theorem head_valid (xs : List α) (h : xs ≠ []) : xs.head? = some (xs.head h) :=
  List.head?_eq_some_head h

theorem index_valid (xs : List α) (i : Nat) (h : i < xs.length) :
    xs[i]? = some xs[i] := List.getElem?_eq_getElem h

/-- Out-of-range observation fails, while source list update leaves the input intact. -/
theorem invalid_index_and_update (xs : List α) (i : Nat) (x : α)
    (h : xs.length ≤ i) : xs[i]? = none ∧ xs.set i x = xs :=
  ⟨List.getElem?_eq_none_iff.mpr h, List.set_eq_of_length_le h⟩

theorem update_observations (xs : List α) (i : Nat) (x : α) (h : i < xs.length) :
    (xs.set i x).length = xs.length ∧ (xs.set i x)[i]? = some x ∧
      ∀ j, i ≠ j → (xs.set i x)[j]? = xs[j]? := by
  refine ⟨List.length_set, List.getElem?_set_self h, ?_⟩
  intro j hj
  exact List.getElem?_set_ne hj

theorem update_repeated_value :
    ([4, 4, 9].set 1 7).length = 3 ∧ ([4, 4, 9].set 1 7)[1]? = some 7 ∧
      ([4, 4, 9].set 1 7)[0]? = some 4 := by
  have h := update_observations [4, 4, 9] 1 7 (by decide)
  exact ⟨h.1, h.2.1, h.2.2 0 (by decide)⟩

theorem invalid_boundary : [1, 2][2]? = none ∧ [1, 2].set 2 9 = [1, 2] :=
  invalid_index_and_update [1, 2] 2 9 (by decide)

/-- Empty lists remain usable even when an element cannot be supplied. -/
theorem empty_payload_queries :
    ([] : List Empty).head? = none ∧ ([] : List Empty)[0]? = none ∧
      ([] : List Empty).tail = [] ∧ ([] : List Empty).dropLast = [] := by
  decide

/-- The take/drop interfaces preserve the entire ordered input at every boundary. -/
theorem split_reassembles (n : Nat) (xs : List α) : xs.take n ++ xs.drop n = xs :=
  List.take_append_drop n xs

theorem overlarge_split :
    [2, 2, 1].take 8 = [2, 2, 1] ∧ [2, 2, 1].drop 8 = [] := by
  decide

theorem last_and_tail_boundaries :
    ([] : List Nat).tail = [] ∧ [3].tail = [] ∧ [3].dropLast = [] ∧
      [3, 4, 3].dropLast = [3, 4] := by
  decide

/-- Here the source concat is List.flatten; empty inner lists and repeats matter. -/
theorem duplicate_pipeline :
    let xs := ([[2, 2], [], [1, 3]] : List (List Nat)).flatten
    xs.length = 4 ∧
      (xs.filter (fun x => decide (x ≤ 2))).map (· + 1) = [3, 3, 2] ∧
      xs.reverse = [3, 1, 2, 2] ∧ xs.sum = 8 := by
  decide

theorem replication_boundaries :
    List.replicate 0 5 = [] ∧ List.replicate 3 5 = [5, 5, 5] := by
  decide

theorem duplicates_are_not_distinct (x : α) (xs : List α) :
    ¬ (x :: x :: xs).Nodup := by
  simp

/-- Arbitrary-relation sortedness checks every later element, as in the source. -/
theorem sorted_wrt_cons (r : α → α → Prop) (x : α) (xs : List α) :
    (x :: xs).Pairwise r ↔ (∀ y ∈ xs, r x y) ∧ xs.Pairwise r :=
  List.pairwise_cons

theorem adjacent_relation_is_insufficient :
    ([0, 1, 2] : List Nat).IsChain (fun x y => y = x + 1) ∧
      ¬ ([0, 1, 2] : List Nat).Pairwise (fun x y => y = x + 1) := by
  decide

/-- These literal sum equations require no associativity or commutativity. -/
theorem sum_source_equations [Add α] [Zero α] (x : α) (xs : List α) :
    ([] : List α).sum = 0 ∧ (x :: xs).sum = x + xs.sum := ⟨rfl, rfl⟩

/-- Associativity justifies the source's right-recursive view of the folded minimum. -/
theorem minimum_source_equation [Min α] [Std.Associative (min : α → α → α)]
    (x : α) (xs : List α) :
    (x :: xs).min? = some (xs.min?.elim x (min x)) := List.min?_cons

theorem minimum_valid [Min α] (xs : List α) (h : xs ≠ []) :
    xs.min? = some (xs.min h) := List.min?_eq_some_min h

theorem minimum_filter_spec [LinearOrder α] (p : α → Bool) (xs : List α) (a : α)
    (h : (xs.filter p).min? = some a) :
    a ∈ xs ∧ p a = true ∧ ∀ b ∈ xs, p b = true → a ≤ b := by
  obtain ⟨ha, hlo⟩ := List.min?_eq_some_iff.mp h
  obtain ⟨ha, hpa⟩ := List.mem_filter.mp ha
  refine ⟨ha, hpa, ?_⟩
  intro b hb hpb
  exact hlo b (List.mem_filter.mpr ⟨hb, hpb⟩)

theorem minimum_repeated_values : ([7, 2, 7] : List Nat).min? = some 2 := by
  rw [minimum_source_equation, minimum_source_equation, minimum_source_equation]
  rfl

theorem minimum_empty : ([] : List Nat).min? = none := List.min?_nil

/-- The minimum interface needs an operation, but no inhabitant or default. -/
theorem empty_payload_minimum :
    @List.min? Empty ⟨fun x _ => nomatch x⟩ [] = none := rfl

theorem filtered_minimum_example :
    (2 : Nat) ∈ [7, 2, 7] ∧ decide (2 ≤ 3) = true ∧
      ∀ b ∈ ([7, 2, 7] : List Nat), decide (b ≤ 3) = true → 2 ≤ b :=
  minimum_filter_spec (fun x => decide (x ≤ 3)) [7, 2, 7] 2 (by decide)

end Examples.ListLibrary

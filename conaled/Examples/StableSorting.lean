import Applications.Sorting.Sort
import Applications.Sorting.SourceMerge

/-! Equal-key payloads, signed keys, and domain-local comparators. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.StableSorting
open Applications.Sorting

abbrev Record := Int × String

def input : List Record := [(2, "first"), (-1, "negative"), (2, "last")]
def expected : List Record := [(-1, "negative"), (2, "first"), (2, "last")]

/-- Independent sortedness, multiplicities and equal-key observations. -/
theorem expected_spec : StableSort Prod.fst input expected where
  sorted := by decide
  perm := List.Perm.swap _ _ _
  stable := by
    intro k
    by_cases hn : (-1 : Int) = k
    · subst k; simp [input, expected]
    · by_cases ht : (2 : Int) = k
      · subst k; simp [input, expected]
      · simp [input, expected, hn, ht]

theorem merge_sort_records : sortOn Prod.fst input = expected :=
  (sortOn_spec Prod.fst input).unique expected_spec

theorem insertion_sort_records : insertionOn Prod.fst input = expected :=
  (insertionOn_spec Prod.fst input).unique expected_spec

theorem realizations_agree : sortOn Prod.fst input = insertionOn Prod.fst input :=
  sortOn_eq_insertionOn Prod.fst input

theorem empty : sortOn Prod.fst ([] : List Record) = [] :=
  sortOn_sorted_fixed _ _ .nil

theorem sorted_fixed : sortOn Prod.fst expected = expected :=
  sortOn_sorted_fixed _ _ expected_spec.sorted

/-- The left block's equal-key records precede those from the right block. -/
theorem merge_equal_key_filter :
    (mergeBy Prod.fst ([(2, "first")] : List Record) [(2, "last")]).filter
        (fun r => decide (r.1 = 2)) = [(2, "first"), (2, "last")] := by
  rw [mergeBy_filter Prod.fst _ _ (by decide) (by decide)]
  rfl

theorem merge_stable :
    Stable Prod.fst ([(2, "first"), (2, "last")] : List Record)
      (mergeBy Prod.fst [(2, "first")] [(2, "last")]) :=
  mergeBy_stable _ _ _ (by decide) (by decide)

theorem merging_sorted_blocks :
    mergeBy Prod.fst ([(2, "first")] : List Record) [(2, "last")] =
      sortOn Prod.fst [(2, "first"), (2, "last")] :=
  mergeBy_eq_sortOn _ _ _ (by decide) (by decide)

theorem source_merge_agrees :
    letI : LE Record := ⟨fun a b => a.1 ≤ b.1⟩
    letI : DecidableLE Record := fun a b => inferInstanceAs (Decidable (a.1 ≤ b.1))
    sourceMerge ([(2, "first")] : List Record) [(2, "last")] =
      mergeBy Prod.fst [(2, "first")] [(2, "last")] :=
  mergeBy_source Prod.fst _ _

/-- First replace payloads with lengths, then discard all but their parity. -/
def lengths (r : Record) : Int × Nat := (r.1, r.2.length)
def parity (r : Int × Nat) : Int × Nat := (r.1, r.2 % 2)

theorem transformed_spec :
    StableSort Prod.fst ((input.map lengths).map parity) ((expected.map lengths).map parity) :=
  (expected_spec.map lengths (fun _ => rfl)).map parity (fun _ => rfl)

theorem transform_then_sort :
    sortOn Prod.fst ((input.map lengths).map parity) = ((expected.map lengths).map parity) :=
  (sortOn_spec Prod.fst _).unique transformed_spec

theorem sort_then_transform :
    sortOn Prod.fst (input.map (parity ∘ lengths)) =
      (sortOn Prod.fst input).map (parity ∘ lengths) :=
  sortOn_map Prod.fst Prod.fst (parity ∘ lengths) (fun _ => rfl) input

/-- This comparator intentionally has no ordering contract on negative keys. -/
def nonnegativeCompare (a b : Record) : Bool :=
  if 0 ≤ a.1 ∧ 0 ≤ b.1 then decide (a.1 ≤ b.1) else false

def nonnegativeInput : List Record := [(2, "first"), (0, "zero"), (2, "last")]

theorem nonnegative_compatible :
    ∀ a ∈ nonnegativeInput, ∀ b ∈ nonnegativeInput,
      (nonnegativeCompare a b = true → a.1 ≤ b.1) ∧
      (nonnegativeCompare a b = false → b.1 ≤ a.1) := by
  intro a ha b hb
  simp only [nonnegativeInput, List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> decide

theorem local_comparator_sorted :
    KeySorted Prod.fst (sortBy nonnegativeCompare nonnegativeInput) :=
  sortBy_sorted_compatible_on Prod.fst nonnegativeCompare nonnegativeInput nonnegative_compatible

theorem local_comparator_perm :
    (sortBy nonnegativeCompare nonnegativeInput).Perm nonnegativeInput :=
  sortBy_perm _ _

theorem comparator_not_globally_compatible :
    ¬ (∀ a b : Record, (nonnegativeCompare a b = true → a.1 ≤ b.1) ∧
      (nonnegativeCompare a b = false → b.1 ≤ a.1)) := by
  intro h
  have wrong := (h (-1, "outside") (0, "inside")).2 rfl
  contradiction

/-- Swapping distinct payloads with equal keys preserves sortedness and permutation. -/
theorem sorted_permutation_not_stable :
    KeySorted Prod.fst ([(2, "last"), (2, "first")] : List Record) ∧
      ([(2, "last"), (2, "first")] : List Record).Perm [(2, "first"), (2, "last")] ∧
      ¬ Stable Prod.fst ([(2, "first"), (2, "last")] : List Record)
        [(2, "last"), (2, "first")] := by
  refine ⟨by decide, List.Perm.swap _ _ _, ?_⟩
  intro h
  have wrong := h 2
  simp at wrong

end Examples.StableSorting

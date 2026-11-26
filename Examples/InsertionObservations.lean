import Applications.Sorting.InsertionObservations
import Examples.StableSorting
import Mathlib.Data.Multiset.ZeroCons

/-!
FDSA's ordinary/keyed insertion observations and their hypothesis boundaries.
The source chapter is by Tobias Nipkow and Christian Sternagel. These original
proofs use existing Lean/Mathlib operations and conaled's stable-sort contract.
No new insertion algorithm or comparison/call-count model is introduced.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.InsertionObservations
open Applications.Sorting
universe u v
variable {α : Type u} {κ : Type v}

/-- Keyed insertion uses the source's nonstrict, left-tie branch. -/
theorem keyed_insert_equations [LE κ] [DecidableLE κ]
    (key : α → κ) (a b : α) (xs : List α) :
    List.orderedInsert (fun x y => key x ≤ key y) a [] = [a] ∧
      List.orderedInsert (fun x y => key x ≤ key y) a (b :: xs) =
        if key a ≤ key b then a :: b :: xs
        else b :: List.orderedInsert (fun x y => key x ≤ key y) a xs :=
  ⟨rfl, rfl⟩

/-- The existing right-fold sorter first sorts the actual tail. -/
theorem keyed_sort_equations [LE κ] [DecidableLE κ]
    (key : α → κ) (a : α) (xs : List α) :
    insertionOn key [] = [] ∧ insertionOn key (a :: xs) =
      List.orderedInsert (fun x y => key x ≤ key y) a (insertionOn key xs) :=
  ⟨rfl, rfl⟩

/-- One new occurrence, exact support and length need no laws on the key order. -/
theorem keyed_insert_observations [LE κ] [DecidableLE κ]
    (key : α → κ) (a : α) (xs : List α) :
    (List.orderedInsert (fun x y => key x ≤ key y) a xs : Multiset α) =
        a ::ₘ (xs : Multiset α) ∧
      (∀ b, b ∈ List.orderedInsert (fun x y => key x ≤ key y) a xs ↔
        b = a ∨ b ∈ xs) ∧
      (List.orderedInsert (fun x y => key x ≤ key y) a xs).length = xs.length + 1 := by
  refine ⟨?_, fun _ => List.mem_orderedInsert _, List.orderedInsert_length _ _ _⟩
  change (List.orderedInsert (fun x y => key x ≤ key y) a xs : Multiset α) =
    ((a :: xs : List α) : Multiset α)
  exact Multiset.coe_eq_coe.mpr (List.perm_orderedInsert _ _ _)

/-- Source (2.4) and its keyed version observe order on mapped keys, not payloads. -/
theorem keyed_sorted_iff [LE κ] [DecidableLE κ] [Std.IsLinearPreorder κ]
    (key : α → κ) (a : α) (xs : List α) :
    ((List.orderedInsert (fun x y => key x ≤ key y) a xs).map key).Pairwise (· ≤ ·) ↔
      (xs.map key).Pairwise (· ≤ ·) := by
  let r := fun x y : α => key x ≤ key y
  let : Std.Total r := ⟨fun x y => Std.le_total (a := key x) (b := key y)⟩
  let : IsTrans α r := ⟨fun _ _ _ hxy hyz => Std.le_trans hxy hyz⟩
  simpa only [List.pairwise_map] using pairwise_orderedInsert_iff r a xs

/-- The positive source helper only needs a preorder on keys. -/
theorem keyed_filter_of_pos [LE κ] [DecidableLE κ] [Std.IsPreorder κ]
    (key : α → κ) (p : α → Bool) (a : α) (xs : List α)
    (hxs : (xs.map key).Pairwise (· ≤ ·)) (ha : p a = true) :
    (List.orderedInsert (fun x y => key x ≤ key y) a xs).filter p =
      List.orderedInsert (fun x y => key x ≤ key y) a (xs.filter p) := by
  let r := fun x y : α => key x ≤ key y
  let : IsTrans α r := ⟨fun _ _ _ hxy hyz => Std.le_trans hxy hyz⟩
  exact filter_orderedInsert_of_pos r p a xs (List.pairwise_map.mp hxs) ha

/-- Full-record multiplicity, mapped-key sortedness and equal-key order are distinct. -/
theorem keyed_sort_observations [LE κ] [DecidableLE κ] [Std.IsLinearPreorder κ]
    [DecidableEq κ] (key : α → κ) (xs : List α) :
    (insertionOn key xs : Multiset α) = (xs : Multiset α) ∧
      ((insertionOn key xs).map key).Pairwise (· ≤ ·) ∧
      ∀ k, (insertionOn key xs).filter (fun x => decide (key x = k)) =
        xs.filter (fun x => decide (key x = k)) := by
  have h := insertionOn_spec key xs
  exact ⟨Multiset.coe_eq_coe.mpr h.perm, List.pairwise_map.mpr h.sorted, h.stable⟩

/-- An arbitrary insertion decision cannot remove an existing inversion. -/
theorem raw_insertion_cannot_repair (r : Nat → Nat → Prop) [DecidableRel r] (a : Nat) :
    ¬ (List.orderedInsert r a [2, 0]).Pairwise (· ≤ ·) := by
  intro h
  have hi := pairwise_of_orderedInsert r (· ≤ ·) a [2, 0] h
  exact (by decide : ¬ ([2, 0] : List Nat).Pairwise (· ≤ ·)) hi

theorem all_members_without_sorted_input :
    List.orderedInsert (· ≤ ·) 0 [2, 0] = [0, 2, 0] :=
  orderedInsert_eq_cons_of_forall (· ≤ ·) 0 [2, 0] (by simp)

/-- The source all-members premise is sufficient, but a tied head alone can suffice. -/
theorem tied_head_ignores_inversion :
    List.orderedInsert (· ≤ ·) 2 [2, 0] = [2, 2, 0] ∧
      ¬ (∀ b ∈ ([2, 0] : List Nat), 2 ≤ b) := by
  refine ⟨List.orderedInsert_cons_of_le _ _ (Nat.le_refl 2), ?_⟩
  simp

/-- Distinct arbitrary payloads with the same key retain the new-before-old tie rule. -/
theorem equal_key_payloads (payload : Type u) (x y : payload) :
    List.orderedInsert (fun a b : Nat × payload => a.1 ≤ b.1) (2, x) [(2, y)] =
      [(2, x), (2, y)] :=
  orderedInsert_eq_cons_of_forall _ _ _ (by simp)

theorem empty_type_sort (xs : List Empty) :
    insertionOn (fun x : Empty => (x.elim : Nat)) xs = [] := by
  cases xs with
  | nil => rfl
  | cons x _ => exact x.elim

theorem empty_payload_sort (xs : List (Nat × Empty)) :
    insertionOn Prod.fst xs = [] ∧ StableSort Prod.fst xs (insertionOn Prod.fst xs) := by
  cases xs with
  | nil => exact ⟨rfl, insertionOn_spec _ _⟩
  | cons x _ => exact x.2.elim

/-- Nil already shows that neither filter law can discard its predicate premise. -/
theorem predicate_premises_matter :
    (List.orderedInsert (· ≤ ·) 0 ([] : List Nat)).filter (fun _ => true) ≠ [] ∧
      (List.orderedInsert (· ≤ ·) 0 ([] : List Nat)).filter (fun _ => false) ≠
        List.orderedInsert (· ≤ ·) 0 ([].filter (fun _ => false)) := by
  decide

/-- The negative law also works for the two extreme, non-ordering decisions. -/
theorem negative_extreme_relations (p : α → Bool) (a : α) (xs : List α)
    (ha : p a = false) :
    (List.orderedInsert (fun _ _ => True) a xs).filter p = xs.filter p ∧
      (List.orderedInsert (fun _ _ => False) a xs).filter p = xs.filter p :=
  ⟨filter_orderedInsert_of_neg _ p a xs ha, filter_orderedInsert_of_neg _ p a xs ha⟩

abbrev Flagged := Nat × Bool
def rawFlags : List Flagged := [(1, true), (3, false), (0, true)]
def sortedFlags : List Flagged := [(0, false), (1, true), (3, true), (4, false)]

/-- Rejection preserves a full semantic-payload subsequence even on unsorted input. -/
theorem negative_filter_unsorted :
    ¬ KeySorted Prod.fst rawFlags ∧
      (List.orderedInsert (fun a b : Flagged => a.1 ≤ b.1) (2, false) rawFlags).filter
        Prod.snd = [(1, true), (0, true)] := by
  refine ⟨by decide, ?_⟩
  calc
    _ = rawFlags.filter Prod.snd := filter_orderedInsert_of_neg _ _ _ _ rfl
    _ = [(1, true), (0, true)] := rfl

/-- Filtering removes both a traversed head and the actual stopping head. -/
theorem positive_filter_discards_stopping_head :
    (List.orderedInsert (fun a b : Flagged => a.1 ≤ b.1) (2, false) sortedFlags).filter
      (fun a => !a.2) = [(0, false), (2, false), (4, false)] := by
  calc
    _ = List.orderedInsert (fun a b : Flagged => a.1 ≤ b.1) (2, false)
        (sortedFlags.filter (fun a => !a.2)) :=
      keyed_filter_of_pos Prod.fst _ _ _ (by decide) rfl
    _ = [(0, false), (2, false), (4, false)] := rfl

def even (n : Nat) : Bool := decide (n % 2 = 0)

/-- A lawful comparison and a retained new value do not replace sortedness. -/
theorem positive_filter_needs_sorted_input :
    even 2 = true ∧ ¬ ([3, 0] : List Nat).Pairwise (· ≤ ·) ∧
      (List.orderedInsert (· ≤ ·) 2 [3, 0]).filter even = [2, 0] ∧
      List.orderedInsert (· ≤ ·) 2 ([3, 0].filter even) = [0, 2] := by
  decide

/-- Equality and the directed cycle 0→1→2→0 give a total but nontransitive relation. -/
abbrev Cycle (a b : Fin 3) : Prop :=
  a = b ∨ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 0)

theorem cycle_total : ∀ a b : Fin 3, Cycle a b ∨ Cycle b a := by decide

theorem cycle_not_transitive :
    ¬ (∀ a b c : Fin 3, Cycle a b → Cycle b c → Cycle a c) := by decide

/-- One finite fixture separates transitivity from totality for both positive laws. -/
theorem transitivity_boundaries :
    ([1, 2] : List (Fin 3)).Pairwise Cycle ∧
      ¬ (List.orderedInsert Cycle 0 [1, 2]).Pairwise Cycle ∧
      (List.orderedInsert Cycle 0 [1, 2]).filter (fun a => decide (a ≠ 1)) = [0, 2] ∧
      List.orderedInsert Cycle 0 ([1, 2].filter (fun a => decide (a ≠ 1))) = [2, 0] := by
  decide

/-- Strict comparison is transitive but loses both a tie's order and pairwise preservation. -/
theorem strict_tie_boundary :
    ([(2, "last")] : List StableSorting.Record).Pairwise (fun a b => a.1 < b.1) ∧
      List.orderedInsert (fun a b : StableSorting.Record => a.1 < b.1)
        (2, "first") [(2, "last")] = [(2, "last"), (2, "first")] ∧
      ¬ ([(2, "last"), (2, "first")] : List StableSorting.Record).Pairwise
        (fun a b => a.1 < b.1) := by
  decide

def signedTail : List StableSorting.Record := [(-1, "negative"), (2, "last")]

theorem signed_tail_fixed : insertionOn Prod.fst signedTail = signedTail :=
  List.Pairwise.insertionSort_eq (by decide)

/-- The negative stability-proof branch uses the actual recursively sorted tail. -/
theorem signed_negative_step :
    (List.orderedInsert (fun a b : StableSorting.Record => a.1 ≤ b.1) (2, "first")
      (insertionOn Prod.fst signedTail)).filter (fun a => decide (a.1 = -1)) =
        [(-1, "negative")] := by
  rw [signed_tail_fixed]
  calc
    _ = signedTail.filter (fun a => decide (a.1 = -1)) :=
      filter_orderedInsert_of_neg _ _ _ _ (by decide)
    _ = [(-1, "negative")] := rfl

/-- The positive stability branch connects filtering to the all-members cons law. -/
theorem signed_positive_step :
    (List.orderedInsert (fun a b : StableSorting.Record => a.1 ≤ b.1) (2, "first")
      (insertionOn Prod.fst signedTail)).filter (fun a => decide (a.1 = 2)) =
        [(2, "first"), (2, "last")] := by
  rw [signed_tail_fixed]
  calc
    _ = List.orderedInsert (fun a b : StableSorting.Record => a.1 ≤ b.1) (2, "first")
        (signedTail.filter (fun a => decide (a.1 = 2))) :=
      keyed_filter_of_pos Prod.fst _ _ _ (by decide) (by decide)
    _ = (2, "first") :: signedTail.filter (fun a => decide (a.1 = 2)) :=
      orderedInsert_eq_cons_of_forall _ _ _ (by decide)
    _ = [(2, "first"), (2, "last")] := rfl

/-- Whole-sort stability concerns one key at a time, not arbitrary filters. -/
theorem stability_is_not_arbitrary_filter :
    (insertionOn Prod.fst StableSorting.input).filter (fun _ => true) ≠
      StableSorting.input.filter (fun _ => true) := by
  rw [StableSorting.insertion_sort_records]
  decide

end Examples.InsertionObservations

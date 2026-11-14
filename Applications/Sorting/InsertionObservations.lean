import Mathlib.Data.List.Sort

/-!
Observations of canonical ordered insertion, used in FDSA §§2.2 and 2.8.
Insertion always keeps every old occurrence. Filtering a rejected new value
therefore needs no ordering law; filtering a retained value also uses the
ordered-input and transitivity hypotheses. These are value laws, not cost laws.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.Sorting
universe u
variable {α : Type u}

/-- An input sublist inherits any pairwise observation of the insertion result. -/
theorem pairwise_of_orderedInsert (r : α → α → Prop) [DecidableRel r]
    (s : α → α → Prop) (a : α) (xs : List α)
    (h : (List.orderedInsert r a xs).Pairwise s) : xs.Pairwise s :=
  List.Pairwise.sublist (List.sublist_orderedInsert (r := r) a xs) h

/-- Constructing sorted output uses order laws; reflecting it to input does not. -/
theorem pairwise_orderedInsert_iff (r : α → α → Prop) [DecidableRel r]
    [Std.Total r] [IsTrans α r] (a : α) (xs : List α) :
    (List.orderedInsert r a xs).Pairwise r ↔ xs.Pairwise r :=
  ⟨pairwise_of_orderedInsert r r a xs,
    fun h => List.Pairwise.orderedInsert (r := r) a xs h⟩

/-- The source's all-members premise suffices even when the old list is unsorted. -/
theorem orderedInsert_eq_cons_of_forall (r : α → α → Prop) [DecidableRel r]
    (a : α) (xs : List α) (h : ∀ b ∈ xs, r a b) :
    List.orderedInsert r a xs = a :: xs := by
  cases xs with
  | nil => rfl
  | cons b xs => exact List.orderedInsert_cons_of_le r xs (h b List.mem_cons_self)

/-- Rejecting the inserted value leaves the entire old filtered subsequence unchanged. -/
theorem filter_orderedInsert_of_neg (r : α → α → Prop) [DecidableRel r]
    (p : α → Bool) (a : α) (xs : List α) (ha : p a = false) :
    (List.orderedInsert r a xs).filter p = xs.filter p := by
  have hs := (List.sublist_orderedInsert (r := r) a xs).filter p
  have hp : ((List.orderedInsert r a xs).filter p).Perm (xs.filter p) := by
    simpa [List.filter_cons, ha] using (List.perm_orderedInsert r a xs).filter p
  exact (hs.eq_of_length hp.length_eq.symm).symm

/-- A retained value can be inserted after filtering a pairwise-ordered input.
Totality, antisymmetry and any equality decision on elements are unnecessary. -/
theorem filter_orderedInsert_of_pos (r : α → α → Prop) [DecidableRel r]
    [IsTrans α r] (p : α → Bool) (a : α) (xs : List α)
    (hxs : xs.Pairwise r) (ha : p a = true) :
    (List.orderedInsert r a xs).filter p = List.orderedInsert r a (xs.filter p) := by
  have hi : (List.orderedInsert r a (xs.filter p)).filter p =
      List.orderedInsert r a (xs.filter p) := by
    apply List.filter_eq_self.mpr
    intro b hb
    rcases (List.mem_orderedInsert r).mp hb with rfl | hb
    · exact ha
    · exact (List.mem_filter.mp hb).2
  have hs := (List.Sublist.orderedInsert_sublist (r := r) a
    (List.filter_sublist (p := p) (l := xs)) hxs).filter p
  rw [hi] at hs
  have hp := ((List.perm_orderedInsert r a xs).filter p).length_eq
  have hl : (List.orderedInsert r a (xs.filter p)).length =
      ((List.orderedInsert r a xs).filter p).length := by
    rw [List.orderedInsert_length]
    simpa [List.filter_cons, ha] using hp.symm
  exact (hs.eq_of_length hl).symm

end Applications.Sorting

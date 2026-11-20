import Mathlib.Data.List.Sort
import Applications.Sorting.Specification

/-!
Observations of canonical ordered insertion, used in FDSA §§2.2 and 2.8.
Insertion always keeps every old occurrence. Filtering a rejected new value
therefore needs no ordering law; filtering a retained value also uses the
ordered-input and transitivity hypotheses. These are value laws, not cost laws.
The indexed insertion proofs also reconstruct VFA Sort's optional positional
route, independently of the pairwise and adjacent-chain correctness proofs.
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

/-- A successful output lookup either finds the inserted value or has an old
index witness. No sortedness or order laws are required. -/
theorem getElem?_orderedInsert_origin (r : α → α → Prop) [DecidableRel r]
    (a : α) (xs : List α) (i : Nat) (v : α)
    (h : (List.orderedInsert r a xs)[i]? = some v) :
    a = v ∨ ∃ j : Nat, xs[j]? = some v := by
  have hv : v ∈ List.orderedInsert r a xs :=
    List.mem_iff_getElem?.mpr ⟨i, h⟩
  rcases (List.mem_orderedInsert r).mp hv with hv | hv
  · exact Or.inl hv.symm
  · exact Or.inr (List.mem_iff_getElem?.mp hv)

private theorem indexed_cons (r : α → α → Prop) (a : α) (xs : List α)
    (hhead : ∀ (i : Nat) (b : α), xs[i]? = some b → r a b)
    (htail : Specification.Indexed r xs) : Specification.Indexed r (a :: xs) := by
  intro i j x y hij hi hj
  cases i with
  | zero =>
      cases j with
      | zero => omega
      | succ j =>
          have hax : a = x := Option.some.inj hi
          subst x
          exact hhead j y hj
  | succ i =>
      cases j with
      | zero => omega
      | succ j => exact htail i j x y (Nat.lt_of_succ_lt_succ hij) hi hj

private theorem indexed_tail (r : α → α → Prop) (a : α) (xs : List α)
    (h : Specification.Indexed r (a :: xs)) : Specification.Indexed r xs := by
  intro i j x y hij hi hj
  exact h (i + 1) (j + 1) x y (Nat.succ_lt_succ hij) hi hj

/-- Direct positional insertion proof: shift successful indices and identify
their origins. This proof does not use pairwise/chain correctness or a bridge
between sortedness specifications. -/
theorem indexed_orderedInsert (r : α → α → Prop) [DecidableRel r]
    [Std.Total r] [IsTrans α r] (a : α) (xs : List α)
    (h : Specification.Indexed r xs) :
    Specification.Indexed r (List.orderedInsert r a xs) := by
  induction xs with
  | nil =>
      apply indexed_cons r a []
      · intro i v hv
        change none = some v at hv
        cases hv
      · intro i j x y hij hi hj
        change none = some x at hi
        cases hi
  | cons b xs ih =>
      have ht := indexed_tail r b xs h
      by_cases hab : r a b
      · rw [List.orderedInsert_cons_of_le r xs hab]
        apply indexed_cons r a (b :: xs)
        · intro i v hv
          cases i with
          | zero =>
              have hb : b = v := Option.some.inj hv
              exact hb ▸ hab
          | succ i =>
              exact IsTrans.trans a b v hab
                (h 0 (i + 1) b v (Nat.zero_lt_succ i) rfl hv)
        · exact h
      · rw [List.orderedInsert_of_not_le r xs hab]
        apply indexed_cons r b (List.orderedInsert r a xs)
        · intro i v hv
          rcases getElem?_orderedInsert_origin r a xs i v hv with hav | ⟨j, hj⟩
          · subst v
            exact (total_of r a b).resolve_left hab
          · exact h 0 (j + 1) b v (Nat.zero_lt_succ j) rfl hj
        · exact ih ht

/-- Tail-first sorting inherits the independent positional insertion proof. -/
theorem indexed_insertionSort (r : α → α → Prop) [DecidableRel r]
    [Std.Total r] [IsTrans α r] (xs : List α) :
    Specification.Indexed r (List.insertionSort r xs) := by
  induction xs with
  | nil =>
      intro i j a b hij hi hj
      change none = some a at hi
      cases hi
  | cons a xs ih =>
      rw [List.insertionSort_cons]
      exact indexed_orderedInsert r a _ ih

end Applications.Sorting

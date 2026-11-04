import Applications.Selection.CountRank
import Applications.Sequences.Chunks
import Mathlib.Algebra.Order.Floor.Ring

/-!
The mathematical median-of-medians pivot and its two-sided occurrence bounds.

Each chunk carries a proof of nonemptiness, so its median is a payload value.
The outer pivot remains optional, including on empty inputs and at chunk size
zero. This is the specification value from FDSA §3.2, not the fast recursive
selection realization or a claim about its execution cost.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.Selection
open Applications.Sequences.Chunks
universe u v
variable {α : Type u} [LinearOrder α]

/-- The lower median of a list with an explicit nonemptiness proof. -/
def lowerMedianValue (xs : List α) (hx : xs ≠ []) : α :=
  (ordered xs)[(xs.length - 1) / 2]'(by
    have hn : 0 < xs.length :=
      Nat.pos_of_ne_zero (fun h => hx (List.length_eq_zero_iff.mp h))
    have hl := (ordered_perm xs).length_eq
    omega)

theorem lowerMedianValue_ranked (xs : List α) (hx : xs ≠ []) :
    RankedAt xs ((xs.length - 1) / 2) (lowerMedianValue xs hx) := by
  apply ranked_iff_index.mpr
  apply List.getElem?_eq_some_iff.mpr
  have hn : 0 < xs.length :=
    Nat.pos_of_ne_zero (fun h => hx (List.length_eq_zero_iff.mp h))
  have hl := (ordered_perm xs).length_eq
  exact ⟨by omega, rfl⟩

theorem lowerMedianValue_mem (xs : List α) (hx : xs ≠ []) :
    lowerMedianValue xs hx ∈ xs := (lowerMedianValue_ranked xs hx).mem

/-- The payload adapter agrees with every valid existing pivot policy. -/
theorem lowerMedianWith_eq_some_value (choose : List α → Option α)
    (hv : PivotValid choose) (xs : List α) (hx : xs ≠ []) :
    lowerMedianWith choose xs = some (lowerMedianValue xs hx) := by
  rw [lowerMedian_value choose hv xs]
  exact ranked_iff_index.mp (lowerMedianValue_ranked xs hx)

theorem lowerMedianValue_count_bounds (xs : List α) (hx : xs ≠ []) :
    xs.countP (fun x => decide (x < lowerMedianValue xs hx)) ≤ (xs.length - 1) / 2 ∧
      xs.countP (fun x => decide (lowerMedianValue xs hx < x)) ≤ xs.length / 2 :=
  lowerMedian_count_bounds _ head_pivot_valid xs _
    (lowerMedianWith_eq_some_value _ head_pivot_valid xs hx)

/-- Mapping proof-carrying nonempty chunks produces payloads directly. -/
def chunkMedians (d : Nat) (xs : List α) : List α :=
  (chop d xs).attach.map fun ys =>
    lowerMedianValue ys.val (chop_mem_ne_nil d xs ys.val ys.property)

@[simp] theorem length_chunkMedians (d : Nat) (xs : List α) :
    (chunkMedians d xs).length = xs.length ⌈/⌉ d := by
  simp only [chunkMedians, List.length_map, List.length_attach, length_chop]

theorem chunkMedians_eq_nil_iff (d : Nat) (xs : List α) :
    chunkMedians d xs = [] ↔ d = 0 ∨ xs = [] := by
  have he : (chunkMedians d xs).length = (chop d xs).length := by
    simp only [chunkMedians, List.length_map, List.length_attach]
  rw [← List.length_eq_zero_iff, he, List.length_eq_zero_iff, chop_eq_nil_iff]

theorem mem_chunkMedians (d : Nat) (xs : List α) (a : α)
    (ha : a ∈ chunkMedians d xs) : a ∈ xs := by
  obtain ⟨ys, _, he⟩ := List.mem_map.mp ha
  rw [← he]
  exact mem_of_mem_chop ys.property (lowerMedianValue_mem _ _)

/-- General chunk size is retained for Exercise 3.8; the chapter uses five. -/
def medianOfMedians (d : Nat) (xs : List α) : Option α :=
  lowerMedianWith List.head? (chunkMedians d xs)

theorem medianOfMedians_some_iff_ranked (d : Nat) (xs : List α) (p : α) :
    medianOfMedians d xs = some p ↔
      RankedAt (chunkMedians d xs) (((chunkMedians d xs).length - 1) / 2) p := by
  rw [medianOfMedians, lowerMedian_value _ head_pivot_valid, ranked_iff_index]

theorem medianOfMedians_none (d : Nat) (xs : List α) :
    medianOfMedians d xs = none ↔ d = 0 ∨ xs = [] := by
  rw [medianOfMedians, lowerMedian_none _ head_pivot_valid, chunkMedians_eq_nil_iff]

theorem medianOfMedians_mem (d : Nat) (xs : List α) (p : α)
    (hp : medianOfMedians d xs = some p) : p ∈ xs :=
  mem_chunkMedians d xs p (lowerMedian_mem _ head_pivot_valid _ p hp)

theorem medianOfMedians_pivot_valid (d : Nat) (hd : 0 < d) :
    PivotValid (medianOfMedians d : List α → Option α) := by
  intro xs hx
  cases hp : medianOfMedians d xs with
  | none =>
    rcases (medianOfMedians_none d xs).mp hp with h | h
    · omega
    · exact False.elim (hx h)
  | some p => exact ⟨p, rfl, medianOfMedians_mem d xs p hp⟩

/-- A non-strict half bound is necessary when the number of chunks is even. -/
theorem medianOfMedians_median_counts (d : Nat) (xs : List α) (p : α)
    (hp : medianOfMedians d xs = some p) :
    (chunkMedians d xs).countP (fun x => decide (x < p)) ≤ (xs.length ⌈/⌉ d) / 2 ∧
      (chunkMedians d xs).countP (fun x => decide (p < x)) ≤ (xs.length ⌈/⌉ d) / 2 := by
  have hm := lowerMedian_count_bounds _ head_pivot_valid (chunkMedians d xs) p hp
  rw [length_chunkMedians] at hm
  constructor <;> omega

/-- The predicate is a relation to the chosen pivot. Its Boolean complement
is taken for either orientation, preserving repeated chunks and occurrences. -/
def chunkMedianGroups (d : Nat) (xs : List α) (r : α → Bool) :
    List (List α) × List (List α) :=
  let chunks := (chop d xs).attach
  let pick := fun ys : {ys // ys ∈ chop d xs} =>
    r (lowerMedianValue ys.val (chop_mem_ne_nil d xs ys.val ys.property))
  ((chunks.filter pick).map Subtype.val,
    (chunks.filter (fun ys => !pick ys)).map Subtype.val)

theorem chunkMedianGroups_perm (d : Nat) (xs : List α) (r : α → Bool) :
    ((chunkMedianGroups d xs r).1 ++ (chunkMedianGroups d xs r).2).Perm (chop d xs) := by
  unfold chunkMedianGroups
  simpa only [List.map_append, List.attach_map_subtype_val] using
    (List.filter_append_perm
      (fun ys : {ys // ys ∈ chop d xs} =>
        r (lowerMedianValue ys.val (chop_mem_ne_nil d xs ys.val ys.property)))
      (chop d xs).attach).map Subtype.val

theorem chunkMedianGroups_multiset (d : Nat) (xs : List α) (r : α → Bool) :
    ((chunkMedianGroups d xs r).1 : Multiset (List α)) +
      ((chunkMedianGroups d xs r).2 : Multiset (List α)) =
        (chop d xs : Multiset (List α)) := by
  rw [Multiset.coe_add]
  exact Multiset.coe_eq_coe.mpr (chunkMedianGroups_perm d xs r)

theorem chunkMedianGroups_lengths (d : Nat) (xs : List α) (r : α → Bool) :
    (chunkMedianGroups d xs r).1.length + (chunkMedianGroups d xs r).2.length =
      xs.length ⌈/⌉ d := by
  have h := (chunkMedianGroups_perm d xs r).length_eq
  simpa only [List.length_append, length_chop] using h

theorem chunkMedianGroups_related_length (d : Nat) (xs : List α) (r : α → Bool) :
    (chunkMedianGroups d xs r).1.length = (chunkMedians d xs).countP r := by
  unfold chunkMedianGroups chunkMedians
  simp only [List.length_map, ← List.countP_eq_length_filter, List.countP_map,
    Function.comp_def]

/-- A chunk whose median is at least the pivot contributes at most half its
size to the strict lower side, including a short final chunk and ties. -/
theorem chunk_count_lt_of_median_ge (d : Nat) (xs ys : List α)
    (hy : ys ∈ chop d xs) (p : α)
    (hp : p ≤ lowerMedianValue ys (chop_mem_ne_nil d xs ys hy)) :
    ys.countP (fun x => decide (x < p)) ≤ d / 2 := by
  have hm := (lowerMedianValue_count_bounds ys (chop_mem_ne_nil d xs ys hy)).1
  have hl := length_mem_chop d xs ys hy
  have hc : ys.countP (fun x => decide (x < p)) ≤
      ys.countP (fun x => decide (x < lowerMedianValue ys (chop_mem_ne_nil d xs ys hy))) := by
    apply List.countP_mono_left
    intro x _ hx
    exact decide_eq_true (lt_of_lt_of_le (of_decide_eq_true hx) hp)
  omega

theorem chunk_count_gt_of_median_le (d : Nat) (xs ys : List α)
    (hy : ys ∈ chop d xs) (p : α)
    (hp : lowerMedianValue ys (chop_mem_ne_nil d xs ys hy) ≤ p) :
    ys.countP (fun x => decide (p < x)) ≤ d / 2 := by
  have hm := (lowerMedianValue_count_bounds ys (chop_mem_ne_nil d xs ys hy)).2
  have hl := length_mem_chop d xs ys hy
  have hc : ys.countP (fun x => decide (p < x)) ≤
      ys.countP (fun x => decide (lowerMedianValue ys (chop_mem_ne_nil d xs ys hy) < x)) := by
    apply List.countP_mono_left
    intro x _ hx
    exact decide_eq_true (lt_of_le_of_lt hp (of_decide_eq_true hx))
  omega

private theorem sum_le_count_split {β : Type v} (zs : List β)
    (cost : β → Nat) (bad : β → Bool) (small big : Nat) (hs : small ≤ big)
    (hc : ∀ z ∈ zs, cost z ≤ if bad z then big else small) :
    (zs.map cost).sum ≤ small * zs.length + (big - small) * zs.countP bad := by
  revert hc
  induction zs with
  | nil => simp
  | cons z zs ih =>
    intro hc
    have hz := hc z (by simp)
    have ht := ih (fun x hx => hc x (by simp [hx]))
    have hsub := Nat.sub_add_cancel hs
    cases hb : bad z with
    | false =>
      simp only [hb, Bool.false_eq_true, ↓reduceIte] at hz
      simp only [List.map_cons, List.sum_cons, List.length_cons, List.countP_cons,
        hb, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.mul_add, Nat.mul_one]
      omega
    | true =>
      simp only [hb, ↓reduceIte] at hz
      simp only [List.map_cons, List.sum_cons, List.length_cons, List.countP_cons,
        hb, ↓reduceIte, Nat.mul_add, Nat.mul_one]
      omega

private theorem chunk_count_bound (d : Nat) (xs : List α) (r bad : α → Bool)
    (hd : 0 < d)
    (hmed : (chunkMedians d xs).countP bad ≤ (xs.length ⌈/⌉ d) / 2)
    (hgood : ∀ ys (hy : ys ∈ chop d xs),
      bad (lowerMedianValue ys (chop_mem_ne_nil d xs ys hy)) = false →
        ys.countP r ≤ d / 2) :
    xs.countP r ≤ d / 2 * (xs.length ⌈/⌉ d) +
      (d - d / 2) * ((xs.length ⌈/⌉ d) / 2) := by
  let chunks := (chop d xs).attach
  let med := fun ys : {ys // ys ∈ chop d xs} =>
    lowerMedianValue ys.val (chop_mem_ne_nil d xs ys.val ys.property)
  have hc : ∀ ys ∈ chunks,
      ys.val.countP r ≤ if bad (med ys) then d else d / 2 := by
    intro ys _
    cases hb : bad (med ys) with
    | false => exact hgood ys.val ys.property hb
    | true => exact List.countP_le_length.trans (length_mem_chop d xs ys.val ys.property)
  have h := sum_le_count_split chunks (fun ys => ys.val.countP r)
    (fun ys => bad (med ys)) (d / 2) d (Nat.div_le_self d 2) hc
  have hsum : (chunks.map (fun ys => ys.val.countP r)).sum = xs.countP r := by
    dsimp only [chunks]
    rw [List.attach_map_val, countP_chop d xs hd r]
  have hlen : chunks.length = xs.length ⌈/⌉ d := by
    simp only [chunks, List.length_attach, length_chop]
  have hbad : chunks.countP (fun ys => bad (med ys)) =
      (chunkMedians d xs).countP bad := by
    dsimp only [chunks, med]
    simp only [chunkMedians, List.countP_map, Function.comp_def]
  rw [hsum, hlen, hbad] at h
  exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hmed) _)

/-- The general group-size bound needed by Exercise 3.8. Both counts retain
multiplicity; no distinctness, full-final-chunk, or parity hypothesis is used. -/
theorem medianOfMedians_count_bounds (d : Nat) (xs : List α) (p : α)
    (hd : 0 < d) (hp : medianOfMedians d xs = some p) :
    xs.countP (fun x => decide (x < p)) ≤
        d / 2 * (xs.length ⌈/⌉ d) + (d - d / 2) * ((xs.length ⌈/⌉ d) / 2) ∧
      xs.countP (fun x => decide (p < x)) ≤
        d / 2 * (xs.length ⌈/⌉ d) + (d - d / 2) * ((xs.length ⌈/⌉ d) / 2) := by
  have hm := medianOfMedians_median_counts d xs p hp
  constructor
  · apply chunk_count_bound d xs (fun x => decide (x < p))
      (fun x => decide (x < p)) hd hm.1
    intro ys hy h
    exact chunk_count_lt_of_median_ge d xs ys hy p
      (le_of_not_gt (of_decide_eq_false h))
  · apply chunk_count_bound d xs (fun x => decide (p < x))
      (fun x => decide (p < x)) hd hm.2
    intro ys hy h
    exact chunk_count_gt_of_median_le d xs ys hy p
      (le_of_not_gt (of_decide_eq_false h))

theorem size_five_count_arithmetic (n : Nat) :
    2 * (n ⌈/⌉ 5) + 3 * ((n ⌈/⌉ 5) / 2) ≤ (7 * n + 30) ⌈/⌉ 10 := by
  simp only [Nat.ceilDiv_eq_add_pred_div]
  omega

theorem medianOfMedians_five_count_bounds (xs : List α) (p : α)
    (hp : medianOfMedians 5 xs = some p) :
    xs.countP (fun x => decide (x < p)) ≤ (7 * xs.length + 30) ⌈/⌉ 10 ∧
      xs.countP (fun x => decide (p < x)) ≤ (7 * xs.length + 30) ⌈/⌉ 10 := by
  have hm := medianOfMedians_count_bounds 5 xs p (by decide) hp
  have ha := size_five_count_arithmetic xs.length
  exact ⟨hm.1.trans ha, hm.2.trans ha⟩

section CeilingCorrespondence
variable (R : Type v) [Field R] [LinearOrder R] [IsOrderedRing R] [FloorRing R]

/-- Natural ceiling division is the exact ceiling of a positive-denominator
quotient in any ordered floor field, in particular the source's real field. -/
theorem ceil_nat_div (n d : Nat) (hd : 0 < d) :
    ⌈(n : R) / (d : R)⌉₊ = n ⌈/⌉ d := by
  apply eq_of_forall_ge_iff
  intro k
  rw [Nat.ceil_le, ceilDiv_le_iff_le_mul hd,
    div_le_iff₀ (Nat.cast_pos.mpr hd : (0 : R) < d), ← Nat.cast_mul, Nat.cast_le]
  simp only [Nat.mul_comm]

/-- The integer expression includes the source's additive three inside the
ceiling; no rounding or short-final-chunk error is dropped. -/
theorem size_five_ceiling (n : Nat) :
    (7 * n + 30) ⌈/⌉ 10 = ⌈(7 : R) * n / 10 + 3⌉₊ := by
  rw [← ceil_nat_div R (7 * n + 30) 10 (by decide)]
  congr 1
  push_cast
  norm_num [add_div]

theorem medianOfMedians_five_ceil_bounds (xs : List α) (p : α)
    (hp : medianOfMedians 5 xs = some p) :
    xs.countP (fun x => decide (x < p)) ≤ ⌈(7 : R) * xs.length / 10 + 3⌉₊ ∧
      xs.countP (fun x => decide (p < x)) ≤ ⌈(7 : R) * xs.length / 10 + 3⌉₊ := by
  rw [← size_five_ceiling R]
  exact medianOfMedians_five_count_bounds xs p hp

end CeilingCorrespondence
end Applications.Selection

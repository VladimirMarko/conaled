import Applications.Segments.Prefixes
import Applications.Optimization.SelectionTies

/-! First-maximum segment selection through the shared OrderDual argmin. -/
set_option autoImplicit false
set_option warningAsError true

namespace Segments
universe u v
variable {α : Type u} {β : Type v}

/-! ## Source first-biased selector and single-witness segment scan -/

/-- Shared first-biased argmin, with reversed integer score and an empty-input fallback. -/
def maxWith (score : α → Int) (fallback : α) (xs : List α) : α :=
  (Optimization.Thinning.argmin (fun x => OrderDual.toDual (score x)) xs).getD fallback

@[simp] theorem maxWith_nil (score : α → Int) (fallback : α) :
    maxWith score fallback [] = fallback := rfl

@[simp] theorem maxWith_singleton (score : α → Int) (fallback x : α) :
    maxWith score fallback [x] = x := rfl

/-- This is the exact source foldr1/Down recurrence, including first-biased ties. -/
theorem maxWith_cons_cons (score : α → Int) (fallback x y : α) (xs : List α) :
    maxWith score fallback (x :: y :: xs) =
      if decide (score (maxWith score fallback (y :: xs)) ≤ score x) then x
      else maxWith score fallback (y :: xs) := by
  let cost : α → OrderDual Int := fun z => OrderDual.toDual (score z)
  cases h : Optimization.Thinning.argmin cost (y :: xs) with
  | none => have := (Optimization.Thinning.argmin_eq_none_iff cost _).mp h; contradiction
  | some z =>
    change (Optimization.Thinning.argmin cost (x :: y :: xs)).getD fallback =
      if decide (score ((Optimization.Thinning.argmin cost (y :: xs)).getD fallback) ≤ score x)
      then x else (Optimization.Thinning.argmin cost (y :: xs)).getD fallback
    rw [Optimization.Thinning.argmin, h]
    simp [cost]

/-- Independent order-sensitive specification of the first maximum in a list. -/
abbrev FirstMaximum (score : α → Int) (xs : List α) (winner : α) : Prop :=
  Optimization.FirstMinimum (fun x => OrderDual.toDual (score x)) xs winner

theorem firstMaximum_mem (score : α → Int) (xs : List α) (winner : α)
    (h : FirstMaximum score xs winner) : winner ∈ xs :=
  (Optimization.Thinning.argmin_correct _ xs winner
    (Optimization.argmin_eq_some_of_firstMinimum _ xs winner h)).1

theorem firstMaximum_maximal (score : α → Int) (xs : List α) (winner : α)
    (h : FirstMaximum score xs winner) : ∀ x ∈ xs, score x ≤ score winner :=
  (Optimization.Thinning.argmin_correct _ xs winner
    (Optimization.argmin_eq_some_of_firstMinimum _ xs winner h)).2

/-- An independent first-maximum certificate determines the exact shared selector. -/
theorem maxWith_eq_of_firstMaximum (score : α → Int) (fallback : α) (xs : List α)
    (winner : α) (h : FirstMaximum score xs winner) : maxWith score fallback xs = winner := by
  unfold maxWith
  rw [Optimization.argmin_eq_some_of_firstMinimum _ xs winner h]
  rfl

theorem maxWith_firstMaximum (score : α → Int) (fallback : α) (xs : List α)
    (hn : xs ≠ []) : FirstMaximum score xs (maxWith score fallback xs) := by
  let cost : α → OrderDual Int := fun x => OrderDual.toDual (score x)
  cases h : Optimization.Thinning.argmin cost xs with
  | none => exact False.elim (hn ((Optimization.Thinning.argmin_eq_none_iff cost xs).mp h))
  | some winner =>
    have hw : maxWith score fallback xs = winner := by
      change (Optimization.Thinning.argmin cost xs).getD fallback = winner
      rw [h]
      rfl
    rw [hw]
    exact Optimization.argmin_firstMinimum cost xs winner h

theorem maxWith_mem (score : α → Int) (fallback : α) (xs : List α) (hn : xs ≠ []) :
    maxWith score fallback xs ∈ xs :=
  firstMaximum_mem score xs _ (maxWith_firstMaximum score fallback xs hn)

theorem maxWith_maximal (score : α → Int) (fallback : α) (xs : List α) (hn : xs ≠ []) :
    ∀ x ∈ xs, score x ≤ score (maxWith score fallback xs) :=
  firstMaximum_maximal score xs _ (maxWith_firstMaximum score fallback xs hn)

theorem maxWith_mem_maxsWith (score : α → Int) (fallback : α) (xs : List α) (hn : xs ≠ []) :
    maxWith score fallback xs ∈ maxsWith score xs :=
  (mem_maxsWith score xs _).mpr
    ⟨maxWith_mem score fallback xs hn, maxWith_maximal score fallback xs hn⟩

/-- Source single-witness reduction over suffix-prefix optima. -/
def maxSegmentThinByPrefixes (bound : Nat) (xs : List Int) : List Int :=
  maxWith List.sum [] ((tails xs).map (msp1 bound))

/-- Actual printed p277 segment algorithm, before changing the prefix representation. -/
def maxSegmentThinScan (bound : Nat) (xs : List Int) : List Int :=
  maxWith List.sum [] ((scanrTotal (op2 bound) [[]] xs).map (fun ps => ps.getLastD []))

theorem thinnedPrefixes_scan (bound : Nat) (xs : List Int) :
    scanrTotal (op2 bound) [[]] xs = (tails xs).map (thinnedPrefixes bound) :=
  scanrTotal_eq _ _ _

/-- Every row used by map last is nonempty, so its total fallback is unused. -/
theorem thinnedScan_rows_ne_nil (bound : Nat) (xs : List Int) :
    ∀ ps ∈ scanrTotal (op2 bound) [[]] xs, ps ≠ [] := by
  rw [thinnedPrefixes_scan]
  intro ps hp
  obtain ⟨suf, _, rfl⟩ := List.mem_map.mp hp
  exact thinnedPrefixes_ne_nil bound suf

/-- Exact witness equality, preserving the source selector's suffix-order tie policy. -/
theorem maxSegmentThinScan_eq (bound : Nat) (xs : List Int) :
    maxSegmentThinScan bound xs = maxSegmentThinByPrefixes bound xs := by
  rw [maxSegmentThinScan, thinnedPrefixes_scan, List.map_map]
  rfl

theorem prefixOptima_ne_nil (bound : Nat) (xs : List Int) :
    (tails xs).map (msp1 bound) ≠ [] := by
  have hm : msp1 bound xs ∈ (tails xs).map (msp1 bound) :=
    List.mem_map.mpr ⟨xs, self_mem_tails xs, rfl⟩
  intro h
  simp [h] at hm

theorem maxSegmentThinByPrefixes_firstMaximum (bound : Nat) (xs : List Int) :
    FirstMaximum List.sum ((tails xs).map (msp1 bound)) (maxSegmentThinByPrefixes bound xs) :=
  maxWith_firstMaximum _ _ _ (prefixOptima_ne_nil bound xs)

theorem maxSegmentThinScan_firstMaximum (bound : Nat) (xs : List Int) :
    FirstMaximum List.sum ((tails xs).map (msp1 bound)) (maxSegmentThinScan bound xs) := by
  rw [maxSegmentThinScan_eq]
  exact maxSegmentThinByPrefixes_firstMaximum bound xs

theorem maxSegmentThinByPrefixes_optimal (bound : Nat) (xs : List Int) :
    SegmentOptimal bound xs (maxSegmentThinByPrefixes bound xs) := by
  have hfirst := maxSegmentThinByPrefixes_firstMaximum bound xs
  have hmem := firstMaximum_mem List.sum _ _ hfirst
  have hmax := firstMaximum_maximal List.sum _ _ hfirst
  obtain ⟨suf, hsuf, heq⟩ := List.mem_map.mp hmem
  have hp := msp1_optimal bound suf
  refine ⟨?_, ?_, ?_⟩
  · rw [← heq]
    exact prefix_of_suffix_isSegment xs suf _ hsuf hp.1
  · rw [← heq]
    exact hp.2.1
  · intro candidate hc hcb
    obtain ⟨before, after, hcat⟩ := hc
    have htail : candidate ++ after ∈ tails xs :=
      (mem_tails xs _).mpr ⟨before, by simpa only [List.append_assoc] using hcat⟩
    have hprefix := msp1_optimal bound (candidate ++ after)
    have hscore := hprefix.2.2 candidate ⟨after, rfl⟩ hcb
    have hselected := hmax _ (List.mem_map.mpr ⟨candidate ++ after, htail, rfl⟩)
    exact Int.le_trans hscore hselected

theorem maxSegmentThinScan_optimal (bound : Nat) (xs : List Int) :
    SegmentOptimal bound xs (maxSegmentThinScan bound xs) := by
  rw [maxSegmentThinScan_eq]
  exact maxSegmentThinByPrefixes_optimal bound xs

/-- Membership of one selected witness in the source result containing all optima. -/
theorem maxSegmentThinScan_mem_mss0 (bound : Nat) (xs : List Int) :
    maxSegmentThinScan bound xs ∈ mss0 bound xs :=
  (mem_mss0 bound xs _).mpr (maxSegmentThinScan_optimal bound xs)

theorem maxSegmentThinScan_sum_eq_optimum (bound : Nat) (xs candidate : List Int)
    (hc : SegmentOptimal bound xs candidate) :
    (maxSegmentThinScan bound xs).sum = candidate.sum :=
  optimal_segment_sum_unique bound xs _ _ (maxSegmentThinScan_optimal bound xs) hc

@[simp] theorem maxSegmentThinScan_nil (bound : Nat) :
    maxSegmentThinScan bound [] = [] := rfl

theorem maxSegmentThinScan_zero (xs : List Int) : maxSegmentThinScan 0 xs = [] :=
  optimal_segment_zero_bound xs _ (maxSegmentThinScan_optimal 0 xs)

theorem maxSegmentThinScan_nonnegative (bound : Nat) (xs : List Int) :
    0 ≤ (maxSegmentThinScan bound xs).sum :=
  optimal_segment_nonnegative bound xs _ (maxSegmentThinScan_optimal bound xs)

example : maxWith List.sum [] [[1, 1], [2]] = [1, 1] := by decide
example : maxSegmentThinScan 2 [1, 1, -10, 2] = [1, 1] := by decide
example : maxSegmentThinScan 2 [2, -10, 1, 1] = [2] := by decide
example : mss0 2 [1, 1, -10, 2] = [[1, 1], [2]] := by decide
example : maxSegmentThinScan 2 [-3, -1] = [] := by decide

/-- Suffix-order certificates recover the precise selected witness, including ties. -/
theorem maxSegmentThinScan_eq_of_firstMaximum (bound : Nat) (xs p : List Int)
    (h : FirstMaximum List.sum ((tails xs).map (msp1 bound)) p) :
    maxSegmentThinScan bound xs = p := by
  rw [maxSegmentThinScan_eq]
  exact maxWith_eq_of_firstMaximum List.sum [] _ p h

end Segments

import Applications.Segments.Prefixes

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
def FirstMaximum (score : α → Int) (xs : List α) (winner : α) : Prop :=
  ∃ before after, xs = before ++ winner :: after ∧
    (∀ x ∈ before, score x < score winner) ∧
    (∀ x ∈ after, score x ≤ score winner)

theorem firstMaximum_mem (score : α → Int) (xs : List α) (winner : α)
    (h : FirstMaximum score xs winner) : winner ∈ xs := by
  obtain ⟨before, after, rfl, _, _⟩ := h
  simp

theorem firstMaximum_maximal (score : α → Int) (xs : List α) (winner : α)
    (h : FirstMaximum score xs winner) : ∀ x ∈ xs, score x ≤ score winner := by
  obtain ⟨before, after, rfl, hb, ha⟩ := h
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact Int.le_of_lt (hb x hx)
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact Int.le_refl _
    · exact ha x hx

/-- An independent first-maximum certificate determines the exact shared selector. -/
theorem maxWith_eq_of_firstMaximum (score : α → Int) (fallback : α) (xs : List α)
    (winner : α) (h : FirstMaximum score xs winner) : maxWith score fallback xs = winner := by
  obtain ⟨before, after, rfl, hb, ha⟩ := h
  let cost : α → OrderDual Int := fun x => OrderDual.toDual (score x)
  have select : ∀ pre : List α, (∀ x ∈ pre, score x < score winner) →
      Optimization.Thinning.argmin cost (pre ++ winner :: after) = some winner := by
    intro pre
    induction pre with
    | nil => intro _; exact Optimization.Thinning.argmin_first cost winner after ha
    | cons x pre ih =>
      intro hx
      have rest := ih (fun y hy => hx y (by simp [hy]))
      have strict := hx x (by simp)
      simp only [List.cons_append, Optimization.Thinning.argmin, rest]
      simp [cost, show ¬ score winner ≤ score x by omega]
  unfold maxWith
  rw [show Optimization.Thinning.argmin (fun x => OrderDual.toDual (score x))
      (before ++ winner :: after) = some winner from select before hb]
  rfl

theorem maxWith_firstMaximum (score : α → Int) (fallback : α) (xs : List α)
    (hn : xs ≠ []) : FirstMaximum score xs (maxWith score fallback xs) := by
  induction xs with
  | nil => exact False.elim (hn rfl)
  | cons x xs ih =>
    cases xs with
    | nil => exact ⟨[], [], rfl, by simp, by simp⟩
    | cons y ys =>
      have hf := ih (by simp)
      have hm := firstMaximum_maximal score (y :: ys) _ hf
      by_cases hx : score (maxWith score fallback (y :: ys)) ≤ score x
      · rw [maxWith_cons_cons]
        simp only [hx, decide_true, ite_true]
        exact ⟨[], y :: ys, rfl, by simp,
          fun z hz => Int.le_trans (hm z hz) hx⟩
      · have hlt : score x < score (maxWith score fallback (y :: ys)) := by omega
        obtain ⟨before, after, hcat, hb, ha⟩ := hf
        rw [maxWith_cons_cons]
        simp only [hx, decide_false, Bool.false_eq_true, ite_false]
        refine ⟨x :: before, after, congrArg (List.cons x) hcat, ?_, ha⟩
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hlt
        · exact hb z hz

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

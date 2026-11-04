import Applications.Selection.MedianOfMedians

/-!
Connected applications of the general pivot bound, FDSA Exercise 3.8(1).

The existing occurrence bound is used for actual partition buckets, arbitrary
positive group sizes, and odd/even concrete inputs with duplicates and a short
last chunk. These are value/count statements; the generalized nested selector
and its recurrence analysis are separate obligations.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.GeneralMedianBounds
open Applications.Selection Applications.Sequences.Chunks
universe u
variable {α : Type u} [LinearOrder α]

theorem partition_bounds (d : Nat) (xs : List α) (p : α)
    (hd : 0 < d) (hp : medianOfMedians d xs = some p) :
    (partition3 p xs).1.length ≤
        d / 2 * (xs.length ⌈/⌉ d) + (d - d / 2) * ((xs.length ⌈/⌉ d) / 2) ∧
      (partition3 p xs).2.2.length ≤
        d / 2 * (xs.length ⌈/⌉ d) + (d - d / 2) * ((xs.length ⌈/⌉ d) / 2) := by
  simpa only [partition3_eq_filters, List.countP_eq_length_filter] using
    medianOfMedians_count_bounds d xs p hd hp

/-- The successful-pivot premise is available for every nonempty input and
positive size; the bound is not merely conditional on an uninhabited case. -/
theorem nonempty_input_has_bounded_pivot (d : Nat) (xs : List α)
    (hd : 0 < d) (hx : xs ≠ []) :
    ∃ p : α, medianOfMedians d xs = some p ∧ p ∈ xs ∧
      (partition3 p xs).1.length ≤
          d / 2 * (xs.length ⌈/⌉ d) + (d - d / 2) * ((xs.length ⌈/⌉ d) / 2) ∧
        (partition3 p xs).2.2.length ≤
          d / 2 * (xs.length ⌈/⌉ d) + (d - d / 2) * ((xs.length ⌈/⌉ d) / 2) := by
  obtain ⟨p, hp, hm⟩ := medianOfMedians_pivot_valid d hd xs hx
  exact ⟨p, hp, hm, partition_bounds d xs p hd hp⟩

theorem three_group_bounds (xs : List α) (p : α)
    (hp : medianOfMedians 3 xs = some p) :
    xs.countP (fun x => decide (x < p)) ≤
        (xs.length ⌈/⌉ 3) + 2 * ((xs.length ⌈/⌉ 3) / 2) ∧
      xs.countP (fun x => decide (p < x)) ≤
        (xs.length ⌈/⌉ 3) + 2 * ((xs.length ⌈/⌉ 3) / 2) := by
  simpa using medianOfMedians_count_bounds 3 xs p (by decide) hp

theorem four_group_bounds (xs : List α) (p : α)
    (hp : medianOfMedians 4 xs = some p) :
    xs.countP (fun x => decide (x < p)) ≤
        2 * (xs.length ⌈/⌉ 4) + 2 * ((xs.length ⌈/⌉ 4) / 2) ∧
      xs.countP (fun x => decide (p < x)) ≤
        2 * (xs.length ⌈/⌉ 4) + 2 * ((xs.length ⌈/⌉ 4) / 2) := by
  simpa using medianOfMedians_count_bounds 4 xs p (by decide) hp

theorem six_group_bounds (xs : List α) (p : α)
    (hp : medianOfMedians 6 xs = some p) :
    xs.countP (fun x => decide (x < p)) ≤
        3 * (xs.length ⌈/⌉ 6) + 3 * ((xs.length ⌈/⌉ 6) / 2) ∧
      xs.countP (fun x => decide (p < x)) ≤
        3 * (xs.length ⌈/⌉ 6) + 3 * ((xs.length ⌈/⌉ 6) / 2) := by
  simpa using medianOfMedians_count_bounds 6 xs p (by decide) hp

theorem constant_input_pivot (d n : Nat) (a : α) (hd : 0 < d) (hn : 0 < n) :
    medianOfMedians d (List.replicate n a) = some a := by
  have hx : List.replicate n a ≠ [] :=
    fun h => Nat.ne_of_gt hn ((List.replicate_eq_nil_iff a).mp h)
  obtain ⟨p, hp, hm⟩ := medianOfMedians_pivot_valid d hd (List.replicate n a) hx
  have he : p = a := List.eq_of_mem_replicate hm
  exact hp.trans (congrArg some he)

theorem constant_input_strict_counts (n : Nat) (a : α) :
    (List.replicate n a).countP (fun x => decide (x < a)) = 0 ∧
      (List.replicate n a).countP (fun x => decide (a < x)) = 0 := by
  simp [List.countP_replicate]

/-- Only the stated agreement on actual nonempty chunks is used. The concrete
cases prove it by occurrence ranks; this does not change the median policy. -/
private theorem chunkMedians_eq_heads (d : Nat) (xs : List Nat)
    (h : ∀ ys (hy : ys ∈ chop d xs),
      lowerMedianValue ys (chop_mem_ne_nil d xs ys hy) = ys.headD 0) :
    chunkMedians d xs = (chop d xs).map (fun ys : List Nat => ys.headD 0) := by
  unfold chunkMedians
  calc
    _ = (chop d xs).attach.map (fun ys => ys.val.headD 0) := by
      apply List.map_congr_left
      intro ys _
      exact h ys.val ys.property
    _ = _ := List.attach_map_val (l := chop d xs) (f := fun ys : List Nat => ys.headD 0)

def oddInput : List Nat := [0, 0, 1, 2, 2, 3, 9]

theorem odd_chops : chop 3 oddInput = [[0, 0, 1], [2, 2, 3], [9]] := by decide

theorem odd_chunk_count : oddInput.length ⌈/⌉ 3 = 3 := by
  have h := congrArg List.length odd_chops
  rw [length_chop] at h
  exact h

theorem odd_medians : chunkMedians 3 oddInput = [0, 2, 9] := by
  have hm (ys : List Nat) (hy : ys ∈ chop 3 oddInput) :
      lowerMedianValue ys (chop_mem_ne_nil 3 oddInput ys hy) = ys.headD 0 := by
    have hy' : ys = [0, 0, 1] ∨ ys = [2, 2, 3] ∨ ys = [9] := by
      simpa only [odd_chops, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] using hy
    rcases hy' with rfl | rfl | rfl <;>
      exact (lowerMedianValue_ranked _ _).unique (ranked_iff_count_bounds.mpr (by decide))
  exact (chunkMedians_eq_heads 3 oddInput hm).trans
    (congrArg (List.map (fun ys : List Nat => ys.headD 0)) odd_chops)

theorem odd_pivot : medianOfMedians 3 oddInput = some 2 := by
  apply (medianOfMedians_some_iff_ranked 3 oddInput 2).mpr
  rw [odd_medians]
  exact ranked_iff_count_bounds.mpr (by decide)

theorem odd_strict_counts : oddInput.countP (fun x => decide (x < 2)) = 3 ∧
    oddInput.countP (fun x => decide (2 < x)) = 2 := by decide

theorem odd_bound_from_general : oddInput.countP (fun x => decide (x < 2)) ≤ 5 ∧
    oddInput.countP (fun x => decide (2 < x)) ≤ 5 := by
  have h := three_group_bounds oddInput 2 odd_pivot
  rw [odd_chunk_count] at h
  exact h

theorem odd_partition_values : partition3 2 oddInput = ([0, 0, 1], [2, 2], [3, 9]) := by
  decide

theorem odd_partition_bounds : (partition3 2 oddInput).1.length ≤ 5 ∧
    (partition3 2 oddInput).2.2.length ≤ 5 := by
  have h := partition_bounds 3 oddInput 2 (by decide) odd_pivot
  rw [odd_chunk_count] at h
  exact h

def evenInput : List Nat := [0, 0, 1, 2, 3, 3, 4, 5, 9]

theorem even_chops : chop 4 evenInput = [[0, 0, 1, 2], [3, 3, 4, 5], [9]] := by decide

theorem even_chunk_count : evenInput.length ⌈/⌉ 4 = 3 := by
  have h := congrArg List.length even_chops
  rw [length_chop] at h
  exact h

theorem even_medians : chunkMedians 4 evenInput = [0, 3, 9] := by
  have hm (ys : List Nat) (hy : ys ∈ chop 4 evenInput) :
      lowerMedianValue ys (chop_mem_ne_nil 4 evenInput ys hy) = ys.headD 0 := by
    have hy' : ys = [0, 0, 1, 2] ∨ ys = [3, 3, 4, 5] ∨ ys = [9] := by
      simpa only [even_chops, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] using hy
    rcases hy' with rfl | rfl | rfl <;>
      exact (lowerMedianValue_ranked _ _).unique (ranked_iff_count_bounds.mpr (by decide))
  exact (chunkMedians_eq_heads 4 evenInput hm).trans
    (congrArg (List.map (fun ys : List Nat => ys.headD 0)) even_chops)

theorem even_pivot : medianOfMedians 4 evenInput = some 3 := by
  apply (medianOfMedians_some_iff_ranked 4 evenInput 3).mpr
  rw [even_medians]
  exact ranked_iff_count_bounds.mpr (by decide)

theorem even_strict_counts : evenInput.countP (fun x => decide (x < 3)) = 4 ∧
    evenInput.countP (fun x => decide (3 < x)) = 3 := by decide

theorem even_bound_from_general : evenInput.countP (fun x => decide (x < 3)) ≤ 8 ∧
    evenInput.countP (fun x => decide (3 < x)) ≤ 8 := by
  have h := four_group_bounds evenInput 3 even_pivot
  rw [even_chunk_count] at h
  exact h

theorem even_partition_values :
    partition3 3 evenInput = ([0, 0, 1, 2], [3, 3], [4, 5, 9]) := by decide

theorem even_partition_bounds : (partition3 3 evenInput).1.length ≤ 8 ∧
    (partition3 3 evenInput).2.2.length ≤ 8 := by
  have h := partition_bounds 4 evenInput 3 (by decide) even_pivot
  rw [even_chunk_count] at h
  exact h

theorem integer_ties_with_short_chunk :
    medianOfMedians 6 (List.replicate 7 (-4 : Int)) = some (-4) ∧
      chop 6 (List.replicate 7 (-4 : Int)) = [List.replicate 6 (-4), [-4]] ∧
        (List.replicate 7 (-4 : Int)).countP (fun x => decide (x < -4)) = 0 ∧
          (List.replicate 7 (-4 : Int)).countP (fun x => decide (-4 < x)) = 0 :=
  ⟨constant_input_pivot 6 7 (-4) (by decide) (by decide), by decide,
    constant_input_strict_counts 7 (-4)⟩

/-- The rounded general bound can exceed the input length on a small input;
the exact zero strict counts above remain compatible with that upper bound. -/
theorem integer_tie_bound :
    (List.replicate 7 (-4 : Int)).countP (fun x => decide (x < -4)) ≤ 9 ∧
      (List.replicate 7 (-4 : Int)).countP (fun x => decide (-4 < x)) ≤ 9 := by
  have h := six_group_bounds (List.replicate 7 (-4 : Int)) (-4)
    (constant_input_pivot 6 7 (-4) (by decide) (by decide))
  have hc : (List.replicate 7 (-4 : Int)).length ⌈/⌉ 6 = 2 := by decide
  rw [hc] at h
  exact h

end Examples.GeneralMedianBounds

import Applications.Parallel.InclusiveScan
import SquareKit.FiniteRecurrences
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Opposite
import Mathlib.Data.List.Range

/-!
# Native affine folds observed through actual certified scans

Opposite endomorphisms execute transitions in their listed order. Applying every
actual inclusive scanner result at an arbitrary base gives all native fold
prefixes. The recipes below make value and order claims only.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.RecurrenceScans

open Applications.Parallel SquareKit.ListFusion SquareKit.FiniteRecurrences
open scoped BigOperators

universe u

/-- Multiplication records chronological application: first `f`, then `g`. -/
theorem chronological_apply {α : Type u} (f g : Function.End α) (b : α) :
    MulOpposite.unop (MulOpposite.op f * MulOpposite.op g) b = g (f b) := rfl

/-- The scanner's identity seed observes to any supplied state, at any universe. -/
theorem inclusive_apply {α : Type u} {s : Shape}
    (p : Scanner s (MulOpposite (Function.End α)))
    (x : s.Data (MulOpposite (Function.End α))) (b : α) :
    (p.inclusive x).map (fun q : MulOpposite (Function.End α) => MulOpposite.unop q b) =
      (s.flatten x).scanl
        (fun (state : α) (q : MulOpposite (Function.End α)) => MulOpposite.unop q state) b := by
  exact p.inclusive_fusion (fun q : MulOpposite (Function.End α) => MulOpposite.unop q b)
    (fun (state : α) (q : MulOpposite (Function.End α)) => MulOpposite.unop q state)
    (fun _ => True) trivial
    (fun _ _ _ => trivial) (fun _ _ _ => rfl) x

/-- Ordered flattening identifies every transition; input length alone would
not determine the observed states. -/
theorem inclusive_transitions {α : Type u} {s : Shape}
    (p : Scanner s (MulOpposite (Function.End α)))
    (x : s.Data (MulOpposite (Function.End α)))
    (fs : List (Function.End α)) (b : α)
    (hflatten : s.flatten x = fs.map MulOpposite.op) :
    (p.inclusive x).map (fun q : MulOpposite (Function.End α) => MulOpposite.unop q b) =
      fs.scanl (fun state f => f state) b := by
  simpa only [hflatten, List.scanl_map, MulOpposite.unop_op] using inclusive_apply p x b

/-- Each observed position is the native fold of the corresponding prefix,
including the empty prefix and the complete transition list. -/
theorem inclusive_transition_prefixes {α : Type u} {s : Shape}
    (p : Scanner s (MulOpposite (Function.End α)))
    (x : s.Data (MulOpposite (Function.End α)))
    (fs : List (Function.End α)) (b : α)
    (hflatten : s.flatten x = fs.map MulOpposite.op) :
    (p.inclusive x).map (fun q : MulOpposite (Function.End α) => MulOpposite.unop q b) =
      (List.range (fs.length + 1)).map (fun j =>
        (fs.take j).foldl (fun state f => f state) b) := by
  rw [inclusive_transitions p x fs b hflatten]
  exact scanl_prefix_values _ _ _

/-- Arbitrary natural weights and tolls, including zero weights, use positive
indices. Every observed prefix agrees with the native indexed affine fold. -/
theorem inclusive_affine_prefixes {s : Shape}
    (p : Scanner s (MulOpposite (Function.End Nat)))
    (x : s.Data (MulOpposite (Function.End Nat)))
    (weight toll : Nat → Nat) (b n : Nat)
    (hflatten : s.flatten x = (List.range' 1 n).map (fun k =>
      MulOpposite.op (show Function.End Nat from fun state => weight k * state + toll k))) :
    (p.inclusive x).map (fun q : MulOpposite (Function.End Nat) => MulOpposite.unop q b) =
      (List.range (n + 1)).map (fun j =>
        (List.range' 1 j).foldl (fun state k => weight k * state + toll k) b) := by
  rw [inclusive_apply p x b, hflatten, List.scanl_map]
  change (List.range' 1 n).scanl (fun state k => weight k * state + toll k) b = _
  rw [scanl_prefix_values]
  simp only [List.length_range']
  apply List.map_congr_left
  intro j hj
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (List.mem_range.mp hj)
  rw [List.take_range'_of_length_ge hjn]

/-! ## A composed four-entry scan followed by a fifth entry -/

def five : ScanPlan := .prod (.comp .pair .pair) .leaf

def fiveAffineInput (weight toll : Nat → Nat) :
    five.shape.Data (MulOpposite (Function.End Nat)) :=
  five.shape.map (fun k =>
    MulOpposite.op (show Function.End Nat from fun state => weight k * state + toll k))
    ((((1, 2), (3, 4)), 5) : ((Nat × Nat) × (Nat × Nat)) × Nat)

theorem five_affine_prefixes (weight toll : Nat → Nat) (b : Nat) :
    (five.scanner.inclusive (fiveAffineInput weight toll)).map
      (fun q : MulOpposite (Function.End Nat) => MulOpposite.unop q b) =
      (List.range 6).map (fun j =>
        (List.range' 1 j).foldl (fun state k => weight k * state + toll k) b) :=
  inclusive_affine_prefixes five.scanner (fiveAffineInput weight toll) weight toll b 5 (by rfl)

/-- The weighted half-sum uses positive indices, through index five. -/
theorem half_sum_five :
    (∑ k ∈ Finset.Ico (1 : Nat) (5 + 1), (k : ℚ) / (2 : ℚ) ^ k) = 57 / 32 :=
  (SquareKit.FiniteSums.half_sum_closed 5).trans (by norm_num)

/-- Both 0! and 1! occur in this native range sum. -/
theorem reciprocal_factorial_five :
    (∑ k ∈ Finset.range 5, 1 / (Nat.factorial k : ℚ)) = 65 / 24 := by
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- Source R211: the public exact identity and the actual scan give the same
endpoint, while the scan observation retains all six states. -/
theorem additive_source_case :
    (List.range' 1 5).foldl (fun x k => x + 2 * k) 3 = 33 ∧
      (five.scanner.inclusive (fiveAffineInput (fun _ => 1) (fun k => 2 * k))).map
        (fun q : MulOpposite (Function.End Nat) => MulOpposite.unop q 3) = [3, 5, 9, 15, 23, 33] := by
  constructor
  · exact (additive_exact 3 2 5).trans (by norm_num [SquareKit.FiniteSums.triangle_exact])
  · rw [five_affine_prefixes]
    rfl

/-- Source R212: the rational normalization yields 210 at the same endpoint
observed from the actual composed scan. -/
theorem doubling_source_case :
    (List.range' 1 5).foldl (fun x k => 2 * x + 2 * k) 3 = 210 ∧
      (five.scanner.inclusive (fiveAffineInput (fun _ => 2) (fun k => 2 * k))).map
        (fun q : MulOpposite (Function.End Nat) => MulOpposite.unop q 3) = [3, 8, 20, 46, 100, 210] := by
  constructor
  · have h : (((List.range' 1 5).foldl (fun x k => 2 * x + 2 * k) 3 : Nat) : ℚ) = 210 :=
      (doubling_normalized_sum 3 2 5).trans (by norm_num [half_sum_five])
    exact_mod_cast h
  · rw [five_affine_prefixes]
    rfl

/-- Source R213: the factorial normalization and the scanner agree, with
independent base three and toll coefficient two. -/
theorem factorial_source_case :
    (List.range' 1 5).foldl (fun x k => k * x + 2 * k) 3 = 1010 ∧
      (five.scanner.inclusive (fiveAffineInput id (fun k => 2 * k))).map
        (fun q : MulOpposite (Function.End Nat) => MulOpposite.unop q 3) = [3, 5, 14, 48, 200, 1010] := by
  constructor
  · have h : (((List.range' 1 5).foldl (fun x k => k * x + 2 * k) 3 : Nat) : ℚ) = 1010 :=
      (factorial_normalized_sum 3 2 5).trans
        (by
          rw [reciprocal_factorial_five]
          norm_num [Nat.factorial])
    exact_mod_cast h
  · rw [five_affine_prefixes]
    rfl

-- These connected normalization values retain the explicit natural accumulator.
example :
    (((List.range' 1 5).foldl (fun x k => 2 * x + 2 * k) 3 : Nat) : ℚ) =
      (2 : ℚ) ^ 5 * (3 + 2 * (57 / 32)) := by
  rw [doubling_normalized_sum, half_sum_five]
  norm_num

example :
    (((List.range' 1 5).foldl (fun x k => k * x + 2 * k) 3 : Nat) : ℚ) =
      (Nat.factorial 5 : ℚ) * (3 + 2 * (65 / 24)) := by
  rw [factorial_normalized_sum, reciprocal_factorial_five]
  norm_num

example :
    (List.range' 1 5).foldl (fun x k => 2 * x + 2 * k) 3 + 14 = 224 := by
  simpa using doubling_exact 3 2 5

/-- Source D162 is a native rational finite sum and satisfies both public bounds. -/
theorem reciprocal_factorial_source_case :
    (∑ k ∈ Finset.range 4, 1 / (Nat.factorial k : ℚ)) = 8 / 3 ∧
      0 ≤ (∑ k ∈ Finset.range 4, 1 / (Nat.factorial k : ℚ)) ∧
      (∑ k ∈ Finset.range 4, 1 / (Nat.factorial k : ℚ)) < 3 := by
  refine ⟨?_, reciprocal_factorial_sum_nonneg 4, reciprocal_factorial_sum_lt_three 4⟩
  norm_num [Finset.sum_range_succ, Nat.factorial]

example :
    (List.range 6).map (fun n => ∑ k ∈ Finset.range n, 1 / (Nat.factorial k : ℚ)) =
      [0, 1, 2, 5 / 2, 8 / 3, 65 / 24] := by
  norm_num [List.range_succ, Finset.sum_range_succ, Nat.factorial]

/-! ## Empty plans, chronology, and resets -/

/-- An actual empty scanner observes its identity as the arbitrary supplied base. -/
theorem empty_observation {α : Type u} (b : α) :
    ((ScanPlan.empty.scanner : Scanner .empty (MulOpposite (Function.End α))).inclusive
      PUnit.unit).map (fun q : MulOpposite (Function.End α) => MulOpposite.unop q b) = [b] := by
  exact (inclusive_apply (α := α) (s := .empty)
    (ScanPlan.empty.scanner : Scanner .empty (MulOpposite (Function.End α)))
    PUnit.unit b).trans (by rfl)

/-- Source D163 retains base three independently of coefficient two. -/
theorem empty_doubling_source_case :
    (List.range' 1 0).foldl (fun x k => 2 * x + 2 * k) 3 = 3 ∧
      ((ScanPlan.empty.scanner : Scanner .empty (MulOpposite (Function.End Nat))).inclusive
        PUnit.unit).map (fun q : MulOpposite (Function.End Nat) => MulOpposite.unop q 3) = [3] :=
  ⟨affine_fold_zero (fun _ => 2) (fun k => 2 * k) 3, empty_observation 3⟩

example : (((List.range' 1 0).foldl (fun x k => 2 * x + 2 * k) 3 : Nat) : ℚ) = 3 :=
  (doubling_normalized_sum 3 2 0).trans (by norm_num)

example : (((List.range' 1 0).foldl (fun x k => k * x + 2 * k) 3 : Nat) : ℚ) = 3 :=
  (factorial_normalized_sum 3 2 0).trans (by norm_num)

example : (((List.range' 1 0).foldl (fun x k => 2 * x + 2 * k) 3 : Nat) : ℚ) ≠ 3 * 2 := by
  norm_num [List.range'_zero, List.foldl_nil]

theorem chronological_pair :
    ((ScanPlan.pair.scanner : Scanner ScanPlan.pair.shape (MulOpposite (Function.End Nat))).inclusive
      (MulOpposite.op (fun state : Nat => 2 * state + 2),
       MulOpposite.op (fun state : Nat => 2 * state + 4))).map
        (fun q : MulOpposite (Function.End Nat) => MulOpposite.unop q 3) = [3, 8, 20] := by
  exact (inclusive_apply (α := Nat) (s := ScanPlan.pair.shape)
    (ScanPlan.pair.scanner : Scanner ScanPlan.pair.shape (MulOpposite (Function.End Nat)))
    (MulOpposite.op (show Function.End Nat from fun state : Nat => 2 * state + 2),
      MulOpposite.op (show Function.End Nat from fun state : Nat => 2 * state + 4))
    3).trans (by rfl)

theorem reversed_pair :
    ((ScanPlan.pair.scanner : Scanner ScanPlan.pair.shape (MulOpposite (Function.End Nat))).inclusive
      (MulOpposite.op (fun state : Nat => 2 * state + 4),
       MulOpposite.op (fun state : Nat => 2 * state + 2))).map
        (fun q : MulOpposite (Function.End Nat) => MulOpposite.unop q 3) = [3, 10, 22] := by
  exact (inclusive_apply (α := Nat) (s := ScanPlan.pair.shape)
    (ScanPlan.pair.scanner : Scanner ScanPlan.pair.shape (MulOpposite (Function.End Nat)))
    (MulOpposite.op (show Function.End Nat from fun state : Nat => 2 * state + 4),
      MulOpposite.op (show Function.End Nat from fun state : Nat => 2 * state + 2))
    3).trans (by rfl)

/-- A zero weight resets every prior base to the toll, including in actual scanning. -/
theorem zero_weight_reset (b : Nat) :
    ((ScanPlan.leaf.scanner : Scanner .leaf (MulOpposite (Function.End Nat))).inclusive
      (MulOpposite.op (fun state : Nat => 0 * state + 7))).map
        (fun q : MulOpposite (Function.End Nat) => MulOpposite.unop q b) = [b, 7] := by
  refine (inclusive_apply (α := Nat) (s := .leaf)
    (ScanPlan.leaf.scanner : Scanner .leaf (MulOpposite (Function.End Nat)))
    (MulOpposite.op (show Function.End Nat from fun state : Nat => 0 * state + 7)) b).trans ?_
  change [b, 0 * b + 7] = [b, 7]
  simp

example :
    ((ScanPlan.leaf.scanner : Scanner .leaf (MulOpposite (Function.End Nat))).inclusive
      (MulOpposite.op (fun state : Nat => 0 * state + 7))).map
        (fun q : MulOpposite (Function.End Nat) => MulOpposite.unop q 123) = [123, 7] := zero_weight_reset 123


/-! ## Arbitrary-toll source cases with distinct complete traces -/

/-- Source G203 uses the actual four-entry composed scanner. Its full trace
retains the independent base and the positive linear toll at each transition. -/
theorem general_doubling_source_case :
    (List.range' 1 4).foldl (fun x k => 2 * x + k) 1 = 42 ∧
      ((ScanPlan.comp .pair .pair).scanner.inclusive
        ((ScanPlan.comp .pair .pair).shape.map
          (fun k : Nat => MulOpposite.op
            (show Function.End Nat from fun state => 2 * state + k))
          (((1, 2), (3, 4)) : (Nat × Nat) × (Nat × Nat)))).map
        (fun q : MulOpposite (Function.End Nat) => MulOpposite.unop q 1) = [1, 3, 8, 19, 42] := by
  constructor
  · exact (affine_fold_succ (fun _ => 2) id 1 3).trans (by rfl)
  · refine (inclusive_affine_prefixes (ScanPlan.comp .pair .pair).scanner
      ((ScanPlan.comp .pair .pair).shape.map
        (fun k : Nat => MulOpposite.op
          (show Function.End Nat from fun state => 2 * state + k))
        (((1, 2), (3, 4)) : (Nat × Nat) × (Nat × Nat)))
      (fun _ => 2) id 1 4 (by rfl)).trans ?_
    rfl

/-- Source G204 uses natural division in its toll. Although its endpoint also
is 42, the full actual scan distinguishes it from the doubling recurrence. -/
theorem half_toll_factorial_source_case :
    (List.range' 1 4).foldl (fun x k => k * x + k / 2) 1 = 42 ∧
      ((ScanPlan.comp .pair .pair).scanner.inclusive
        ((ScanPlan.comp .pair .pair).shape.map
          (fun k : Nat => MulOpposite.op
            (show Function.End Nat from fun state => k * state + k / 2))
          (((1, 2), (3, 4)) : (Nat × Nat) × (Nat × Nat)))).map
        (fun q : MulOpposite (Function.End Nat) => MulOpposite.unop q 1) = [1, 1, 3, 10, 42] := by
  constructor
  · exact (affine_fold_succ id (fun k => k / 2) 1 3).trans (by rfl)
  · refine (inclusive_affine_prefixes (ScanPlan.comp .pair .pair).scanner
      ((ScanPlan.comp .pair .pair).shape.map
        (fun k : Nat => MulOpposite.op
          (show Function.End Nat from fun state => k * state + k / 2))
        (((1, 2), (3, 4)) : (Nat × Nat) × (Nat × Nat)))
      id (fun k => k / 2) 1 4 (by rfl)).trans ?_
    rfl

end Examples.RecurrenceScans

namespace Examples.RecurrenceScans

open Applications.Parallel SquareKit.FiniteRecurrences

/-- Source R214: the actual four-transition scanner retains all corrected-model prefixes. -/
theorem two_param_source_case :
    (List.range' 1 4).foldl (fun x _ => x + 3 * 5) (2 * 5 * 5) = 110 ∧
      ((ScanPlan.comp .pair .pair).scanner.inclusive
        ((ScanPlan.comp .pair .pair).shape.map
          (fun _ : Nat => MulOpposite.op
            (show Function.End Nat from fun state => 1 * state + 3 * 5))
          (((1, 2), (3, 4)) : (Nat × Nat) × (Nat × Nat)))).map
        (fun q : MulOpposite (Function.End Nat) => MulOpposite.unop q (2 * 5 * 5)) =
          [50, 65, 80, 95, 110] := by
  constructor
  · exact (constant_toll_exact (2 * 5 * 5) (3 * 5) 4).trans (by decide)
  · refine (inclusive_affine_prefixes (ScanPlan.comp .pair .pair).scanner
      ((ScanPlan.comp .pair .pair).shape.map
        (fun _ : Nat => MulOpposite.op
          (show Function.End Nat from fun state => 1 * state + 3 * 5))
        (((1, 2), (3, 4)) : (Nat × Nat) × (Nat × Nat)))
      (fun _ => 1) (fun _ => 3 * 5) (2 * 5 * 5) 4 (by rfl)).trans ?_
    rfl

/-- Source G205: natural division and the actual three-entry scan give the half-toll trace. -/
theorem two_run_half_toll_source_case :
    (List.range' 1 3).foldl (fun x _ => x + 4 / 2) (4 * 4) = 22 ∧
      ((ScanPlan.prod .pair .leaf).scanner.inclusive
        ((ScanPlan.prod .pair .leaf).shape.map
          (fun _ : Nat => MulOpposite.op
            (show Function.End Nat from fun state => 1 * state + 4 / 2))
          (((1, 2), 3) : (Nat × Nat) × Nat))).map
        (fun q : MulOpposite (Function.End Nat) => MulOpposite.unop q (4 * 4)) =
          [16, 18, 20, 22] := by
  constructor
  · exact (constant_toll_exact (4 * 4) (4 / 2) 3).trans (by decide)
  · refine (inclusive_affine_prefixes (ScanPlan.prod .pair .leaf).scanner
      ((ScanPlan.prod .pair .leaf).shape.map
        (fun _ : Nat => MulOpposite.op
          (show Function.End Nat from fun state => 1 * state + 4 / 2))
        (((1, 2), 3) : (Nat × Nat) × Nat))
      (fun _ => 1) (fun _ => 4 / 2) (4 * 4) 3 (by rfl)).trans ?_
    rfl

/-- Source D164: the printed m-toll uses its positive index and a distinct complete trace. -/
theorem printed_m_toll_source_case :
    (List.range' 1 4).foldl (fun x k => x + 1 * k) 1 = 11 ∧
      ((ScanPlan.comp .pair .pair).scanner.inclusive
        ((ScanPlan.comp .pair .pair).shape.map
          (fun k : Nat => MulOpposite.op
            (show Function.End Nat from fun state => 1 * state + k))
          (((1, 2), (3, 4)) : (Nat × Nat) × (Nat × Nat)))).map
        (fun q : MulOpposite (Function.End Nat) => MulOpposite.unop q 1) = [1, 2, 4, 7, 11] := by
  constructor
  · exact (additive_exact 1 1 4).trans (by norm_num [SquareKit.FiniteSums.triangle_exact])
  · refine (inclusive_affine_prefixes (ScanPlan.comp .pair .pair).scanner
      ((ScanPlan.comp .pair .pair).shape.map
        (fun k : Nat => MulOpposite.op
          (show Function.End Nat from fun state => 1 * state + k))
        (((1, 2), (3, 4)) : (Nat × Nat) × (Nat × Nat)))
      (fun _ => 1) id 1 4 (by rfl)).trans ?_
    rfl

end Examples.RecurrenceScans

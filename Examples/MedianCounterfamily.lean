import Applications.Selection.MedianCounterfamily

/-!
Connected cases for the infinite Exercise 3.7 counterfamily. The first input
already has five greater entries among six; successive inputs add ten entries
and seven greater entries. These finite cases consume the universal family
proof, whose all-index assertion is retained separately.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.MedianCounterfamily
open Applications.Selection Applications.Selection.MedianCounterfamily
open Applications.Sequences.Chunks

theorem first_input : family 0 = [1, 1, 1, 1, 1, 0] := by decide

theorem first_chops : chop 5 (family 0) = [[1, 1, 1, 1, 1], [0]] := chop_family 0

theorem first_medians : chunkMedians 5 (family 0) = [1, 0] := chunkMedians_family 0

theorem first_pivot : medianOfMedians 5 (family 0) = some 0 := family_pivot 0

theorem first_counts : (family 0).length = 6 ∧
    (family 0).countP (fun x => decide (0 < x)) = 5 :=
  ⟨family_length 0, family_count_gt 0⟩

theorem first_strict_percentage :
    7 * (family 0).length < 10 * (family 0).countP (fun x => decide (0 < x)) :=
  family_strict_seventy 0

theorem second_chops : chop 5 (family 1) =
    [[0, 0, 0, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1], [0]] := chop_family 1

theorem second_medians : chunkMedians 5 (family 1) = [0, 1, 1, 0] := chunkMedians_family 1

theorem second_pivot : medianOfMedians 5 (family 1) = some 0 := family_pivot 1

theorem second_counts : (family 1).length = 16 ∧
    (family 1).countP (fun x => decide (0 < x)) = 12 :=
  ⟨family_length 1, family_count_gt 1⟩

theorem second_has_duplicates : ¬(family 1).Nodup := by decide

theorem third_counts : (family 2).length = 26 ∧
    (family 2).countP (fun x => decide (0 < x)) = 19 :=
  ⟨family_length 2, family_count_gt 2⟩

theorem growth_at_every_index (i : Nat) :
    (family i).length < (family (i + 1)).length :=
  family_lengths_strictMono (by omega)

theorem positive_denominator_at_every_index (i : Nat) : (family i).length ≠ 0 :=
  Nat.ne_of_gt (family_positive i)

/-- Strict failure of the exact seventy-percent ratio bound does not contradict the
book's proved additive allowance, which still bounds this entire family. -/
theorem book_ceiling_still_bounds (i : Nat) :
    (family i).countP (fun x => decide (0 < x)) ≤ (7 * (family i).length + 30) ⌈/⌉ 10 :=
  (medianOfMedians_five_count_bounds (family i) 0 (family_pivot i)).2

theorem dropping_allowance_fails (i : Nat) :
    ¬10 * (family i).countP (fun x => decide (0 < x)) ≤ 7 * (family i).length :=
  Nat.not_le_of_gt (family_strict_seventy i)

theorem actual_pivot_comparison (i p : Nat)
    (hp : medianOfMedians 5 (family i) = some p) :
    0 < (family i).length ∧
      7 * (family i).length < 10 * (family i).countP (fun x => decide (p < x)) :=
  ⟨family_positive i, family_pivot_strict_seventy i p hp⟩

end Examples.MedianCounterfamily

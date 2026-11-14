import Applications.Resources.HalvingTrace

/-! Positive scalar traces and explicitly aligned charges, not algorithm runtimes.
The independently calculated expectations are recorded before implementation.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.HalvingTrace
open Resources.HalvingTrace

theorem power_two_trace : Halves 8 [8, 4, 2, 1] := by
  exact Halves.step (m := 4) (by decide)
    (Halves.step (m := 2) (by decide)
      (Halves.step (m := 1) (by decide) (Halves.stop (by decide))))

theorem power_two_values :
    ([8, 4, 2, 1] : List Nat).sum = 15 ∧
      ([8, 4, 2, 1] : List Nat).length - 1 = 3 := by decide

theorem power_two_bounds :
    8 ≤ ([8, 4, 2, 1] : List Nat).sum ∧
      ([8, 4, 2, 1] : List Nat).sum ≤ 16 ∧
      ([8, 4, 2, 1] : List Nat).length - 1 ≤ Nat.log 2 8 ∧
      ([8, 4, 2, 1] : List Nat).length - 1 ≤ Nat.clog 2 8 :=
  ⟨initial_le_sum power_two_trace, sum_le_twice power_two_trace,
    edges_le_log power_two_trace, edges_le_clog power_two_trace⟩

theorem odd_trace : Halves 7 [7, 3, 1] := by
  exact step_of_le_half (m := 3) (by decide)
    (step_of_le_half (m := 1) (by decide) (Halves.stop (by decide)))

theorem odd_values :
    ([7, 3, 1] : List Nat).sum = 11 ∧
      ([7, 3, 1] : List Nat).length - 1 = 2 ∧
      Nat.log 2 7 = 2 ∧ Nat.clog 2 7 = 3 := by decide

theorem odd_bounds :
    ([7, 3, 1] : List Nat).sum ≤ 14 ∧
      ([7, 3, 1] : List Nat).length - 1 ≤ Nat.log 2 7 ∧
      ([7, 3, 1] : List Nat).length - 1 ≤ Nat.clog 2 7 :=
  ⟨sum_le_twice odd_trace, edges_le_log odd_trace, edges_le_clog odd_trace⟩

theorem singleton_trace : Halves 1 [1] := Halves.stop (by decide)

theorem singleton_values :
    ([1] : List Nat).sum = 1 ∧ ([1] : List Nat).length = 1 ∧
      ([1] : List Nat).length - 1 = 0 := by decide

theorem singleton_forced (sizes : List Nat) (trace : Halves 1 sizes) :
    sizes = [1] := singleton_at_one trace

theorem early_stop : Halves 8 [8] := Halves.stop (by decide)

theorem early_stop_bounds :
    ([8] : List Nat).sum ≤ 16 ∧ ([8] : List Nat).length - 1 ≤ Nat.clog 2 8 :=
  ⟨sum_le_twice early_stop, edges_le_clog early_stop⟩

theorem zero_rejected (sizes : List Nat) : ¬ Halves 0 sizes := zero_impossible sizes

theorem insufficient_halving : ¬ Halves 3 [3, 2] := by
  intro trace
  have impossible := next_halved trace
  omega

theorem fixed_tariff_alignment :
    List.Forall₂ (fun size charge : Nat => charge ≤ 3 * size + 2)
      [8, 4, 2, 1] [26, 14, 8, 5] :=
  .cons (by decide) (.cons (by decide) (.cons (by decide) (.cons (by decide) .nil)))

theorem fixed_tariff_value : ([26, 14, 8, 5] : List Nat).sum = 53 := by decide

theorem fixed_tariff_bounds :
    8 ≤ ([26, 14, 8, 5] : List Nat).sum ∧
      ([26, 14, 8, 5] : List Nat).sum ≤ 80 := by
  constructor
  · apply initial_le_charges power_two_trace
    exact .cons (by decide) (.cons (by decide) (.cons (by decide) (.cons (by decide) .nil)))
  · exact tariff_sum_le power_two_trace 3 2 fixed_tariff_alignment

end Examples.HalvingTrace

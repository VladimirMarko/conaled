import Applications.Numerals.Floating
import Applications.Numerals.Decimal
import Applications.Floating.Observation

/-!
# Source floating numeral values and counterexamples

These are small, explicit cases of the pinned logical operations. Bit equality,
finite rational observation and exact decimal meaning remain distinct. None of
these cases is an arbitrary-input rounding bound or a native-execution theorem.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.FloatingNumerals

open Numerals.Floating
open _root_.Floating.Observation

theorem fraction64_empty_bits : (fraction64 []).toBits = 0 := by decide +kernel
theorem fraction32_empty_bits : (fraction32 []).toBits = 0 := by decide +kernel

theorem fraction64_eighth :
    (fraction64 [1, 2, 5]).toBits = 0x3fc0000000000000 ∧
    decode64 (fraction64 [1, 2, 5]) = some (1 / 8 : ℚ) := by
  decide +kernel

theorem fraction32_eighth :
    (fraction32 [1, 2, 5]).toBits = 0x3e000000 ∧
    decode32 (fraction32 [1, 2, 5]) = some (1 / 8 : ℚ) := by
  decide +kernel

theorem fraction64_tenth :
    (fraction64 [1]).toBits = 0x3fb999999999999a ∧
    decode64 (fraction64 [1]) = some (3602879701896397 / 36028797018963968 : ℚ) ∧
    decode64 (fraction64 [1]) ≠ some (1 / 10 : ℚ) := by
  decide +kernel

theorem fraction32_tenth :
    (fraction32 [1]).toBits = 0x3dcccccd ∧
    decode32 (fraction32 [1]) = some (13421773 / 134217728 : ℚ) ∧
    decode32 (fraction32 [1]) ≠ some (1 / 10 : ℚ) := by
  decide +kernel

theorem fraction64_printed_example :
    (fraction64 [1, 4, 8, 4, 9, 3]).toBits = 0x3fc301d19157abb9 ∧
    decode64 (fraction64 [1, 4, 8, 4, 9, 3]) =
      some (5350024155737017 / 36028797018963968 : ℚ) := by
  decide +kernel

theorem fraction32_printed_example :
    (fraction32 [1, 4, 8, 4, 9, 3]).toBits = 0x3e180e8d ∧
    decode32 (fraction32 [1, 4, 8, 4, 9, 3]) =
      some (9965197 / 67108864 : ℚ) := by
  decide +kernel

theorem fraction64_nines_round_to_one :
    fraction64 (List.replicate 17 9) = (1 : Float) ∧
    decode64 (fraction64 (List.replicate 17 9)) = some 1 := by
  decide +kernel

theorem fraction32_nines_round_to_one :
    fraction32 (List.replicate 8 9) = (1 : Float32) ∧
    decode32 (fraction32 (List.replicate 8 9)) = some 1 := by
  decide +kernel

theorem fraction32_underflow :
    fraction32 (List.replicate 45 0 ++ [1]) = (0 : Float32) ∧
    decode32 (fraction32 (List.replicate 45 0 ++ [1])) = some 0 := by
  decide +kernel

theorem fraction64_tenth_error :
    decode64 (fraction64 [1]) =
      some (Numerals.Decimal.fractionFold [1] + 1 / 180143985094819840) := by
  decide +kernel

theorem fraction32_tenth_error :
    decode32 (fraction32 [1]) =
      some (Numerals.Decimal.fractionFold [1] + 1 / 671088640) := by
  decide +kernel

theorem fraction64_printed_error :
    decode64 (fraction64 [1, 4, 8, 4, 9, 3]) =
      some (Numerals.Decimal.fractionFold [1, 4, 8, 4, 9, 3] +
        7809 / 562949953421312000000) := by
  decide +kernel

theorem fraction32_printed_error :
    decode32 (fraction32 [1, 4, 8, 4, 9, 3]) =
      some (Numerals.Decimal.fractionFold [1, 4, 8, 4, 9, 3] +
        7157 / 1048576000000) := by
  decide +kernel

theorem fraction64_differs_from_decimal :
    (fraction64 [0, 7]).toBits = 0x3fb1eb851eb851eb ∧
    (0.07 : Float).toBits = 0x3fb1eb851eb851ec ∧
    fraction64 [0, 7] ≠ (0.07 : Float) := by
  decide +kernel

theorem fraction32_differs_from_decimal :
    (fraction32 [0, 3]).toBits = 0x3cf5c290 ∧
    (0.03 : Float32).toBits = 0x3cf5c28f ∧
    fraction32 [0, 3] ≠ (0.03 : Float32) := by
  decide +kernel

theorem fraction64_strict_bound_counterexample :
    Numerals.Decimal.Digits (List.replicate 17 9) ∧
    Numerals.Decimal.fractionFold (List.replicate 17 9) < 1 ∧
    decode64 (fraction64 (List.replicate 17 9)) = some 1 := by
  have hd : Numerals.Decimal.Digits (List.replicate 17 9) := by
    intro d h
    simp only [List.mem_replicate] at h
    omega
  exact ⟨hd, (Numerals.Decimal.fractionFold_bounds _ hd).2, fraction64_nines_round_to_one.2⟩

theorem fraction32_strict_bound_counterexample :
    Numerals.Decimal.Digits (List.replicate 8 9) ∧
    Numerals.Decimal.fractionFold (List.replicate 8 9) < 1 ∧
    decode32 (fraction32 (List.replicate 8 9)) = some 1 := by
  have hd : Numerals.Decimal.Digits (List.replicate 8 9) := by
    intro d h
    simp only [List.mem_replicate] at h
    omega
  exact ⟨hd, (Numerals.Decimal.fractionFold_bounds _ hd).2, fraction32_nines_round_to_one.2⟩

theorem fraction32_underflow_positive_exact :
    0 < Numerals.Decimal.fractionFold (List.replicate 45 0 ++ [1]) ∧
    decode32 (fraction32 (List.replicate 45 0 ++ [1])) = some 0 := by
  decide +kernel

theorem fraction64_out_of_domain_overflow :
    (fraction64 [2 ^ 1024]).isInf = true ∧ decode64 (fraction64 [2 ^ 1024]) = none := by
  decide +kernel

theorem fraction32_out_of_domain_overflow :
    (fraction32 [2 ^ 128]).isInf = true ∧ decode32 (fraction32 [2 ^ 128]) = none := by
  decide +kernel

end Examples.FloatingNumerals

import Applications.Numerals.FloatingObserver

/-!
# Bounded certificates for the ten individual decimal digits

These finite kernel checks specialize the proved observer and source bound test.
They do not discharge a local rounding hypothesis for arbitrary proper-digit lists.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Numerals.Floating

open _root_.Floating.Observation

theorem certify64_single_digit (d : Nat) (hd : d < 10) :
    certify64 [d] (1 / (2 : ℚ) ^ 54) = true := by
  have checked : ∀ i : Fin 10, certify64 [i.val] (1 / (2 : ℚ) ^ 54) = true := by
    decide +kernel
  exact checked ⟨d, hd⟩

theorem certify32_single_digit (d : Nat) (hd : d < 10) :
    certify32 [d] (1 / (2 : ℚ) ^ 25) = true := by
  have checked : ∀ i : Fin 10, certify32 [i.val] (1 / (2 : ℚ) ^ 25) = true := by
    decide +kernel
  exact checked ⟨d, hd⟩

theorem fraction64_single_digit_error (d : Nat) (hd : d < 10) :
    ∃ value, decode64 (fraction64 [d]) = some value ∧
      |value - Decimal.fractionRat [d]| ≤ 1 / (2 : ℚ) ^ 54 :=
  certify64_sound [d] _ (certify64_single_digit d hd)

theorem fraction32_single_digit_error (d : Nat) (hd : d < 10) :
    ∃ value, decode32 (fraction32 [d]) = some value ∧
      |value - Decimal.fractionRat [d]| ≤ 1 / (2 : ℚ) ^ 25 :=
  certify32_sound [d] _ (certify32_single_digit d hd)

end Numerals.Floating

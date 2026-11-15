import Applications.Floating.ArithmeticCore

/-!
# Numerical preservation of actual floating packing

Canonical finite representations roundtrip through the pinned core's pack and
unpack operations when no overflow occurs. Normal, subnormal and signed-zero
cases retain the actual implicit bit, truncation and exponent bias.

Finite results of unpacking bit patterns are canonical. Arbitrary finite
constructors need not be canonical. Bit-pattern validity alone does not assert
preservation of the represented rational.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Floating.Packing

open Float.Model Float.Model.UnpackedFloat
open Floating.Observation (dyadicValue dyadicValue_eq)

def Canonical (format : Format) : UnpackedFloat → Prop
  | .zero _ => True
  | .finite _ m e _ => e = format.targetExponent (totalExponent m e)
  | _ => False

def NoOverflow (format : Format) : UnpackedFloat → Prop
  | .zero _ => True
  | .finite _ _ e _ =>
      e + (format.exponentBias : Int) + (format.mantissaBitsWithoutImplicit : Int) + 1 <
        ((2 ^ format.exponentBits : Nat) : Int)
  | _ => False

@[simp] theorem unpackSign_packComponents (format : Format) (sign : Sign)
    (exponent : BitVec format.exponentBits) (mantissa : BitVec format.mantissaBitsWithoutImplicit) :
    unpackSign (packComponents format sign exponent mantissa) = sign.toBitVec := by
  ext i hi
  have zero : i = 0 := by omega
  subst i
  simp [unpackSign, packComponents, BitVec.getLsbD_append, BitVec.getLsbD_eq_getElem,
    BitVec.getElem_append,
    show ¬ format.mantissaBitsWithoutImplicit + format.exponentBits <
      format.mantissaBitsWithoutImplicit by omega]

@[simp] theorem sign_roundtrip (sign : Sign) : Sign.ofBitVec sign.toBitVec = sign := by
  cases sign <;> simp [Sign.ofBitVec, Sign.toBitVec]

theorem canonical_finite_bounds (format : Format) (sign : Sign) (m : Nat) (e : Int)
    (positive : 0 < m) (h : Canonical format (.finite sign m e positive)) :
    format.minExponent ≤ e ∧ m.log2 + 1 ≤ format.mantissaBits ∧
      (m.log2 + 1 < format.mantissaBits → e = format.minExponent) := by
  simp only [Canonical, Format.targetExponent, totalExponent] at h
  have left := Int.le_max_left ((m.log2 : Int) + 1 + e - (format.mantissaBits : Int))
    format.minExponent
  have right := Int.le_max_right ((m.log2 : Int) + 1 + e - (format.mantissaBits : Int))
    format.minExponent
  constructor
  · omega
  constructor
  · omega
  intro smaller
  by_cases atFloor : ((m.log2 : Int) + 1 + e - (format.mantissaBits : Int)) ≤ format.minExponent
  · rw [Int.max_eq_right atFloor] at h
    exact h
  · rw [Int.max_eq_left (by omega)] at h
    omega

theorem minExponent_bias (format : Format) :
    format.minExponent + (format.exponentBias : Int) +
      (format.mantissaBitsWithoutImplicit : Int) = 1 := by
  have positive : 1 ≤ (2 : Nat) ^ (format.exponentBits - 1) := Nat.one_le_two_pow
  change (3 : Int) - ((2 ^ (format.exponentBits - 1) : Nat) : Int) -
    (1 + (format.mantissaBitsWithoutImplicit : Int)) +
    ((2 ^ (format.exponentBits - 1) - 1 : Nat) : Int) +
    (format.mantissaBitsWithoutImplicit : Int) = 1
  omega

theorem unpack_zero_pack (format : Format) (sign : Sign) :
    UnpackedFloat.unpack format (pack format (.zero sign)) = .zero sign := by
  have exponentNonzero : format.exponentBits ≠ 0 := by have := format.he; omega
  simp [UnpackedFloat.pack, packedZero, UnpackedFloat.unpack, exponentNonzero]

theorem unpack_finite_pack (format : Format) (sign : Sign) (m : Nat) (e : Int) (positive : 0 < m)
    (canonical : Canonical format (.finite sign m e positive))
    (noOverflow : NoOverflow format (.finite sign m e positive)) :
    UnpackedFloat.unpack format (pack format (.finite sign m e positive)) =
      .finite sign m e positive := by
  have bounds := canonical_finite_bounds format sign m e positive canonical
  have floorBias := minExponent_bias format
  let biased : Nat :=
    (e + (format.exponentBias : Int) + (format.mantissaBitsWithoutImplicit : Int)).toNat
  have biasedValue : (biased : Int) =
      e + (format.exponentBias : Int) + (format.mantissaBitsWithoutImplicit : Int) := by
    dsimp [biased]
    omega
  have biasedPositive : 0 < biased := by omega
  have biasedFits : biased + 1 < 2 ^ format.exponentBits := by
    change e + (format.exponentBias : Int) + (format.mantissaBitsWithoutImplicit : Int) + 1 <
      ((2 ^ format.exponentBits : Nat) : Int) at noOverflow
    omega
  have biasedBound : biased < 2 ^ format.exponentBits := by omega
  have biasedNat : (BitVec.ofNat format.exponentBits biased).toNat = biased := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt biasedBound]
  have biasedNonzero : BitVec.ofNat format.exponentBits biased ≠ 0#_ := by
    intro h
    have := congrArg BitVec.toNat h
    simp [biasedNat] at this
    omega
  have biasedNotReserved : BitVec.ofNat format.exponentBits biased ≠ -1#_ := by
    intro same
    have h := congrArg BitVec.toNat same
    rw [biasedNat, BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes] at h
    omega
  have zeroNotReserved : (0#format.exponentBits) ≠ -1#format.exponentBits := by
    intro same
    have h := congrArg BitVec.toNat same
    change 0 = (-1#format.exponentBits).toNat at h
    rw [BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes] at h
    have p := Nat.one_lt_two_pow (show format.exponentBits ≠ 0 by have := format.he; omega)
    omega
  by_cases normal : m.log2 + 1 = format.mantissaBits
  · have logarithm : m.log2 = format.mantissaBitsWithoutImplicit := by
      simp only [Format.mantissaBits] at normal
      omega
    have mantissaLower : 2 ^ format.mantissaBitsWithoutImplicit ≤ m := by
      have h := Nat.log2_self_le (Nat.ne_of_gt positive)
      rw [logarithm] at h
      exact h
    have mantissaUpper :
        m < 2 ^ format.mantissaBitsWithoutImplicit + 2 ^ format.mantissaBitsWithoutImplicit := by
      have h := Nat.lt_log2_self (n := m)
      rw [logarithm, Nat.two_pow_succ] at h
      exact h
    have remainder : 2 ^ format.mantissaBitsWithoutImplicit +
        m % 2 ^ format.mantissaBitsWithoutImplicit = m := by
      have p : 0 < 2 ^ format.mantissaBitsWithoutImplicit := Nat.two_pow_pos _
      have lower : 1 ≤ m / 2 ^ format.mantissaBitsWithoutImplicit :=
        (Nat.le_div_iff_mul_le p).mpr (by simpa using mantissaLower)
      have upper : m / 2 ^ format.mantissaBitsWithoutImplicit < 2 :=
        (Nat.div_lt_iff_lt_mul p).mpr (by simpa [Nat.two_mul] using mantissaUpper)
      have division : m / 2 ^ format.mantissaBitsWithoutImplicit = 1 := by omega
      have h := Nat.mod_add_div m (2 ^ format.mantissaBitsWithoutImplicit)
      rw [division, Nat.mul_one] at h
      omega
    simp only [UnpackedFloat.pack]
    change UnpackedFloat.unpack format (if 2 ^ format.exponentBits ≤ biased + 1 then _
      else if m.log2 + 1 = format.mantissaBits then _ else _) = _
    rw [ite_eq_right (by omega), ite_eq_left normal]
    change UnpackedFloat.unpack format
      (packComponents format sign (BitVec.ofNat _ biased) (BitVec.ofNat _ m)) = _
    simp only [UnpackedFloat.unpack, unpackMantissa_packComponents, unpackExponent_packComponents,
      unpackSign_packComponents, sign_roundtrip, biasedNotReserved, biasedNonzero, biasedNat,
      ↓reduceIte]
    have exponent : (biased : Int) -
        ((format.exponentBias : Int) + (format.mantissaBitsWithoutImplicit : Int)) = e := by omega
    have mantissa : (1#1 ++ BitVec.ofNat format.mantissaBitsWithoutImplicit m).toNat = m := by
      rw [BitVec.toNat_append]
      simp only [BitVec.toNat_ofNat]
      rw [← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt m (Nat.two_pow_pos _)),
        Nat.shiftLeft_eq, Nat.one_mul]
      exact remainder
    simp only [exponent, mantissa]
  · have logarithm : m.log2 < format.mantissaBitsWithoutImplicit := by
      simp only [Format.mantissaBits] at bounds normal
      omega
    have mantissaBound : m < 2 ^ format.mantissaBitsWithoutImplicit :=
      (Nat.log2_lt (Nat.ne_of_gt positive)).mp logarithm
    have atFloor : e = format.minExponent := bounds.2.2 (by omega)
    have mantissaNat : (BitVec.ofNat format.mantissaBitsWithoutImplicit m).toNat = m := by
      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt mantissaBound]
    have mantissaNonzero : BitVec.ofNat format.mantissaBitsWithoutImplicit m ≠ 0#_ := by
      intro h
      have := congrArg BitVec.toNat h
      simp [mantissaNat] at this
      omega
    simp only [UnpackedFloat.pack]
    change UnpackedFloat.unpack format (if 2 ^ format.exponentBits ≤ biased + 1 then _
      else if m.log2 + 1 = format.mantissaBits then _ else _) = _
    rw [ite_eq_right (by omega), ite_eq_right normal]
    simp only [UnpackedFloat.unpack, unpackMantissa_packComponents, unpackExponent_packComponents,
      unpackSign_packComponents, sign_roundtrip, mantissaNonzero, ↓reduceIte,
      BitVec.toNat_zero, mantissaNat]
    have exponent : (0 : Int) -
        ((format.exponentBias : Int) + (format.mantissaBitsWithoutImplicit : Int)) + 1 = e := by omega
    simp only [zeroNotReserved, ite_false, ↓reduceDIte, Int.natCast_zero, exponent]

theorem unpack_pack (format : Format) (value : UnpackedFloat) (canonical : Canonical format value)
    (noOverflow : NoOverflow format value) :
    UnpackedFloat.unpack format (pack format value) = value := by
  cases value with
  | infinity sign => exact False.elim canonical
  | notANumber => exact False.elim canonical
  | zero sign => exact unpack_zero_pack format sign
  | finite sign m e positive => exact unpack_finite_pack format sign m e positive canonical noOverflow

theorem pack_numeric (format : Format) (value : UnpackedFloat) (canonical : Canonical format value)
    (noOverflow : NoOverflow format value) :
    Observation.unpack (UnpackedFloat.unpack format (pack format value)) = Observation.unpack value := by
  rw [unpack_pack format value canonical noOverflow]

theorem leading_one_value (width : Nat) (value : BitVec width) :
    (1#1 ++ value).toNat = 2 ^ width + value.toNat := by
  rw [BitVec.toNat_append]
  change 1 <<< width ||| value.toNat = _
  rw [← Nat.shiftLeft_add_eq_or_of_lt value.isLt, Nat.shiftLeft_eq, Nat.one_mul]

theorem leading_one_log2 (width : Nat) (value : BitVec width) :
    (1#1 ++ value).toNat.log2 = width := by
  rw [leading_one_value]
  have positive := Nat.two_pow_pos width
  have bound := value.isLt
  apply (Nat.log2_eq_iff (by omega)).mpr
  constructor
  · omega
  · rw [Nat.two_pow_succ]
    omega

/-- Finiteness here belongs to the result of actual bit-pattern unpacking. -/
theorem unpack_canonical (format : Format) (bits : BitVec format.numBits)
    (finite : (UnpackedFloat.unpack format bits).isFinite = true) :
    Canonical format (UnpackedFloat.unpack format bits) := by
  unfold UnpackedFloat.unpack at finite ⊢
  dsimp only at finite ⊢
  split
  · split <;> simp_all [UnpackedFloat.isFinite]
  · split
    · split
      · trivial
      · rename_i notReserved exponentZero mantissaNonzero
        simp only [Canonical, Format.targetExponent, totalExponent]
        have mantissaPositive : (unpackMantissa bits).toNat ≠ 0 := by
          intro zero
          apply mantissaNonzero
          apply BitVec.eq_of_toNat_eq
          simpa using zero
        have logarithm : (unpackMantissa bits).toNat.log2 < format.mantissaBitsWithoutImplicit :=
          (Nat.log2_lt mantissaPositive).mpr (unpackMantissa bits).isLt
        have bias := minExponent_bias format
        have exponent : (unpackExponent bits).toNat = 0 := by rw [exponentZero]; rfl
        rw [exponent]
        have floor : (0 : Int) -
            ((format.exponentBias : Int) + (format.mantissaBitsWithoutImplicit : Int)) + 1 =
              format.minExponent := by omega
        simp only [Int.natCast_zero, floor]
        apply Eq.symm
        apply Int.max_eq_right
        simp only [Format.mantissaBits]
        omega
    · simp only [Canonical, Format.targetExponent, totalExponent, leading_one_log2]
      have bias := minExponent_bias format
      have exponentPositive : 0 < (unpackExponent bits).toNat := by
        rename_i notReserved exponentNonzero
        by_cases zero : (unpackExponent bits).toNat = 0
        · have same : unpackExponent bits = 0#_ := BitVec.eq_of_toNat_eq (by simpa using zero)
          exact False.elim (exponentNonzero same)
        · omega
      simp only [Format.mantissaBits]
      have exponent : (format.mantissaBitsWithoutImplicit : Int) + 1 +
          ((unpackExponent bits).toNat -
            ((format.exponentBias : Int) + (format.mantissaBitsWithoutImplicit : Int))) -
          (1 + (format.mantissaBitsWithoutImplicit : Int)) =
            (unpackExponent bits).toNat -
              ((format.exponentBias : Int) + (format.mantissaBitsWithoutImplicit : Int)) := by omega
      simp only [Int.natCast_add, Int.natCast_one]
      rw [exponent]
      exact (Int.max_eq_left (by omega)).symm

theorem exponent_le_three (m : Nat) (e : Int) (positive : 0 < m)
    (upper : dyadicValue m e ≤ 10) : e ≤ 3 := by
  cases e with
  | negSucc n => omega
  | ofNat n =>
    have castBound : ((m * 2 ^ n : Nat) : Rat) ≤ ((10 : Nat) : Rat) := by
      simpa only [Observation.dyadicValue_ofNat, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using upper
    have bound : m * 2 ^ n ≤ 10 := Rat.natCast_le_natCast.mp castBound
    have atLeastOne : 1 ≤ m := positive
    have power := Nat.mul_le_mul_right (2 ^ n) atLeastOne
    simp only [Nat.one_mul] at power
    have powerBound : 2 ^ n ≤ 10 := Nat.le_trans power bound
    have logarithm := (Nat.le_log2 (n := 10) (by decide)).mpr powerBound
    change n ≤ 3 at logarithm
    change (n : Int) ≤ 3
    omega

theorem noOverflow64_of_decode (value : UnpackedFloat) (q : Rat)
    (decoded : Observation.unpack value = some q) (nonnegative : 0 ≤ q) (upper : q ≤ 10) :
    NoOverflow Format.binary64 value := by
  rcases ArithmeticCore.nonnegative_unpacked_cases value q decoded nonnegative with
    ⟨sign, rfl, rfl⟩ | ⟨m, e, positive, rfl, rfl⟩
  · trivial
  · have bound := exponent_le_three m e positive upper
    change e + 1023 + 52 + 1 < 2048
    omega

theorem noOverflow32_of_decode (value : UnpackedFloat) (q : Rat)
    (decoded : Observation.unpack value = some q) (nonnegative : 0 ≤ q) (upper : q ≤ 10) :
    NoOverflow Format.binary32 value := by
  rcases ArithmeticCore.nonnegative_unpacked_cases value q decoded nonnegative with
    ⟨sign, rfl, rfl⟩ | ⟨m, e, positive, rfl, rfl⟩
  · trivial
  · have bound := exponent_le_three m e positive upper
    change e + 127 + 23 + 1 < 256
    omega

theorem canonical_of_decode (format : Format) (bits : BitVec format.numBits) (q : Rat)
    (decoded : Observation.unpack (UnpackedFloat.unpack format bits) = some q) :
    Canonical format (UnpackedFloat.unpack format bits) := by
  apply unpack_canonical
  rw [← Observation.unpack_isSome, decoded]
  rfl

theorem model64_unpack_canonical (value : Float.Model) (q : Rat)
    (decoded : Observation.unpack value.unpack = some q) : Canonical Format.binary64 value.unpack :=
  canonical_of_decode Format.binary64 value.toBits.toBitVec q decoded

theorem model32_unpack_canonical (value : Float32.Model) (q : Rat)
    (decoded : Observation.unpack value.unpack = some q) : Canonical Format.binary32 value.unpack :=
  canonical_of_decode Format.binary32 value.toBits.toBitVec q decoded

theorem model64_pack_numeric (value : UnpackedFloat) (q : Rat)
    (canonical : Canonical Format.binary64 value) (decoded : Observation.unpack value = some q)
    (nonnegative : 0 ≤ q) (upper : q ≤ 10) :
    Observation.unpack (Float.Model.pack value).unpack = some q := by
  change Observation.unpack (UnpackedFloat.unpack Format.binary64 (pack Format.binary64 value)) = _
  rw [pack_numeric _ _ canonical (noOverflow64_of_decode value q decoded nonnegative upper), decoded]

theorem model32_pack_numeric (value : UnpackedFloat) (q : Rat)
    (canonical : Canonical Format.binary32 value) (decoded : Observation.unpack value = some q)
    (nonnegative : 0 ≤ q) (upper : q ≤ 10) :
    Observation.unpack (Float32.Model.pack value).unpack = some q := by
  change Observation.unpack (UnpackedFloat.unpack Format.binary32 (pack Format.binary32 value)) = _
  rw [pack_numeric _ _ canonical (noOverflow32_of_decode value q decoded nonnegative upper), decoded]

end Floating.Packing

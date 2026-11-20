import Mathlib.Data.Num.Lemmas
import Mathlib.Data.PNat.Equiv

/-!
# Positive binary keys and their natural observations

The numeric observation sends `one`, `bit0 p`, and `bit1 p` to one,
twice the child value, and twice the child value plus one. The shifted
natural key sends positive one to zero. The two conventions are kept
separate, with explicit inverse and injectivity laws.

This integrates the useful staged positive-key mathematics into its maintained
owner. Comparisons use numeric order. These value correspondences make no
claim about the work of key construction or numeric conversion.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Numerals.PositiveKeys

universe u

/-- The unshifted positive numeric value. -/
abbrev numeric (p : PosNum) : Nat := (p : Nat)

theorem numeric_one : numeric PosNum.one = 1 :=
  PosNum.cast_one'

theorem numeric_bit0 (p : PosNum) : numeric (PosNum.bit0 p) = 0 + 2 * numeric p := by
  simpa only [numeric, Nat.zero_add, two_mul] using (PosNum.cast_bit0 (α := Nat) p)

theorem numeric_bit1 (p : PosNum) : numeric (PosNum.bit1 p) = 1 + 2 * numeric p := by
  calc
    numeric (PosNum.bit1 p) = (numeric p + numeric p) + 1 := PosNum.cast_bit1 p
    _ = 1 + 2 * numeric p := by rw [two_mul, Nat.add_comm 1]

theorem numeric_pos (p : PosNum) : 0 < numeric p := PosNum.to_nat_pos p

theorem one_le_numeric (p : PosNum) : 1 ≤ numeric p := numeric_pos p

theorem numeric_injective : Function.Injective numeric := by
  intro p q h
  exact PosNum.to_nat_inj.mp h

/-- Retain the numeric value and its positivity witness. -/
def toPNat (p : PosNum) : ℕ+ := ⟨numeric p, numeric_pos p⟩

@[simp] theorem toPNat_value (p : PosNum) : (toPNat p : Nat) = numeric p := rfl

theorem toPNat_injective : Function.Injective toPNat := by
  intro p q h
  apply numeric_injective
  exact congrArg (fun n : ℕ+ => (n : Nat)) h

/-- Encode natural key n as the existing positive binary value n + 1. -/
abbrev encode : Nat → PosNum := PosNum.ofNatSucc

/-- Observe a positive binary value as a key starting at zero. -/
def decode (p : PosNum) : Nat := (toPNat p).natPred

theorem decode_eq_numeric_pred (p : PosNum) : decode p = (numeric p).pred := rfl

theorem numeric_eq_decode_add_one (p : PosNum) : numeric p = decode p + 1 := by
  have h := congrArg (fun q : ℕ+ => (q : Nat)) (PNat.succPNat_natPred (toPNat p))
  exact h.symm

theorem numeric_encode (n : Nat) : numeric (encode n) = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change numeric (PosNum.succ (encode n)) = (n + 1) + 1
    calc
      numeric (PosNum.succ (encode n)) = numeric (encode n) + 1 := PosNum.succ_to_nat _
      _ = (n + 1) + 1 := congrArg (fun k : Nat => k + 1) ih

theorem toPNat_encode (n : Nat) : toPNat (encode n) = n.succPNat := by
  apply PNat.coe_injective
  change numeric (encode n) = n + 1
  exact numeric_encode n

@[simp] theorem decode_encode (n : Nat) : decode (encode n) = n := by
  calc
    (toPNat (encode n)).natPred = n.succPNat.natPred :=
      congrArg PNat.natPred (toPNat_encode n)
    _ = n := Nat.natPred_succPNat n

@[simp] theorem encode_decode (p : PosNum) : encode (decode p) = p := by
  apply toPNat_injective
  calc
    toPNat (encode (decode p)) = (decode p).succPNat := toPNat_encode _
    _ = toPNat p := PNat.succPNat_natPred (toPNat p)

theorem encode_injective : Function.Injective encode := by
  intro m n h
  simpa only [decode_encode] using congrArg decode h

theorem decode_injective : Function.Injective decode := by
  intro p q h
  simpa only [encode_decode] using congrArg encode h

/-- The inverse PNat adapter uses the already established shifted encoding. -/
def ofPNat (p : ℕ+) : PosNum := encode p.natPred

@[simp] theorem toPNat_ofPNat (p : ℕ+) : toPNat (ofPNat p) = p :=
  (toPNat_encode p.natPred).trans (PNat.succPNat_natPred p)

@[simp] theorem ofPNat_toPNat (p : PosNum) : ofPNat (toPNat p) = p := encode_decode p

def binaryPNatEquiv : PosNum ≃ ℕ+ where
  toFun := toPNat
  invFun := ofPNat
  left_inv := ofPNat_toPNat
  right_inv := toPNat_ofPNat

def binaryNatEquiv : PosNum ≃ Nat where
  toFun := decode
  invFun := encode
  left_inv := encode_decode
  right_inv := decode_encode

/-- PNat's existing equivalence makes the same shifted observation. -/
theorem pnat_equiv_observation (p : PosNum) : Equiv.pnatEquivNat (toPNat p) = decode p := rfl

/-- The equal comparator branch identifies the binary keys themselves. -/
theorem cmp_eq_iff (p q : PosNum) : PosNum.cmp p q = .eq ↔ p = q := PosNum.cmp_eq p q

theorem cmp_lt_iff (p q : PosNum) : PosNum.cmp p q = .lt ↔ numeric p < numeric q :=
  (PosNum.lt_to_nat.trans PosNum.lt_iff_cmp).symm

theorem cmp_gt_iff (p q : PosNum) : PosNum.cmp p q = .gt ↔ numeric q < numeric p := by
  constructor
  · intro h
    have correct := PosNum.cmp_to_nat p q
    simpa only [h] using correct
  · intro h
    by_contra hne
    have hpq : p ≤ q := PosNum.le_iff_cmp.mpr hne
    have hnumeric : numeric p ≤ numeric q := PosNum.le_to_nat.mpr hpq
    exact (Nat.not_lt_of_ge hnumeric) h

theorem cmp_encoded_eq_iff (m n : Nat) : PosNum.cmp (encode m) (encode n) = .eq ↔ m = n := by
  rw [cmp_eq_iff]
  exact encode_injective.eq_iff

theorem cmp_encoded_lt_iff (m n : Nat) : PosNum.cmp (encode m) (encode n) = .lt ↔ m < n := by
  rw [cmp_lt_iff, numeric_encode, numeric_encode]
  omega

theorem cmp_encoded_gt_iff (m n : Nat) : PosNum.cmp (encode m) (encode n) = .gt ↔ n < m := by
  rw [cmp_gt_iff, numeric_encode, numeric_encode]
  omega

/-- Any Nat-indexed observation is recovered after binary encoding and decoding. -/
theorem observation_roundtrip {α : Type u} (observe : Nat → α) :
    (observe ∘ decode) ∘ encode = observe := by
  funext n
  change observe (decode (encode n)) = observe n
  rw [decode_encode]


/-- Every positive-indexed observation is recovered by the inverse key transport. -/
theorem positive_observation_roundtrip {α : Type u} (observe : PosNum → α) :
    (observe ∘ encode) ∘ decode = observe := by
  funext p
  change observe (encode (decode p)) = observe p
  rw [encode_decode]

@[simp] theorem encode_zero : encode 0 = PosNum.one := rfl

@[simp] theorem decode_one : decode PosNum.one = 0 := by
  simpa only [encode_zero] using decode_encode 0

@[simp] theorem encode_one : encode 1 = PosNum.bit0 PosNum.one := rfl

end Numerals.PositiveKeys

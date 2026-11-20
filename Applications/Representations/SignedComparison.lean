import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Order.Basic
import Init.Data.BitVec.Lemmas
import Init.Data.SInt.Lemmas

/-!
# Signed comparisons and their mathematical interpretation

The operation data are an ordinary carrier, decoder and two Boolean comparisons.
Reflection suffices for proof-carrying decisions; injectivity is needed only to
recover a linear order on the original carrier. The order below explicitly keeps
the supplied decision procedures. No global signed order on `BitVec` is installed.

Finite signed words and `Int64` have different explicit ranges. Conversion and
addition preserve mathematical integers only under their stated range or overflow
conditions. These proofs make no claim about compiler correctness or running time.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Representations.SignedComparison

universe u
variable {W : Type u}

abbrev strictOrder (decode : W → Int) : LT W := ⟨fun a b => decode a < decode b⟩
abbrev nonstrictOrder (decode : W → Int) : LE W := ⟨fun a b => decode a ≤ decode b⟩

def strictDecision (decode : W → Int) (ltb : W → W → Bool)
    (hlt : ∀ a b, ltb a b = true ↔ decode a < decode b) (a b : W) :
    Decidable (decode a < decode b) := decidable_of_bool (ltb a b) (hlt a b)

def nonstrictDecision (decode : W → Int) (leb : W → W → Bool)
    (hle : ∀ a b, leb a b = true ↔ decode a ≤ decode b) (a b : W) :
    Decidable (decode a ≤ decode b) := decidable_of_bool (leb a b) (hle a b)

theorem decide_strictDecision (decode : W → Int) (ltb : W → W → Bool)
    (hlt : ∀ a b, ltb a b = true ↔ decode a < decode b) (a b : W) :
    @decide (decode a < decode b) (strictDecision decode ltb hlt a b) = ltb a b := by
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using (hlt a b).symm

theorem decide_nonstrictDecision (decode : W → Int) (leb : W → W → Bool)
    (hle : ∀ a b, leb a b = true ↔ decode a ≤ decode b) (a b : W) :
    @decide (decode a ≤ decode b) (nonstrictDecision decode leb hle a b) = leb a b := by
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using (hle a b).symm

theorem strict_false_iff (decode : W → Int) (ltb : W → W → Bool)
    (hlt : ∀ a b, ltb a b = true ↔ decode a < decode b) (a b : W) :
    ltb a b = false ↔ decode b ≤ decode a := by
  rw [Bool.eq_false_iff, ne_eq, hlt, not_lt]

theorem nonstrict_false_iff (decode : W → Int) (leb : W → W → Bool)
    (hle : ∀ a b, leb a b = true ↔ decode a ≤ decode b) (a b : W) :
    leb a b = false ↔ decode b < decode a := by
  rw [Bool.eq_false_iff, ne_eq, hle, not_le]

theorem strict_self (decode : W → Int) (ltb : W → W → Bool)
    (hlt : ∀ a b, ltb a b = true ↔ decode a < decode b) (a : W) :
    ltb a a = false := (strict_false_iff decode ltb hlt a a).mpr le_rfl

/-- Only the proof-bearing partial order is lifted. Decisions, and the default
`min`, `max`, equality and `compare` implementations, use the supplied Booleans. -/
@[instance_reducible]
def linearOrder (decode : W → Int) (ltb leb : W → W → Bool)
    (hinj : Function.Injective decode)
    (hlt : ∀ a b, ltb a b = true ↔ decode a < decode b)
    (hle : ∀ a b, leb a b = true ↔ decode a ≤ decode b) : LinearOrder W where
  toPartialOrder := (LinearOrder.lift' decode hinj).toPartialOrder
  le_total a b := le_total (decode a) (decode b)
  toDecidableLT := strictDecision decode ltb hlt
  toDecidableLE := nonstrictDecision decode leb hle

/-- The explicit decision argument matters: a newly inferred decision for the
unfolded relation may instead compare decoded integers. -/
theorem linearOrder_decide_lt (decode : W → Int) (ltb leb : W → W → Bool)
    (hinj : Function.Injective decode)
    (hlt : ∀ a b, ltb a b = true ↔ decode a < decode b)
    (hle : ∀ a b, leb a b = true ↔ decode a ≤ decode b) (a b : W) :
    @decide (decode a < decode b)
      ((linearOrder decode ltb leb hinj hlt hle).toDecidableLT a b) = ltb a b :=
  decide_strictDecision decode ltb hlt a b

theorem linearOrder_decide_le (decode : W → Int) (ltb leb : W → W → Bool)
    (hinj : Function.Injective decode)
    (hlt : ∀ a b, ltb a b = true ↔ decode a < decode b)
    (hle : ∀ a b, leb a b = true ↔ decode a ≤ decode b) (a b : W) :
    @decide (decode a ≤ decode b)
      ((linearOrder decode ltb leb hinj hlt hle).toDecidableLE a b) = leb a b :=
  decide_nonstrictDecision decode leb hle a b

def nonstrictOfStrict (ltb : W → W → Bool) (a b : W) : Bool := !(ltb b a)

theorem nonstrictOfStrict_correct (decode : W → Int) (ltb : W → W → Bool)
    (hlt : ∀ a b, ltb a b = true ↔ decode a < decode b) (a b : W) :
    nonstrictOfStrict ltb a b = true ↔ decode a ≤ decode b := by
  change (!(ltb b a)) = true ↔ decode a ≤ decode b
  simpa using strict_false_iff decode ltb hlt b a

@[instance_reducible]
def linearOrderOfStrict (decode : W → Int) (ltb : W → W → Bool)
    (hinj : Function.Injective decode)
    (hlt : ∀ a b, ltb a b = true ↔ decode a < decode b) : LinearOrder W :=
  linearOrder decode ltb (nonstrictOfStrict ltb) hinj hlt
    (nonstrictOfStrict_correct decode ltb hlt)

theorem linearOrderOfStrict_decide_lt (decode : W → Int) (ltb : W → W → Bool)
    (hinj : Function.Injective decode)
    (hlt : ∀ a b, ltb a b = true ↔ decode a < decode b) (a b : W) :
    @decide (decode a < decode b)
      ((linearOrderOfStrict decode ltb hinj hlt).toDecidableLT a b) = ltb a b :=
  decide_strictDecision decode ltb hlt a b

def intLtb (a b : Int) : Bool := decide (a < b)
def intLeb (a b : Int) : Bool := decide (a ≤ b)
def intEqb (a b : Int) : Bool := decide (a = b)
def intGtb (a b : Int) : Bool := intLtb b a
def intGeb (a b : Int) : Bool := intLeb b a

theorem int_decode_injective : Function.Injective (id : Int → Int) := fun _ _ h => h
theorem intLtb_true_iff (a b : Int) : intLtb a b = true ↔ a < b := by simp [intLtb]
theorem intLtb_false_iff (a b : Int) : intLtb a b = false ↔ b ≤ a := by simp [intLtb]
theorem intLeb_true_iff (a b : Int) : intLeb a b = true ↔ a ≤ b := by simp [intLeb]
theorem intLeb_false_iff (a b : Int) : intLeb a b = false ↔ b < a := by simp [intLeb]
theorem intEqb_true_iff (a b : Int) : intEqb a b = true ↔ a = b := by simp [intEqb]
theorem intEqb_false_iff (a b : Int) : intEqb a b = false ↔ a ≠ b := by simp [intEqb]
theorem intGtb_true_iff (a b : Int) : intGtb a b = true ↔ b < a := by simp [intGtb, intLtb]
theorem intGtb_false_iff (a b : Int) : intGtb a b = false ↔ a ≤ b := by simp [intGtb, intLtb]
theorem intGeb_true_iff (a b : Int) : intGeb a b = true ↔ b ≤ a := by simp [intGeb, intLeb]
theorem intGeb_false_iff (a b : Int) : intGeb a b = false ↔ a < b := by simp [intGeb, intLeb]

abbrev wordLtb {w : Nat} (a b : BitVec w) : Bool := a.slt b
abbrev wordLeb {w : Nat} (a b : BitVec w) : Bool := a.sle b

theorem word_decode_injective (w : Nat) : Function.Injective (@BitVec.toInt w) :=
  fun _ _ h => BitVec.eq_of_toInt_eq h

theorem wordLtb_true_iff {w : Nat} (a b : BitVec w) :
    wordLtb a b = true ↔ a.toInt < b.toInt := BitVec.slt_iff_toInt_lt

theorem wordLtb_false_iff {w : Nat} (a b : BitVec w) :
    wordLtb a b = false ↔ b.toInt ≤ a.toInt :=
  strict_false_iff BitVec.toInt wordLtb wordLtb_true_iff a b

theorem wordLeb_true_iff {w : Nat} (a b : BitVec w) :
    wordLeb a b = true ↔ a.toInt ≤ b.toInt := BitVec.sle_iff_toInt_le

theorem wordLeb_false_iff {w : Nat} (a b : BitVec w) :
    wordLeb a b = false ↔ b.toInt < a.toInt :=
  nonstrict_false_iff BitVec.toInt wordLeb wordLeb_true_iff a b

theorem word_toInt_range {w : Nat} (x : BitVec w) :
    -(2 : Int) ^ (w - 1) ≤ x.toInt ∧ x.toInt < (2 : Int) ^ (w - 1) :=
  ⟨BitVec.le_toInt x, BitVec.toInt_lt⟩

theorem word_ofInt_toInt {w : Nat} (hw : 0 < w) (n : Int)
    (lower : -(2 : Int) ^ (w - 1) ≤ n) (upper : n < (2 : Int) ^ (w - 1)) :
    (BitVec.ofInt w n).toInt = n := BitVec.toInt_ofInt_eq_self hw lower upper

theorem word_representable_iff {w : Nat} (hw : 0 < w) (n : Int) :
    (∃ x : BitVec w, x.toInt = n) ↔
      -(2 : Int) ^ (w - 1) ≤ n ∧ n < (2 : Int) ^ (w - 1) := by
  constructor
  · rintro ⟨x, rfl⟩
    exact word_toInt_range x
  · intro h
    exact ⟨BitVec.ofInt w n, word_ofInt_toInt hw n h.1 h.2⟩

theorem word_ofNat_toInt {w : Nat} (hw : 0 < w) (n : Nat) (upper : n < 2 ^ (w - 1)) :
    (BitVec.ofNat w n).toInt = (n : Int) := by
  have hp : 0 ≤ (2 : Int) ^ (w - 1) := Int.pow_nonneg (by decide)
  have hu : (n : Int) < (2 : Int) ^ (w - 1) := by exact_mod_cast upper
  exact word_ofInt_toInt hw n (by omega) hu

theorem word63_toInt_range (x : BitVec 63) :
    -(2 : Int) ^ 62 ≤ x.toInt ∧ x.toInt < (2 : Int) ^ 62 := word_toInt_range x

/-- Width zero has precisely one decoded value; the positive-width image
characterization is deliberately not applied here. -/
theorem word_zero_width_image (n : Int) : (∃ x : BitVec 0, x.toInt = n) ↔ n = 0 := by
  constructor
  · rintro ⟨x, rfl⟩
    exact BitVec.toInt_zero_length x
  · rintro rfl
    exact ⟨0, BitVec.toInt_zero⟩

theorem word_zero_width_comparisons (a b : BitVec 0) :
    wordLtb a b = false ∧ wordLeb a b = true := by
  simp only [wordLtb_false_iff, wordLeb_true_iff, BitVec.toInt_zero_length, le_refl, and_self]

theorem word_add_modular {w : Nat} (a b : BitVec w) :
    (a + b).toInt = (a.toInt + b.toInt).bmod (2 ^ w) := BitVec.toInt_add a b

theorem word_add_no_overflow {w : Nat} (a b : BitVec w) (safe : ¬ a.saddOverflow b) :
    (a + b).toInt = a.toInt + b.toInt := BitVec.toInt_add_of_not_saddOverflow safe

theorem four_bit_overflow :
    (BitVec.ofInt 4 7 + BitVec.ofInt 4 1).toInt = -8 ∧
      (BitVec.ofInt 4 7).toInt + (BitVec.ofInt 4 1).toInt = 8 := by
  constructor
  · rw [word_add_modular]
    decide
  · decide

theorem four_bit_no_overflow : (BitVec.ofInt 4 2 + BitVec.ofInt 4 1).toInt = 3 := by
  exact (word_add_no_overflow _ _ (by decide)).trans (by decide)

theorem signed_unsigned_disagree :
    wordLtb (BitVec.ofInt 4 (-1)) (BitVec.ofInt 4 0) = true ∧
      decide (BitVec.ofInt 4 (-1) < BitVec.ofInt 4 0) = false := by decide

/-- Pin the existing native signed decisions explicitly. Their runtime overrides
are part of the ordinary Lean compiler/runtime trust boundary. -/
def int64Ltb (a b : Int64) : Bool := @decide (a < b) (Int64.decLt a b)
def int64Leb (a b : Int64) : Bool := @decide (a ≤ b) (Int64.decLe a b)

theorem int64_decode_injective : Function.Injective Int64.toInt := fun _ _ h => Int64.toInt.inj h

theorem int64Ltb_true_iff (a b : Int64) : int64Ltb a b = true ↔ a.toInt < b.toInt := by
  simpa only [int64Ltb, decide_eq_true_eq] using (Int64.lt_iff_toInt_lt (x := a) (y := b))

theorem int64Ltb_false_iff (a b : Int64) : int64Ltb a b = false ↔ b.toInt ≤ a.toInt :=
  strict_false_iff Int64.toInt int64Ltb int64Ltb_true_iff a b

theorem int64Leb_true_iff (a b : Int64) : int64Leb a b = true ↔ a.toInt ≤ b.toInt := by
  simpa only [int64Leb, decide_eq_true_eq] using (Int64.le_iff_toInt_le (x := a) (y := b))

theorem int64Leb_false_iff (a b : Int64) : int64Leb a b = false ↔ b.toInt < a.toInt :=
  nonstrict_false_iff Int64.toInt int64Leb int64Leb_true_iff a b

theorem int64_toInt_range (x : Int64) : -(2 : Int) ^ 63 ≤ x.toInt ∧ x.toInt < (2 : Int) ^ 63 :=
  ⟨Int64.le_toInt x, Int64.toInt_lt x⟩

theorem int64_ofInt_toInt (n : Int) (lower : -(2 : Int) ^ 63 ≤ n) (upper : n < (2 : Int) ^ 63) :
    (Int64.ofInt n).toInt = n := Int64.toInt_ofInt_of_le lower upper

theorem int64_representable_iff (n : Int) :
    (∃ x : Int64, x.toInt = n) ↔ -(2 : Int) ^ 63 ≤ n ∧ n < (2 : Int) ^ 63 := by
  constructor
  · rintro ⟨x, rfl⟩
    exact int64_toInt_range x
  · intro h
    exact ⟨Int64.ofInt n, int64_ofInt_toInt n h.1 h.2⟩

theorem int64_ofNat_toInt (n : Nat) (upper : n < 2 ^ 63) : (Int64.ofInt n).toInt = (n : Int) := by
  apply int64_ofInt_toInt
  · omega
  · exact_mod_cast upper

end Representations.SignedComparison

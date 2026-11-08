import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Tactic

/-! Finite-word representation of depth/index ordering. The offset must make
signed depths nonnegative; the radix must exceed every admitted index. -/
namespace Sequences.LCA.WordKey

def pack (stride height index : Nat) : Nat := height * stride + index

theorem pack_lt_iff (hi : i < stride) (hj : j < stride) :
    pack stride a i < pack stride b j ↔ a < b ∨ a = b ∧ i < j := by
  unfold pack
  constructor
  · intro h
    by_cases hab : a < b
    · exact Or.inl hab
    · have hba : b ≤ a := by omega
      by_cases he : a = b
      · exact Or.inr ⟨he, by subst b; omega⟩
      · have hm := Nat.mul_le_mul_right stride (show b + 1 ≤ a by omega)
        simp only [Nat.add_mul, Nat.one_mul] at hm
        omega
  · rintro (h | ⟨rfl,h⟩)
    · have hm := Nat.mul_le_mul_right stride (show a + 1 ≤ b by omega)
      simp only [Nat.add_mul, Nat.one_mul] at hm
      omega
    · omega

theorem pack_le_iff (hi : i < stride) (hj : j < stride) :
    pack stride a i ≤ pack stride b j ↔ a < b ∨ a = b ∧ i ≤ j := by
  have h := pack_lt_iff (a := b) (b := a) hj hi
  omega

theorem pack_lt_capacity (hi : i < stride) (ha : a < heights) :
    pack stride a i < heights * stride := by
  have hm := Nat.mul_le_mul_right stride (show a + 1 ≤ heights by omega)
  simp only [Nat.add_mul, Nat.one_mul] at hm
  unfold pack
  omega

@[simp] theorem pack_mod (hi : i < stride) : pack stride a i % stride = i := by
  simp [pack, Nat.add_mod, Nat.mod_eq_of_lt hi]

@[simp] theorem pack_div (hi : i < stride) : pack stride a i / stride = a := by
  have hs : 0 < stride := by omega
  simp [pack, Nat.add_div, Nat.div_eq_of_lt hi, hs, Nat.mod_lt _ hs]

def encode (offset : Int) (stride : Nat) (depth : Int) (index : Nat) : Nat :=
  pack stride (depth + offset).toNat index

theorem encode_le_iff (ha : 0 ≤ a + offset) (hb : 0 ≤ b + offset)
    (hi : i < stride) (hj : j < stride) :
    encode offset stride a i ≤ encode offset stride b j ↔
      (toLex (a,i) : Int ×ₗ Nat) ≤ toLex (b,j) := by
  rw [Prod.Lex.le_iff]
  change pack stride (a+offset).toNat i ≤ pack stride (b+offset).toNat j ↔
    a < b ∨ a = b ∧ i ≤ j
  rw [pack_le_iff hi hj]
  omega

theorem encode_lt_capacity (hi : i < stride) (ha : (depth + offset).toNat < heights) :
    encode offset stride depth i < heights * stride := pack_lt_capacity hi ha

theorem encode_fits_word (hi : i < stride) (ha : (depth + offset).toNat < heights)
    (hc : heights * stride ≤ 2 ^ width) :
    encode offset stride depth i < 2 ^ width :=
  (encode_lt_capacity hi ha).trans_le hc

/-- Every bounded radix rectangle has a finite word-width witness. -/
theorem capacity_has_width (heights stride : Nat) :
    ∃ width, heights * stride ≤ 2 ^ width := by
  refine ⟨heights * stride, ?_⟩
  exact Nat.le_of_lt (Nat.lt_two_pow_self)

example : encode 2 4 (-1) 3 < encode 2 4 0 0 := by decide
example : encode 2 4 (-1) 1 ≤ encode 2 4 (-1) 3 :=
  (encode_le_iff (by decide) (by decide) (by decide) (by decide)).2 (by decide)
example : encode 2 4 (-1) 3 < 2 ^ 4 :=
  encode_fits_word (heights := 4) (by decide) (by decide) (by decide)
/-- Without the index bound, radix representations need not be unique. -/
example : pack 2 0 3 = pack 2 1 1 := rfl
/-- A negative shifted depth is truncated, so its order cannot be reflected. -/
example : encode 0 4 (-2) 0 = encode 0 4 (-1) 0 := rfl

end Sequences.LCA.WordKey

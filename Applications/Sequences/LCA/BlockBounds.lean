import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-! Integer parameter bounds for the shared-table construction. These are
arithmetic lemmas, not a resource theorem for an implementation. -/
namespace Sequences.LCA

def blockSize (n : Nat) : Nat := max 1 (Nat.log 2 n / 2)

theorem blockSize_pos (n : Nat) : 0 < blockSize n := by
  simp only [blockSize]
  omega

theorem square_le_two_pow (b : Nat) : b * b ≤ 2 ^ (b + 1) := by
  by_cases hb : b < 3
  · interval_cases b <;> decide
  · have hb : 3 ≤ b := by omega
    induction b, hb using Nat.le_induction with
    | base => decide
    | succ b hb ih =>
      calc
        (b + 1) * (b + 1) ≤ 2 * (b * b) := by nlinarith
        _ ≤ 2 * 2 ^ (b + 1) := Nat.mul_le_mul_left 2 (ih (by omega))
        _ = 2 ^ (b + 1 + 1) := by rw [pow_succ]; omega

theorem quadratic_class_bound (b : Nat) :
    b * b * 2 ^ b ≤ 2 * 2 ^ (2 * b) := by
  calc
    b * b * 2 ^ b ≤ 2 ^ (b + 1) * 2 ^ b :=
      Nat.mul_le_mul_right _ (square_le_two_pow b)
    _ = 2 * 2 ^ (2 * b) := by
      rw [← pow_add]
      have he : b + 1 + b = 2 * b + 1 := by omega
      rw [he, pow_succ]
      omega

theorem blockSize_large (hn : 4 ≤ n) :
    blockSize n = Nat.log 2 n / 2 := by
  have hl : 2 ≤ Nat.log 2 n := by
    by_contra h
    have hh := (Nat.log_lt_iff_lt_pow (by decide : 1 < 2) (by omega : n ≠ 0)).mp
      (show Nat.log 2 n < 2 by omega)
    norm_num at hh
    omega
  simp only [blockSize]
  omega

theorem blockSize_exponent (hn : 4 ≤ n) : 2 * blockSize n ≤ Nat.log 2 n := by
  rw [blockSize_large hn]
  omega

theorem class_entries_linear (hn : 4 ≤ n) :
    blockSize n * blockSize n * 2 ^ blockSize n ≤ 2 * n := by
  calc
    _ ≤ 2 * 2 ^ (2 * blockSize n) := quadratic_class_bound _
    _ ≤ 2 * 2 ^ Nat.log 2 n := Nat.mul_le_mul_left 2
      (Nat.pow_le_pow_right (by decide) (blockSize_exponent hn))
    _ ≤ 2 * n := Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (by omega))

example : blockSize 1 = 1 := by decide
example : blockSize 3 = 1 := by decide
example : blockSize 16 = 2 := by decide
example : blockSize 256 = 4 := by decide

theorem blockSize_le (hn : 0 < n) : blockSize n ≤ n := by
  have := Nat.log_le_self 2 n
  simp only [blockSize]
  omega

def blockCount (n : Nat) : Nat := (n + blockSize n - 1) / blockSize n

theorem blockCount_le (hn : 0 < n) : blockCount n ≤ n := by
  have hb := blockSize_pos n
  unfold blockCount
  apply Nat.div_le_of_le_mul
  have hf : (blockSize n - 1) + 1 = blockSize n := by omega
  have hp : blockSize n - 1 ≤ n * (blockSize n - 1) := by
    simpa using Nat.mul_le_mul_right (blockSize n - 1) hn
  have he : blockSize n * n = n + n * (blockSize n - 1) := by
    conv_lhs => rw [← hf]
    ring
  omega

theorem blockCount_mul_le (n : Nat) :
    blockCount n * blockSize n ≤ n + blockSize n := by
  have := Nat.div_mul_le_self (n + blockSize n - 1) (blockSize n)
  unfold blockCount
  omega

/-- Even allocating every macro row at full width costs only linear space.
The actual sparse construction may omit entries that overrun the last block. -/
theorem macro_entries_linear (hn : 0 < n) :
    blockCount n * (Nat.log 2 (blockCount n) + 1) ≤ 8 * n := by
  have hb := blockSize_pos n
  have hbn := blockSize_le hn
  have hm := blockCount_mul_le n
  have hl := Nat.log_mono_right (b := 2) (blockCount_le hn)
  have hx : Nat.log 2 n + 1 ≤ 4 * blockSize n := by
    simp only [blockSize]
    omega
  calc
    _ ≤ blockCount n * (4 * blockSize n) := Nat.mul_le_mul_left _ (by omega)
    _ = 4 * (blockCount n * blockSize n) := by ring
    _ ≤ 4 * (n + blockSize n) := Nat.mul_le_mul_left 4 hm
    _ ≤ 8 * n := by omega

end Sequences.LCA

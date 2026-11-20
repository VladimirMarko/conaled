import Applications.Trees.AVL.Basic
import Applications.Trees.Shape
import Mathlib.Data.Nat.Init
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.NormNum.Basic

/-! Direct elementary height bounds and almost-completeness for AVL shapes.
The height-indexed two-step proof does not use a Fibonacci size theorem.
All sizes below count external leaves; the empty tree has one such leaf.
Actual height and a stored height are connected only under cache validity.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees.AVL
universe u
variable {α : Type u}

/-- The two-step motive is generalized over every balanced tree of the given height. -/
private theorem two_pow_ceil_half_le_numLeaves_at_height (n : Nat) :
    ∀ t : BinaryTree α, Balanced t → t.height = n →
      2 ^ ((n + 1) / 2) ≤ t.numLeaves := by
  induction n using Nat.twoStepInduction with
  | zero =>
      intro t _ height
      cases t with
      | nil => exact Nat.le_refl 1
      | node a l r =>
          simp only [BinaryTree.height] at height
          omega
  | one =>
      intro t _ height
      cases t with
      | nil =>
          simp only [BinaryTree.height] at height
          omega
      | node a l r =>
          change 2 ≤ l.numLeaves + r.numLeaves
          have hl := BinaryTree.numLeaves_pos l
          have hr := BinaryTree.numLeaves_pos r
          omega
  | more n ihn ihn1 =>
      intro t balanced height
      cases t with
      | nil =>
          simp only [BinaryTree.height] at height
          omega
      | node a l r =>
          rcases (balanced_node a l r).mp balanced with ⟨hl, hr, hlr, hrl⟩
          have hm : max l.height r.height = n + 1 := by
            change max l.height r.height + 1 = n + 2 at height
            omega
          have hlh : l.height = n ∨ l.height = n + 1 := by omega
          have hrh : r.height = n ∨ r.height = n + 1 := by omega
          have childBound (s : BinaryTree α) (hs : Balanced s)
              (hh : s.height = n ∨ s.height = n + 1) :
              2 ^ ((n + 1) / 2) ≤ s.numLeaves := by
            rcases hh with hh | hh
            · exact ihn s hs hh
            · exact (Nat.pow_le_pow_right (by decide : 0 < 2)
                (Nat.div_le_div_right (Nat.le_succ (n + 1)))).trans (ihn1 s hs hh)
          have lowerLeft := childBound l hl hlh
          have lowerRight := childBound r hr hrh
          have exponent : (n + 2 + 1) / 2 = (n + 1) / 2 + 1 := by
            omega
          change 2 ^ ((n + 2 + 1) / 2) ≤ l.numLeaves + r.numLeaves
          rw [exponent, Nat.pow_add_one']
          omega

/-- The direct ceil-half bound supplies the rounding strength needed by the logarithm. -/
theorem two_pow_ceil_half_height_le_numLeaves (t : BinaryTree α) (h : Balanced t) :
    2 ^ ((t.height + 1) / 2) ≤ t.numLeaves :=
  two_pow_ceil_half_le_numLeaves_at_height t.height t h rfl

/-- The literal floor-half estimate follows from the stronger direct bound. -/
theorem two_pow_half_height_le_numLeaves (t : BinaryTree α) (h : Balanced t) :
    2 ^ (t.height / 2) ≤ t.numLeaves :=
  (Nat.pow_le_pow_right (by decide : 0 < 2)
    (Nat.div_le_div_right (Nat.le_succ t.height))).trans
    (two_pow_ceil_half_height_le_numLeaves t h)

/-- The exact zero-additive logarithmic consequence, including the empty tree. -/
theorem height_le_two_mul_logb_numLeaves (t : BinaryTree α) (h : Balanced t) :
    (t.height : ℝ) ≤ 2 * Real.logb 2 (t.numLeaves : ℝ) := by
  let k : Nat := (t.height + 1) / 2
  have powerNat : 2 ^ k ≤ t.numLeaves := two_pow_ceil_half_height_le_numLeaves t h
  have powerReal : (2 : ℝ) ^ k ≤ (t.numLeaves : ℝ) := by
    have castPower : ((2 ^ k : Nat) : ℝ) ≤ (t.numLeaves : ℝ) :=
      Nat.cast_le.mpr powerNat
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using castPower
  have base : (1 : ℝ) < 2 := by norm_num
  have leaves : (0 : ℝ) < (t.numLeaves : ℝ) :=
    Nat.cast_pos.mpr (BinaryTree.numLeaves_pos t)
  have logBound := (Real.logb_le_logb base
    (pow_pos (by norm_num : (0 : ℝ) < 2) k) leaves).mpr powerReal
  rw [Real.logb_pow, Real.logb_self_eq_one base, mul_one] at logBound
  have rounding : t.height ≤ 2 * k := by
    have remainder := Nat.mod_lt (t.height + 1) (by decide : 0 < 2)
    have decomposition := Nat.mod_add_div (t.height + 1) 2
    dsimp [k]
    omega
  have roundingReal : (t.height : ℝ) ≤ 2 * (k : ℝ) := by
    have castRounding : (t.height : ℝ) ≤ ((2 * k : Nat) : ℝ) :=
      Nat.cast_le.mpr rounding
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using castRounding
  exact roundingReal.trans
    (mul_le_mul_of_nonneg_left logBound (by norm_num : (0 : ℝ) ≤ 2))

/-- Cached validity supplies balance of the erased shape without changing its measures. -/
theorem two_pow_ceil_half_height_le_numLeaves_of_valid
    (t : BinaryTree (α × Nat)) (h : Valid t) :
    2 ^ ((t.height + 1) / 2) ≤ t.numLeaves := by
  simpa only [Cached.height_erase, Cached.numLeaves_erase] using
    two_pow_ceil_half_height_le_numLeaves (Cached.erase t) h.1

theorem two_pow_half_height_le_numLeaves_of_valid
    (t : BinaryTree (α × Nat)) (h : Valid t) :
    2 ^ (t.height / 2) ≤ t.numLeaves := by
  simpa only [Cached.height_erase, Cached.numLeaves_erase] using
    two_pow_half_height_le_numLeaves (Cached.erase t) h.1

theorem height_le_two_mul_logb_numLeaves_of_valid
    (t : BinaryTree (α × Nat)) (h : Valid t) :
    (t.height : ℝ) ≤ 2 * Real.logb 2 (t.numLeaves : ℝ) := by
  simpa only [Cached.height_erase, Cached.numLeaves_erase] using
    height_le_two_mul_logb_numLeaves (Cached.erase t) h.1

/-- Stored height is usable only through the existing valid-cache equality. -/
theorem two_pow_ceil_half_ht_le_numLeaves (t : BinaryTree (α × Nat)) (h : Valid t) :
    2 ^ ((ht t + 1) / 2) ≤ t.numLeaves := by
  rw [ht_eq_height t h]
  exact two_pow_ceil_half_height_le_numLeaves_of_valid t h

theorem two_pow_half_ht_le_numLeaves (t : BinaryTree (α × Nat)) (h : Valid t) :
    2 ^ (ht t / 2) ≤ t.numLeaves := by
  rw [ht_eq_height t h]
  exact two_pow_half_height_le_numLeaves_of_valid t h

theorem ht_le_two_mul_logb_numLeaves (t : BinaryTree (α × Nat)) (h : Valid t) :
    (ht t : ℝ) ≤ 2 * Real.logb 2 (t.numLeaves : ℝ) := by
  rw [ht_eq_height t h]
  exact height_le_two_mul_logb_numLeaves_of_valid t h

/-- A numerical pair separating the floor estimate from the claimed log inference.
This is not an assertion that an AVL tree has height three and two leaves. -/
theorem floor_power_log_gap :
    (2 : Nat) ^ (3 / 2) ≤ 2 ∧ ¬ ((3 : ℝ) ≤ 2 * Real.logb 2 (2 : ℝ)) := by
  constructor
  · decide
  · rw [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
    norm_num

/-- Global external-leaf depth control implies the existing recursive local balance. -/
theorem balanced_of_almostComplete (t : BinaryTree α) (h : Trees.AlmostComplete t) :
    Balanced t := by
  revert h
  induction t with
  | nil =>
      intro _
      exact balanced_nil
  | node a l r ihl ihr =>
      intro h
      have children := Trees.almostComplete_children a l r h
      have ml := Trees.minHeight_le_height l
      have mr := Trees.minHeight_le_height r
      have parent : max l.height r.height ≤ min (Trees.minHeight l) (Trees.minHeight r) + 1 := by
        simp only [Trees.AlmostComplete, BinaryTree.height, Trees.minHeight_node] at h
        omega
      refine (balanced_node a l r).mpr ⟨ihl children.1, ihr children.2, ?_, ?_⟩
      · omega
      · omega

/-- Correct annotation supplies cache validity; the global shape premise supplies balance. -/
theorem valid_annotate_of_almostComplete
    (t : BinaryTree α) (h : Trees.AlmostComplete t) : Valid (annotate t) :=
  (valid_annotate_iff t).mpr (balanced_of_almostComplete t h)

end Trees.AVL

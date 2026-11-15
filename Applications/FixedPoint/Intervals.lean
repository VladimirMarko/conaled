import Applications.FixedPoint.Core

namespace BoundedArithmetic

def singleton (a : Scalar) : Box := ⟨a, a, a, le_rfl, le_rfl⟩

def Scalar.neg (a : Scalar) : Scalar := ⟨-a.ticks, by have := a.upper; omega,
  by have := a.lower; omega⟩

def neg (a : Box) : Box :=
  ⟨a.value.neg, a.hi.neg, a.lo.neg, neg_le_neg a.value_hi, neg_le_neg a.lo_value⟩

def add (a b : Box) : Option Box :=
  pack (a.value.ticks + b.value.ticks) (a.lo.ticks + b.lo.ticks) (a.hi.ticks + b.hi.ticks)

def sub (a b : Box) : Option Box := add a (neg b)

def min4 (a b c d : ℤ) : ℤ := min (min a b) (min c d)
def max4 (a b c d : ℤ) : ℤ := max (max a b) (max c d)

def mul (a b : Box) : Option Box :=
  pack (down (a.value.ticks * b.value.ticks) 256)
    (down (min4 (a.lo.ticks * b.lo.ticks) (a.lo.ticks * b.hi.ticks)
      (a.hi.ticks * b.lo.ticks) (a.hi.ticks * b.hi.ticks)) 256)
    (up (max4 (a.lo.ticks * b.lo.ticks) (a.lo.ticks * b.hi.ticks)
      (a.hi.ticks * b.lo.ticks) (a.hi.ticks * b.hi.ticks)) 256)

private def divPositive (a b : Box) : Option Box :=
  pack (down (a.value.ticks * 256) b.value.ticks)
    (min4 (down (a.lo.ticks * 256) b.lo.ticks) (down (a.lo.ticks * 256) b.hi.ticks)
      (down (a.hi.ticks * 256) b.lo.ticks) (down (a.hi.ticks * 256) b.hi.ticks))
    (max4 (up (a.lo.ticks * 256) b.lo.ticks) (up (a.lo.ticks * 256) b.hi.ticks)
      (up (a.hi.ticks * 256) b.lo.ticks) (up (a.hi.ticks * 256) b.hi.ticks))

/-- Reject every denominator enclosure containing zero, even if its center is nonzero. -/
def divide (a b : Box) : Option Box :=
  if 0 < b.lo.ticks then divPositive a b
  else if b.hi.ticks < 0 then divPositive (neg a) (neg b)
  else none

theorem singleton_contains (a : Scalar) : Contains (singleton a) a.decode := ⟨le_rfl, le_rfl⟩

theorem neg_contains {a : Box} {x : ℝ} (hx : Contains a x) : Contains (neg a) (-x) := by
  simpa [Contains, neg, Scalar.neg, Scalar.decode, neg_div] using
    And.intro (neg_le_neg hx.2) (neg_le_neg hx.1)

theorem pack_contains {v l h : ℤ} {b : Box} {x : ℝ} (hb : pack v l h = some b)
    (hl : (l : ℝ) / 256 ≤ x) (hh : x ≤ (h : ℝ) / 256) : Contains b x := by
  rcases pack_fields hb with ⟨_, rfl, rfl⟩
  exact ⟨hl, hh⟩

theorem add_contains {a b c : Box} {x y : ℝ} (hc : add a b = some c)
    (hx : Contains a x) (hy : Contains b y) : Contains c (x + y) := by
  apply pack_contains hc
  · simpa [Scalar.decode, add_div] using add_le_add hx.1 hy.1
  · simpa [Scalar.decode, add_div] using add_le_add hx.2 hy.2

theorem sub_contains {a b c : Box} {x y : ℝ} (hc : sub a b = some c)
    (hx : Contains a x) (hy : Contains b y) : Contains c (x - y) := by
  simpa [sub_eq_add_neg] using add_contains hc hx (neg_contains hy)

private theorem product_bounds {l h x : ℝ} (hx : l ≤ x ∧ x ≤ h) (y : ℝ) :
    min (l * y) (h * y) ≤ x * y ∧ x * y ≤ max (l * y) (h * y) := by
  by_cases hy : 0 ≤ y
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hx.1 hy),
      (mul_le_mul_of_nonneg_right hx.2 hy).trans (le_max_right _ _)⟩
  · have hy' : y ≤ 0 := le_of_not_ge hy
    exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hx.2 hy'),
      (mul_le_mul_of_nonpos_right hx.1 hy').trans (le_max_left _ _)⟩

/-- Four endpoint enclosure, with no sign restriction on either operand. -/
theorem four_products {al ah bl bh x y : ℝ} (hx : al ≤ x ∧ x ≤ ah)
    (hy : bl ≤ y ∧ y ≤ bh) :
    min (min (al * bl) (al * bh)) (min (ah * bl) (ah * bh)) ≤ x * y ∧
    x * y ≤ max (max (al * bl) (al * bh)) (max (ah * bl) (ah * bh)) := by
  have hxy := product_bounds hx y
  have hl := product_bounds hy al
  have hh := product_bounds hy ah
  simp only [mul_comm bl, mul_comm bh, mul_comm y] at hl hh
  constructor
  · exact (le_min ((min_le_left _ _).trans hl.1)
        ((min_le_right _ _).trans hh.1)).trans hxy.1
  · exact hxy.2.trans (max_le (hl.2.trans (le_max_left _ _))
      (hh.2.trans (le_max_right _ _)))

theorem mul_contains {a b c : Box} {x y : ℝ} (hc : mul a b = some c)
    (hx : Contains a x) (hy : Contains b y) : Contains c (x * y) := by
  have hx' : (a.lo.ticks : ℝ) ≤ 256*x ∧ 256*x ≤ a.hi.ticks := by
    rcases hx with ⟨hl, hh⟩
    dsimp [Scalar.decode] at hl hh
    constructor <;> linarith
  have hy' : (b.lo.ticks : ℝ) ≤ 256*y ∧ 256*y ≤ b.hi.ticks := by
    rcases hy with ⟨hl, hh⟩
    dsimp [Scalar.decode] at hl hh
    constructor <;> linarith
  have hp := four_products hx' hy'
  have hl := (down_bounds (min4 (a.lo.ticks*b.lo.ticks) (a.lo.ticks*b.hi.ticks)
    (a.hi.ticks*b.lo.ticks) (a.hi.ticks*b.hi.ticks)) (by norm_num : (0:ℤ)<256)).1
  have hh := (up_bounds (max4 (a.lo.ticks*b.lo.ticks) (a.lo.ticks*b.hi.ticks)
    (a.hi.ticks*b.lo.ticks) (a.hi.ticks*b.hi.ticks)) (by norm_num : (0:ℤ)<256)).1
  simp only [min4, max4, Int.cast_min, Int.cast_max, Int.cast_mul, Int.cast_ofNat] at hl hh
  apply pack_contains hc
  · dsimp [min4]
    nlinarith [hp.1]
  · dsimp [max4]
    nlinarith [hp.2]

private theorem ratio_down (a b : Scalar) (hb : 0 < b.ticks) :
    (down (a.ticks * 256) b.ticks : ℝ) / 256 ≤ a.decode / b.decode := by
  have h := (down_bounds (a.ticks * 256) hb).1
  have h' := div_le_div_of_nonneg_right h (by norm_num : (0:ℝ)≤256)
  convert h' using 1
  simp [Scalar.decode, Int.cast_mul]
  ring

private theorem ratio_up (a b : Scalar) (hb : 0 < b.ticks) :
    a.decode / b.decode ≤ (up (a.ticks * 256) b.ticks : ℝ) / 256 := by
  have h := (up_bounds (a.ticks * 256) hb).1
  have h' := div_le_div_of_nonneg_right h (by norm_num : (0:ℝ)≤256)
  convert h' using 1
  simp [Scalar.decode, Int.cast_mul]
  ring

private theorem divPositive_contains {a b c : Box} {x y : ℝ}
    (hc : divPositive a b = some c) (hb : 0 < b.lo.ticks)
    (hx : Contains a x) (hy : Contains b y) : Contains c (x / y) := by
  have hbhi : 0 < b.hi.ticks := hb.trans_le (b.lo_value.trans b.value_hi)
  have hb' : 0 < b.lo.decode := by
    dsimp [Scalar.decode]
    exact div_pos (by exact_mod_cast hb) (by norm_num)
  have hyr : 1 / b.hi.decode ≤ 1 / y ∧ 1 / y ≤ 1 / b.lo.decode :=
    ⟨one_div_le_one_div_of_le (hb'.trans_le hy.1) hy.2,
      one_div_le_one_div_of_le hb' hy.1⟩
  have hp := four_products hx hyr
  simp only [mul_one_div] at hp
  have hl1 := ratio_down a.lo b.lo hb
  have hl2 := ratio_down a.lo b.hi hbhi
  have hl3 := ratio_down a.hi b.lo hb
  have hl4 := ratio_down a.hi b.hi hbhi
  have hh1 := ratio_up a.lo b.lo hb
  have hh2 := ratio_up a.lo b.hi hbhi
  have hh3 := ratio_up a.hi b.lo hb
  have hh4 := ratio_up a.hi b.hi hbhi
  apply pack_contains hc
  · simp only [min4, Int.cast_min, ← min_div_div_right (by norm_num : (0:ℝ)≤256)]
    have h := min_le_min (min_le_min hl1 hl2) (min_le_min hl3 hl4)
    exact h.trans (by simpa only [min_comm] using hp.1)
  · simp only [max4, Int.cast_max, ← max_div_div_right (by norm_num : (0:ℝ)≤256)]
    have h := max_le_max (max_le_max hh1 hh2) (max_le_max hh3 hh4)
    apply le_trans _ h
    simpa only [max_comm] using hp.2

theorem divide_contains {a b c : Box} {x y : ℝ} (hc : divide a b = some c)
    (hx : Contains a x) (hy : Contains b y) : Contains c (x / y) := by
  unfold divide at hc
  split at hc
  · exact divPositive_contains hc ‹_› hx hy
  · split at hc
    · have hb : 0 < (neg b).lo.ticks := by
        dsimp [neg, Scalar.neg]
        omega
      simpa using divPositive_contains hc hb (neg_contains hx) (neg_contains hy)
    · simp at hc

theorem divide_rejects_zero {a b : Box} (hb : Contains b 0) : divide a b = none := by
  have hl : b.lo.ticks ≤ 0 := by
    have := hb.1
    dsimp [Scalar.decode] at this
    have : (b.lo.ticks : ℝ) ≤ 0 := by linarith
    exact_mod_cast this
  have hh : 0 ≤ b.hi.ticks := by
    have := hb.2
    dsimp [Scalar.decode] at this
    have : (0:ℝ) ≤ b.hi.ticks := by linarith
    exact_mod_cast this
  simp [divide, not_lt.mpr hl, not_lt.mpr hh]

theorem mul_selected {a b c : Box} (hc : mul a b = some c) :
    c.value.decode = roundReal (a.value.decode * b.value.decode) := by
  have hv := (pack_fields hc).1
  dsimp [Scalar.decode, roundReal]
  rw [hv]
  have hf : 256 * ((a.value.ticks:ℝ)/256 * ((b.value.ticks:ℝ)/256)) =
      ((a.value.ticks * b.value.ticks : ℤ):ℝ) / 256 := by push_cast; ring
  rw [hf]
  have hfloor := Int.floor_div_cast_of_nonneg (k := ℝ) (by norm_num : (0:ℤ)≤256)
    ((a.value.ticks * b.value.ticks : ℤ):ℝ)
  norm_num only [Int.cast_ofNat, Int.floor_intCast] at hfloor
  rw [hfloor]
  rfl

theorem add_selected {a b c : Box} (hc : add a b = some c) :
    c.value.decode = a.value.decode + b.value.decode := by
  have h := (pack_fields hc).1
  simp [Scalar.decode, h, add_div]

theorem sub_selected {a b c : Box} (hc : sub a b = some c) :
    c.value.decode = a.value.decode - b.value.decode := by
  simpa [neg, Scalar.neg, Scalar.decode, sub_eq_add_neg, neg_div] using add_selected hc

theorem mul_local_error {a b c : Box} (hc : mul a b = some c) :
    |c.value.decode - a.value.decode * b.value.decode| ≤ 1/256 := by
  rw [mul_selected hc]
  exact roundReal_error _

private theorem divPositive_error {a b c : Box} (hc : divPositive a b = some c)
    (hb : 0 < b.lo.ticks) :
    |c.value.decode - a.value.decode / b.value.decode| < 1/256 := by
  have hd : 0 < b.value.ticks := hb.trans_le b.lo_value
  have h := rounded_error (a.value.ticks*256) hd
  have hv := (pack_fields hc).1
  have heq : (((a.value.ticks*256:ℤ):ℝ) / b.value.ticks) / 256 =
      a.value.decode / b.value.decode := by
    simp [Scalar.decode, Int.cast_mul]
    ring
  rw [heq] at h
  simpa only [Scalar.decode, hv] using h

theorem divide_local_error {a b c : Box} (hc : divide a b = some c) :
    |c.value.decode - a.value.decode / b.value.decode| < 1/256 := by
  unfold divide at hc
  split at hc
  · exact divPositive_error hc ‹_›
  · split at hc
    · have hb : 0 < (neg b).lo.ticks := by dsimp [neg, Scalar.neg]; omega
      simpa only [neg, Scalar.neg, Scalar.decode, Int.cast_neg, neg_div, div_neg, neg_neg] using divPositive_error hc hb
    · simp at hc

/-- Absolute value for admission formulas; zero is a conservative lower endpoint. -/
def absolute (a : Box) : Option Box :=
  pack |a.value.ticks| 0 (max |a.lo.ticks| |a.hi.ticks|)

theorem absolute_contains {a b : Box} {x : ℝ} (hb : absolute a = some b)
    (hx : Contains a x) : Contains b |x| := by
  apply pack_contains hb
  · simpa only [Int.cast_zero, zero_div] using abs_nonneg x
  · have hx' : (a.lo.ticks:ℝ) ≤ 256*x ∧ 256*x ≤ a.hi.ticks := by
      rcases hx with ⟨hl, hh⟩
      dsimp [Scalar.decode] at hl hh
      constructor <;> linarith
    have h : |256*x| ≤ max |(a.lo.ticks:ℝ)| |(a.hi.ticks:ℝ)| := by
      rw [abs_le]
      constructor
      · have := neg_abs_le (a.lo.ticks:ℝ)
        have := le_max_left |(a.lo.ticks:ℝ)| |(a.hi.ticks:ℝ)|
        linarith [hx'.1]
      · exact hx'.2.trans ((le_abs_self _).trans (le_max_right _ _))
    simp only [abs_mul, abs_of_pos (by norm_num : (0:ℝ)<256)] at h
    push_cast
    linarith

/-- Successful division separates every possible denominator, not just its center. -/
theorem divide_separated {a b c : Box} (hc : divide a b = some c)
    {y : ℝ} (hy : Contains b y) : 1/256 ≤ |y| := by
  unfold divide at hc
  split at hc
  · have hi : (1:ℝ) ≤ b.lo.ticks := by exact_mod_cast (show 1 ≤ b.lo.ticks by omega)
    have h := hy.1
    dsimp [Scalar.decode] at h
    have hy0 : 0 ≤ y := by linarith
    rw [abs_of_nonneg hy0]
    linarith
  · split at hc
    · have hi : (b.hi.ticks:ℝ) ≤ -1 := by exact_mod_cast (show b.hi.ticks ≤ -1 by omega)
      have h := hy.2
      dsimp [Scalar.decode] at h
      have hy0 : y ≤ 0 := by linarith
      rw [abs_of_nonpos hy0]
      linarith
    · simp at hc

end BoundedArithmetic

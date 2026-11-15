import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Signed fixed-point storage and outward certificates. Integers in stored values
are bounded; real numbers occur only in specifications and proofs. -/
namespace BoundedArithmetic

structure Scalar where
  ticks : ℤ
  lower : -65536 ≤ ticks
  upper : ticks ≤ 65536
  deriving DecidableEq, Repr

noncomputable def Scalar.decode (a : Scalar) : ℝ := a.ticks / 256

structure Box where
  value : Scalar
  lo : Scalar
  hi : Scalar
  lo_value : lo.ticks ≤ value.ticks
  value_hi : value.ticks ≤ hi.ticks
  deriving DecidableEq, Repr

/-- Validate both the stored range and the enclosure of the selected value. -/
def pack (v l h : ℤ) : Option Box :=
  if hl : -65536 ≤ l then
    if hh : h ≤ 65536 then
      if hlv : l ≤ v then
        if hvh : v ≤ h then
          some ⟨⟨v, hl.trans hlv, hvh.trans hh⟩,
            ⟨l, hl, hlv.trans (hvh.trans hh)⟩,
            ⟨h, hl.trans (hlv.trans hvh), hh⟩, hlv, hvh⟩
        else none
      else none
    else none
  else none

theorem pack_fields {v l h : ℤ} {b : Box} (hb : pack v l h = some b) :
    b.value.ticks = v ∧ b.lo.ticks = l ∧ b.hi.ticks = h := by
  unfold pack at hb
  split at hb <;> simp_all
  rcases hb with ⟨_, _, _, rfl⟩
  exact ⟨rfl, rfl, rfl⟩

noncomputable def Contains (b : Box) (x : ℝ) : Prop :=
  b.lo.decode ≤ x ∧ x ≤ b.hi.decode

/-- Exact integer radius: the certificate itself is never rounded inward. -/
def Box.radius (b : Box) : ℤ :=
  max (b.value.ticks - b.lo.ticks) (b.hi.ticks - b.value.ticks)

theorem radius_range (b : Box) : 0 ≤ b.radius ∧ b.radius ≤ 131072 := by
  unfold Box.radius
  constructor
  · exact (sub_nonneg.mpr b.lo_value).trans (le_max_left _ _)
  · apply max_le <;> have := b.value.lower <;> have := b.value.upper <;>
      have := b.lo.lower <;> have := b.hi.upper <;> omega

theorem certificate_sound {b : Box} {x : ℝ} (hx : Contains b x) :
    |b.value.decode - x| ≤ (b.radius : ℝ) / 256 := by
  have hl : b.value.ticks - b.lo.ticks ≤ b.radius := le_max_left _ _
  have hh : b.hi.ticks - b.value.ticks ≤ b.radius := le_max_right _ _
  have hl' : (b.value.ticks : ℝ) - b.lo.ticks ≤ b.radius := by exact_mod_cast hl
  have hh' : (b.hi.ticks : ℝ) - b.value.ticks ≤ b.radius := by exact_mod_cast hh
  rcases hx with ⟨hx, hy⟩
  dsimp [Scalar.decode] at *
  rw [abs_le]
  constructor <;> linarith

theorem selected_contains (b : Box) : Contains b b.value.decode := by
  constructor <;> unfold Scalar.decode <;> apply div_le_div_of_nonneg_right _ (by norm_num)
  · exact_mod_cast b.lo_value
  · exact_mod_cast b.value_hi

theorem decode_injective : Function.Injective Scalar.decode := by
  intro a b h
  have ht : a.ticks = b.ticks := by
    unfold Scalar.decode at h
    have : (a.ticks : ℝ) = b.ticks := by linarith
    exact_mod_cast this
  cases a; cases b; cases ht; rfl

/-- Euclidean division by a positive denominator rounds toward negative infinity. -/
def down (n d : ℤ) : ℤ := n / d
/-- Directed upward division, including negative numerators. -/
def up (n d : ℤ) : ℤ := -((-n) / d)

theorem down_bounds (n : ℤ) {d : ℤ} (hd : 0 < d) :
    (down n d : ℝ) ≤ (n : ℝ) / d ∧ (n : ℝ) / d < (down n d : ℝ) + 1 := by
  have hf : ⌊(n : ℝ) / d⌋ = down n d := by
    simp [down, Int.floor_div_cast_of_nonneg hd.le]
  rw [← hf]
  exact ⟨Int.floor_le _, Int.lt_floor_add_one _⟩

theorem up_bounds (n : ℤ) {d : ℤ} (hd : 0 < d) :
    (n : ℝ) / d ≤ (up n d : ℝ) ∧ (up n d : ℝ) < (n : ℝ) / d + 1 := by
  have h := down_bounds (-n) hd
  simp only [down, Int.cast_neg, neg_div] at h
  simp only [up, Int.cast_neg]
  constructor <;> linarith

theorem rounded_error (n : ℤ) {d : ℤ} (hd : 0 < d) :
    |(down n d : ℝ) / 256 - ((n : ℝ) / d) / 256| < 1 / 256 := by
  have h := down_bounds n hd
  rw [abs_of_nonpos (by linarith)]
  linarith

theorem tick_add_range (a b : Scalar) :
    -131072 ≤ a.ticks + b.ticks ∧ a.ticks + b.ticks ≤ 131072 := by
  have := a.lower; have := a.upper; have := b.lower; have := b.upper
  omega

theorem tick_sub_range (a b : Scalar) :
    -131072 ≤ a.ticks - b.ticks ∧ a.ticks - b.ticks ≤ 131072 := by
  have := a.lower; have := a.upper; have := b.lower; have := b.upper
  omega

theorem tick_mul_range (a b : Scalar) : |a.ticks * b.ticks| ≤ 4294967296 := by
  have ha : |a.ticks| ≤ 65536 := abs_le.mpr ⟨a.lower, a.upper⟩
  have hb : |b.ticks| ≤ 65536 := abs_le.mpr ⟨b.lower, b.upper⟩
  rw [abs_mul]
  nlinarith [abs_nonneg a.ticks, abs_nonneg b.ticks]

theorem tick_numerator_range (a : Scalar) : |a.ticks * 256| ≤ 16777216 := by
  rw [abs_mul]
  norm_num
  have ha : |a.ticks| ≤ 65536 := abs_le.mpr ⟨a.lower, a.upper⟩
  omega

/-- Positive integer division cannot create an unbounded quotient intermediate. -/
theorem quotient_range (n : ℤ) {d : ℤ} (hd : 0 < d) :
    |down n d| ≤ |n| + 1 ∧ |up n d| ≤ |n| + 1 := by
  have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hn : |(n:ℝ) / d| ≤ |(n:ℝ)| := by
    rw [abs_div, abs_of_pos (by linarith : (0:ℝ)<d)]
    exact div_le_self (abs_nonneg _) hd'
  have hn' := abs_le.mp hn
  have hl := down_bounds n hd
  have hh := up_bounds n hd
  have hdl : |(down n d : ℝ)| ≤ |(n:ℝ)| + 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hul : |(up n d : ℝ)| ≤ |(n:ℝ)| + 1 := by
    rw [abs_le]
    constructor <;> linarith
  exact ⟨by exact_mod_cast hdl, by exact_mod_cast hul⟩

/-- Semantic floor map used to connect the executable primitive to error composition. -/
noncomputable def roundReal (x : ℝ) : ℝ := (⌊256*x⌋ : ℝ) / 256

theorem roundReal_bounds (x : ℝ) : roundReal x ≤ x ∧ x < roundReal x + 1/256 := by
  have hl := Int.floor_le (256*x)
  have hh := Int.lt_floor_add_one (256*x)
  dsimp [roundReal]
  constructor <;> linarith

theorem roundReal_error (x : ℝ) : |roundReal x - x| ≤ 1/256 := by
  have h := roundReal_bounds x
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- A finite code records the storage cardinality, independently of Lean's Int allocator. -/
def Scalar.code (a : Scalar) : Fin 131073 :=
  ⟨(a.ticks + 65536).toNat, by have := a.lower; have := a.upper; omega⟩

theorem code_injective : Function.Injective Scalar.code := by
  intro a b h
  have hc := congrArg Fin.val h
  have ha := a.lower
  have hb := b.lower
  have ht : a.ticks = b.ticks := by dsimp [Scalar.code] at hc; omega
  cases a; cases b; cases ht; rfl

theorem decode_range (a : Scalar) : -256 ≤ a.decode ∧ a.decode ≤ 256 := by
  have hl : (-65536:ℝ) ≤ a.ticks := by exact_mod_cast a.lower
  have hh : (a.ticks:ℝ) ≤ 65536 := by exact_mod_cast a.upper
  dsimp [Scalar.decode]
  constructor <;> linarith

theorem decode_zero_iff (a : Scalar) : a.decode = 0 ↔ a.ticks = 0 := by
  simp [Scalar.decode]

theorem pack_rejects_upper {v l h : ℤ} (hh : 65536 < h) : pack v l h = none := by
  unfold pack
  split <;> simp [not_le.mpr hh]

theorem pack_rejects_lower {v l h : ℤ} (hl : l < -65536) : pack v l h = none := by
  simp [pack, not_le.mpr hl]

theorem multiplication_rounding_range (a b : Scalar) :
    |down (a.ticks*b.ticks) 256| ≤ 4294967297 ∧
    |up (a.ticks*b.ticks) 256| ≤ 4294967297 := by
  have h := quotient_range (a.ticks*b.ticks) (by norm_num : (0:ℤ)<256)
  have hp := tick_mul_range a b
  constructor <;> omega

theorem division_rounding_range (a b : Scalar) (hb : 0 < b.ticks) :
    1 ≤ b.ticks ∧ b.ticks ≤ 65536 ∧
    |down (a.ticks*256) b.ticks| ≤ 16777217 ∧
    |up (a.ticks*256) b.ticks| ≤ 16777217 := by
  have h := quotient_range (a.ticks*256) hb
  have hp := tick_numerator_range a
  have hu := b.upper
  omega

end BoundedArithmetic

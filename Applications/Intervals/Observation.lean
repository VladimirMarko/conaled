import Applications.Intervals.ExactArithmetic

/-! Executable zero observations from rational enclosures of exact real values. -/

namespace IntervalAnalysis

/-- Unknown means these bounds do not justify a zero decision by this observer. -/
def observeZero (I : Interval) : Option Bool :=
  if I.hi < 0 ∨ 0 < I.lo then some false
  else if I.lo = 0 ∧ I.hi = 0 then some true
  else none

/-- A reported decision holds for every real point admitted by the enclosure. -/
theorem observeZero_sound {I : Interval} {x : ℝ} (hx : Exact.ContainsReal I x)
    {b : Bool} (hb : observeZero I = some b) : (b = true ↔ x = 0) := by
  unfold observeZero at hb
  split at hb
  next hout =>
    have hb' : b = false := (Option.some.inj hb).symm
    subst b
    simp only [Bool.false_eq_true, false_iff]
    rcases hout with hneg | hpos
    · have hh : (I.hi : ℝ) < 0 := by exact_mod_cast hneg
      intro hz
      rw [hz] at hx
      linarith [hx.2]
    · have hl : (0 : ℝ) < I.lo := by exact_mod_cast hpos
      intro hz
      rw [hz] at hx
      linarith [hx.1]
  next hout =>
    split at hb
    next hz =>
      have hb' : b = true := (Option.some.inj hb).symm
      subst b
      simp only [true_iff]
      rcases hx with ⟨hl, hh⟩
      rw [hz.1, Rat.cast_zero] at hl
      rw [hz.2, Rat.cast_zero] at hh
      exact le_antisymm hh hl
    next hz => cases hb

/-- The observation composes with the existing exact-real enclosure addition law. -/
theorem observeZero_add {I J : Interval} {x y : ℝ}
    (hx : Exact.ContainsReal I x) (hy : Exact.ContainsReal J y) {b : Bool}
    (hb : observeZero (add I J) = some b) : (b = true ↔ x + y = 0) :=
  observeZero_sound (Exact.add_containsReal hx hy) hb

/-- This obstruction concerns information in an interval, independently of computability. -/
theorem no_exact_zero_decoder : ¬ ∃ d : Interval → Bool,
    ∀ I x, Exact.ContainsReal I x → (d I = true ↔ x = 0) := by
  rintro ⟨d, hd⟩
  have h0 : Exact.ContainsReal unitBox 0 := by norm_num [Exact.ContainsReal, unitBox]
  have h1 : Exact.ContainsReal unitBox 1 := by norm_num [Exact.ContainsReal, unitBox]
  have h := (hd unitBox 1 h1).mp ((hd unitBox 0 h0).mpr rfl)
  norm_num at h

end IntervalAnalysis

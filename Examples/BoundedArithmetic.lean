import Applications.FixedPoint.Expressions
import SquareKit.Numerical.Error

namespace BoundedArithmetic.Examples

/-- Observe all three physically stored values, not only the selected center. -/
def observe (b : Option Box) : Option (ℤ × ℤ × ℤ) :=
  b.map fun x => (x.value.ticks, x.lo.ticks, x.hi.ticks)

def oneTick : Scalar := ⟨1, by norm_num, by norm_num⟩
def one : Scalar := ⟨256, by norm_num, by norm_num⟩
def threeHalves : Scalar := ⟨384, by norm_num, by norm_num⟩
def minusHalf : Scalar := ⟨-128, by norm_num, by norm_num⟩
def largest : Scalar := ⟨65536, by norm_num, by norm_num⟩
def uncertain : Box := ⟨oneTick, oneTick.neg, oneTick, by decide, by decide⟩
def nearThreshold : Box :=
  ⟨⟨255, by norm_num, by norm_num⟩, ⟨254, by norm_num, by norm_num⟩,
    ⟨257, by norm_num, by norm_num⟩, by decide, by decide⟩

example : observe (sub (singleton threeHalves) (singleton threeHalves)) =
    some (0, 0, 0) := by decide
example : observe (mul (singleton oneTick) (singleton oneTick)) = some (0, 0, 1) := by decide
example : observe (mul (singleton oneTick.neg) (singleton oneTick)) = some (-1, -1, 0) := by decide
example : observe (divide (singleton oneTick) (singleton oneTick)) = some (256, 256, 256) := by decide
example : observe (divide (singleton oneTick) (singleton oneTick.neg)) = some (-256, -256, -256) := by decide
example : divide (singleton oneTick) uncertain = none := by decide
example : divide (singleton oneTick) (singleton ⟨0, by norm_num, by norm_num⟩) = none := by decide
example : add (singleton largest) (singleton oneTick) = none := by decide
example : mul (singleton largest) (singleton threeHalves) = none := by decide
example : divide (singleton largest) (singleton oneTick) = none := by decide
example : nearThreshold.value.ticks < one.ticks ∧ below nearThreshold one = false := by decide

def underflowBox : Box :=
  ⟨oneTick.neg, oneTick.neg, ⟨0, by norm_num, by norm_num⟩, by decide, by decide⟩

theorem signed_underflow_enclosure : Contains underflowBox (-1/65536) := by
  have h := mul_contains (a := singleton oneTick.neg) (b := singleton oneTick)
    (c := underflowBox) (by decide) (singleton_contains _) (singleton_contains _)
  norm_num [Scalar.decode, oneTick, Scalar.neg] at h
  simpa only [neg_div] using h

theorem signed_underflow_certificate :
    |underflowBox.value.decode - (-1/65536)| ≤ (underflowBox.radius:ℝ)/256 :=
  certificate_sound signed_underflow_enclosure

noncomputable def first (x : ℝ) : ℝ := (3/2)*x
noncomputable def second (x : ℝ) : ℝ := (-1/2)*x
noncomputable def firstRounded (x : ℝ) : ℝ := roundReal (first x)
noncomputable def secondRounded (x : ℝ) : ℝ := roundReal (second x)

noncomputable def firstBound : NumericalError.Bound := ⟨3/2, 1/256⟩
noncomputable def secondBound : NumericalError.Bound := ⟨1/2, 1/256⟩

theorem first_lipschitz : LipschitzOnWith firstBound.sensitivity first (Set.Icc (-1) 1) := by
  apply lipschitzOnWith_iff_dist_le_mul.mpr
  intro x _ y _
  simp only [Real.dist_eq, first, firstBound, NNReal.coe_div, NNReal.coe_ofNat]
  rw [← mul_sub, abs_mul]
  norm_num

theorem second_lipschitz : LipschitzOnWith secondBound.sensitivity second (Set.Icc (-2) 2) := by
  apply lipschitzOnWith_iff_dist_le_mul.mpr
  intro x _ y _
  simp only [Real.dist_eq, second, secondBound, NNReal.coe_div, NNReal.coe_ofNat]
  rw [← mul_sub, abs_mul]
  norm_num

theorem first_uniform : NumericalError.UniformOn (Set.Icc (-1) 1)
    firstRounded first firstBound.localError := by
  intro x _
  simpa [Real.dist_eq, firstRounded, firstBound] using roundReal_error (first x)

theorem second_uniform : NumericalError.UniformOn (Set.Icc (-2) 2)
    secondRounded second secondBound.localError := by
  intro x _
  simpa [Real.dist_eq, secondRounded, secondBound] using roundReal_error (second x)

theorem exact_admitted : Set.MapsTo first (Set.Icc (-1) 1) (Set.Icc (-2) 2) := by
  intro x hx
  dsimp [first]
  constructor <;> linarith [hx.1, hx.2]

theorem rounded_admitted : Set.MapsTo firstRounded (Set.Icc (-1) 1) (Set.Icc (-2) 2) := by
  intro x hx
  have h := roundReal_bounds (first x)
  dsimp [first, firstRounded] at *
  constructor <;> linarith [hx.1, hx.2]

/-- Both actual and ideal intermediates are admitted before composing errors. -/
theorem composed_error {xhat x e : ℝ} (hh : xhat ∈ Set.Icc (-1) 1)
    (hx : x ∈ Set.Icc (-1) 1) (he : dist xhat x ≤ e) :
    dist (secondRounded (firstRounded xhat)) (second (first x)) ≤
      (firstBound.comp secondBound).apply e :=
  NumericalError.compose first_lipschitz first_uniform second_lipschitz second_uniform
    exact_admitted rounded_admitted hh hx he

/-- The composition theorem bounds the selected output of two executed multiplications. -/
theorem executed_composition {input intermediate output : Box} {x e : ℝ}
    (h₁ : mul (singleton threeHalves) input = some intermediate)
    (h₂ : mul (singleton minusHalf) intermediate = some output)
    (hh : input.value.decode ∈ Set.Icc (-1) 1) (hx : x ∈ Set.Icc (-1) 1)
    (he : dist input.value.decode x ≤ e) :
    dist output.value.decode (second (first x)) ≤ (firstBound.comp secondBound).apply e := by
  have h := composed_error hh hx he
  have hm₁ := mul_selected h₁
  have hm₂ := mul_selected h₂
  change intermediate.value.decode = roundReal (threeHalves.decode * input.value.decode) at hm₁
  change output.value.decode = roundReal (minusHalf.decode * intermediate.value.decode) at hm₂
  rw [show threeHalves.decode = 3/2 by norm_num [threeHalves, Scalar.decode]] at hm₁
  rw [show minusHalf.decode = -1/2 by norm_num [minusHalf, Scalar.decode]] at hm₂
  simpa only [firstRounded, secondRounded, first, second, ← hm₁, ← hm₂] using h

def firstOutput : Box :=
  ⟨oneTick, oneTick, ⟨2, by norm_num, by norm_num⟩, by decide, by decide⟩
def secondOutput : Box :=
  ⟨oneTick.neg, oneTick.neg, ⟨0, by norm_num, by norm_num⟩, by decide, by decide⟩

example : mul (singleton threeHalves) (singleton oneTick) = some firstOutput := by decide
example : mul (singleton minusHalf) firstOutput = some secondOutput := by decide

theorem concrete_composition :
    dist secondOutput.value.decode (-3/1024) ≤ 3/512 := by
  have h := executed_composition (input := singleton oneTick) (intermediate := firstOutput)
    (output := secondOutput) (x := 1/256) (e := 0) (by decide) (by decide)
    (by norm_num [singleton, Scalar.decode, oneTick]) (by norm_num)
    (by norm_num [singleton, Scalar.decode, oneTick])
  norm_num [second, first, firstBound, secondBound, NumericalError.Bound.comp,
    NumericalError.Bound.apply] at h
  simpa only [neg_div] using h

#eval show IO Unit from do
  if observe (mul (singleton oneTick.neg) (singleton oneTick)) != some (-1,-1,0) ||
      observe (divide (singleton oneTick) (singleton oneTick.neg)) != some (-256,-256,-256) ||
      (divide (singleton oneTick) uncertain).isSome ||
      (add (singleton largest) (singleton oneTick)).isSome then
    throw (IO.userError "bounded signed primitive runtime checks failed")
  IO.println "bounded signed primitive runtime checks passed"

end BoundedArithmetic.Examples

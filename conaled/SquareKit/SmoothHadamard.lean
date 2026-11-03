import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Experimental smooth parameter integration and global Hadamard factorization. -/

open MeasureTheory Filter Set
open scoped Topology ContDiff Interval

namespace SquareKit.SmoothHadamard

universe u

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

noncomputable def parameterDerivative (f : E × ℝ → F) (p : E × ℝ) : E →L[ℝ] F :=
  (fderiv ℝ f p).comp (ContinuousLinearMap.inl ℝ E ℝ)

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
theorem partial_smooth {f : E × ℝ → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (parameterDerivative f) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_comp contDiff_const

omit [CompleteSpace F] in
theorem integral_hasFDerivAt {f : E × ℝ → F} (hf : ContDiff ℝ ∞ f)
    (a b : ℝ) (x : E) :
    HasFDerivAt (fun x => ∫ t in a..b, f (x, t))
      (∫ t in a..b, parameterDerivative f (x, t)) x := by
  let : ProperSpace E := FiniteDimensional.proper_rclike ℝ E
  have hp := (partial_smooth hf).continuous
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x 1).prod (isCompact_uIcc : IsCompact (uIcc a b))).exists_bound_of_continuousOn hp.continuousOn
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.ball x 1) (bound := fun _ => C) (Metric.ball_mem_nhds x zero_lt_one)
  · exact Eventually.of_forall fun y => (hf.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hf.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b
  · exact (hp.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact Eventually.of_forall fun t ht y hy => hC (y,t) ⟨Metric.mem_closedBall.mpr (le_of_lt hy), uIoc_subset_uIcc ht⟩
  · exact intervalIntegrable_const
  · filter_upwards [] with t ht y hy
    exact (hf.differentiable (by simp) (y,t)).hasFDerivAt.comp y
      ((hasFDerivAt_id y).prodMk (hasFDerivAt_const t y))

theorem integral_smooth {f : E × ℝ → F} (hf : ContDiff ℝ ∞ f) (a b : ℝ) :
    ContDiff ℝ ∞ (fun x => ∫ t in a..b, f (x,t)) := by
  apply contDiff_infty.mpr
  intro n
  induction n generalizing F with
  | zero =>
    exact contDiff_zero.mpr (show Differentiable ℝ _ from
      (fun x => (integral_hasFDerivAt hf a b x).differentiableAt)).continuous
  | succ n ih =>
    apply contDiff_succ_iff_hasFDerivAt.mpr
    exact ⟨_, ih (partial_smooth hf), integral_hasFDerivAt hf a b⟩

/-- Integrating the derivative along the segment gives jointly smooth coefficients. -/
noncomputable def coefficient {n : ℕ} (f : (Fin n → ℝ) → ℝ) (i : Fin n)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  ∫ t in (0:ℝ)..1, fderiv ℝ f (p.2 + t • (p.1 - p.2)) (Pi.single i 1)

theorem coefficient_smooth {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (i : Fin n) : ContDiff ℝ ∞ (coefficient f i) := by
  unfold coefficient
  apply integral_smooth (f := fun p : ((Fin n → ℝ) × (Fin n → ℝ)) × ℝ => fderiv ℝ f (p.1.2 + p.2 • (p.1.1 - p.1.2)) (Pi.single i 1))
  exact ((hf.fderiv_right (m := ∞) (by simp)).comp
    (contDiff_fst.snd.add (contDiff_snd.smul (contDiff_fst.fst.sub contDiff_fst.snd)))).clm_apply contDiff_const

theorem factorization {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (x y : Fin n → ℝ) :
    f x - f y = ∑ i, (x i - y i) * coefficient f i (x,y) := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => f (y + t • (x-y)))
      (fderiv ℝ f (y + t • (x-y)) (x-y)) t :=
    (hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
      (by simpa using ((hasDerivAt_id t).smul_const (x-y) |>.const_add y))
  have hc : Continuous (fun t : ℝ => fderiv ℝ f (y + t • (x-y)) (x-y)) :=
    ((hf.fderiv_right (m := ∞) (by simp)).continuous.comp
      (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (hc.intervalIntegrable 0 1)
  simp only [one_smul, zero_smul, add_zero, add_sub_cancel] at h
  rw [← h]
  have hex (t : ℝ) : fderiv ℝ f (y + t • (x-y)) (x-y) =
      ∑ i, (x i - y i) * fderiv ℝ f (y + t • (x-y)) (Pi.single i 1) := by
    let d := fderiv ℝ f (y + t • (x-y))
    calc
      d (x-y) = d (∑ i, Pi.single i ((x-y) i)) := by rw [Finset.univ_sum_single]
      _ = ∑ i, d (Pi.single i ((x-y) i)) := map_sum d _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← smul_eq_mul, ← map_smul]
        congr 1
        ext j
        simp [Pi.single_apply]
  simp_rw [hex]
  rw [intervalIntegral.integral_finsetSum]
  · simp only [coefficient, intervalIntegral.integral_const_mul]
  · intro i _
    exact (continuous_const.mul (((hf.fderiv_right (m := ∞) (by simp)).continuous.comp
      (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const)).intervalIntegrable 0 1

end SquareKit.SmoothHadamard

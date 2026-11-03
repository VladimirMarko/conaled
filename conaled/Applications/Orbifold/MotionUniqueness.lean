import Applications.Orbifold.TimedCommands
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! Uniqueness of the coupled disk position and frame equation on finite clocks.
Compactness of the compared curves supplies bounds away from the disk boundary. -/
noncomputable section
open Set
namespace Orbifold.DiskTransport
open DiskConnection

/-- The frame is represented by its value at body vector `1`. -/
def motionField (v : ℂ) (omega : ℝ) (q : ℂ × ℂ) : ℂ × ℂ :=
  (q.2 * v, -coefficient q.1 (q.2 * v) * q.2 + q.2 * (omega : ℂ) * Complex.I)

theorem motionField_smooth (v : ℂ) (omega R B : ℝ) (hR : R < 1) :
    ContDiffOn ℝ 1 (motionField v omega)
      (Metric.closedBall (0 : ℂ) R ×ˢ Metric.closedBall (0 : ℂ) B) := by
  have hn : ∀ q ∈ Metric.closedBall (0 : ℂ) R ×ˢ Metric.closedBall (0 : ℂ) B,
      (1 - (Complex.normSq q.1 : ℂ)) ≠ 0 := by
    intro q hq
    have hnorm : ‖q.1‖ ≤ R := by simpa using hq.1
    have hi : Complex.normSq q.1 < 1 := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg q.1]
    exact_mod_cast ne_of_gt (sub_pos.mpr hi)
  unfold motionField coefficient gap
  simp only [Complex.ofReal_sub, Complex.ofReal_one]
  simp only [Complex.normSq_apply] at hn ⊢
  have hc : ContDiff ℝ 1 (fun q : ℂ × ℂ => (starRingEnd ℂ) q.1) :=
    Complex.conjCLE.contDiff.comp contDiff_fst
  have hr : ContDiff ℝ 1 (fun q : ℂ × ℂ => q.1.re) :=
    Complex.reCLM.contDiff.comp contDiff_fst
  have hi : ContDiff ℝ 1 (fun q : ℂ × ℂ => q.1.im) :=
    Complex.imCLM.contDiff.comp contDiff_fst
  have ho : ContDiff ℝ 1 ((↑) : ℝ → ℂ) := Complex.ofRealCLM.contDiff
  simp only [div_eq_mul_inv]
  fun_prop (disch := aesop)

/-- Solutions are unique on the closed interval, including zero duration.
Actual derivatives of extensions at endpoints suffice; the ODE theorem uses
right derivatives in the interval and continuity at the terminal point. -/
theorem motion_unique {v : ℂ} {omega T : ℝ} (hT : 0 ≤ T)
    {f g : ℝ → ℂ × ℂ}
    (hf : ∀ t ∈ Icc 0 T, HasDerivAt f (motionField v omega (f t)) t)
    (hg : ∀ t ∈ Icc 0 T, HasDerivAt g (motionField v omega (g t)) t)
    (hfi : ∀ t ∈ Icc 0 T, ‖(f t).1‖ < 1)
    (hgi : ∀ t ∈ Icc 0 T, ‖(g t).1‖ < 1)
    (h0 : f 0 = g 0) : EqOn f g (Icc 0 T) := by
  have hfc : ContinuousOn f (Icc 0 T) := fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (Icc 0 T) := fun t ht => (hg t ht).continuousAt.continuousWithinAt
  obtain ⟨a, ha, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT)
    (hfc.fst.norm.sup hgc.fst.norm)
  obtain ⟨b, hb, hbound⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT)
    (hfc.snd.norm.sup hgc.snd.norm)
  let R := max ‖(f a).1‖ ‖(g a).1‖
  let B := max ‖(f b).2‖ ‖(g b).2‖
  have hR : R < 1 := max_lt (hfi a ha) (hgi a ha)
  let S := Metric.closedBall (0 : ℂ) R ×ˢ Metric.closedBall (0 : ℂ) B
  have hfs : ∀ t ∈ Icc 0 T, f t ∈ S := by
    intro t ht
    constructor
    · simpa using (le_max_left _ _).trans (hmax ht)
    · simpa using (le_max_left _ _).trans (hbound ht)
  have hgs : ∀ t ∈ Icc 0 T, g t ∈ S := by
    intro t ht
    constructor
    · simpa using (le_max_right _ _).trans (hmax ht)
    · simpa using (le_max_right _ _).trans (hbound ht)
  obtain ⟨K, hK⟩ := (motionField_smooth v omega R B hR).exists_lipschitzOnWith
    (by norm_num) ((convex_closedBall (0 : ℂ) R).prod (convex_closedBall (0 : ℂ) B))
    ((isCompact_closedBall (0 : ℂ) R).prod (isCompact_closedBall (0 : ℂ) B))
  exact ODE_solution_unique_of_mem_Icc_right (v := fun _ => motionField v omega)
    (s := fun _ => S) (fun _ _ => hK) hfc
    (fun t ht => (hf t (mem_Icc_of_Ico ht)).hasDerivWithinAt)
    (fun t ht => hfs t (mem_Icc_of_Ico ht)) hgc
    (fun t ht => (hg t (mem_Icc_of_Ico ht)).hasDerivWithinAt)
    (fun t ht => hgs t (mem_Icc_of_Ico ht)) h0

/-- Position and the value at `1` determine an oriented disk frame. -/
theorem pose_eq_of_frame {p q : Pose} (ha : p.a = q.a) (hf : p.frame 1 = q.frame 1) : p = q := by
  apply QuarterTurn.pose_ext ha
  have hn : 1 - (Complex.normSq q.a : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (sub_pos.mpr q.inside)
  simp only [Pose.frame, mul_one, ha] at hf
  have h : (1 - (Complex.normSq q.a : ℂ)) * (p.u - q.u) = 0 := by
    linear_combination 2 * hf
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hn)

private theorem pose_coordinates_derivative {f : ℝ → Pose} {v : ℂ} {omega t : ℝ}
    (hp : HasDerivAt (fun r => (f r).a) ((f t).frame v) t)
    (hf : HasDerivAt (fun r => (f r).frame 1)
      ((f t).frame ((omega : ℂ) * Complex.I * 1) -
        christoffel (f t).a ((f t).frame v) ((f t).frame 1)) t) :
    HasDerivAt (fun r => ((f r).a, (f r).frame 1))
      (motionField v omega ((f t).a, (f t).frame 1)) t := by
  convert hp.prodMk hf using 1
  apply Prod.ext <;> simp [motionField, Pose.frame, christoffel, coefficient] <;> ring

/-- Every pose-valued solution of the stated equations agrees with the
constructed command. No bounds or ODE certificate for the construction are
caller inputs. Competing solutions supply actual derivatives on `[0,T]`. -/
theorem Control.unique (c : Control) (p : Pose) (T : ℝ) (hT : 0 ≤ T)
    (f : ℝ → Pose) (h0 : f 0 = p)
    (hp : ∀ t ∈ Icc 0 T, HasDerivAt (fun r => (f r).a) ((f t).frame c.velocity) t)
    (hf : ∀ t ∈ Icc 0 T, ∀ w : ℂ, HasDerivAt (fun r => (f r).frame w)
      ((f t).frame ((c.angularVelocity : ℂ) * Complex.I * w) -
        christoffel (f t).a ((f t).frame c.velocity) ((f t).frame w)) t) :
    EqOn f (c.trajectory p) (Icc 0 T) := by
  have hin (q : Pose) : ‖q.a‖ < 1 := by
    have h := q.inside
    rw [Complex.normSq_eq_norm_sq] at h
    nlinarith [norm_nonneg q.a]
  have h := motion_unique hT
    (fun t ht => pose_coordinates_derivative (hp t ht) (hf t ht 1))
    (fun t _ => pose_coordinates_derivative (c.position_equation p t) (c.frame_equation p t 1))
    (fun t _ => hin (f t)) (fun t _ => hin (c.trajectory p t))
    (by simp [h0])
  intro t ht
  exact pose_eq_of_frame (congrArg Prod.fst (h ht)) (congrArg Prod.snd (h ht))
end Orbifold.DiskTransport

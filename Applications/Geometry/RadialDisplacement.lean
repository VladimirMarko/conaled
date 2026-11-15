import Applications.Geometry.RadialBranches
import Applications.Geometry.RadialTransport

/-! Local radial displacement and the separate domains of its factors. -/
noncomputable section
namespace RadialMetric
open Set Metric Complex
open scoped Topology

theorem branch_inverse_smooth : ContDiffAt ℝ ⊤ (branch.symm : State → State) 0 := by
  have h := jointExp_smooth.to_localInverse jointExp_derivative (by simp)
  have hz : jointExp (0 : State) = 0 := by ext <;> simp [jointExp,expMap_zero]
  rw [hz] at h
  convert! h using 1

theorem branch_inverse_derivative :
    HasFDerivAt (branch.symm : State → State) (jointDerivative.symm : State →L[ℝ] State) 0 := by
  have h := (jointExp_smooth.hasStrictFDerivAt' jointExp_derivative (by simp)).to_localInverse
  have hz : jointExp (0 : State) = 0 := by ext <;> simp [jointExp,expMap_zero]
  rw [hz] at h
  convert! h.hasFDerivAt using 1

def originLog (y : ℂ) : ℂ := logMap (0,y)

theorem originLog_zero : originLog 0 = 0 := log_zero

theorem originLog_smooth : ContDiffAt ℝ ⊤ originLog 0 := by
  have hin : ContDiffAt ℝ ⊤ (ContinuousLinearMap.inr ℝ ℂ ℂ : ℂ → State) 0 :=
    (ContinuousLinearMap.inr ℝ ℂ ℂ).contDiff.contDiffAt
  have hs := (contDiffAt_snd.comp 0 branch_inverse_smooth)
  have he : (ContinuousLinearMap.inr ℝ ℂ ℂ) (0 : ℂ) = 0 := map_zero _
  rw [← he] at hs
  convert! hs.comp 0 hin using 1

theorem originLog_derivative : HasFDerivAt originLog (ContinuousLinearMap.id ℝ ℂ) 0 := by
  have hs := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp (0 : State) branch_inverse_derivative
  have he : (ContinuousLinearMap.inr ℝ ℂ ℂ) (0 : ℂ) = 0 := map_zero _
  rw [← he] at hs
  have h := hs.comp (0 : ℂ) (ContinuousLinearMap.inr ℝ ℂ ℂ).hasFDerivAt
  convert! h using 1
  apply ContinuousLinearMap.ext
  intro z
  change z = z - 0
  simp

def radialParallel (x v : ℂ) : ℂ := (Real.exp (-normSq x) : ℂ)*v

def displacement (p : State) : ℂ := expMap (p.1,radialParallel p.1 (originLog p.2))

/-- Each exponential and inverse is used only on its own justified branch. -/
def DisplacementDomain (p : State) : Prop :=
  (0,p.2) ∈ branch.target ∧ (p.1,radialParallel p.1 (originLog p.2)) ∈ branch.source

theorem displacement_zero : displacement 0 = 0 := by
  simp only [displacement, Prod.fst_zero, Prod.snd_zero, originLog_zero, radialParallel, mul_zero]
  exact expMap_zero

theorem normSq_smooth : ContDiff ℝ ⊤ (normSq : ℂ → ℝ) := by
  convert! (Complex.reCLM.contDiff.pow 2).add (Complex.imCLM.contDiff.pow 2) using 1
  funext z; simp [Complex.normSq_apply,pow_two]

def displacementVelocity (p : State) : ℂ := radialParallel p.1 (originLog p.2)

theorem displacementVelocity_smooth : ContDiffAt ℝ ⊤ displacementVelocity 0 := by
  have hf := (Complex.ofRealCLM.contDiff.comp (normSq_smooth.neg.exp)).contDiffAt.comp
    (0 : State) contDiffAt_fst
  have hg := originLog_smooth.comp (0 : State) contDiffAt_snd
  convert! hf.mul hg using 1

theorem displacementVelocity_derivative :
    HasFDerivAt displacementVelocity (ContinuousLinearMap.snd ℝ ℂ ℂ) 0 := by
  have hf := (Complex.ofRealCLM.contDiff.comp (normSq_smooth.neg.exp)).differentiable
    (by simp : (⊤ : WithTop ℕ∞) ≠ 0)
  have hff := (hf 0).hasFDerivAt.comp (0 : State) (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt
  have hgg := originLog_derivative.comp (0 : State) (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt
  convert! hff.mul hgg using 1
  apply ContinuousLinearMap.ext
  intro p
  simp [originLog_zero, normSq_zero, Function.comp_def]

theorem displacement_smooth : ContDiffAt ℝ ⊤ displacement 0 := by
  have hi := contDiffAt_fst.prodMk displacementVelocity_smooth
  have he : ((0 : State).1,displacementVelocity 0) = (0 : State) := by
    simp [displacementVelocity,radialParallel,originLog_zero]
  have hf := expMap_smooth
  rw [← he] at hf
  convert! hf.comp 0 hi using 1

theorem displacement_derivative : HasFDerivAt displacement expDerivative 0 := by
  have hi := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.prodMk displacementVelocity_derivative
  have he : ((0 : State).1,displacementVelocity 0) = (0 : State) := by
    simp [displacementVelocity,radialParallel,originLog_zero]
  have hf := expMap_derivative
  rw [← he] at hf
  convert! hf.comp 0 hi using 1

theorem displacement_domain_near_zero : ∀ᶠ p in 𝓝 (0 : State), DisplacementDomain p := by
  have hc1 : ContinuousAt (fun p : State => ((0 : ℂ),p.2)) 0 := by fun_prop
  have hc2 := (contDiffAt_fst.prodMk displacementVelocity_smooth).continuousAt
  have h1 := hc1.tendsto.eventually branch_neighborhoods.2
  have hz : ((0 : State).1,displacementVelocity 0) = (0 : State) := by
    simp [displacementVelocity,radialParallel,originLog_zero]
  have h2 : ∀ᶠ p in 𝓝 (0 : State), (p.1,displacementVelocity p) ∈ branch.source := by
    apply hc2.tendsto.eventually
    rw [hz]
    exact branch_neighborhoods.1
  filter_upwards [h1,h2] with p hp hq
  exact ⟨hp,hq⟩

theorem displacement_left_unit {y : ℂ} (hy : (0,y) ∈ branch.target) :
    displacement (0,y) = y := by
  change expMap (0,radialParallel 0 (originLog y)) = y
  simp only [radialParallel,normSq_zero,neg_zero,Real.exp_zero,Complex.ofReal_one,one_mul]
  exact exp_log hy

end RadialMetric

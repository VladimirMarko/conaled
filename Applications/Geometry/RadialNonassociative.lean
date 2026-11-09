import Applications.Geometry.RadialAssociator

/-! A concrete associator of the actual local operation, with error control. -/
noncomputable section
namespace RadialMetric.Nonassociative
open Set Metric Complex Asymptotics
open scoped Topology ComplexConjugate

def xy (t : ℝ) : State := (t,t*I)
def yz (t : ℝ) : State := (t*I,t*I)
def leftInput (t : ℝ) : State := (displacement (xy t),t*I)
def rightInput (t : ℝ) : State := (t,displacement (yz t))
def leftLinear (t : ℝ) : State := (t+t*I,t*I)
def rightLinear (t : ℝ) : State := (t,t*I+t*I)
def associator (t : ℝ) : ℂ := displacement (leftInput t)-displacement (rightInput t)

@[simp] theorem xy_zero : xy 0 = 0 := by simp [xy]
@[simp] theorem yz_zero : yz 0 = 0 := by simp [yz]
@[simp] theorem leftInput_zero : leftInput 0 = 0 := by simp [leftInput,displacement_zero]
@[simp] theorem rightInput_zero : rightInput 0 = 0 := by simp [rightInput,displacement_zero]
@[simp] theorem leftLinear_zero : leftLinear 0 = 0 := by simp [leftLinear]
@[simp] theorem rightLinear_zero : rightLinear 0 = 0 := by simp [rightLinear]

@[local fun_prop] theorem realCast_smooth : ContDiffAt ℝ ⊤ (fun t : ℝ => (t : ℂ)) 0 :=
  Complex.ofRealCLM.contDiff.contDiffAt

theorem xy_smooth : ContDiffAt ℝ ⊤ xy 0 := by unfold xy; fun_prop
theorem yz_smooth : ContDiffAt ℝ ⊤ yz 0 := by unfold yz; fun_prop
theorem leftLinear_smooth : ContDiffAt ℝ ⊤ leftLinear 0 := by unfold leftLinear; fun_prop
theorem rightLinear_smooth : ContDiffAt ℝ ⊤ rightLinear 0 := by unfold rightLinear; fun_prop

theorem leftInput_smooth : ContDiffAt ℝ ⊤ leftInput 0 := by
  have h := displacement_smooth
  rw [← xy_zero] at h
  exact (h.comp 0 xy_smooth).prodMk (by fun_prop)

theorem rightInput_smooth : ContDiffAt ℝ ⊤ rightInput 0 := by
  have h := displacement_smooth
  rw [← yz_zero] at h
  exact (by fun_prop : ContDiffAt ℝ ⊤ (fun t : ℝ => (t : ℂ)) 0).prodMk (h.comp 0 yz_smooth)

private theorem input_bound {f : ℝ → State} (hf : ContDiffAt ℝ ⊤ f 0) (h0 : f 0 = 0) :
    f =O[𝓝 (0 : ℝ)] (fun t => ‖t‖) := by
  have h := (hf.differentiableAt (by simp)).isBigO_sub.norm_right
  simpa only [h0,sub_zero] using h

private theorem compose_error {f : State → ℂ} {g : ℝ → State} {n : ℕ}
    (hf : f =O[𝓝 (0 : State)] (fun p => ‖p‖^n))
    (hg : ContDiffAt ℝ ⊤ g 0) (h0 : g 0 = 0) :
    (fun t => f (g t)) =O[𝓝 (0 : ℝ)] (fun t => ‖t‖^n) := by
  have ht := hg.continuousAt.tendsto
  rw [h0] at ht
  exact (hf.comp_tendsto ht).trans ((input_bound hg h0).norm_left.pow n)

theorem leftInput_deviation : (fun t => leftInput t-leftLinear t)
    =O[𝓝 (0 : ℝ)] (fun t => ‖t‖^3) := by
  have h := compose_error displacement_deviation xy_smooth xy_zero
  have hz : (fun _ : ℝ => (0 : ℂ)) =O[𝓝 0] (fun t => ‖t‖^3) := isBigO_zero _ _
  apply (h.prod_left hz).congr_left
  intro t
  ext <;> simp [xy,leftInput,leftLinear]

theorem rightInput_deviation : (fun t => rightInput t-rightLinear t)
    =O[𝓝 (0 : ℝ)] (fun t => ‖t‖^3) := by
  have h := compose_error displacement_deviation yz_smooth yz_zero
  have hz : (fun _ : ℝ => (0 : ℂ)) =O[𝓝 0] (fun t => ‖t‖^3) := isBigO_zero _ _
  apply (hz.prod_left h).congr_left
  intro t
  ext <;> simp [yz,rightInput,rightLinear]

theorem cubic_associator (t : ℝ) :
    cubicCorrection (xy t)-cubicCorrection (yz t)+cubicCorrection (leftLinear t)-
      cubicCorrection (rightLinear t) = 2*(t : ℂ)^3 := by
  simp only [cubicCorrection,xy,yz,leftLinear,rightLinear, map_add,map_mul,
    Complex.conj_ofReal,Complex.conj_I]
  ring_nf
  simp [Complex.I_sq]

theorem associator_remainder : (fun t => associator t+2*(t : ℂ)^3)
    =O[𝓝 (0 : ℝ)] (fun t => ‖t‖^5) := by
  have hxy := compose_error displacement_cubic_error xy_smooth xy_zero
  have hyz := compose_error displacement_cubic_error yz_smooth yz_zero
  have hl := compose_error displacement_cubic_error leftInput_smooth leftInput_zero
  have hr := compose_error displacement_cubic_error rightInput_smooth rightInput_zero
  have hdl := cubicCorrection_difference (input_bound leftInput_smooth leftInput_zero)
    (input_bound leftLinear_smooth leftLinear_zero) leftInput_deviation
  have hdr := cubicCorrection_difference (input_bound rightInput_smooth rightInput_zero)
    (input_bound rightLinear_smooth rightLinear_zero) rightInput_deviation
  apply (((((hxy.sub hyz).add hl).sub hr).sub hdl).add hdr).congr_left
  intro t
  rw [← cubic_associator t]
  simp only [xy,yz,leftInput,rightInput,associator]
  ring

/-- The actual associator cannot vanish for all sufficiently small positive inputs. -/
theorem associator_nonzero_near : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < t → associator t ≠ 0 := by
  have he := associator_remainder.trans_isLittleO
    (isLittleO_norm_pow_norm_pow (E' := ℝ) (by norm_num : 3 < 5))
  filter_upwards [he.eventuallyLE] with t ht hpos hz
  rw [hz,zero_add,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hpos] at ht
  norm_num only [Complex.norm_ofNat,Real.norm_eq_abs,abs_pow,abs_norm] at ht
  have hp : 0 < t^3 := pow_pos hpos 3
  rw [abs_of_pos hpos] at ht
  linarith

theorem domains_near : ∀ᶠ t in 𝓝 (0 : ℝ),
    DisplacementDomain (xy t) ∧ DisplacementDomain (yz t) ∧
    DisplacementDomain (leftInput t) ∧ DisplacementDomain (rightInput t) := by
  have hxy := xy_smooth.continuousAt.tendsto
  have hyz := yz_smooth.continuousAt.tendsto
  have hl := leftInput_smooth.continuousAt.tendsto
  have hr := rightInput_smooth.continuousAt.tendsto
  rw [xy_zero] at hxy
  rw [yz_zero] at hyz
  rw [leftInput_zero] at hl
  rw [rightInput_zero] at hr
  filter_upwards [hxy.eventually displacement_domain_near_zero,hyz.eventually displacement_domain_near_zero,
    hl.eventually displacement_domain_near_zero,hr.eventually displacement_domain_near_zero] with t h1 h2 h3 h4
  exact ⟨h1,h2,h3,h4⟩

theorem positive_nonassociative_client : ∃ t : ℝ, 0 < t ∧
    DisplacementDomain (xy t) ∧ DisplacementDomain (yz t) ∧
    DisplacementDomain (leftInput t) ∧ DisplacementDomain (rightInput t) ∧
    displacement (leftInput t) ≠ displacement (rightInput t) := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (domains_near.and associator_nonzero_near)
  have ht : r/2 ∈ ball (0 : ℝ) r := by
    rw [mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos (half_pos hr)]
    linarith
  obtain ⟨⟨h1,h2,h3,h4⟩,hn⟩ := hball ht
  refine ⟨r/2,half_pos hr,h1,h2,h3,h4,?_⟩
  exact sub_ne_zero.mp (hn (half_pos hr))

end RadialMetric.Nonassociative

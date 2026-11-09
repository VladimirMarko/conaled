import Applications.Geometry.RadialExponential

/-! Local exponential/log branches of the fixed metric, restricted to initial
states whose selected bounded ODE solution has been identified. -/
noncomputable section
namespace RadialMetric
open Set Metric
open scoped Topology

def jointExp (p : State) : State := (p.1,expMap p)

def jointDerivative : State ≃L[ℝ] State where
  toFun p := (p.1,p.1+p.2)
  invFun p := (p.1,p.2-p.1)
  map_add' p q := by ext <;> simp <;> abel
  map_smul' c p := by ext <;> simp [smul_add]
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem jointExp_smooth : ContDiffAt ℝ ⊤ jointExp 0 :=
  contDiffAt_fst.prodMk expMap_smooth

theorem jointExp_derivative :
    HasFDerivAt jointExp (jointDerivative : State →L[ℝ] State) 0 := by
  have h := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.prodMk expMap_derivative
  convert! h using 1

def rawBranch : OpenPartialHomeomorph State State :=
  jointExp_smooth.toOpenPartialHomeomorph jointExp jointExp_derivative (by simp)

theorem rawBranch_zero : (0 : State) ∈ rawBranch.source :=
  jointExp_smooth.mem_toOpenPartialHomeomorph_source jointExp_derivative (by simp)

/-- Restrict to the neighborhood where the exponential is the bounded selected flow. -/
def branch : OpenPartialHomeomorph State State := rawBranch.restr {p | Admitted p}

theorem branch_zero : (0 : State) ∈ branch.source := by
  exact ⟨rawBranch_zero, mem_interior_iff_mem_nhds.mpr admitted_near_zero⟩

theorem branch_source_actual {p : State} (hp : p ∈ branch.source) : Admitted p := by
  exact (interior_subset (s := {p | Admitted p})) hp.2

@[simp] theorem branch_apply (p : State) : branch p = jointExp p := rfl

theorem branch_target_zero : (0 : State) ∈ branch.target := by
  have h := branch.map_source branch_zero
  have hz : branch (0 : State) = 0 := by ext <;> simp [branch_apply,jointExp,expMap_zero]
  rwa [hz] at h

def logMap (p : State) : ℂ := (branch.symm p).2

theorem inverse_base {p : State} (hp : p ∈ branch.target) : (branch.symm p).1 = p.1 := by
  have h := congrArg Prod.fst (branch.right_inv hp)
  change (branch.symm p).1 = p.1 at h
  exact h

theorem exp_log {p : State} (hp : p ∈ branch.target) :
    expMap (p.1,logMap p) = p.2 := by
  have h := congrArg Prod.snd (branch.right_inv hp)
  change expMap (branch.symm p) = p.2 at h
  have he : (p.1,logMap p) = branch.symm p := by
    ext
    · exact (inverse_base hp).symm
    · rfl
  rw [he]
  exact h

theorem log_exp {p : State} (hp : p ∈ branch.source) :
    logMap (p.1,expMap p) = p.2 := congrArg Prod.snd (branch.left_inv hp)

theorem log_zero : logMap 0 = 0 := by
  have h := branch.left_inv branch_zero
  have hz : branch (0 : State) = 0 := by ext <;> simp [branch_apply,jointExp,expMap_zero]
  rw [hz] at h
  exact congrArg Prod.snd h

theorem log_admitted {p : State} (hp : p ∈ branch.target) :
    Admitted (p.1,logMap p) := by
  have h := branch_source_actual (branch.map_target hp)
  have he : (p.1,logMap p) = branch.symm p := by
    ext
    · exact (inverse_base hp).symm
    · rfl
  rwa [he]

/-- Both branch domains are genuine nonempty open neighborhoods. -/
theorem branch_neighborhoods : branch.source ∈ 𝓝 (0 : State) ∧ branch.target ∈ 𝓝 (0 : State) :=
  ⟨branch.open_source.mem_nhds branch_zero, branch.open_target.mem_nhds branch_target_zero⟩

end RadialMetric

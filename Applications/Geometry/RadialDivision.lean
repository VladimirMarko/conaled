import Applications.Geometry.RadialSymmetry

/-! Left and right local division are independent inverse-function applications.
Their domains are retained separately; no bounded neighborhood is declared
closed under every displacement. -/
noncomputable section
namespace RadialMetric
open Set Metric
open scoped Topology

def leftJoint (p : State) : State := (p.1,displacement p)
def rightJoint (p : State) : State := (p.2,displacement p)

def rightDerivative : State ≃L[ℝ] State where
  toFun p := (p.2,p.1+p.2)
  invFun p := (p.2-p.1,p.1)
  map_add' p q := by ext <;> simp <;> abel
  map_smul' c p := by ext <;> simp [smul_add]
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem leftJoint_smooth : ContDiffAt ℝ ⊤ leftJoint 0 :=
  contDiffAt_fst.prodMk displacement_smooth

theorem rightJoint_smooth : ContDiffAt ℝ ⊤ rightJoint 0 :=
  contDiffAt_snd.prodMk displacement_smooth

theorem leftJoint_derivative :
    HasFDerivAt leftJoint (jointDerivative : State →L[ℝ] State) 0 := by
  convert! (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.prodMk displacement_derivative using 1

theorem rightJoint_derivative :
    HasFDerivAt rightJoint (rightDerivative : State →L[ℝ] State) 0 := by
  convert! (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.prodMk displacement_derivative using 1

def leftBranch : OpenPartialHomeomorph State State :=
  (leftJoint_smooth.toOpenPartialHomeomorph leftJoint leftJoint_derivative (by simp)).restr
    {p | DisplacementDomain p}
def rightBranch : OpenPartialHomeomorph State State :=
  (rightJoint_smooth.toOpenPartialHomeomorph rightJoint rightJoint_derivative (by simp)).restr
    {p | DisplacementDomain p}

theorem leftBranch_zero : (0 : State) ∈ leftBranch.source :=
  ⟨leftJoint_smooth.mem_toOpenPartialHomeomorph_source leftJoint_derivative (by simp),
    mem_interior_iff_mem_nhds.mpr displacement_domain_near_zero⟩

theorem rightBranch_zero : (0 : State) ∈ rightBranch.source :=
  ⟨rightJoint_smooth.mem_toOpenPartialHomeomorph_source rightJoint_derivative (by simp),
    mem_interior_iff_mem_nhds.mpr displacement_domain_near_zero⟩

theorem leftBranch_target_zero : (0 : State) ∈ leftBranch.target := by
  have h := leftBranch.map_source leftBranch_zero
  have hz : leftBranch (0 : State) = 0 := by
    change ((0 : State).1,displacement 0) = 0
    rw [displacement_zero]; rfl
  rwa [hz] at h

theorem rightBranch_target_zero : (0 : State) ∈ rightBranch.target := by
  have h := rightBranch.map_source rightBranch_zero
  have hz : rightBranch (0 : State) = 0 := by
    change ((0 : State).2,displacement 0) = 0
    rw [displacement_zero]; rfl
  rwa [hz] at h

def leftDivide (x z : ℂ) : ℂ := (leftBranch.symm (x,z)).2
def rightDivide (y z : ℂ) : ℂ := (rightBranch.symm (y,z)).1

theorem left_division {x z : ℂ} (h : (x,z) ∈ leftBranch.target) :
    DisplacementDomain (x,leftDivide x z) ∧ displacement (x,leftDivide x z) = z := by
  have he := leftBranch.right_inv h
  have hb := congrArg Prod.fst he
  change (leftBranch.symm (x,z)).1 = x at hb
  have hp : (x,leftDivide x z) = leftBranch.symm (x,z) := by
    ext
    · exact hb.symm
    · rfl
  rw [hp]
  refine ⟨(interior_subset (s := {p | DisplacementDomain p})) (leftBranch.map_target h).2,?_⟩
  exact congrArg Prod.snd he

theorem right_division {y z : ℂ} (h : (y,z) ∈ rightBranch.target) :
    DisplacementDomain (rightDivide y z,y) ∧ displacement (rightDivide y z,y) = z := by
  have he := rightBranch.right_inv h
  have hb := congrArg Prod.fst he
  change (rightBranch.symm (y,z)).2 = y at hb
  have hp : (rightDivide y z,y) = rightBranch.symm (y,z) := by
    ext
    · rfl
    · exact hb.symm
  rw [hp]
  refine ⟨(interior_subset (s := {p | DisplacementDomain p})) (rightBranch.map_target h).2,?_⟩
  exact congrArg Prod.snd he

theorem left_division_unique {x y z : ℂ} (hp : (x,y) ∈ leftBranch.source)
    (hz : displacement (x,y) = z) : y = leftDivide x z := by
  have h := congrArg Prod.snd (leftBranch.left_inv hp)
  change leftDivide x (displacement (x,y)) = y at h
  rw [hz] at h
  exact h.symm

theorem right_division_unique {x y z : ℂ} (hp : (x,y) ∈ rightBranch.source)
    (hz : displacement (x,y) = z) : x = rightDivide y z := by
  have h := congrArg Prod.fst (rightBranch.left_inv hp)
  change rightDivide y (displacement (x,y)) = x at h
  rw [hz] at h
  exact h.symm

end RadialMetric

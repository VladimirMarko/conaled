import Applications.Orbifolds.SmoothComparison
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-! The finite linear quarter-turn action, independent of projective disk motions.
The ellipse is the image of the open unit disk under real-axis scaling by two. -/

noncomputable section
open Diffeology MulAction Complex
open scoped Manifold ContDiff
namespace Orbifolds.QuarterTurn

abbrev C4 := rootsOfUnity 4 ℂ

/-- The positive quarter-turn, identified by its complex scalar. -/
def quarterTurn : C4 :=
  ⟨⟨Complex.I, -Complex.I, by simp, by simp⟩,
    (mem_rootsOfUnity' 4 _).mpr (by norm_num)⟩

@[simp] theorem quarterTurn_scalar : (quarterTurn.val : ℂ) = Complex.I := rfl

/-- The ellipse generator specified directly in real coordinates. -/
def ellipseQuarterTurn (z : ℂ) : ℂ := ⟨-2 * z.im, z.re / 2⟩

theorem card_C4 : Nat.card C4 = 4 := Complex.card_rootsOfUnity 4

def disk : TopologicalSpace.Opens ℂ := ⟨Metric.ball 0 1, Metric.isOpen_ball⟩
abbrev Disk := ↥disk

/-- The real coordinate change `(x,y) ↦ (2*x,y)`. -/
def stretch : ℂ ≃L[ℝ] ℂ where
  toFun z := ⟨2 * z.re, z.im⟩
  invFun z := ⟨z.re / 2, z.im⟩
  left_inv z := by apply Complex.ext <;> simp
  right_inv z := by apply Complex.ext <;> simp; ring
  map_add' z w := by apply Complex.ext <;> simp; ring
  map_smul' r z := by apply Complex.ext <;> simp; ring
  continuous_toFun := by
    have h : (fun z : ℂ => (⟨2 * z.re, z.im⟩ : ℂ)) =
        fun z => (2 * z.re : ℂ) + z.im * Complex.I := by
      funext z; apply Complex.ext <;> simp
    rw [h]; fun_prop
  continuous_invFun := by
    have h : (fun z : ℂ => (⟨z.re / 2, z.im⟩ : ℂ)) =
        fun z => (z.re / 2 : ℂ) + z.im * Complex.I := by
      funext z; apply Complex.ext <;> simp
    rw [h]; fun_prop

@[simp] theorem stretch_re (z : ℂ) : (stretch z).re = 2 * z.re := rfl
@[simp] theorem stretch_im (z : ℂ) : (stretch z).im = z.im := rfl
@[simp] theorem stretch_symm_re (z : ℂ) : (stretch.symm z).re = z.re / 2 := rfl
@[simp] theorem stretch_symm_im (z : ℂ) : (stretch.symm z).im = z.im := rfl

theorem stretch_nonidentity : stretch 1 ≠ (1 : ℂ) := by
  intro h
  have := congrArg Complex.re h
  norm_num at this

def ellipse : TopologicalSpace.Opens ℂ :=
  ⟨stretch.symm ⁻¹' (disk : Set ℂ), disk.isOpen.preimage stretch.symm.continuous⟩
abbrev Ellipse := ↥ellipse

def diskEllipse : Diffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) Disk Ellipse ∞ where
  toFun z := ⟨stretch z, by change stretch.symm (stretch z) ∈ (disk : Set ℂ); simp⟩
  invFun z := ⟨stretch.symm z, z.property⟩
  left_inv z := Subtype.ext (stretch.symm_apply_apply z)
  right_inv z := Subtype.ext (stretch.apply_symm_apply z)
  contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff ellipse _).mp
    (stretch.contDiff.contMDiff.comp contMDiff_subtype_val)
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff disk _).mp
    (stretch.symm.contDiff.contMDiff.comp contMDiff_subtype_val)

instance diskAction : MulAction C4 Disk where
  smul g z := ⟨(g.val : ℂ) * z, by
    have hn := Complex.norm_eq_one_of_mem_rootsOfUnity g.property
    simpa [disk, Metric.mem_ball, dist_zero_right, norm_mul, hn] using z.property⟩
  one_smul z := by
    apply Subtype.ext
    change (1 : ℂ) * (z : ℂ) = z
    simp
  mul_smul g h z := by
    apply Subtype.ext
    change ((g.val : ℂ) * (h.val : ℂ)) * (z : ℂ) = (g.val : ℂ) * ((h.val : ℂ) * z)
    exact mul_assoc _ _ _

instance ellipseAction : MulAction C4 Ellipse where
  smul g z := diskEllipse (g • diskEllipse.symm z)
  one_smul z := by
    change diskEllipse ((1 : C4) • diskEllipse.symm z) = z
    simp
  mul_smul g h z := by
    change diskEllipse ((g * h) • diskEllipse.symm z) =
      diskEllipse (g • diskEllipse.symm (diskEllipse (h • diskEllipse.symm z)))
    simp [mul_smul]

@[simp] theorem disk_smul_coe (g : C4) (z : Disk) :
    ((g • z : Disk) : ℂ) = (g.val : ℂ) * z := rfl

theorem diskEllipse_equivariant (g : C4) (z : Disk) :
    diskEllipse (g • z) = (MulEquiv.refl C4) g • diskEllipse z := by
  change diskEllipse (g • z) = diskEllipse (g • diskEllipse.symm (diskEllipse z))
  rw [diskEllipse.symm_apply_apply]

def coordinateChange : CoordinateChange (MulEquiv.refl C4) Disk Ellipse :=
  manifoldCoordinateChange diskEllipse diskEllipse_equivariant

/-- Every group element is a power of multiplication by `i`. -/
theorem scalar_eq_pow (g : C4) : ∃ k < 4, Complex.I ^ k = (g.val : ℂ) :=
  Complex.isPrimitiveRoot_I.eq_pow_of_pow_eq_one ((mem_rootsOfUnity' 4 g.val).mp g.property)

def origin : Disk := ⟨0, by simp [disk]⟩

theorem origin_stabilizer : stabilizer C4 origin = ⊤ := by
  ext g
  simp only [Subgroup.mem_top, iff_true, mem_stabilizer_iff]
  apply Subtype.ext
  simp [origin]

theorem nonzero_stabilizer (z : Disk) (hz : (z : ℂ) ≠ 0) : stabilizer C4 z = ⊥ := by
  ext g
  simp only [mem_stabilizer_iff, Subgroup.mem_bot]
  constructor
  · intro h
    apply Subtype.ext
    apply Units.ext
    have hm := congrArg Subtype.val h
    change (g.val : ℂ) * (z : ℂ) = (z : ℂ) at hm
    exact (mul_right_cancel₀ hz (hm.trans (one_mul _).symm))
  · rintro rfl
    exact one_smul _ _

theorem disk_action_smooth (g : C4) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun z : Disk => g • z) := by
  apply (ContMDiff.subtypeVal_comp_iff disk _).mp
  exact (contDiff_const.mul contDiff_id).contMDiff.comp contMDiff_subtype_val

theorem ellipse_action_smooth (g : C4) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun z : Ellipse => g • z) :=
  diskEllipse.contMDiff.comp ((disk_action_smooth g).comp diskEllipse.symm.contMDiff)

/-- The comparison on orbit spaces uses manifold smoothness in both directions. -/
def quotientComparison := manifoldQuotient diskEllipse diskEllipse_equivariant

theorem disk_topology :
    @DiffeologicalSpace.dTopology Disk (IsManifold.toDiffeology 𝓘(ℝ, ℂ) Disk) =
      (inferInstance : TopologicalSpace Disk) := IsManifold.dTopology_eq 𝓘(ℝ, ℂ) Disk

theorem ellipse_topology :
    @DiffeologicalSpace.dTopology Ellipse (IsManifold.toDiffeology 𝓘(ℝ, ℂ) Ellipse) =
      (inferInstance : TopologicalSpace Ellipse) := IsManifold.dTopology_eq 𝓘(ℝ, ℂ) Ellipse

theorem disk_induced : IsManifold.toDiffeology 𝓘(ℝ, ℂ) Disk =
    DiffeologicalSpace.induced (Subtype.val : Disk → ℂ) (NormedSpace.toDiffeology ℂ) := by
  rw [IsManifold.open_toDiffeology, IsManifold.toDiffeology_eq_normedSpace]

theorem ellipse_induced : IsManifold.toDiffeology 𝓘(ℝ, ℂ) Ellipse =
    DiffeologicalSpace.induced (Subtype.val : Ellipse → ℂ) (NormedSpace.toDiffeology ℂ) := by
  rw [IsManifold.open_toDiffeology, IsManifold.toDiffeology_eq_normedSpace]

/-- Conjugacy of actual manifold tangent maps for the disk-to-ellipse change. -/
theorem diskEllipse_tangent (g : C4) :
    tangentMap 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) diskEllipse ∘
        tangentMap 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun z : Disk => g • z) =
      tangentMap 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun z : Ellipse => g • z) ∘
        tangentMap 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) diskEllipse :=
  tangent_intertwining _ diskEllipse_equivariant diskEllipse.contMDiff g
    (disk_action_smooth g) (ellipse_action_smooth g)

/-- The open-submanifold charts identify every disk tangent space with `ℂ`.
In these coordinates the derivative is the same linear rotation as the action. -/
theorem disk_tangent (g : C4) (z : Disk) (v : ℂ) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun w : Disk => g • w) z v = (g.val : ℂ) * v := by
  have hval (w : Disk) : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (Subtype.val : Disk → ℂ) w =
      ContinuousLinearMap.id ℝ ℂ := mfderiv_extChartAt_self (I := 𝓘(ℝ, ℂ)) (x := w)
  have h : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
      ((Subtype.val : Disk → ℂ) ∘ (fun w : Disk => g • w)) z =
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
      ((fun w : ℂ => (g.val : ℂ) * w) ∘ (Subtype.val : Disk → ℂ)) z := rfl
  have hv : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (Subtype.val : Disk → ℂ) := contMDiff_subtype_val
  have hm : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun w : ℂ => (g.val : ℂ) * w) :=
    (contDiff_const.mul contDiff_id).contMDiff
  rw [mfderiv_comp z (hv.mdifferentiable (by simp) _)
    ((disk_action_smooth g).mdifferentiable (by simp) _),
    mfderiv_comp z (hm.mdifferentiable (by simp) _)
    (hv.mdifferentiable (by simp) _), hval, hval] at h
  have h' := congrArg (fun L => L v) h
  change mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun w : Disk => g • w) z v =
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun w : ℂ => (g.val : ℂ) * w) (z : ℂ) v at h'
  rw [h', mfderiv_eq_fderiv]
  change fderiv ℝ (fun w : ℂ => (g.val : ℂ) * w) z v = (g.val : ℂ) * v
  have hd := ((hasFDerivAt_id (𝕜 := ℝ) (z : ℂ)).const_mul (g.val : ℂ)).fderiv
  dsimp only [id] at hd
  rw [hd]
  rfl

/-- The tangent action is `v ↦ i^k*v`, for all four rotations and all disk points. -/
theorem disk_tangent_power (g : C4) : ∃ k < 4, ∀ (z : Disk) (v : ℂ),
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun w : Disk => g • w) z v = Complex.I ^ k * v := by
  obtain ⟨k, hk, he⟩ := scalar_eq_pow g
  exact ⟨k, hk, fun z v => (disk_tangent g z v).trans (by rw [he])⟩

/-- Conjugating the representation by real-axis scaling gives the ellipse action. -/
theorem ellipse_action_coordinates (g : C4) (z : Ellipse) :
    ((g • z : Ellipse) : ℂ) = stretch ((g.val : ℂ) * stretch.symm z) := rfl

/-- The transported action agrees with the independent ellipse formula. -/
theorem ellipse_quarterTurn_coordinates (z : Ellipse) :
    ((quarterTurn • z : Ellipse) : ℂ) = ellipseQuarterTurn z := by
  rw [ellipse_action_coordinates, quarterTurn_scalar]
  apply Complex.ext <;> simp [ellipseQuarterTurn, Complex.mul_re, Complex.mul_im]

/-- Derivative of the coordinate change in the open-submanifold charts. -/
theorem diskEllipse_derivative (z : Disk) (v : ℂ) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) diskEllipse z v = stretch v := by
  have hval (w : Ellipse) : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
      (Subtype.val : Ellipse → ℂ) w = ContinuousLinearMap.id ℝ ℂ :=
    mfderiv_extChartAt_self (I := 𝓘(ℝ, ℂ)) (x := w)
  have hdisk : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
      (Subtype.val : Disk → ℂ) z = ContinuousLinearMap.id ℝ ℂ :=
    mfderiv_extChartAt_self (I := 𝓘(ℝ, ℂ)) (x := z)
  have hv : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (Subtype.val : Ellipse → ℂ) :=
    contMDiff_subtype_val
  have hd : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (Subtype.val : Disk → ℂ) :=
    contMDiff_subtype_val
  have hs : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ stretch := stretch.contDiff.contMDiff
  have he : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
      ((Subtype.val : Ellipse → ℂ) ∘ diskEllipse) z =
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
      (stretch ∘ (Subtype.val : Disk → ℂ)) z := rfl
  rw [mfderiv_comp z (hv.mdifferentiable (by simp) _)
    (diskEllipse.contMDiff.mdifferentiable (by simp) _),
    mfderiv_comp z (hs.mdifferentiable (by simp) _)
    (hd.mdifferentiable (by simp) _), hval, hdisk, mfderiv_eq_fderiv,
    stretch.hasFDerivAt.fderiv] at he
  exact congrArg (fun L => L v) he

/-- The tangent comparison determines the ellipse derivative at every point. -/
theorem ellipse_tangent (g : C4) (z : Ellipse) (v : ℂ) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun w : Ellipse => g • w) z v =
      stretch ((g.val : ℂ) * stretch.symm v) := by
  have h := congrFun (diskEllipse_tangent g)
    (⟨diskEllipse.symm z, stretch.symm v⟩ : TangentBundle 𝓘(ℝ, ℂ) Disk)
  have hv := congrArg (fun p : TangentBundle 𝓘(ℝ, ℂ) Ellipse => p.2) h
  dsimp only [Function.comp_apply, tangentMap] at hv
  rw [disk_tangent, diskEllipse_derivative, diskEllipse_derivative,
    stretch.apply_symm_apply, diskEllipse.apply_symm_apply] at hv
  exact hv.symm

/-- The actual manifold derivative has coordinates `(-2*v.im, v.re/2)`. -/
theorem ellipse_quarterTurn_tangent (z : Ellipse) (v : ℂ) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun w : Ellipse => quarterTurn • w) z v =
      ellipseQuarterTurn v := by
  rw [ellipse_tangent, quarterTurn_scalar]
  apply Complex.ext <;> simp [ellipseQuarterTurn, Complex.mul_re, Complex.mul_im]

def half : Disk := ⟨(1 / 2 : ℂ), by
  norm_num [disk, Metric.mem_ball, dist_zero_right, norm_div]⟩

theorem diskEllipse_nonidentity : (diskEllipse half : ℂ) ≠ (half : ℂ) := by
  intro h
  have hr := congrArg Complex.re h
  change (stretch (1 / 2 : ℂ)).re = (1 / 2 : ℂ).re at hr
  simp only [stretch_re] at hr
  norm_num at hr

end Orbifolds.QuarterTurn

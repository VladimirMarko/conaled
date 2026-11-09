import Applications.Orbifold.Kinetic.Regularity

noncomputable section
open scoped ContDiff
namespace Orbifold.Kinetic
open DiskConnection

def legendreMinus (h : ℝ) (p : ℂ × ℂ) : ℂ × ℂ := (p.1,-d1 h p.1 p.2)
def legendrePlus (h : ℝ) (p : ℂ × ℂ) : ℂ × ℂ := (p.2,d2 h p.1 p.2)

def minusBlock (c : ℝ) (hc : c ≠ 0) : (ℂ × ℂ) ≃L[ℝ] (ℂ × ℂ) where
  toFun p := (p.1,c • (p.2-p.1))
  invFun p := (p.1,p.1+c⁻¹ • p.2)
  map_add' p q := by ext <;> simp [smul_add,smul_sub] <;> abel
  map_smul' r p := by ext <;> simp [smul_sub,smul_smul,mul_comm] <;> ring
  left_inv p := by simp [smul_smul,hc]
  right_inv p := by simp [smul_smul,hc]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def plusBlock (c : ℝ) (hc : c ≠ 0) : (ℂ × ℂ) ≃L[ℝ] (ℂ × ℂ) where
  toFun p := (p.2,c • (p.2-p.1))
  invFun p := (p.1-c⁻¹ • p.2,p.1)
  map_add' p q := by ext <;> simp [smul_add,smul_sub] <;> abel
  map_smul' r p := by ext <;> simp [smul_sub,smul_smul,mul_comm] <;> ring
  left_inv p := by simp [smul_smul,hc]
  right_inv p := by simp [smul_smul,hc]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem diagonalScale_nonzero {h : ℝ} {x : ℂ} (hh : h ≠ 0) (hg : gap x ≠ 0) :
    diagonalScale h x ≠ 0 := div_ne_zero (by norm_num) (mul_ne_zero hh (pow_ne_zero 2 hg))

theorem minus_derivative (h : ℝ) (x : ℂ) (hh : h ≠ 0) (hg : gap x ≠ 0) :
    HasFDerivAt (legendreMinus h)
      (minusBlock (diagonalScale h x) (diagonalScale_nonzero hh hg) : (ℂ × ℂ) →L[ℝ] (ℂ × ℂ)) (x,x) := by
  convert (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.prodMk
    (d1_joint_diagonal h x hh hg).neg using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro p
    simp [minusBlock,deltaLinear]

theorem plus_derivative (h : ℝ) (x : ℂ) (hh : h ≠ 0) (hg : gap x ≠ 0) :
    HasFDerivAt (legendrePlus h)
      (plusBlock (diagonalScale h x) (diagonalScale_nonzero hh hg) : (ℂ × ℂ) →L[ℝ] (ℂ × ℂ)) (x,x) := by
  convert (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.prodMk
    (d2_joint_diagonal h x hh hg) using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro p
    simp [plusBlock,deltaLinear]

theorem d1_smooth (h : ℝ) (p : ℂ × ℂ) (hh : h ≠ 0)
    (hg : gap (midpoint p.1 p.2) ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : ℂ × ℂ => d1 h q.1 q.2) p := by
  have hgap := (gap_smooth.comp midpoint_smooth).contDiffAt (x := p)
  have ha := (contDiffAt_const (c := (4 : ℝ))).div (contDiffAt_const.mul (hgap.pow 2))
    (mul_ne_zero hh (pow_ne_zero 2 hg))
  have hb := ((contDiffAt_const (c := (4 : ℝ))).mul (normSq_smooth.comp (contDiff_snd.sub contDiff_fst)).contDiffAt) |>.div
    (contDiffAt_const.mul (hgap.pow 3)) (mul_ne_zero hh (pow_ne_zero 3 hg))
  exact (ha.neg.smul (contDiffAt_snd.sub contDiffAt_fst)).add (hb.smul midpoint_smooth.contDiffAt)

theorem d2_smooth (h : ℝ) (p : ℂ × ℂ) (hh : h ≠ 0)
    (hg : gap (midpoint p.1 p.2) ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : ℂ × ℂ => d2 h q.1 q.2) p := by
  have hgap := (gap_smooth.comp midpoint_smooth).contDiffAt (x := p)
  have ha := (contDiffAt_const (c := (4 : ℝ))).div (contDiffAt_const.mul (hgap.pow 2))
    (mul_ne_zero hh (pow_ne_zero 2 hg))
  have hb := ((contDiffAt_const (c := (4 : ℝ))).mul (normSq_smooth.comp (contDiff_snd.sub contDiff_fst)).contDiffAt) |>.div
    (contDiffAt_const.mul (hgap.pow 3)) (mul_ne_zero hh (pow_ne_zero 3 hg))
  exact (ha.smul (contDiffAt_snd.sub contDiffAt_fst)).add (hb.smul midpoint_smooth.contDiffAt)

/-- The physically admitted endpoints form an open set; h is positive in every branch. -/
def endpointDomain : Set (ℂ × ℂ) := {p | Complex.normSq p.1 < 1 ∧ Complex.normSq p.2 < 1}

theorem endpointDomain_open : IsOpen endpointDomain :=
  (isOpen_lt (normSq_smooth.continuous.comp continuous_fst) continuous_const).inter
    (isOpen_lt (normSq_smooth.continuous.comp continuous_snd) continuous_const)

theorem minus_smooth (h : ℝ) (x : ℂ) (hh : h ≠ 0) (hg : gap x ≠ 0) :
    ContDiffAt ℝ ∞ (legendreMinus h) (x,x) :=
  contDiffAt_fst.prodMk (d1_smooth h (x,x) hh (by simpa using hg)).neg

theorem plus_smooth (h : ℝ) (x : ℂ) (hh : h ≠ 0) (hg : gap x ≠ 0) :
    ContDiffAt ℝ ∞ (legendrePlus h) (x,x) :=
  contDiffAt_snd.prodMk (d2_smooth h (x,x) hh (by simpa using hg))

def minusBranch (h : ℝ) (x : ℂ) (hh : 0 < h) (hx : Complex.normSq x < 1) :
    OpenPartialHomeomorph (ℂ × ℂ) (ℂ × ℂ) :=
  ((minus_smooth h x (ne_of_gt hh) (ne_of_gt (sub_pos.mpr hx))).toOpenPartialHomeomorph
    (legendreMinus h) (minus_derivative h x (ne_of_gt hh) (ne_of_gt (sub_pos.mpr hx)))
    (by simp)).restr endpointDomain

def plusBranch (h : ℝ) (x : ℂ) (hh : 0 < h) (hx : Complex.normSq x < 1) :
    OpenPartialHomeomorph (ℂ × ℂ) (ℂ × ℂ) :=
  ((plus_smooth h x (ne_of_gt hh) (ne_of_gt (sub_pos.mpr hx))).toOpenPartialHomeomorph
    (legendrePlus h) (plus_derivative h x (ne_of_gt hh) (ne_of_gt (sub_pos.mpr hx)))
    (by simp)).restr endpointDomain

theorem minusBranch_contains (h : ℝ) (x : ℂ) (hh : 0 < h) (hx : Complex.normSq x < 1) :
    (x,x) ∈ (minusBranch h x hh hx).source := by
  rw [minusBranch,OpenPartialHomeomorph.restr_source' _ _ endpointDomain_open]
  exact ⟨ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _,hx,hx⟩

theorem plusBranch_contains (h : ℝ) (x : ℂ) (hh : 0 < h) (hx : Complex.normSq x < 1) :
    (x,x) ∈ (plusBranch h x hh hx).source := by
  rw [plusBranch,OpenPartialHomeomorph.restr_source' _ _ endpointDomain_open]
  exact ⟨ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _,hx,hx⟩

theorem minusBranch_inverse (h : ℝ) (x : ℂ) (hh : 0 < h) (hx : Complex.normSq x < 1)
    {p : ℂ × ℂ} (hp : p ∈ (minusBranch h x hh hx).source) :
    (minusBranch h x hh hx).symm (legendreMinus h p) = p :=
  (minusBranch h x hh hx).left_inv hp

theorem plusBranch_inverse (h : ℝ) (x : ℂ) (hh : 0 < h) (hx : Complex.normSq x < 1)
    {p : ℂ × ℂ} (hp : p ∈ (plusBranch h x hh hx).source) :
    (plusBranch h x hh hx).symm (legendrePlus h p) = p :=
  (plusBranch h x hh hx).left_inv hp

theorem minusBranch_unique (h : ℝ) (x : ℂ) (hh : 0 < h) (hx : Complex.normSq x < 1)
    {p q : ℂ × ℂ} (hp : p ∈ (minusBranch h x hh hx).source)
    (hq : q ∈ (minusBranch h x hh hx).source) (he : legendreMinus h p = legendreMinus h q) :
    p = q := (minusBranch h x hh hx).injOn hp hq he

theorem plusBranch_unique (h : ℝ) (x : ℂ) (hh : 0 < h) (hx : Complex.normSq x < 1)
    {p q : ℂ × ℂ} (hp : p ∈ (plusBranch h x hh hx).source)
    (hq : q ∈ (plusBranch h x hh hx).source) (he : legendrePlus h p = legendrePlus h q) :
    p = q := (plusBranch h x hh hx).injOn hp hq he

theorem minus_inverse_smooth (h : ℝ) (x : ℂ) (hh : 0 < h) (hx : Complex.normSq x < 1) :
    ContDiffAt ℝ ∞ (minusBranch h x hh hx).symm (legendreMinus h (x,x)) :=
  (minus_smooth h x (ne_of_gt hh) (ne_of_gt (sub_pos.mpr hx))).to_localInverse
    (minus_derivative h x (ne_of_gt hh) (ne_of_gt (sub_pos.mpr hx))) (by simp)

theorem plus_inverse_smooth (h : ℝ) (x : ℂ) (hh : 0 < h) (hx : Complex.normSq x < 1) :
    ContDiffAt ℝ ∞ (plusBranch h x hh hx).symm (legendrePlus h (x,x)) :=
  (plus_smooth h x (ne_of_gt hh) (ne_of_gt (sub_pos.mpr hx))).to_localInverse
    (plus_derivative h x (ne_of_gt hh) (ne_of_gt (sub_pos.mpr hx))) (by simp)

end Orbifold.Kinetic

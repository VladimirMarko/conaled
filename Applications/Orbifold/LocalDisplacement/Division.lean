import Applications.Orbifold.LocalDisplacement

/-! Explicit local division branches. Branch membership checks the solved point;
no numerical inverse solver or decidable real membership is asserted. -/
noncomputable section
open scoped ComplexConjugate
namespace Orbifold.LocalDisplacement

def leftDivide (a z : ℂ) : ℂ := gyroAdd (-a) z

theorem left_inverse (a b : ℂ) (ha : Complex.normSq a < 1)
    (hb : Complex.normSq b < 1) : leftDivide a (gyroAdd a b) = b := by
  have hd := disk_denominator a b ha hb
  have hn : Complex.normSq (-a) < 1 := by simpa using ha
  have he := disk_denominator (-a) (gyroAdd a b) hn (gyroAdd_inside a b ha hb)
  dsimp [leftDivide, gyroAdd] at *
  simp only [map_neg] at *
  apply (div_eq_iff he).mpr
  have hq := div_mul_cancel₀ (a+b) hd
  linear_combination hq

/-- Solve x + b = z * (1 + conj x * b), a real-linear equation in x. -/
def rightDivide (b z : ℂ) : ℂ :=
  ((z-b) + (z*b) * conj (z-b)) / (1 - (z*b) * conj (z*b))

theorem right_denominator (b z : ℂ) (hb : Complex.normSq b < 1)
    (hz : Complex.normSq z < 1) : 1 - (z*b) * conj (z*b) ≠ 0 := by
  rw [Complex.mul_conj]
  have h : Complex.normSq (z*b) < 1 := by
    rw [map_mul]
    nlinarith [Complex.normSq_nonneg b, Complex.normSq_nonneg z]
  exact_mod_cast ne_of_gt (sub_pos.mpr h)

theorem right_linear (b z : ℂ) (hb : Complex.normSq b < 1)
    (hz : Complex.normSq z < 1) :
    rightDivide b z - z*b*conj (rightDivide b z) = z-b := by
  have hd := right_denominator b z hb hz
  have hc : conj (1 - (z*b) * conj (z*b)) = 1 - (z*b) * conj (z*b) := by
    simp [mul_comm]
  unfold rightDivide
  rw [map_div₀, hc]
  field_simp
  simp only [map_add, map_sub, map_mul, Complex.conj_conj]
  ring

theorem right_solve (b z : ℂ) (hb : Complex.normSq b < 1)
    (hz : Complex.normSq z < 1) (hx : Complex.normSq (rightDivide b z) < 1) :
    gyroAdd (rightDivide b z) b = z := by
  apply (div_eq_iff (disk_denominator _ _ hx hb)).mpr
  have h := right_linear b z hb hz
  linear_combination h

/-- Actual branch domains, including the computed solution. -/
def LeftBranch (a z : ℂ) := a ∈ U ∧ z ∈ U ∧ leftDivide a z ∈ U

def RightBranch (b z : ℂ) := b ∈ U ∧ z ∈ U ∧ rightDivide b z ∈ U

theorem left_solve {a z : ℂ} (h : LeftBranch a z) : gyroAdd a (leftDivide a z) = z := by
  have hn : Complex.normSq (-a) < 1 := by simpa using mem_disk h.1
  simpa [leftDivide] using left_inverse (-a) z hn (mem_disk h.2.1)

theorem left_branch_admissible {a z : ℂ} (h : LeftBranch a z) :
    Admissible a (leftDivide a z) := ⟨h.1,h.2.2,by rw [left_solve h]; exact h.2.1⟩

theorem right_branch_admissible {b z : ℂ} (h : RightBranch b z) :
    Admissible (rightDivide b z) b :=
  ⟨h.2.2,h.1,by rw [right_solve _ _ (mem_disk h.1) (mem_disk h.2.1) (mem_disk h.2.2)]; exact h.2.1⟩

theorem left_unique {a z x : ℂ} (ha : a ∈ U) (hx : x ∈ U)
    (he : gyroAdd a x = z) : leftDivide a z = x := by
  rw [← he]
  exact left_inverse a x (mem_disk ha) (mem_disk hx)

theorem right_unique {b z x : ℂ} (hb : b ∈ U) (hz : z ∈ U) (hx : x ∈ U)
    (he : gyroAdd x b = z) : rightDivide b z = x := by
  have hlin : x - z*b*conj x = z-b := by
    have h := (div_eq_iff (disk_denominator x b (mem_disk hx) (mem_disk hb))).mp he
    linear_combination h
  have hc := congrArg conj hlin
  simp only [map_sub, map_mul, Complex.conj_conj] at hc
  apply (div_eq_iff (right_denominator b z (mem_disk hb) (mem_disk hz))).mpr
  simp only [map_sub, map_mul]
  linear_combination -hlin - (z*b)*hc

theorem leftDivide_continuousAt {a z : ℂ} (ha : a ∈ U) (hz : z ∈ U) :
    ContinuousAt (fun p : ℂ × ℂ => leftDivide p.1 p.2) (a,z) := by
  have hn : -a ∈ U := by simpa [U] using ha
  have hm : ContinuousAt (fun p : ℂ × ℂ => (-p.1,p.2)) (a,z) :=
    continuousAt_fst.neg.prodMk continuousAt_snd
  exact (gyroAdd_contDiffAt hn hz).continuousAt.comp (f := fun p : ℂ × ℂ => (-p.1,p.2)) hm

theorem rightDivide_continuousAt {b z : ℂ} (hb : b ∈ U) (hz : z ∈ U) :
    ContinuousAt (fun p : ℂ × ℂ => rightDivide p.1 p.2) (b,z) := by
  unfold rightDivide
  fun_prop (disch := exact right_denominator b z (mem_disk hb) (mem_disk hz))

theorem leftBranch_open : IsOpen {p : ℂ × ℂ | LeftBranch p.1 p.2} := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have ha := (isOpen_U.preimage continuous_fst).mem_nhds hp.1
  have hz := (isOpen_U.preimage continuous_snd).mem_nhds hp.2.1
  have hx := (leftDivide_continuousAt hp.1 hp.2.1) (isOpen_U.mem_nhds hp.2.2)
  filter_upwards [ha,hz,hx] with q hqa hqz hqx using ⟨hqa,hqz,hqx⟩

theorem rightBranch_open : IsOpen {p : ℂ × ℂ | RightBranch p.1 p.2} := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hb := (isOpen_U.preimage continuous_fst).mem_nhds hp.1
  have hz := (isOpen_U.preimage continuous_snd).mem_nhds hp.2.1
  have hx := (rightDivide_continuousAt hp.1 hp.2.1) (isOpen_U.mem_nhds hp.2.2)
  filter_upwards [hb,hz,hx] with q hqb hqz hqx using ⟨hqb,hqz,hqx⟩

theorem leftBranch_near_origin : {p : ℂ × ℂ | LeftBranch p.1 p.2} ∈ nhds (0,0) := by
  apply leftBranch_open.mem_nhds
  norm_num [LeftBranch,leftDivide,U]

theorem rightBranch_near_origin : {p : ℂ × ℂ | RightBranch p.1 p.2} ∈ nhds (0,0) := by
  apply rightBranch_open.mem_nhds
  norm_num [RightBranch,rightDivide,U]

end Orbifold.LocalDisplacement

import Applications.Orbifold.StandardForm
import Applications.Orbifolds.QuarterTurn

/-! Disk coordinates of negative lines for the experimental projective model.
The disk carrier is shared with the conventional quarter-turn application. -/
noncomputable section
open scoped ComplexConjugate
namespace Orbifold
abbrev Disk := Orbifolds.QuarterTurn.Disk

theorem disk_mem (z : ℂ) : z ∈ Orbifolds.QuarterTurn.disk ↔ Complex.normSq z < 1 := by
  change dist z 0 < 1 ↔ _
  rw [dist_zero_right, Complex.normSq_eq_norm_sq]
  constructor <;> intro h
  · nlinarith [norm_nonneg z]
  · nlinarith [norm_nonneg z]

theorem diskForm_self (v : DiskVector) :
    (diskForm v v).re = Complex.normSq (v 0) - Complex.normSq (v 1) := by
  simp [diskForm_apply, Complex.normSq_apply, Complex.mul_re]

theorem negative_last_ne_zero (v : DiskVector) (h : (diskForm v v).re < 0) :
    v 1 ≠ 0 := by
  intro hz
  rw [diskForm_self, hz] at h
  have hn := Complex.normSq_nonneg (v 0)
  simp only [map_zero, sub_zero] at h
  linarith

/-- Projective validity is negative form value, not merely a nonzero vector. -/
def diskOfVector (v : DiskVector) (h : (diskForm v v).re < 0) : Disk :=
  ⟨v 0 / v 1, (disk_mem _).mpr (by
    rw [Complex.normSq_div, div_lt_one (Complex.normSq_pos.mpr (negative_last_ne_zero v h))]
    linarith [diskForm_self v])⟩

def lineOfDisk (z : Disk) : NegativeLine diskForm :=
  ⟨Projectivization.mk ℂ ![z.val, 1] (by intro h; have := congrFun h 1; simp at this),
    (negative_mk_iff _ _ _).mpr (by
      rw [diskForm_self]
      simpa using sub_neg.mpr ((disk_mem _).mp z.property))⟩

def diskOfLine (p : NegativeLine diskForm) : Disk :=
  diskOfVector p.val.rep ((negative_mk_iff _ _ p.val.rep_nonzero).mp (by
    simpa only [Projectivization.mk_rep] using p.property))

theorem diskOfLine_eq (p : NegativeLine diskForm) (v : DiskVector) (hv : v ≠ 0)
    (hp : Projectivization.mk ℂ v hv = p.val) :
    (diskOfLine p : ℂ) = v 0 / v 1 := by
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ p.val.rep_nonzero hv).mp
    ((Projectivization.mk_rep p.val).trans hp.symm)
  change p.val.rep 0 / p.val.rep 1 = _
  rw [← ha]
  simp only [Units.smul_def, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ a.ne_zero

/-- The standard-form negative lines are exactly the open disk. -/
def diskEquiv : NegativeLine diskForm ≃ Disk where
  toFun := diskOfLine
  invFun := lineOfDisk
  left_inv p := by
    apply Subtype.ext
    rw [← Projectivization.mk_rep p.val]
    apply (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mpr
    have hn := negative_last_ne_zero p.val.rep
      ((negative_mk_iff _ _ p.val.rep_nonzero).mp (by simpa only [Projectivization.mk_rep] using p.property))
    refine ⟨(Units.mk0 (p.val.rep 1) hn)⁻¹, ?_⟩
    ext i; fin_cases i
    · change (p.val.rep 1)⁻¹ * p.val.rep 0 = p.val.rep 0 / p.val.rep 1
      simp [div_eq_mul_inv, mul_comm]
    · change (p.val.rep 1)⁻¹ * p.val.rep 1 = 1
      exact inv_mul_cancel₀ hn
  right_inv z := by
    apply Subtype.ext
    rw [diskOfLine_eq (lineOfDisk z) ![z.val, 1]
      (by intro h; have := congrFun h 1; simp at this) rfl]
    simp

end Orbifold

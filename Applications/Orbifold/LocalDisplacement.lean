import Applications.Bracketing.PartialEvaluation
import Applications.Orbifold.PoseConnection
import Applications.Orbifold.QuarterTurn
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Local Möbius displacement arithmetic. Parenthesization and alignment are data;
this endpoint interface does not assert a geodesic or path-transport contract. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped ComplexConjugate ContDiff
namespace Orbifold.LocalDisplacement

/-- Strict half-radius disk. -/
def U : Set ℂ := {z | Complex.normSq z < 1/4}

theorem zero_mem : (0 : ℂ) ∈ U := by norm_num [U]

theorem isOpen_U : IsOpen U := isOpen_lt Complex.continuous_normSq continuous_const

theorem mem_disk {z : ℂ} (h : z ∈ U) : Complex.normSq z < 1 := by
  dsimp [U] at h
  linarith

theorem strict_subdomain : U ⊂ {z : ℂ | Complex.normSq z < 1} := by
  apply Set.ssubset_iff_subset_ne.mpr
  refine ⟨fun _ h => mem_disk h, ?_⟩
  intro he
  have h : (3/4 : ℂ) ∈ U := by rw [he]; norm_num [Complex.normSq_apply]
  norm_num [U,Complex.normSq_apply] at h

def Admissible (a b : ℂ) : Prop := a ∈ U ∧ b ∈ U ∧ gyroAdd a b ∈ U

@[simp] theorem zero_left (b : ℂ) : gyroAdd 0 b = b := by simp [gyroAdd]
@[simp] theorem zero_right (a : ℂ) : gyroAdd a 0 = a := by simp [gyroAdd]

theorem unit_admissible {a : ℂ} (h : a ∈ U) : Admissible 0 a ∧ Admissible a 0 := by
  simpa [Admissible] using And.intro (And.intro zero_mem (And.intro h h))
    (And.intro h (And.intro zero_mem h))

theorem gyroAdd_contDiffAt {a b : ℂ} (ha : a ∈ U) (hb : b ∈ U) :
    ContDiffAt ℝ ∞ (fun p : ℂ × ℂ => gyroAdd p.1 p.2) (a,b) := by
  unfold gyroAdd
  have hc : ContDiff ℝ ∞ (fun p : ℂ × ℂ => conj p.1) :=
    Complex.conjCLE.contDiff.comp contDiff_fst
  have hn : ContDiffAt ℝ ∞ (fun p : ℂ × ℂ => p.1 + p.2) (a,b) :=
    contDiffAt_fst.add contDiffAt_snd
  have hd : ContDiffAt ℝ ∞ (fun p : ℂ × ℂ => 1 + conj p.1 * p.2) (a,b) :=
    contDiffAt_const.add (hc.contDiffAt.mul contDiffAt_snd)
  convert hn.mul (hd.inv (disk_denominator a b (mem_disk ha) (mem_disk hb))) using 1
  ext p
  simp only [div_eq_mul_inv, Pi.inv_apply]

theorem admissible_open : IsOpen {p : ℂ × ℂ | Admissible p.1 p.2} := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have ha : ∀ᶠ q : ℂ × ℂ in nhds p, q.1 ∈ U :=
    (isOpen_U.preimage continuous_fst).mem_nhds hp.1
  have hb : ∀ᶠ q : ℂ × ℂ in nhds p, q.2 ∈ U :=
    (isOpen_U.preimage continuous_snd).mem_nhds hp.2.1
  have hc := (gyroAdd_contDiffAt hp.1 hp.2.1).continuousAt (isOpen_U.mem_nhds hp.2.2)
  filter_upwards [ha, hb, hc] with q hqa hqb hqc using ⟨hqa,hqb,hqc⟩

theorem admissible_near_origin : {p : ℂ × ℂ | Admissible p.1 p.2} ∈ nhds (0,0) :=
  admissible_open.mem_nhds (unit_admissible zero_mem).1

end Orbifold.LocalDisplacement

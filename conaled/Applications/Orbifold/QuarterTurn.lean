import Applications.Orbifold.Pose

/-! Quarter-turn relabeling of framed disk poses. The action groupoid keeps
symmetry labels; only prescribed right increments descend to the orbit space. -/
noncomputable section
open scoped ComplexConjugate
open MulAction CategoryTheory
namespace Orbifold
namespace QuarterTurn
abbrev C4 := Orbifolds.QuarterTurn.C4

theorem phase_unit (g : C4) : Complex.normSq (g.val : ℂ) = 1 := by
  rw [Complex.normSq_eq_norm_sq, Complex.norm_eq_one_of_mem_rootsOfUnity g.property]
  norm_num

def rotation (g : C4) : Pose := ⟨0, g.val, by norm_num, phase_unit g⟩

def rotate (g : C4) (p : Pose) : Pose where
  a := (g.val : ℂ) * p.a
  u := (g.val : ℂ) * p.u
  inside := by simpa [map_mul, phase_unit] using p.inside
  unit := by simp [map_mul, phase_unit, p.unit]

@[ext] theorem pose_ext {p q : Pose} (ha : p.a = q.a) (hu : p.u = q.u) : p = q := by
  cases p; cases q; simp_all

instance : MulAction C4 Pose where
  smul := rotate
  one_smul p := by
    change rotate 1 p = p
    apply pose_ext <;> simp [rotate]
  mul_smul g h p := by
    change rotate (g * h) p = rotate g (rotate h p)
    apply pose_ext <;> simp [rotate, mul_assoc]

theorem rotate_eq_comp (g : C4) (p : Pose) : g • p = (rotation g).comp p := by
  change rotate g p = _
  apply pose_ext <;> simp [rotate, rotation, Pose.comp, gyroAdd, gyration]

theorem right_increment_equivariant (h : Pose) (g : C4) (p : Pose) :
    (g • p).comp h = g • (p.comp h) := by
  simp only [rotate_eq_comp, Pose.comp_assoc]

/-- A labeled arrow remains labeled after a prescribed body increment. -/
def incrementFunctor (h : Pose) : ActionCategory C4 Pose ⥤ ActionCategory C4 Pose :=
  Orbifolds.actionFunctor (MonoidHom.id C4) (fun p : Pose => p.comp h) (right_increment_equivariant h)

theorem increment_label (h : Pose) {p q : ActionCategory C4 Pose} (f : p ⟶ q) :
    ((incrementFunctor h).map f).hom = f.hom := rfl

/-- This update is well-defined on left orbits; it is not orbit multiplication. -/
def incrementSquare (h : Pose) :=
  Orbifolds.orbitSquare (MonoidHom.id C4) (fun p : Pose => p.comp h) (right_increment_equivariant h)

theorem increment_identity (x : Quotient (orbitRel C4 Pose)) :
    (incrementSquare Pose.identity).spec x = x := by
  induction x using Quotient.inductionOn with
  | h p =>
    change Quotient.mk _ (p.comp Pose.identity) = Quotient.mk _ p
    congr 1
    apply Pose.motion_injective
    simp [Pose.motion_comp]

theorem increment_comp (h k : Pose) (x : Quotient (orbitRel C4 Pose)) :
    (incrementSquare k).spec ((incrementSquare h).spec x) =
      (incrementSquare (h.comp k)).spec x := by
  induction x using Quotient.inductionOn with
  | h p =>
    change Quotient.mk _ ((p.comp h).comp k) = Quotient.mk _ (p.comp (h.comp k))
    rw [Pose.comp_assoc]

theorem pose_stabilizer (p : Pose) : stabilizer C4 p = ⊥ := by
  ext g
  simp only [mem_stabilizer_iff, Subgroup.mem_bot]
  constructor
  · intro h
    have hu := congrArg Pose.u h
    change (g.val : ℂ) * p.u = p.u at hu
    have hp : p.u ≠ 0 := by intro h; have := p.unit; simp [h] at this
    have hg : (g.val : ℂ) = 1 := mul_right_cancel₀ hp (hu.trans (one_mul _).symm)
    apply Subtype.ext; apply Units.ext
    exact hg
  · rintro rfl; exact one_smul _ _

/-- The same C4 disk action supplies both apex and regular-point isotropy. -/
theorem origin_stabilizer : stabilizer C4 Orbifolds.QuarterTurn.origin = ⊤ :=
  Orbifolds.QuarterTurn.origin_stabilizer

theorem nonzero_stabilizer (z : Disk) (hz : z.val ≠ 0) : stabilizer C4 z = ⊥ :=
  Orbifolds.QuarterTurn.nonzero_stabilizer z hz

theorem rotate_motion (g : C4) (p : Pose) :
    (g • p).motion = (rotation g).motion * p.motion := by
  rw [rotate_eq_comp, Pose.motion_comp]

theorem matrix_relabel_increment (g : C4) (p h : Pose) :
    MatrixBackend.Hermitian.decode Pose.standardBasis diskForm ((g • p).certified * h.certified) =
      (rotation g).motion * (p.comp h).motion := by
  rw [map_mul]
  change (g • p).motion * h.motion = _
  rw [rotate_motion, Pose.motion_comp, mul_assoc]

/-- The invalid independent-representative addition is an exact rational calculation. -/
theorem quotient_addition_values :
    gyroAdd (1/5 : ℂ) (1/5) = 5/13 ∧ gyroAdd (1/5 : ℂ) (-1/5) = 0 := by
  norm_num [gyroAdd, map_ofNat]

def fifth : Disk := ⟨1/5, (disk_mem _).mpr (by norm_num)⟩
def minusFifth : Disk := ⟨-1/5, (disk_mem _).mpr (by norm_num)⟩

theorem second_inputs_same_orbit :
    Quotient.mk (orbitRel C4 Disk) fifth = Quotient.mk _ minusFifth := by
  apply Quotient.sound
  apply (mem_orbit_iff).mpr
  refine ⟨Orbifolds.QuarterTurn.quarterTurn ^ 2, ?_⟩
  apply Subtype.ext
  change (Complex.I ^ 2) * (-1/5 : ℂ) = 1/5
  norm_num

def position (p : Pose) : Disk := ⟨p.a, (disk_mem _).mpr p.inside⟩

theorem position_equivariant (g : C4) (p : Pose) : position (g • p) = g • position p := rfl

def positionFunctor : ActionCategory C4 Pose ⥤ ActionCategory C4 Disk :=
  Orbifolds.actionFunctor (MonoidHom.id C4) position position_equivariant

def doubledFifth : Disk := ⟨5/13, (disk_mem _).mpr (by norm_num)⟩

theorem addition_outputs_different_orbits :
    Quotient.mk (orbitRel C4 Disk) doubledFifth ≠
      Quotient.mk _ Orbifolds.QuarterTurn.origin := by
  intro h
  obtain ⟨g, hg⟩ := (mem_orbit_iff).mp (Quotient.exact h)
  have := congrArg Subtype.val hg
  change (g.val : ℂ) * 0 = (5/13 : ℂ) at this
  norm_num at this

end QuarterTurn
end Orbifold

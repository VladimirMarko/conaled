import Applications.Orbifold.Clifford.Rotor

/-! Certified boosts and chosen rotation lifts. Square roots here are exact
real operations, not an executable acquisition or rounded validation routine. -/
noncomputable section
namespace Orbifold.Clifford.Rotor

/-- A chosen rotation lift; `(a,d)` and `(-a,-d)` have the same geometric turn. -/
def rotation (a d : ℝ) (h : a^2+d^2=1) : Rotor :=
  ⟨⟨a,0,0,d⟩, by simpa [norm] using h⟩

/-- A positive-time boost certificate, stated independently of the disk action. -/
structure Boost where
  t : ℝ
  x : ℝ
  y : ℝ
  positive : 0 < t
  normalized : t^2-x^2-y^2=1

def Boost.rotor (b : Boost) : Rotor := ⟨⟨b.t,b.x,b.y,0⟩, by simpa [norm] using b.normalized⟩

/-- The admitted carrier has a constructive boost/rotation generation witness. -/
inductive Generated : Rotor → Prop
  | rotation (a d : ℝ) (h : a^2+d^2=1) : Generated (rotation a d h)
  | boost (b : Boost) : Generated b.rotor
  | comp {r s : Rotor} : Generated r → Generated s → Generated (comp r s)

private theorem root_sq (r : Rotor) : (Real.sqrt (scale r))^2 = scale r :=
  Real.sq_sqrt (le_of_lt (scale_pos r))
private theorem root_ne (r : Rotor) : Real.sqrt (scale r) ≠ 0 :=
  ne_of_gt (Real.sqrt_pos.mpr (scale_pos r))

def boostPart (r : Rotor) : Boost where
  t := Real.sqrt (scale r)
  x := (r.val.a*r.val.b+r.val.c*r.val.d) / Real.sqrt (scale r)
  y := (r.val.a*r.val.c-r.val.b*r.val.d) / Real.sqrt (scale r)
  positive := Real.sqrt_pos.mpr (scale_pos r)
  normalized := by
    have hn := r.prop
    have hh := root_sq r
    have hr := root_ne r
    dsimp [norm] at hn
    field_simp
    rw [hh]
    have hh4 : (Real.sqrt (scale r))^4 = (scale r)^2 := by
      calc _ = ((Real.sqrt (scale r))^2)^2 := by ring
           _ = _ := by rw [hh]
    rw [hh4]
    dsimp [scale]
    linear_combination (r.val.a^2+r.val.d^2)*hn

theorem rotationPart_unit (r : Rotor) :
    (r.val.a / Real.sqrt (scale r))^2 + (r.val.d / Real.sqrt (scale r))^2 = 1 := by
  have hr := root_ne r
  field_simp
  rw [root_sq]
  rfl

def rotationPart (r : Rotor) : Rotor :=
  rotation (r.val.a / Real.sqrt (scale r)) (r.val.d / Real.sqrt (scale r)) (rotationPart_unit r)

theorem decomposition (r : Rotor) : comp (boostPart r).rotor (rotationPart r) = r := by
  have hr := root_ne r
  have hh := root_sq r
  apply Subtype.ext
  ext <;> simp [comp,product,boostPart,Boost.rotor,rotationPart,rotation] <;>
    field_simp <;> rw [hh] <;> dsimp [scale] <;> ring

theorem generated (r : Rotor) : Generated r := by
  rw [← decomposition r]
  exact Generated.comp (Generated.boost _) (Generated.rotation _ _ _)

/-- A disk displacement acquires a positive boost using an exact positive square root. -/
def ofDisk (z : Disk) : Boost where
  t := 1 / Real.sqrt (1-Complex.normSq z.val)
  x := z.val.re / Real.sqrt (1-Complex.normSq z.val)
  y := z.val.im / Real.sqrt (1-Complex.normSq z.val)
  positive := one_div_pos.mpr (Real.sqrt_pos.mpr (sub_pos.mpr ((disk_mem z.val).mp z.prop)))
  normalized := by
    have hg := sub_pos.mpr ((disk_mem z.val).mp z.prop)
    have hr := ne_of_gt (Real.sqrt_pos.mpr hg)
    have hh := Real.sq_sqrt (le_of_lt hg)
    field_simp
    rw [hh]
    simp [Complex.normSq_apply]
    ring

theorem Boost.point (b : Boost) : (pose b.rotor).a = (⟨b.x/b.t,b.y/b.t⟩ : ℂ) := by
  have ht := ne_of_gt b.positive
  apply Complex.ext <;> simp [pose,Rotor.point,scale,Boost.rotor] <;> field_simp

theorem Boost.phase (b : Boost) : (pose b.rotor).u = 1 := by
  have ht := ne_of_gt b.positive
  apply Complex.ext <;> simp [pose,Rotor.phase,scale,Boost.rotor,ht]

theorem ofDisk_point (z : Disk) : (pose (ofDisk z).rotor).a = z.val := by
  rw [Boost.point]
  have hr := ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr ((disk_mem z.val).mp z.prop)))
  apply Complex.ext <;> simp [ofDisk] <;> field_simp

theorem rotation_point (a d : ℝ) (h : a^2+d^2=1) : (pose (rotation a d h)).a = 0 := by
  apply Complex.ext <;> simp [pose,point,rotation]

theorem rotation_phase (a d : ℝ) (h : a^2+d^2=1) :
    (pose (rotation a d h)).u = (⟨a^2-d^2,-2*a*d⟩ : ℂ) := by
  simp [pose,phase,scale,rotation,h]

/-- Conversion takes a certified half-phase as data, without selecting an angle branch. -/
def ofPose (p : Pose) (a d : ℝ) (h : a^2+d^2=1) : Rotor :=
  comp (ofDisk ⟨p.a,(disk_mem p.a).mpr p.inside⟩).rotor (rotation a d h)

theorem pose_ofPose (p : Pose) (a d : ℝ) (h : a^2+d^2=1)
    (hphase : (⟨a^2-d^2,-2*a*d⟩ : ℂ) = p.u) : pose (ofPose p a d h) = p := by
  have hp := ofDisk_point (⟨p.a,(disk_mem p.a).mpr p.inside⟩ : Disk)
  have hu := Boost.phase (ofDisk (⟨p.a,(disk_mem p.a).mpr p.inside⟩ : Disk))
  have hz := rotation_point a d h
  have hw := (rotation_phase a d h).trans hphase
  rw [ofPose,pose_comp]
  have hpa : ((pose (ofDisk ⟨p.a,(disk_mem p.a).mpr p.inside⟩).rotor).comp
      (pose (rotation a d h))).a = p.a := by
    simp [Pose.comp,hp,hu,hz,gyroAdd]
  have hpu : ((pose (ofDisk ⟨p.a,(disk_mem p.a).mpr p.inside⟩).rotor).comp
      (pose (rotation a d h))).u = p.u := by
    simp [Pose.comp,hp,hu,hz,hw,gyration]
  have hext : ∀ p q : Pose, p.a = q.a → p.u = q.u → p = q := by
    intro p q ha hu
    cases p
    cases q
    simp_all
  exact hext _ _ hpa hpu

end Orbifold.Clifford.Rotor

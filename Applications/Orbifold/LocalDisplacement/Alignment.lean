import Applications.Orbifold.LocalDisplacement

noncomputable section
open scoped ComplexConjugate
open CategoryTheory
namespace Orbifold.LocalDisplacement
open QuarterTurn (C4 phase_unit)

def phase (g : C4) : ℂ := g.val

theorem phase_norm (g : C4) : Complex.normSq (phase g) = 1 := phase_unit g

theorem phase_conj (g : C4) : conj (phase g) * phase g = 1 := by
  rw [mul_comm, Complex.mul_conj, phase_norm]
  norm_num

theorem rotate_mem (g : C4) {z : ℂ} (h : z ∈ U) : phase g * z ∈ U := by
  simpa [U, map_mul, phase_norm] using h

theorem diagonal (g : C4) (a b : ℂ) :
    gyroAdd (phase g*a) (phase g*b) = phase g * gyroAdd a b := by
  have hc := phase_conj g
  have hd : conj (phase g*a) * (phase g*b) = conj a*b := by
    rw [map_mul]
    calc
      conj (phase g)*conj a*(phase g*b) = (conj (phase g)*phase g)*(conj a*b) := by ring
      _ = conj a*b := by rw [hc]; ring
  rw [gyroAdd,hd,gyroAdd,← mul_add,mul_div_assoc]

theorem rotate_admissible (g : C4) {a b : ℂ} (h : Admissible a b) :
    Admissible (phase g*a) (phase g*b) :=
  ⟨rotate_mem g h.1,rotate_mem g h.2.1,by rw [diagonal]; exact rotate_mem g h.2.2⟩

theorem tree_rotation (g : C4) (t : Bracketing.Tree ℂ) (ht : t.Valid U gyroAdd) :
    (t.map (fun z => phase g*z)).eval gyroAdd = phase g*t.eval gyroAdd ∧
      (t.map (fun z => phase g*z)).Valid U gyroAdd :=
  t.preservation _ _ _ U U (fun _ h => rotate_mem g h)
    (fun x _ y _ _ => (diagonal g x y).symm) ht

/-- Relative alignment remains selected data, not inferred from the endpoint. -/
def endpoint (g : C4) (a b : ℂ) := gyroAdd a (phase g*b)

def Aligned (g : C4) (a b : ℂ) := Admissible a (phase g*b)

def alignedPose (g : C4) (a : ℂ) (ha : a ∈ U) : Pose :=
  ⟨a,phase g,mem_disk ha,phase_norm g⟩

def differential (g : C4) (a b v : ℂ) : ℂ :=
  (1 - (Complex.normSq a : ℂ))*phase g / (1 + conj a*phase g*b)^2 * v

theorem endpoint_derivative (g : C4) {a b : ℂ} (ha : a ∈ U) (hb : b ∈ U) :
    HasDerivAt (endpoint g a) (differential g a b 1) b := by
  have h := Pose.hasDerivAt_mobius (alignedPose g a ha) ⟨b,(disk_mem _).mpr (mem_disk hb)⟩
  convert h using 1
  · funext z
    simp [endpoint,gyroAdd,alignedPose,Pose.mobius,mul_assoc]
  · simp [differential,Pose.derivative,alignedPose]

/-- Independently changing representatives requires changing the relative label. -/
def relabel (h k g : C4) : C4 := h*g*k⁻¹

theorem relabel_phase (h k g : C4) : phase (relabel h k g)*phase k = phase h*phase g := by
  change (((h*g*k⁻¹)*k).val : ℂ) = ((h*g).val : ℂ)
  rw [mul_assoc (h*g), inv_mul_cancel, mul_one]

theorem endpoint_relabel (h k g : C4) (a b : ℂ) :
    endpoint (relabel h k g) (phase h*a) (phase k*b) = phase h * endpoint g a b := by
  unfold endpoint
  have he : phase (relabel h k g)*(phase k*b) = phase h*(phase g*b) := by
    rw [← mul_assoc,relabel_phase,mul_assoc]
  rw [he,diagonal]

theorem aligned_relabel (h k g : C4) {a b : ℂ} (hab : Aligned g a b) :
    Aligned (relabel h k g) (phase h*a) (phase k*b) := by
  have he : phase (relabel h k g)*(phase k*b) = phase h*(phase g*b) := by
    rw [← mul_assoc,relabel_phase,mul_assoc]
  unfold Aligned
  rw [he]
  exact rotate_admissible h hab

theorem differential_relabel (h k g : C4) (a b v : ℂ) :
    differential (relabel h k g) (phase h*a) (phase k*b) (phase k*v) =
      phase h * differential g a b v := by
  have hd : conj (phase h*a)*phase (relabel h k g)*(phase k*b) = conj a*phase g*b := by
    rw [map_mul]
    calc
      conj (phase h)*conj a*phase (relabel h k g)*(phase k*b) =
          (conj (phase h))* (phase (relabel h k g)*phase k)*conj a*b := by ring
      _ = conj a*phase g*b := by
        rw [relabel_phase]
        calc
          _ = (conj (phase h)*phase h)*conj a*phase g*b := by ring
          _ = _ := by rw [phase_conj]; ring
  unfold differential
  rw [map_mul,phase_norm,one_mul,hd]
  calc
    _ = ((1-(Complex.normSq a : ℂ))*(phase (relabel h k g)*phase k) /
        (1+conj a*phase g*b)^2)*v := by ring
    _ = _ := by rw [relabel_phase]; ring

/-- The actual groupoid arrow selected by a relative label. -/
def alignmentArrow (g : C4) (b : Disk) :
    (↑b : ActionCategory C4 Disk) ⟶ (↑(g • b) : ActionCategory C4 Disk) :=
  CategoryTheory.Functor.Elements.homMk g rfl

theorem alignmentArrow_label (g : C4) (b : Disk) : (alignmentArrow g b).hom = g := rfl

/-- Two locally admitted endpoint operations, with the selected derivative in
its leaf input. This transports a tangent differential, not a path field. -/
theorem composed_derivative (g h : C4) {a b c : ℂ}
    (ha : a ∈ U) (hb : b ∈ U) (hc : c ∈ U) (hin : endpoint h b c ∈ U) :
    HasDerivAt (fun z => endpoint g a (endpoint h b z))
      (differential g a (endpoint h b c) (differential h b c 1)) c := by
  have hout := endpoint_derivative g ha hin
  have hinner := endpoint_derivative h hb hc
  convert hout.comp c hinner using 1 <;> first | rfl | (dsimp [differential]; ring)

end Orbifold.LocalDisplacement

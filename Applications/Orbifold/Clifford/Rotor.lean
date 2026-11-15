import Applications.Orbifold.Clifford.Coordinates

/-! Normalized even Clifford coordinates and their exact disk interpretation.
This carrier does not assert membership in Mathlib's generated spin group. -/
noncomputable section
open Matrix
namespace Orbifold.Clifford

/-- Certified invertible even elements in the four-coordinate realization. -/
abbrev Rotor := {r : Coordinates // norm r = 1}

namespace Rotor

def identity : Rotor := ⟨scalar 1, by norm_num [norm,scalar]⟩
def comp (r s : Rotor) : Rotor := ⟨product r.val s.val, by rw [norm_product,r.prop,s.prop]; norm_num⟩
def inv (r : Rotor) : Rotor := ⟨reversed r.val, by simpa [norm,reversed] using r.prop⟩
def clifford (r : Rotor) : Algebra := value r.val

@[simp] theorem clifford_identity : clifford identity = 1 := by simp [clifford,identity]
@[simp] theorem clifford_comp (r s : Rotor) : clifford (comp r s) = clifford r * clifford s :=
  value_product _ _
theorem clifford_inv (r : Rotor) : clifford (inv r) = CliffordAlgebra.reverse (clifford r) :=
  value_reversed _
theorem inv_comp (r : Rotor) : comp (inv r) r = identity := by
  apply Subtype.ext
  exact (reversed_product r.val).trans (congrArg scalar r.prop)
theorem comp_inv (r : Rotor) : comp r (inv r) = identity := by
  apply Subtype.ext
  exact (product_reversed r.val).trans (congrArg scalar r.prop)
theorem identity_comp (r : Rotor) : comp identity r = r := by
  apply Subtype.ext; apply value_injective
  change clifford (comp identity r) = clifford r
  simp
theorem comp_identity (r : Rotor) : comp r identity = r := by
  apply Subtype.ext; apply value_injective
  change clifford (comp r identity) = clifford r
  simp
theorem comp_assoc (r s t : Rotor) : comp (comp r s) t = comp r (comp s t) :=
  Subtype.ext (product_assoc _ _ _)

/-- The unit is constructed from the actual Clifford product and reverse. -/
def unit (r : Rotor) : Algebraˣ where
  val := clifford r
  inv := clifford (inv r)
  val_inv := by rw [← clifford_comp,comp_inv,clifford_identity]
  inv_val := by rw [← clifford_comp,inv_comp,clifford_identity]

def scale (r : Rotor) : ℝ := r.val.a^2+r.val.d^2

theorem scale_pos (r : Rotor) : 0 < scale r := by
  have h := r.prop
  dsimp [norm] at h
  dsimp [scale]
  nlinarith [sq_nonneg r.val.b,sq_nonneg r.val.c]

def point (r : Rotor) : ℂ :=
  ⟨(r.val.a*r.val.b+r.val.c*r.val.d)/scale r,
   (r.val.a*r.val.c-r.val.b*r.val.d)/scale r⟩
def phase (r : Rotor) : ℂ :=
  ⟨(r.val.a^2-r.val.d^2)/scale r, -2*r.val.a*r.val.d/scale r⟩

theorem point_gap (r : Rotor) : 1 - Complex.normSq (point r) = 1 / scale r := by
  have hn := r.prop
  have hs := ne_of_gt (scale_pos r)
  dsimp [norm] at hn
  simp [point,Complex.normSq_apply]
  field_simp
  dsimp [scale]
  nlinarith [sq_nonneg r.val.b,sq_nonneg r.val.c]

theorem point_inside (r : Rotor) : Complex.normSq (point r) < 1 := by
  have h := point_gap r
  have hp : 0 < 1 / scale r := one_div_pos.mpr (scale_pos r)
  linarith

theorem phase_unit (r : Rotor) : Complex.normSq (phase r) = 1 := by
  have hs := ne_of_gt (scale_pos r)
  simp [phase,Complex.normSq_apply]
  field_simp
  dsimp [scale]
  ring

def pose (r : Rotor) : Pose := ⟨point r,phase r,point_inside r,phase_unit r⟩

theorem sandwich_encode (r : Rotor) : sandwichMatrix r.val = Lorentz.encode (pose r) := by
  have hn := r.prop
  have hs := ne_of_gt (scale_pos r)
  have hg := point_gap r
  dsimp [norm] at hn
  simp only [Lorentz.encode, Lorentz.boost, Lorentz.rotation, pose, hg]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sandwichMatrix, point, phase, Matrix.mul_apply,Fin.sum_univ_three,
      -Complex.ofReal_div,-Complex.ofReal_sub,-Complex.ofReal_mul,-Complex.ofReal_add] <;>
    field_simp <;> dsimp [scale] <;>
    solve
    | ring
    | linear_combination (r.val.a^2+r.val.d^2)*(r.val.a^2-r.val.d^2)*hn
    | linear_combination r.val.a*r.val.d*(r.val.a^2+r.val.d^2)*hn
    | linear_combination -r.val.a*r.val.d*(r.val.a^2+r.val.d^2)*hn

def realized (r : Rotor) : Lorentz.Realized :=
  ⟨sandwichMatrix r.val, ⟨pose r,(sandwich_encode r).symm⟩⟩

theorem realized_ofPose (r : Rotor) : realized r = Lorentz.Realized.ofPose (pose r) :=
  Subtype.ext (sandwich_encode r)
@[simp] theorem decode_realized (r : Rotor) : (realized r).decode = pose r := by
  rw [realized_ofPose,Lorentz.Realized.decode_ofPose]

theorem matrix_comp (r s : Rotor) :
    sandwichMatrix (comp r s).val = sandwichMatrix r.val * sandwichMatrix s.val := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [comp,product,sandwichMatrix,Matrix.mul_apply,Fin.sum_univ_three] <;> ring

@[simp] theorem realized_identity : realized identity = Lorentz.Realized.identity := by
  apply Subtype.ext
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [realized,identity,scalar,sandwichMatrix,Lorentz.Realized.identity]

theorem realized_comp (r s : Rotor) : realized (comp r s) = (realized r).comp (realized s) :=
  Subtype.ext (matrix_comp r s)

theorem pose_comp (r s : Rotor) : pose (comp r s) = (pose r).comp (pose s) := by
  rw [← decode_realized,realized_comp,Lorentz.Realized.decode_comp,decode_realized,decode_realized]

theorem realized_inv (r : Rotor) : realized (inv r) = (realized r).inv := by
  have h := congrArg (fun A => A.comp ((realized r).inv))
    (congrArg realized (inv_comp r))
  rw [realized_comp,realized_identity,Lorentz.Realized.comp_assoc,
    Lorentz.Realized.comp_inv,Lorentz.Realized.comp_identity,
    Lorentz.Realized.identity_comp] at h
  exact h

def composeList : List Rotor → Rotor
  | [] => identity
  | r::rs => comp r (composeList rs)

theorem realized_composeList (rs : List Rotor) :
    realized (composeList rs) = Lorentz.Realized.composeList (rs.map realized) := by
  induction rs with
  | nil => exact realized_identity
  | cons r rs ih => simpa [composeList,Lorentz.Realized.composeList] using
      (realized_comp r (composeList rs)).trans (congrArg ((realized r).comp) ih)

def neg (r : Rotor) : Rotor := ⟨⟨-r.val.a,-r.val.b,-r.val.c,-r.val.d⟩, by
  simpa [norm] using r.prop⟩

@[simp] theorem clifford_neg (r : Rotor) : clifford (neg r) = -clifford r := by
  simp [clifford,value_expansion,neg]
  abel

theorem realized_neg (r : Rotor) : realized (neg r) = realized r := by
  apply Subtype.ext
  ext i j; fin_cases i <;> fin_cases j <;> simp [realized,neg,sandwichMatrix]

theorem kernel (r : Rotor) : realized r = Lorentz.Realized.identity ↔
    r = identity ∨ r = neg identity := by
  constructor
  · intro h
    have hm := congrArg Subtype.val h
    have h00 := congrArg (fun M : Lorentz.Matrix3 => M 0 0) hm
    have h11 := congrArg (fun M : Lorentz.Matrix3 => M 1 1) hm
    simp [realized,sandwichMatrix,Lorentz.Realized.identity] at h00 h11
    have hn := r.prop
    dsimp [norm] at hn
    have hb : r.val.b = 0 := by nlinarith [sq_nonneg r.val.b,sq_nonneg r.val.c]
    have hc : r.val.c = 0 := by nlinarith [sq_nonneg r.val.b,sq_nonneg r.val.c]
    have hd : r.val.d = 0 := by nlinarith [sq_nonneg r.val.d]
    have ha : r.val.a = 1 ∨ r.val.a = -1 := by
      have hh : (r.val.a-1)*(r.val.a+1)=0 := by nlinarith
      rcases mul_eq_zero.mp hh with hh | hh
      · left; linarith
      · right; linarith
    rcases ha with ha | ha
    · left; apply Subtype.ext; ext <;> simp [identity,scalar,ha,hb,hc,hd]
    · right; apply Subtype.ext; ext <;> simp [identity,scalar,neg,ha,hb,hc,hd]
  · rintro (rfl | rfl)
    · exact realized_identity
    · rw [realized_neg,realized_identity]

theorem neg_identity_comp (r : Rotor) : comp (neg identity) r = neg r := by
  apply Subtype.ext
  ext <;> simp [comp,neg,identity,scalar,product]

theorem realized_eq_iff (r s : Rotor) : realized r = realized s ↔ r = s ∨ r = neg s := by
  constructor
  · intro h
    have hk : realized (comp r (inv s)) = Lorentz.Realized.identity := by
      rw [realized_comp,h,realized_inv,Lorentz.Realized.comp_inv]
    rcases (kernel _).mp hk with hh | hh
    · left
      have he := congrArg (fun t => comp t s) hh
      simpa only [comp_assoc,inv_comp,comp_identity,identity_comp] using he
    · right
      have he := congrArg (fun t => comp t s) hh
      simpa only [comp_assoc,inv_comp,comp_identity,neg_identity_comp] using he
  · rintro (rfl | rfl)
    · rfl
    · exact realized_neg s

/-- Equality of observations, proved above to be exactly the sign relation. -/
def signSetoid : Setoid Rotor := Setoid.ker realized
abbrev Geometry := Quotient signSetoid

def quotientRealized : Geometry → Lorentz.Realized := Quotient.lift realized (fun _ _ h => h)

theorem quotientRealized_injective : Function.Injective quotientRealized := by
  intro r s h
  induction r using Quotient.inductionOn with | _ r =>
    induction s using Quotient.inductionOn with | _ s =>
      exact Quotient.sound h

theorem quotient_sign (r : Rotor) :
    (Quotient.mk signSetoid (neg r) : Geometry) = Quotient.mk signSetoid r :=
  Quotient.sound (realized_neg r)

theorem pose_eq_iff (r s : Rotor) : pose r = pose s ↔ r = s ∨ r = neg s := by
  rw [← realized_eq_iff]
  constructor
  · intro h; rw [realized_ofPose,realized_ofPose,h]
  · intro h; simpa using congrArg Lorentz.Realized.decode h

/-- The selected lift acts on any valid point, with exactly the native derivative. -/
theorem point_action (r : Rotor) (z : Disk) :
    Lorentz.pointAction (sandwichMatrix r.val) z = ((pose r).act z : ℂ) := by
  rw [sandwich_encode,Lorentz.pointAction_encode]

theorem frame_action (r : Rotor) (z : Disk) (v : ℂ) :
    Lorentz.frameAction (sandwichMatrix r.val) z v = (pose r).derivative z.val * v := by
  rw [sandwich_encode,Lorentz.frameAction_encode]

theorem point_observation (r : Rotor) : Lorentz.point (sandwichMatrix r.val) = (pose r).a := by
  rw [sandwich_encode,Lorentz.point_encode]
theorem frame_observation (r : Rotor) (w : ℂ) :
    Lorentz.frame (sandwichMatrix r.val) w = (pose r).frame w := by
  rw [sandwich_encode,Lorentz.frame_encode]

/-- Point and the entire oriented frame are exactly the geometric observations. -/
theorem observations_eq_iff (r s : Rotor) :
    ((pose r).a = (pose s).a ∧ ∀ w, (pose r).frame w = (pose s).frame w) ↔
      r = s ∨ r = neg s := by
  rw [← pose_eq_iff]
  constructor
  · rintro ⟨ha,hf⟩
    have hh := hf 1
    simp only [Pose.frame,mul_one,ha] at hh
    have hg : (1 - (Complex.normSq (pose s).a : ℂ)) ≠ 0 := by
      exact_mod_cast ne_of_gt (sub_pos.mpr (pose s).inside)
    have hu : (pose r).u = (pose s).u := by
      have he := congrArg (fun z : ℂ => z*2) hh
      field_simp at he
      exact he
    have hext : ∀ p q : Pose, p.a = q.a → p.u = q.u → p = q := by
      intro p q ha hu; cases p; cases q; simp_all
    exact hext _ _ ha hu
  · intro h; simp [h]

def quotientComp (r s : Geometry) : Geometry := Quotient.liftOn₂ r s
  (fun r s => Quotient.mk signSetoid (comp r s)) (by
    intro r s r' s' hr hs
    apply Quotient.sound
    change realized (comp r s) = realized (comp r' s')
    rw [realized_comp,realized_comp,hr,hs])

theorem quotientComp_realized (r s : Geometry) :
    quotientRealized (quotientComp r s) = (quotientRealized r).comp (quotientRealized s) := by
  induction r using Quotient.inductionOn with | _ r =>
    induction s using Quotient.inductionOn with | _ s => exact realized_comp r s

theorem unit_sandwich (r : Rotor) (X : Lorentz.Vector) :
    (r.unit : Algebra) * primal X * (r.unit⁻¹ : Algebraˣ) =
      primal (sandwichMatrix r.val *ᵥ X) := by
  change clifford r * primal X * clifford (inv r) = _
  rw [clifford_inv]
  exact sandwich_primal _ _

theorem pose_composeList (rs : List Rotor) :
    (composeList rs).pose = Pose.composeList (rs.map pose) := by
  rw [← decode_realized,realized_composeList,Lorentz.Realized.decode_composeList,List.map_map]
  simp only [decode_realized,Function.comp_def]

theorem finite_frame (rs : List Rotor) (w : ℂ) :
    Lorentz.frame (sandwichMatrix (composeList rs).val) w =
      (Pose.composeList (rs.map pose)).frame w := by
  rw [frame_observation,pose_composeList]

theorem finite_pointAction (rs : List Rotor) (z : Disk) :
    Lorentz.pointAction (sandwichMatrix (composeList rs).val) z =
      ((Pose.composeList (rs.map pose)).act z : ℂ) := by
  rw [point_action,pose_composeList]

theorem finite_frameAction (rs : List Rotor) (z : Disk) (v : ℂ) :
    Lorentz.frameAction (sandwichMatrix (composeList rs).val) z v =
      (Pose.composeList (rs.map pose)).derivative z.val * v := by
  rw [frame_action,pose_composeList]

end Rotor
end Orbifold.Clifford

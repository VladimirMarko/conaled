import Applications.Orbifold.Clifford.Generators
import Examples.LorentzMotion

/-! Actual Clifford lifts consumed through the existing motion specification.
The independent matrices and expected composed frame come from LorentzMotion. -/
noncomputable section
open Orbifold Orbifold.Clifford Matrix CategoryTheory
namespace Examples.CliffordMotion

@[reducible] def representation : Squares.Rep :=
  ⟨Rotor, Motion diskForm, fun r => r.pose.motion⟩

def compositionSquare : Squares.Square (Squares.product representation representation) representation where
  impl rs := rs.1.comp rs.2
  spec pq := pq.1 * pq.2
  commutes rs := by
    change (rs.1.comp rs.2).pose.motion = rs.1.pose.motion * rs.2.pose.motion
    rw [Rotor.pose_comp,Pose.motion_comp]

def agreement := Squares.synchronize compositionSquare
  DiskRealizations.poseCompositionSquare (fun _ => rfl)

def first : Rotor := ⟨⟨3/4,1/4,-1/4,-3/4⟩,by norm_num [Clifford.norm]⟩

def second : Rotor := ⟨⟨8/Real.sqrt 75,1/Real.sqrt 75,2/Real.sqrt 75,-4/Real.sqrt 75⟩,by
  have hs : Real.sqrt 75 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hh : (Real.sqrt 75)^2 = 75 := Real.sq_sqrt (by norm_num)
  dsimp [Clifford.norm]
  field_simp
  rw [hh]
  norm_num⟩

theorem first_realized : first.realized = LorentzMotion.first := by
  apply Subtype.ext
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [Rotor.realized,first,sandwichMatrix,LorentzMotion.first,LorentzMotion.firstMatrix]

theorem second_realized : second.realized = LorentzMotion.second := by
  have hs : Real.sqrt 75 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hh : (Real.sqrt 75)^2 = 75 := Real.sq_sqrt (by norm_num)
  apply Subtype.ext
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Rotor.realized,second,sandwichMatrix,LorentzMotion.second,LorentzMotion.secondMatrix] <;>
    field_simp <;> nlinarith

example : first.comp second ≠ second.comp first := by
  intro h
  have hm := congrArg Rotor.realized h
  rw [Rotor.realized_comp,Rotor.realized_comp,first_realized,second_realized] at hm
  have he := congrArg (fun A : Lorentz.Realized => A.val 0 1) hm
  norm_num [Lorentz.Realized.comp,LorentzMotion.first,LorentzMotion.second,
    LorentzMotion.firstMatrix,LorentzMotion.secondMatrix,Matrix.mul_apply,Fin.sum_univ_three] at he

theorem composed_point : Lorentz.point (sandwichMatrix (first.comp second).val) = (1/11 : ℂ) := by
  have h := congrArg Subtype.val (Rotor.realized_comp first second)
  rw [first_realized,second_realized] at h
  change sandwichMatrix (first.comp second).val = LorentzMotion.first.val * LorentzMotion.second.val at h
  rw [h,LorentzMotion.composed_point]

theorem composed_frame (w : ℂ) :
    Lorentz.frame (sandwichMatrix (first.comp second).val) w = ((-48+36*Complex.I)/121)*w := by
  have h := congrArg Subtype.val (Rotor.realized_comp first second)
  rw [first_realized,second_realized] at h
  change sandwichMatrix (first.comp second).val = LorentzMotion.first.val * LorentzMotion.second.val at h
  rw [h,LorentzMotion.composed_full_frame]

/-- Any finite sequence of independently supplied certified rotors. -/
theorem finite_motion (rs : List Rotor) :
    (Rotor.composeList rs).pose.motion = (rs.map (fun r => r.pose.motion)).prod := by
  induction rs with
  | nil => simp [Rotor.composeList,← Rotor.decode_realized,Rotor.realized_identity,
      Lorentz.Realized.decode_identity,Pose.motion_identity]
  | cons r rs ih =>
      simpa [Rotor.composeList,Rotor.pose_comp,Pose.motion_comp] using
        congrArg (fun m => r.pose.motion*m) ih

example (rs : List Rotor) (z : Disk) (v : ℂ) :
    Lorentz.frameAction (sandwichMatrix (Rotor.composeList rs).val) z v =
      (Rotor.composeList rs).pose.derivative z.val * v := Rotor.frame_action _ _ _

example (r : Rotor) (z : Disk) (v : ℂ) :
    Lorentz.frameAction r.inv.realized.val (r.realized.act z)
      (Lorentz.frameAction r.realized.val z v) = v := by
  rw [Rotor.realized_inv]
  exact Lorentz.frameAction_inverse _ _ _

/-- This is a lift of a geometric quarter turn, with its sign retained. -/
def quarter : Rotor := Rotor.rotation (1/Real.sqrt 2) (-1/Real.sqrt 2) (by
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hh : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp
  rw [hh]
  norm_num)
def half : Rotor := Rotor.rotation 0 (-1) (by norm_num)

theorem quarter_squared : quarter.comp quarter = half := by
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hh : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  apply Subtype.ext
  ext <;> simp [quarter,half,Rotor.comp,Rotor.rotation,product] <;> field_simp <;> nlinarith

theorem half_squared : half.comp half = Rotor.neg Rotor.identity := by
  apply Subtype.ext
  ext <;> norm_num [half,Rotor.comp,Rotor.rotation,Rotor.identity,Rotor.neg,Clifford.scalar,product]

theorem full_turn_sign : Rotor.composeList [quarter,quarter,quarter,quarter] = Rotor.neg Rotor.identity := by
  simp only [Rotor.composeList,Rotor.comp_identity]
  rw [← Rotor.comp_assoc,quarter_squared,half_squared]

example : Rotor.composeList [quarter,quarter,quarter,quarter] ≠ Rotor.identity := by
  rw [full_turn_sign]
  intro h
  have ha := congrArg (fun r : Rotor => r.val.a) h
  norm_num [Rotor.neg,Rotor.identity,Clifford.scalar] at ha

example : (Rotor.composeList [quarter,quarter,quarter,quarter]).realized = Lorentz.Realized.identity := by
  rw [full_turn_sign,Rotor.realized_neg,Rotor.realized_identity]

example (r : Rotor) (z : Disk) (v : ℂ) :
    Lorentz.frameAction (sandwichMatrix r.neg.val) z v =
      Lorentz.frameAction (sandwichMatrix r.val) z v := by
  have h := congrArg Subtype.val (Rotor.realized_neg r)
  change sandwichMatrix r.neg.val = sandwichMatrix r.val at h
  rw [h]

/-- The null and zero multivectors cannot be admitted by the norm certificate. -/
example : ¬ ∃ r : Rotor, r.val = ⟨1,1,0,0⟩ := by
  rintro ⟨r,h⟩
  have hn := r.prop
  rw [h] at hn
  norm_num [Clifford.norm] at hn
example : ¬ ∃ r : Rotor, r.val = Clifford.scalar 0 := by
  rintro ⟨r,h⟩
  have hn := r.prop
  rw [h] at hn
  norm_num [Clifford.norm,Clifford.scalar] at hn

theorem quarter_realized : quarter.realized =
    Lorentz.Realized.ofPose (QuarterTurn.rotation Orbifolds.QuarterTurn.quarterTurn) := by
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hh : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  apply Subtype.ext
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Rotor.realized,quarter,Rotor.rotation,sandwichMatrix,Lorentz.Realized.ofPose,
      Lorentz.encode,Lorentz.boost,Lorentz.rotation,QuarterTurn.rotation,
      Orbifolds.QuarterTurn.quarterTurn] <;>
    field_simp <;> nlinarith

/-- A selected arrow label is retained alongside the chosen Clifford lift. -/
def selected (k : AtlasIsotropy.C2) := (AtlasIsotropy.selectedLabel k, quarter)

example (k : AtlasIsotropy.C2) : (selected k).2.realized =
    Lorentz.Realized.ofPose (QuarterTurn.rotation (selected k).1.1) := quarter_realized

example : (selected 1).2.clifford = (selected AtlasIsotropy.kernel).2.clifford := rfl
example : selected 1 ≠ selected AtlasIsotropy.kernel := by
  intro h
  have hk := congrArg (fun x => x.1.2 (0 : Fin 2)) h
  norm_num [selected,AtlasIsotropy.selectedLabel,AtlasIsotropy.close,
    AtlasIsotropy.kernel,Equiv.swap_apply_def] at hk

example (r : Rotor) {p q : ActionCategory QuarterTurn.C4 Pose} (f : p ⟶ q) :
    ((QuarterTurn.incrementFunctor r.pose).map f).hom = f.hom := QuarterTurn.increment_label _ f

theorem double_full_turn :
    (Rotor.composeList [quarter,quarter,quarter,quarter]).comp
      (Rotor.composeList [quarter,quarter,quarter,quarter]) = Rotor.identity := by
  rw [full_turn_sign]
  apply Subtype.ext
  ext <;> norm_num [Rotor.comp,Rotor.neg,Rotor.identity,Clifford.scalar,product]

example (X : Lorentz.Vector) :
    first.clifford * primal X * CliffordAlgebra.reverse first.clifford =
      primal (LorentzMotion.firstMatrix *ᵥ X) := by
  have h := congrArg Subtype.val first_realized
  change sandwichMatrix first.val = LorentzMotion.firstMatrix at h
  simpa only [Rotor.clifford,h] using sandwich_primal first.val X

end Examples.CliffordMotion
